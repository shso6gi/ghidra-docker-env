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
    _object_target_key_is_specific,
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


def _write_phase2_run_manifest(
    root: Path,
    *,
    extra_args: str = "--no-completed-recovery-proofs",
    run_kind: str = "phase2_function_call_full_matrix_pre_producer",
    expected_final_result_movement: str = "none",
    expected_reason_movement: str = "call_effect_summary_proof/object_evidence_collected/pending_proof",
    validation_skip_completed: str = "0",
    phase2_run_expected_movement_gate: str = "1",
):
    root.mkdir(parents=True, exist_ok=True)
    (root / "run_manifest.txt").write_text(
        "\n".join(
            [
                "run_kind=" + run_kind,
                "target_reason=equivalence_blocking_unsafety",
                "expected_final_result_movement=" + expected_final_result_movement,
                "expected_reason_movement=" + expected_reason_movement,
                "validation_skip_completed=" + validation_skip_completed,
                "function_call_extra_equiv_args=" + extra_args,
                "phase2_run_expected_movement_gate=" + phase2_run_expected_movement_gate,
            ]
        )
    )


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
        ("function_ref", ("function", "B10", 0x401000)),
        (
            "pcode_op",
            "B10",
            ("function_entry", "ram", 0x401000),
            ("seq_target", "ram", 0x401020),
            31,
            7,
            8,
            0,
        ),
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


def test_phase2_call_effect_specificity_rejects_legacy_pcode_ref():
    legacy_target = (
        "unsupported_call_effect",
        "function1",
        ("function_ref", ("function", "B10", 0x401000)),
        ("pcode_op", 0x401020, 31, 7, 0, "CALLIND"),
        None,
        ("typed_target_expression", ("storage", ("register", "a0", 8))),
        7,
        "target_identity_unavailable",
    )
    full_target = (
        "unsupported_call_effect",
        "function1",
        ("function_ref", ("function", "B10", 0x401000)),
        (
            "pcode_op",
            "B10",
            ("function_entry", "ram", 0x401000),
            ("seq_target", "ram", 0x401020),
            31,
            7,
            8,
            0,
        ),
        None,
        ("typed_target_expression", ("storage", ("register", "a0", 8))),
        7,
        "target_identity_unavailable",
    )

    assert _object_target_key_is_specific(legacy_target) is False
    assert _object_target_key_is_specific(full_target) is True


def test_phase2_call_effect_specificity_requires_canonical_function_binary_id():
    full_target = _pending_reason().object_target_key
    missing_binary_target = (
        full_target[0],
        full_target[1],
        ("function_ref", ("function", None, 0x401000)),
        *full_target[3:],
    )
    program_uid_target = (
        full_target[0],
        full_target[1],
        ("function_ref", ("function", 10, 0x401000)),
        *full_target[3:],
    )
    code_address_program_uid_target = (
        full_target[0],
        full_target[1],
        ("function_ref", ("code_address", 10, 0x401000)),
        *full_target[3:],
    )

    assert _object_target_key_is_specific(missing_binary_target) is False
    assert _object_target_key_is_specific(program_uid_target) is False
    assert _object_target_key_is_specific(code_address_program_uid_target) is False
    assert _object_target_key_is_specific(full_target) is True


def test_phase2_call_effect_specificity_requires_integer_effect_ordinal():
    full_target = _pending_reason().object_target_key
    missing_ordinal_target = full_target[:6] + (None,) + full_target[7:]
    text_ordinal_target = full_target[:6] + ("7",) + full_target[7:]
    bool_ordinal_target = full_target[:6] + (True,) + full_target[7:]

    assert _object_target_key_is_specific(missing_ordinal_target) is False
    assert _object_target_key_is_specific(text_ordinal_target) is False
    assert _object_target_key_is_specific(bool_ordinal_target) is False
    assert _object_target_key_is_specific(full_target) is True


def _old_blocking_reason():
    return make_unknown_reason(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY,
        decision_effect="blocks_equivalence",
        reason_scope="function",
    )


def _write_all_representative_logs(root: Path, payload_by_function=None):
    payload_by_function = payload_by_function or {}
    _write_phase2_run_manifest(root)
    for _entry_id, function, _binary_pair, left, right in REPRESENTATIVES:
        payload = payload_by_function.get(function) or _payload(function, left, right, None, [_pending_reason()])
        _write_log(root, function, left, right, payload)


def _write_all_baseline_representative_logs(root: Path, payload_by_function=None):
    payload_by_function = payload_by_function or {}
    for _entry_id, function, _binary_pair, left, right in REPRESENTATIVES:
        payload = payload_by_function.get(function) or _payload(function, left, right, None, [_old_blocking_reason()])
        _write_log(root, function, left, right, payload)


def _ready_phase2_manifest(tmp_path):
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
    return json.loads(path.read_text())


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
    assert manifest["phase2_producer_config_gate"]["passed"] is True
    assert manifest["overall_baseline_comparison_gate"]["passed"] is True
    assert {entry["movement_status"] for entry in manifest["entries"]} == {"expected_movement"}
    validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_validator_rejects_ready_true_with_failed_entry(tmp_path):
    manifest = _ready_phase2_manifest(tmp_path)
    manifest["entries"][0]["movement_status"] = "failed"
    manifest["entries"][0]["failed_kinds"] = ["target_reason_missing"]
    manifest["phase2_ready"] = True

    with pytest.raises(ValueError, match="target_reason_missing"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_validator_rejects_ready_true_with_tampered_summary_count(tmp_path):
    manifest = _ready_phase2_manifest(tmp_path)
    manifest["movement_summary"]["passed"] = 999
    manifest["phase2_ready"] = True

    with pytest.raises(ValueError, match="movement_summary_passed_mismatch"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_validator_rejects_ready_true_without_baseline_gate(tmp_path):
    manifest = _ready_phase2_manifest(tmp_path)
    manifest.pop("overall_baseline_comparison_gate")
    manifest["phase2_ready"] = True

    with pytest.raises(ValueError, match="overall_baseline_comparison_gate_missing"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_validator_rejects_ready_true_without_producer_gate(tmp_path):
    manifest = _ready_phase2_manifest(tmp_path)
    manifest.pop("phase2_producer_config_gate")
    manifest["phase2_ready"] = True

    with pytest.raises(ValueError, match="phase2_producer_config_gate_missing"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_rejects_missing_phase2_producer_manifest(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(current_root)
    (current_root / "run_manifest.txt").unlink()

    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir,
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase2_ready"] is False
    assert manifest["phase2_producer_config_gate"]["passed"] is False
    assert "phase2_producer_run_manifest_missing" in manifest["movement_summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="phase2_producer_run_manifest_missing"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_rejects_phase2_producer_manifest_without_completed_recovery_flag(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(current_root)
    _write_phase2_run_manifest(current_root, extra_args="")

    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir,
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase2_ready"] is False
    assert manifest["phase2_producer_config_gate"]["passed"] is False
    assert "phase2_producer_recovery_flags_missing" in manifest["movement_summary"]["failed_kinds"]
    root_gate = manifest["phase2_producer_config_gate"]["roots"]["function_call"]
    assert root_gate["missing_required_equivalence_args"] == ["--no-completed-recovery-proofs"]
    with pytest.raises(ValueError, match="phase2_producer_recovery_flags_missing"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_producer_manifest_does_not_require_no_retry_phases(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(current_root)
    _write_phase2_run_manifest(current_root, extra_args="--no-completed-recovery-proofs")

    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir,
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase2_producer_config_gate"]["passed"] is True
    root_gate = manifest["phase2_producer_config_gate"]["roots"]["function_call"]
    assert root_gate["missing_required_equivalence_args"] == []
    assert "--no-retry-phases" not in root_gate["required_equivalence_args"]


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("run_kind", "phase2_function_call_full_matrix_current"),
        ("expected_final_result_movement", "normal-current-baseline-comparison"),
        ("expected_reason_movement", "none-required-by-this-wrapper"),
        ("validation_skip_completed", "1"),
        ("phase2_run_expected_movement_gate", "0"),
    ],
)
def test_phase2_rejects_phase2_producer_manifest_value_mismatch(tmp_path, field, value):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(current_root)
    _write_phase2_run_manifest(current_root, **{field: value})

    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir,
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase2_ready"] is False
    assert manifest["phase2_producer_config_gate"]["passed"] is False
    assert "phase2_producer_run_manifest_values_mismatch" in manifest["movement_summary"]["failed_kinds"]
    root_gate = manifest["phase2_producer_config_gate"]["roots"]["function_call"]
    assert field in root_gate["mismatched_required_run_manifest_values"]
    with pytest.raises(ValueError, match="phase2_producer_run_manifest_values_mismatch"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_validator_rejects_ready_true_with_failed_baseline_gate(tmp_path):
    manifest = _ready_phase2_manifest(tmp_path)
    manifest["overall_baseline_comparison_gate"] = {
        "passed": False,
        "status": "failed",
        "failed_kinds": ["baseline_log_root_missing"],
    }
    manifest["phase2_ready"] = True

    with pytest.raises(ValueError, match="baseline_log_root_missing"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_validator_rejects_non_mapping_entry(tmp_path):
    manifest = _ready_phase2_manifest(tmp_path)
    manifest["entries"][0] = "not-a-mapping"
    manifest["phase2_ready"] = True

    with pytest.raises(ValueError, match="entry_not_mapping"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_validator_rejects_duplicate_representative_entry_id(tmp_path):
    manifest = _ready_phase2_manifest(tmp_path)
    manifest["entries"][1]["entry_id"] = manifest["entries"][0]["entry_id"]
    manifest["phase2_ready"] = True

    with pytest.raises(ValueError, match="representative_entry_duplicate_id"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_validator_rejects_wrong_baseline_git_head(tmp_path):
    manifest = _ready_phase2_manifest(tmp_path)
    manifest["baseline_git_head"] = "wrong-head"
    manifest["phase2_ready"] = True

    with pytest.raises(ValueError, match="baseline_git_head_mismatch"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_validator_rejects_wrong_manifest_kind(tmp_path):
    manifest = _ready_phase2_manifest(tmp_path)
    manifest["manifest_kind"] = "wrong-kind"
    manifest["phase2_ready"] = True

    with pytest.raises(ValueError, match="manifest_kind_mismatch"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_validator_rejects_wrong_baseline_id(tmp_path):
    manifest = _ready_phase2_manifest(tmp_path)
    manifest["baseline_id"] = "wrong-baseline"
    manifest["phase2_ready"] = True

    with pytest.raises(ValueError, match="baseline_id_mismatch"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_validator_rejects_missing_entries(tmp_path):
    manifest = _ready_phase2_manifest(tmp_path)
    manifest.pop("entries")
    manifest["phase2_ready"] = True

    with pytest.raises(ValueError, match="entries_missing"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_build_rejects_missing_phase1_manifest_index(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    (phase1_dir / "phase1_manifest_index.json").unlink()
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(current_root)

    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir,
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    assert manifest["phase2_ready"] is False
    assert manifest["phase1_manifest_index_gate"]["passed"] is False
    assert "baseline_id_mismatch" in manifest["phase1_manifest_index_gate"]["failed_kinds"]
    assert "baseline_git_head_mismatch" in manifest["phase1_manifest_index_gate"]["failed_kinds"]
    with pytest.raises(ValueError, match="baseline_id_mismatch"):
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


def test_phase2_accepts_solver_rewrite_proof_failure_to_sat_unsafety(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(current_root)
    _write_log(
        baseline_root,
        "fc_recursive_sum",
        "B1",
        "B8",
        _payload(
            "fc_recursive_sum",
            "function_call_test-arm64-clang-O0",
            "function_call_test-arm64-gcc-O3",
            None,
            [
                make_unknown_reason(
                    UnknownReasonId.SOLVER_PROVEN_REWRITE_PROOF_FAILED
                ),
                make_unknown_reason(UnknownReasonId.UNRESOLVED_EXPRESSION),
            ],
        ),
    )
    _write_log(
        current_root,
        "fc_recursive_sum",
        "B1",
        "B8",
        _payload(
            "fc_recursive_sum",
            "function_call_test-arm64-clang-O0",
            "function_call_test-arm64-gcc-O3",
            None,
            [
                make_unknown_reason(UnknownReasonId.SAT_UNSAFETY),
                make_unknown_reason(UnknownReasonId.UNRESOLVED_EXPRESSION),
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


def test_phase2_rejects_solver_rewrite_proof_failure_to_unrelated_reason(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(current_root)
    _write_log(
        baseline_root,
        "fc_recursive_sum",
        "B1",
        "B8",
        _payload(
            "fc_recursive_sum",
            "function_call_test-arm64-clang-O0",
            "function_call_test-arm64-gcc-O3",
            None,
            [
                make_unknown_reason(
                    UnknownReasonId.SOLVER_PROVEN_REWRITE_PROOF_FAILED
                ),
            ],
        ),
    )
    _write_log(
        current_root,
        "fc_recursive_sum",
        "B1",
        "B8",
        _payload(
            "fc_recursive_sum",
            "function_call_test-arm64-clang-O0",
            "function_call_test-arm64-gcc-O3",
            None,
            [make_unknown_reason(UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING)],
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
        "return_width_bridge_missing" in key
        for key in unexpected["pair_result_multiset_delta"]
    )


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
