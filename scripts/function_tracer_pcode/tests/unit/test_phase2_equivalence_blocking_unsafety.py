# -*- coding: utf-8 -*-

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    UnknownRecoveryProofObligation,
    UnknownReasonId,
    build_proof_obligation_id,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.validation.phase2_equivalence_blocking_unsafety import (
    _object_target_key_is_specific,
    _parse_current_log_roots,
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
    validation_require_phase2_object_keys: str = "1",
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
                "validation_require_phase2_object_keys=" + validation_require_phase2_object_keys,
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


def _payload(
    function: str,
    left_binary: str,
    right_binary: str,
    is_equivalent,
    reasons,
    *,
    completed_recovery_proof_evidence=None,
):
    payload = {
        "function1_name": function,
        "function2_name": function,
        "binary1_name": left_binary,
        "binary2_name": right_binary,
        "is_equivalent": is_equivalent,
        "is_timeout": False,
        "error_message": None,
        "unknown_reasons": [
            reason.to_dict() if hasattr(reason, "to_dict") else reason
            for reason in reasons
        ],
    }
    if completed_recovery_proof_evidence is not None:
        payload["completed_recovery_proof_evidence"] = list(completed_recovery_proof_evidence)
    return payload


def _pending_reason(*, object_target_key=None, proof_obligation_id=None):
    target = object_target_key or (
        "unsupported_call_effect",
        "function1",
        ("function_ref", ("function", "B10", 0x401000)),
        (
            "runtime_ref",
            "unsupported_call_effect",
            (
                "pcode_op_ref",
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
            ),
            (
                "callee_identity",
                (
                    "unknown",
                    "B10",
                    ("target_expression", ("typed_target_expression", ("storage", ("register", "a0", 8)))),
                ),
            ),
            ("typed_target_expression", ("typed_target_expression", ("storage", ("register", "a0", 8)))),
        ),
        (
            "callsite_storage",
            (
                "pcode_op_ref",
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
            ),
            (
                "callee_identity",
                (
                    "unknown",
                    "B10",
                    ("target_expression", ("typed_target_expression", ("storage", ("register", "a0", 8)))),
                ),
            ),
            ("target_expression", ("typed_target_expression", ("storage", ("register", "a0", 8)))),
        ),
        ("effect_ordinal", 7),
        "target_identity_unavailable",
    )
    return make_unknown_reason(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY,
        decision_effect="blocks_equivalence",
        reason_scope="function",
        recovery_proof_kind=UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
        recovery_proof_obligations=(
            UnknownRecoveryProofObligation.create(
                UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
                "object_evidence_collected",
                required_evidence=(
                    "call_effect_summary",
                    "runtime_ref",
                    "callsite_storage",
                ),
                description="Collect object-derived call/effect evidence before using UNSAT as equivalence proof.",
            ),
        ),
        proof_stage="object_evidence_collected",
        evidence_kind="call_effect_summary",
        object_target_key=target,
        object_evidence=_object_evidence_for_target(target),
        proof_obligation_id=proof_obligation_id,
        recovery_action="call_effect_summary_proof_required",
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
    )


def _object_evidence_for_target(target):
    if not isinstance(target, tuple) or not target:
        return None
    target_kind = target[0]
    evidence = {
        "object_derived": True,
        "evidence_version": 1,
        "evidence_kind": "call_effect_summary",
        "blocker_reason": "function1:unsupported_call_effect_summary",
        "blocker_reason_kind": "unsupported_call_effect_summary",
        "object_target_kind": target_kind,
        "left_function": "func1",
        "right_function": "func2",
        "side": target[1] if len(target) > 1 else None,
        "analysis_key": target[2] if len(target) > 2 else None,
    }
    if target_kind == "unsupported_call_effect" and len(target) >= 7:
        evidence.update(
            {
                "runtime_ref": target[3],
                "callsite_storage": target[4],
                "effect_ordinal": target[5],
                "unsupported_reason": target[6],
                "call_effect_summary_status": target[6],
            }
        )
        return evidence
    if target_kind == "call_argument_evidence" and len(target) >= 8:
        runtime_ref = (
            "runtime_ref",
            "call_argument",
            ("pcode_op_ref", target[3]),
            ("callee_identity", target[4]),
        )
        callsite_storage = (
            "callsite_storage",
            "call_argument",
            ("argument_keys", target[5]),
        )
        evidence.update(
            {
                "runtime_ref": runtime_ref,
                "callee_identity": target[4],
                "argument_storage": target[5],
                "coverage_complete": target[6],
                "recovery_status": target[7],
                "callsite_storage": callsite_storage,
                "call_effect_summary_status": target[7],
            }
        )
        return evidence
    if target_kind == "call_target_resolution_evidence" and len(target) >= 9:
        evidence.update(
            {
                "runtime_ref": target[3],
                "callsite_storage": target[4],
                "resolution_kind": target[5],
                "path_conditions": target[6],
                "target_conditions": target[7],
                "effect_ordinal": target[8],
                "call_effect_summary_status": "target_resolution_pending_proof",
            }
        )
        return evidence
    if target_kind == "deferred_call" and len(target) >= 9:
        evidence.update(
            {
                "deferred_call_site": target[3],
                "pcode_op_ref": target[4],
                "callee_identity": target[5],
                "target_expression": target[6],
                "argument_storage": target[7],
                "call_effect_summary_status": target[8],
            }
        )
        return evidence
    return None


def _completed_call_effect_proof_evidence(reason=None):
    reason = reason or _pending_reason()
    proof_obligation_id = build_proof_obligation_id(
        "equivalence_blocking_unsafety",
        "object_evidence_collected",
        "call_effect_summary_proof",
        "call_effect_summary",
        reason.object_target_key,
    )
    return {
        "object_derived": True,
        "status": "complete",
        "reason_id": "equivalence_blocking_unsafety",
        "recovery_proof_kind": "call_effect_summary_proof",
        "proof_stage": "object_evidence_collected",
        "evidence_kind": "call_effect_summary",
        "object_target_key": reason.object_target_key,
        "proof_obligation_id": proof_obligation_id,
        "proof_source": "self_recursive_no_store_call_effect_summary",
    }


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
            "runtime_ref",
            "unsupported_call_effect",
            (
                "pcode_op_ref",
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
            ),
            (
                "callee_identity",
                (
                    "unknown",
                    "B10",
                    ("target_expression", ("typed_target_expression", ("storage", ("register", "a0", 8)))),
                ),
            ),
            ("typed_target_expression", ("typed_target_expression", ("storage", ("register", "a0", 8)))),
        ),
        (
            "callsite_storage",
            (
                "pcode_op_ref",
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
            ),
            (
                "callee_identity",
                (
                    "unknown",
                    "B10",
                    ("target_expression", ("typed_target_expression", ("storage", ("register", "a0", 8)))),
                ),
            ),
            ("target_expression", ("typed_target_expression", ("storage", ("register", "a0", 8)))),
        ),
        ("effect_ordinal", 7),
        "target_identity_unavailable",
    )

    assert _object_target_key_is_specific(legacy_target) is False
    assert _object_target_key_is_specific(full_target) is True


def test_phase2_log_root_parser_rejects_unknown_category_typo():
    with pytest.raises(ValueError, match="unknown log root category"):
        _parse_current_log_roots(("functoin_call=/tmp/does-not-exist",))


def test_phase2_build_rejects_unknown_current_log_root_category(tmp_path):
    phase1_dir = tmp_path / "phase1"
    _representative_manifest(phase1_dir)

    with pytest.raises(ValueError, match="unknown log root category"):
        build_phase2_equivalence_blocking_unsafety_movement(
            phase1_dir=phase1_dir,
            output_dir=tmp_path / "phase2",
            current_log_roots={"functoin_call": tmp_path / "logs"},
            baseline_log_roots={"function_call": tmp_path / "baseline"},
        )


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
    missing_ordinal_target = full_target[:5] + (("effect_ordinal", None),) + full_target[6:]
    text_ordinal_target = full_target[:5] + (("effect_ordinal", "7"),) + full_target[6:]
    bool_ordinal_target = full_target[:5] + (("effect_ordinal", True),) + full_target[6:]

    assert _object_target_key_is_specific(missing_ordinal_target) is False
    assert _object_target_key_is_specific(text_ordinal_target) is False
    assert _object_target_key_is_specific(bool_ordinal_target) is False
    assert _object_target_key_is_specific(full_target) is True


def test_phase2_call_effect_specificity_rejects_missing_callee_identity_sentinel():
    full_target = _pending_reason().object_target_key
    runtime_ref_without_callee = full_target[3][:3] + (("callee_identity", None),) + full_target[3][4:]
    unknown_without_provenance = full_target[3][:3] + (("callee_identity", ("unknown", "B10")),) + full_target[3][4:]
    unknown_without_binary = (
        full_target[3][:3]
        + (
            (
                "callee_identity",
                (
                    "unknown",
                    None,
                    ("target_expression", ("typed_target_expression", ("storage", ("register", "a0", 8)))),
                ),
            ),
        )
        + full_target[3][4:]
    )

    assert _object_target_key_is_specific(full_target[:3] + (runtime_ref_without_callee,) + full_target[4:]) is False
    assert _object_target_key_is_specific(full_target[:3] + (unknown_without_provenance,) + full_target[4:]) is False
    assert _object_target_key_is_specific(full_target[:3] + (unknown_without_binary,) + full_target[4:]) is False
    assert _object_target_key_is_specific(full_target) is True


def test_phase2_call_effect_specificity_rejects_known_callee_without_concrete_address():
    full_target = _pending_reason().object_target_key
    function_without_entry = (
        full_target[3][:3]
        + (("callee_identity", ("function", "B10", None)),)
        + full_target[3][4:]
    )
    code_address_without_address = (
        full_target[4][:2]
        + (("callee_identity", ("code_address", "B10", "bad")),)
        + full_target[4][3:]
    )
    function_with_entry = (
        full_target[3][:3]
        + (("callee_identity", ("function", "B10", 0x401234)),)
        + full_target[3][4:]
    )
    storage_with_function_entry = (
        full_target[4][:2]
        + (("callee_identity", ("function", "B10", 0x401234)),)
        + full_target[4][3:]
    )
    code_address_with_address = (
        full_target[4][:2]
        + (("callee_identity", ("code_address", "B10", 0x401234)),)
        + full_target[4][3:]
    )
    runtime_with_code_address = (
        full_target[3][:3]
        + (("callee_identity", ("code_address", "B10", 0x401234)),)
        + full_target[3][4:]
    )

    assert _object_target_key_is_specific(full_target[:3] + (function_without_entry,) + full_target[4:]) is False
    assert _object_target_key_is_specific(full_target[:4] + (code_address_without_address,) + full_target[5:]) is False
    assert (
        _object_target_key_is_specific(
            full_target[:3] + (function_with_entry, storage_with_function_entry) + full_target[5:]
        )
        is True
    )
    assert (
        _object_target_key_is_specific(
            full_target[:3] + (runtime_with_code_address, code_address_with_address) + full_target[5:]
        )
        is True
    )


def test_phase2_call_effect_specificity_requires_runtime_and_storage_consistency():
    full_target = _pending_reason().object_target_key
    pcode_ref = full_target[4][1][1]
    mismatched_pcode_ref = pcode_ref[:5] + (pcode_ref[5] + 1,) + pcode_ref[6:]
    storage_with_different_pcode = (
        full_target[4][:1]
        + (("pcode_op_ref", mismatched_pcode_ref),)
        + full_target[4][2:]
    )
    storage_with_different_callee = (
        full_target[4][:2]
        + (("callee_identity", ("function", "B10", 0x401234)),)
        + full_target[4][3:]
    )
    storage_with_different_target_expression = (
        full_target[4][:3]
        + (("target_expression", ("typed_target_expression", ("storage", ("register", "a1", 8)))),)
    )

    assert _object_target_key_is_specific(full_target[:4] + (storage_with_different_pcode,) + full_target[5:]) is False
    assert _object_target_key_is_specific(full_target[:4] + (storage_with_different_callee,) + full_target[5:]) is False
    assert (
        _object_target_key_is_specific(
            full_target[:4] + (storage_with_different_target_expression,) + full_target[5:]
        )
        is False
    )
    assert _object_target_key_is_specific(full_target) is True


def test_phase2_call_argument_evidence_specificity_requires_pcode_and_target_identity():
    full_target = (
        "call_argument_evidence",
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
        ("function", "B10", 0x402000),
        (
            ("argument", 0, ("runtime_ref", ("parameter", "B10", 0x401000, 1))),
        ),
        True,
        "complete",
    )
    missing_binary_pcode = full_target[:3] + (
        (
            "pcode_op",
            None,
            ("function_entry", "ram", 0x401000),
            ("seq_target", "ram", 0x401020),
            31,
            7,
            8,
            0,
        ),
    ) + full_target[4:]
    missing_target_address = full_target[:4] + (("function", "B10", None),) + full_target[5:]
    unknown_target = full_target[:4] + (("unknown", "B10", ("target_expression", ("runtime_ref", "fp"))),) + full_target[5:]
    missing_status = full_target[:7] + (None,)

    assert _object_target_key_is_specific(missing_binary_pcode) is False
    assert _object_target_key_is_specific(missing_target_address) is False
    assert _object_target_key_is_specific(unknown_target) is False
    assert _object_target_key_is_specific(missing_status) is False
    assert _object_target_key_is_specific(full_target) is True


def test_phase2_call_target_resolution_specificity_requires_condition_payloads():
    pcode_ref = (
        "pcode_op",
        "B10",
        ("function_entry", "ram", 0x401000),
        ("seq_target", "ram", 0x401020),
        31,
        7,
        8,
        0,
    )
    target_expr = ("typed_target_expression", ("storage", ("register", "a0", 8)))
    callee_identity = ("callee_identity", ("function", "B10", 0x402000))
    runtime_ref = (
        "runtime_ref",
        "call_target_resolution",
        ("pcode_op_ref", pcode_ref),
        callee_identity,
        ("typed_target_expression", target_expr),
    )
    callsite_storage = (
        "callsite_storage",
        ("pcode_op_ref", pcode_ref),
        callee_identity,
        ("target_expression", target_expr),
    )
    full_target = (
        "call_target_resolution_evidence",
        "function1",
        ("function_ref", ("function", "B10", 0x401000)),
        runtime_ref,
        callsite_storage,
        ("resolution_kind", "pathless_target_resolution"),
        ("path_conditions", (("condition", False, ("expr", "param_1", 0)),)),
        ("target_conditions", ()),
        ("effect_ordinal", 0),
    )
    path_condition_none = full_target[:6] + (("path_conditions", (None,)),) + full_target[7:]
    missing_condition_payload = full_target[:6] + (
        ("path_conditions", (("condition", False, None),)),
    ) + full_target[7:]
    wrong_condition_shape = full_target[:6] + (
        ("path_conditions", (("condition", False),)),
    ) + full_target[7:]
    target_condition_with_none_nested = full_target[:7] + (
        ("target_conditions", (("condition", True, ("expr", None)),)),
    ) + full_target[8:]

    assert _object_target_key_is_specific(path_condition_none) is False
    assert _object_target_key_is_specific(missing_condition_payload) is False
    assert _object_target_key_is_specific(wrong_condition_shape) is False
    assert _object_target_key_is_specific(target_condition_with_none_nested) is False
    assert _object_target_key_is_specific(full_target) is True


def _old_blocking_reason():
    return make_unknown_reason(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY,
        decision_effect="blocks_equivalence",
        reason_scope="function",
    )


def _legacy_sat_unsafety_reason():
    return make_unknown_reason(
        UnknownReasonId.SAT_UNSAFETY,
        recovery_proof_kind=UnknownRecoveryProofKind.NONE,
        recovery_proof_obligations=(),
        proof_stage=None,
    )


def _pending_sat_unsafety_reason():
    return make_unknown_reason(
        UnknownReasonId.SAT_UNSAFETY,
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
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


def test_phase2_rejects_target_reason_only_unknown_to_eq_even_with_completed_proof(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    completed_evidence = _completed_call_effect_proof_evidence()
    _write_all_representative_logs(
        current_root,
        payload_by_function={
            "fc_dispatch_indirect": _payload(
                "fc_dispatch_indirect",
                "B10",
                "B11",
                True,
                [],
                completed_recovery_proof_evidence=[
                    {
                        "side": "function1",
                        "function_name": "fc_dispatch_indirect",
                        "binary_name": "function_call_test-arm64-clang-O2",
                        "binary_id": "B10",
                        "evidence": completed_evidence,
                    },
                ],
            )
        },
    )

    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir,
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    dispatch_entry = next(
        entry
        for entry in manifest["entries"]
        if entry["function"] == "fc_dispatch_indirect"
    )
    allowed_movements = manifest["overall_baseline_comparison_gate"]["allowed_final_result_movements"]

    assert dispatch_entry["movement_status"] == "failed"
    assert "target_reason_unknown_to_eq_not_allowed" in dispatch_entry["failed_kinds"]
    assert manifest["phase2_ready"] is False
    assert manifest["overall_baseline_comparison_gate"]["passed"] is False
    assert allowed_movements == []
    assert (
        "target_reason_unknown_to_eq_not_allowed"
        in manifest["overall_baseline_comparison_gate"]["failed_kinds"]
    )
    with pytest.raises(ValueError, match="target_reason_unknown_to_eq_not_allowed"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_rejects_target_reason_only_unknown_to_eq_without_completed_proof(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(
        current_root,
        payload_by_function={
            "fc_dispatch_indirect": _payload(
                "fc_dispatch_indirect",
                "B10",
                "B11",
                True,
                [],
            )
        },
    )

    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir,
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    manifest = json.loads(path.read_text())
    dispatch_entry = next(
        entry
        for entry in manifest["entries"]
        if entry["function"] == "fc_dispatch_indirect"
    )

    assert dispatch_entry["movement_status"] == "failed"
    assert "target_reason_unknown_to_eq_not_allowed" in dispatch_entry["failed_kinds"]
    assert manifest["phase2_ready"] is False
    assert manifest["overall_baseline_comparison_gate"]["passed"] is False
    assert (
        "target_reason_unknown_to_eq_not_allowed"
        in manifest["overall_baseline_comparison_gate"]["failed_kinds"]
    )
    assert manifest["overall_baseline_comparison_gate"]["allowed_final_result_movements"] == []
    with pytest.raises(ValueError, match="target_reason_unknown_to_eq_not_allowed"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_validator_rejects_tampered_unknown_to_eq_allowed_movement(tmp_path):
    manifest = _ready_phase2_manifest(tmp_path)
    entry = manifest["entries"][0]
    entry["accepted_reason_records"] = []
    entry["final_result_movement"] = "target_reason_unknown_to_eq"
    manifest["overall_baseline_comparison_gate"]["allowed_final_result_movements"] = [
        {
            "function": entry["function"],
            "binary_pair": entry["binary_pair"],
            "status_movement": "UNKNOWN->EQ",
            "removed_reasons": {"equivalence_blocking_unsafety": 1},
        },
    ]
    manifest["phase2_ready"] = True

    with pytest.raises(ValueError, match="not_allowed"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_rejects_unknown_to_eq_when_non_target_reason_disappears(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(
        baseline_root,
        payload_by_function={
            "fc_dispatch_indirect": _payload(
                "fc_dispatch_indirect",
                "B10",
                "B11",
                None,
                [
                    _old_blocking_reason(),
                    make_unknown_reason(UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING),
                ],
            )
        },
    )
    _write_all_representative_logs(
        current_root,
        payload_by_function={
            "fc_dispatch_indirect": _payload(
                "fc_dispatch_indirect",
                "B10",
                "B11",
                True,
                [],
            )
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
    assert manifest["overall_baseline_comparison_gate"]["passed"] is False
    assert "unexpected_non_target_final_result_movement" in manifest["movement_summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="unexpected_non_target_final_result_movement"):
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


def test_phase2_validator_rejects_tampered_accepted_required_evidence(tmp_path):
    manifest = _ready_phase2_manifest(tmp_path)
    manifest["entries"][0]["accepted_reason_records"][0]["required_evidence"] = [
        "call_effect_summary",
    ]
    manifest["phase2_ready"] = True

    with pytest.raises(ValueError, match="entry_accepted_reason_required_evidence_mismatch"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_validator_rechecks_accepted_proof_obligation_id(tmp_path):
    manifest = _ready_phase2_manifest(tmp_path)
    manifest["entries"][0]["accepted_reason_records"][0]["proof_obligation_id"] = "stale-id"
    manifest["phase2_ready"] = True

    with pytest.raises(ValueError, match="entry_accepted_reason_proof_obligation_id_mismatch"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_validator_rechecks_accepted_object_target_key_specificity(tmp_path):
    manifest = _ready_phase2_manifest(tmp_path)
    manifest["entries"][0]["accepted_reason_records"][0]["object_target_key"] = [
        "runtime_ref",
        "B10",
    ]
    manifest["phase2_ready"] = True

    with pytest.raises(ValueError, match="entry_accepted_reason_object_target_key_not_specific"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_rejects_expected_movement_without_object_evidence(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    reason_payload = _pending_reason().to_dict()
    reason_payload.pop("object_evidence", None)
    _write_all_representative_logs(
        current_root,
        {
            "fc_apply_indirect": _payload(
                "fc_apply_indirect",
                "B10",
                "B11",
                None,
                [reason_payload],
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
    assert "object_evidence_missing_or_inconsistent" in manifest["movement_summary"]["failed_kinds"]
    with pytest.raises(ValueError, match="object_evidence_missing_or_inconsistent"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_validator_rechecks_accepted_object_evidence_matches_target(tmp_path):
    manifest = _ready_phase2_manifest(tmp_path)
    manifest["entries"][0]["accepted_reason_records"][0]["object_evidence"]["runtime_ref"] = [
        "runtime_ref",
        "wrong",
    ]
    manifest["phase2_ready"] = True

    with pytest.raises(ValueError, match="entry_accepted_reason_object_evidence_missing_or_inconsistent"):
        validate_phase2_equivalence_blocking_unsafety_movement(manifest)


def test_phase2_validator_rechecks_accepted_recovery_action(tmp_path):
    manifest = _ready_phase2_manifest(tmp_path)
    manifest["entries"][0]["accepted_reason_records"][0]["recovery_action"] = "solver_retry"
    manifest["phase2_ready"] = True

    with pytest.raises(ValueError, match="entry_accepted_reason_recovery_action_mismatch"):
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
        ("validation_require_phase2_object_keys", "0"),
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


def test_phase2_rejects_call_effect_obligation_without_runtime_and_storage_evidence(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    reason_payload = _pending_reason().to_dict()
    reason_payload["recovery_proof_obligations"][0]["required_evidence"] = [
        "call_effect_summary",
    ]
    _write_all_representative_logs(
        current_root,
        {
            "fc_apply_indirect": _payload(
                "fc_apply_indirect",
                "B10",
                "B11",
                None,
                [reason_payload],
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
    assert (
        "recovery_proof_obligation_required_evidence_mismatch"
        in manifest["movement_summary"]["failed_kinds"]
    )


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


def test_phase2_accepts_return_width_bridge_reclassification_to_equivalence_blocker(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(current_root)
    _write_log(
        baseline_root,
        "fc_apply_indirect",
        "B1",
        "B2",
        _payload(
            "fc_apply_indirect",
            "function_call_test-arm64-clang-O0",
            "function_call_test-arm64-clang-O1",
            None,
            [make_unknown_reason(UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING)],
        ),
    )
    _write_log(
        current_root,
        "fc_apply_indirect",
        "B1",
        "B2",
        _payload(
            "fc_apply_indirect",
            "function_call_test-arm64-clang-O0",
            "function_call_test-arm64-clang-O1",
            None,
            [_pending_reason()],
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


def test_phase2_after_pairs_scope_supports_reduced_gate_validation(tmp_path):
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
            "function_call_test-arm64-clang-O0",
            "function_call_test-arm64-clang-O1",
            None,
            [make_unknown_reason(UnknownReasonId.UNRESOLVED_EXPRESSION)],
        ),
    )

    all_scope_path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir / "all",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    all_scope_manifest = json.loads(all_scope_path.read_text())
    assert all_scope_manifest["overall_baseline_comparison_gate"]["passed"] is False
    assert "total_result_count_delta" in all_scope_manifest["movement_summary"]["failed_kinds"]

    after_pairs_path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=phase1_dir,
        output_dir=output_dir / "after_pairs",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        baseline_match_scope="after-pairs",
    )
    after_pairs_manifest = json.loads(after_pairs_path.read_text())
    assert after_pairs_manifest["phase2_ready"] is True
    assert after_pairs_manifest["overall_baseline_comparison_gate"]["passed"] is True
    assert after_pairs_manifest["overall_baseline_comparison_gate"]["baseline_match_scope"] == "after-pairs"
    validate_phase2_equivalence_blocking_unsafety_movement(after_pairs_manifest)


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


def test_phase2_accepts_target_reason_exposure_without_final_result_movement(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(current_root)
    _write_log(
        baseline_root,
        "fc_target_exposure",
        "B1",
        "B2",
        _payload(
            "fc_target_exposure",
            "function_call_test-arm64-clang-O0",
            "function_call_test-arm64-clang-O1",
            None,
            [make_unknown_reason(UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING)],
        ),
    )
    _write_log(
        current_root,
        "fc_target_exposure",
        "B1",
        "B2",
        _payload(
            "fc_target_exposure",
            "function_call_test-arm64-clang-O0",
            "function_call_test-arm64-clang-O1",
            None,
            [
                make_unknown_reason(UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING),
                _pending_reason(),
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
    unexpected = manifest["overall_baseline_comparison_gate"]["unexpected_deltas"]
    assert unexpected["pair_result_multiset_delta"] == {}


def test_phase2_accepts_target_exposure_with_existing_blocker_detail_backlog(tmp_path):
    phase1_dir = tmp_path / "phase1"
    baseline_root = tmp_path / "baseline" / "function_call"
    current_root = tmp_path / "logs" / "function_call"
    output_dir = tmp_path / "phase2"
    _representative_manifest(phase1_dir)
    _write_all_baseline_representative_logs(baseline_root)
    _write_all_representative_logs(current_root)
    _write_log(
        baseline_root,
        "fc_existing_blocker_detail",
        "B1",
        "B10",
        _payload(
            "fc_existing_blocker_detail",
            "function_call_test-arm64-clang-O0",
            "function_call_test-mips64-clang-O1",
            None,
            [
                _legacy_sat_unsafety_reason(),
                make_unknown_reason(UnknownReasonId.UNRESOLVED_EXPRESSION),
            ],
        ),
    )
    _write_log(
        current_root,
        "fc_existing_blocker_detail",
        "B1",
        "B10",
        _payload(
            "fc_existing_blocker_detail",
            "function_call_test-arm64-clang-O0",
            "function_call_test-mips64-clang-O1",
            None,
            [
                _pending_sat_unsafety_reason(),
                _pending_sat_unsafety_reason(),
                _pending_sat_unsafety_reason(),
                make_unknown_reason(UnknownReasonId.UNRESOLVED_EXPRESSION),
                make_unknown_reason(UnknownReasonId.UNRESOLVED_EXPRESSION),
                _pending_reason(),
                _pending_reason(),
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
    unexpected = manifest["overall_baseline_comparison_gate"]["unexpected_deltas"]
    assert unexpected["reason_record_multiset_delta"] == {}
    assert unexpected["proof_action_multiset_delta"] == {}
    assert unexpected["validation_unknown_unit_multiset_delta"] == {}


def test_phase2_rejects_non_target_unknown_to_eq_return_coverage_gap_disappearance(tmp_path):
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
        "B3",
        "B7",
        _payload(
            "fc_recursive_sum",
            "function_call_test-arm64-clang-O2",
            "function_call_test-arm64-gcc-O2",
            None,
            [make_unknown_reason(UnknownReasonId.RETURN_COVERAGE_GAP)],
        ),
    )
    _write_log(
        current_root,
        "fc_recursive_sum",
        "B3",
        "B7",
        _payload(
            "fc_recursive_sum",
            "function_call_test-arm64-clang-O2",
            "function_call_test-arm64-gcc-O2",
            True,
            [],
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
    assert manifest["overall_baseline_comparison_gate"]["passed"] is False
    failed = manifest["movement_summary"]["failed_kinds"]
    assert "final_result_count_delta" in failed
    assert "unknown_final_result_delta" in failed
    assert "pair_result_tuple_delta" in failed
    assert "unexpected_non_target_final_result_movement" in failed
    unexpected = manifest["overall_baseline_comparison_gate"]["unexpected_deltas"]
    movement = unexpected["non_target_final_result_movements"][0]
    assert movement["pair_identity"] == {
        "function": "fc_recursive_sum",
        "binary_pair": (
            "function_call_test-arm64-clang-O2 ↔ "
            "function_call_test-arm64-gcc-O2"
        ),
    }
    assert movement["status_movement"] == "UNKNOWN->EQ"
    assert movement["non_target_disappeared_reasons"] == ["return_coverage_gap"]
    assert movement["non_target_reason_movement"] is True
    count_deltas = movement["count_kind_deltas"]
    assert any(
        "return_coverage_gap" in key
        for key in count_deltas["validation_unknown_unit"]
    )
    assert any(
        "return_coverage_gap" in key
        for key in count_deltas["reason_record"]
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
            [make_unknown_reason(UnknownReasonId.READONLY_IDENTITY_MISSING)],
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
