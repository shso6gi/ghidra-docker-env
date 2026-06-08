# -*- coding: utf-8 -*-

import json

from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownReasonId,
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    UnknownRecoveryProofObligation,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.validation.log_reuse_gate import (
    validation_log_reuse_failures,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
)


def _write_log(path, payload):
    path.write_text(
        "\n".join(
            (
                "Result: UNKNOWN",
                RESULT_JSON_BEGIN,
                json.dumps(payload),
                RESULT_JSON_END,
            )
        )
    )


def _payload(*reasons):
    return {
        "function1_name": "fc_apply_indirect",
        "function2_name": "fc_apply_indirect",
        "binary1_name": "function_call_test-mips64-clang-O1",
        "binary2_name": "function_call_test-mips64-clang-O2",
        "is_equivalent": None,
        "is_timeout": False,
        "unknown_reasons": [reason.to_dict() for reason in reasons],
    }


def _full_object_target_key():
    return (
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
        ("typed_target_expression", ("expression", ("parameter", "fp", ("int", 0), 8))),
        7,
        "target_identity_unavailable",
    )


def _legacy_object_target_key():
    return (
        "unsupported_call_effect",
        "function1",
        ("function_ref", ("function", 3730480557554171168, 0x401000)),
        ("pcode_op", 0x401020, 31, 7, 0, "CALLIND"),
        None,
        ("typed_target_expression", ("expression", ("parameter", "fp", ("int", 0), 8))),
        7,
        "target_identity_unavailable",
    )


def _phase2_reason(object_target_key, *, evidence_kind="call_effect_summary"):
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
        evidence_kind=evidence_kind,
        object_target_key=object_target_key,
        recovery_action="call_effect_summary_proof_required",
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
    )


def test_log_reuse_gate_accepts_complete_log_without_phase2_key_requirement(tmp_path):
    path = tmp_path / "pair.log"
    _write_log(path, _payload(_phase2_reason(_legacy_object_target_key())))

    assert validation_log_reuse_failures(path) == ()


def test_log_reuse_gate_accepts_canonical_phase2_object_key(tmp_path):
    path = tmp_path / "pair.log"
    _write_log(path, _payload(_phase2_reason(_full_object_target_key())))

    assert validation_log_reuse_failures(path, require_phase2_object_keys=True) == ()


def test_log_reuse_gate_rejects_legacy_phase2_object_key(tmp_path):
    path = tmp_path / "pair.log"
    _write_log(path, _payload(_phase2_reason(_legacy_object_target_key())))

    failures = validation_log_reuse_failures(path, require_phase2_object_keys=True)

    assert "phase2_object_target_key_missing_or_not_specific" in failures


def test_log_reuse_gate_rejects_missing_phase2_evidence_kind(tmp_path):
    path = tmp_path / "pair.log"
    _write_log(path, _payload(_phase2_reason(_full_object_target_key(), evidence_kind=None)))

    failures = validation_log_reuse_failures(path, require_phase2_object_keys=True)

    assert "phase2_evidence_kind_missing" in failures


def test_log_reuse_gate_rejects_unexpected_phase2_evidence_kind(tmp_path):
    path = tmp_path / "pair.log"
    _write_log(path, _payload(_phase2_reason(_full_object_target_key(), evidence_kind="log_prose")))

    failures = validation_log_reuse_failures(path, require_phase2_object_keys=True)

    assert "phase2_evidence_kind_mismatch" in failures


def test_log_reuse_gate_rejects_phase2_obligation_without_runtime_and_storage_evidence(tmp_path):
    path = tmp_path / "pair.log"
    payload = _payload(_phase2_reason(_full_object_target_key()))
    payload["unknown_reasons"][0]["recovery_proof_obligations"][0]["required_evidence"] = [
        "call_effect_summary",
    ]
    _write_log(path, payload)

    failures = validation_log_reuse_failures(path, require_phase2_object_keys=True)

    assert "phase2_recovery_proof_obligation_required_evidence_mismatch" in failures


def test_log_reuse_gate_rejects_call_effect_key_without_integer_effect_ordinal(tmp_path):
    path = tmp_path / "pair.log"
    target = _full_object_target_key()
    missing_ordinal = target[:6] + (None,) + target[7:]
    text_ordinal = target[:6] + ("7",) + target[7:]
    _write_log(
        path,
        _payload(
            _phase2_reason(missing_ordinal),
            _phase2_reason(text_ordinal),
        ),
    )

    failures = validation_log_reuse_failures(path, require_phase2_object_keys=True)

    assert "phase2_object_target_key_missing_or_not_specific" in failures


def test_log_reuse_gate_rejects_raw_reason_without_proof_obligation_id(tmp_path):
    path = tmp_path / "pair.log"
    payload = _payload(_phase2_reason(_full_object_target_key()))
    payload["unknown_reasons"][0].pop("proof_obligation_id")
    _write_log(path, payload)

    failures = validation_log_reuse_failures(path, require_phase2_object_keys=True)

    assert "phase2_proof_obligation_id_missing" in failures


def test_log_reuse_gate_rejects_raw_reason_with_null_proof_obligation_id(tmp_path):
    path = tmp_path / "pair.log"
    payload = _payload(_phase2_reason(_full_object_target_key()))
    payload["unknown_reasons"][0]["proof_obligation_id"] = None
    _write_log(path, payload)

    failures = validation_log_reuse_failures(path, require_phase2_object_keys=True)

    assert "phase2_proof_obligation_id_missing" in failures


def test_log_reuse_gate_rejects_old_call_effect_blocker_without_proof_detail(tmp_path):
    path = tmp_path / "pair.log"
    old_reason = make_unknown_reason(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY,
        decision_effect="blocks_equivalence",
        reason_scope="function",
        detail="function1:unsupported_call_effect_summary",
        evidence_refs=("function1:unsupported_call_effect_summary",),
    )
    _write_log(path, _payload(old_reason))

    failures = validation_log_reuse_failures(path, require_phase2_object_keys=True)

    assert "phase2_recovery_proof_kind_missing" in failures
    assert "phase2_object_target_key_missing_or_not_specific" in failures


def test_log_reuse_gate_rejects_incomplete_log(tmp_path):
    path = tmp_path / "pair.log"
    path.write_text("Result: UNKNOWN\n")

    assert validation_log_reuse_failures(path) == ("result_json_incomplete",)
