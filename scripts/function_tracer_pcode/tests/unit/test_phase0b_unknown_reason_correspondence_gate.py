# -*- coding: utf-8 -*-

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.equivalence.unknown_reason import UnknownReasonId, make_unknown_reason
from scripts.function_tracer_pcode.validation.phase0b_unknown_reason_correspondence_gate import (
    build_phase0b_unknown_reason_correspondence_gate,
    validate_phase0b_unknown_reason_correspondence_gate,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import RESULT_JSON_BEGIN, RESULT_JSON_END


def test_phase0b_unknown_reason_correspondence_gate_accepts_classified_diagnostics(tmp_path):
    raw_dir = _write_fixture(tmp_path)

    path = build_phase0b_unknown_reason_correspondence_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
    )
    gate = json.loads(path.read_text())

    assert gate["phase0b_unknown_reason_correspondence_ready"] is True
    assert gate["combined_blocking_classification_counts"] == {}
    assert gate["combined_classification_counts"] == {
        "proof_action_expansion": 2,
    }
    validate_phase0b_unknown_reason_correspondence_gate(gate)


def test_phase0b_unknown_reason_correspondence_gate_rejects_unknown_log_without_typed_payload(tmp_path):
    raw_dir = _write_fixture(tmp_path)
    stale = raw_dir / "logs" / "function_call" / "fc_stale" / "fc_stale_B1_B2.log"
    stale.parent.mkdir(parents=True)
    stale.write_text("Result: UNKNOWN\nhuman-only diagnostic\n", encoding="utf-8")

    path = build_phase0b_unknown_reason_correspondence_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
    )
    gate = json.loads(path.read_text())

    assert gate["phase0b_unknown_reason_correspondence_ready"] is False
    assert gate["combined_blocking_classification_counts"] == {"raw_log_missing": 1}
    with pytest.raises(ValueError, match="category_blocking_correspondence_absent"):
        validate_phase0b_unknown_reason_correspondence_gate(gate)


def test_phase0b_unknown_reason_correspondence_gate_rejects_baseline_identity_drift(tmp_path):
    raw_dir = _write_fixture(tmp_path)
    manifest_path = raw_dir / "artifact_manifest.json"
    manifest = json.loads(manifest_path.read_text())
    manifest["git_head"] = "different"
    manifest_path.write_text(json.dumps(manifest), encoding="utf-8")

    path = build_phase0b_unknown_reason_correspondence_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
    )
    gate = json.loads(path.read_text())

    assert gate["phase0b_unknown_reason_correspondence_ready"] is False
    with pytest.raises(ValueError, match="baseline_git_head_expected"):
        validate_phase0b_unknown_reason_correspondence_gate(gate)


def _write_fixture(tmp_path: Path) -> Path:
    raw_dir = tmp_path / "raw"
    raw_dir.mkdir()
    (raw_dir / "artifact_manifest.json").write_text(
        json.dumps(
            {
                "baseline_id": "observed-v0@0a53352",
                "git_head": "0a53352cf3c9528abfb654906ed7b963474bedc5",
            }
        ),
        encoding="utf-8",
    )
    _write_log(
        raw_dir / "logs" / "function_call" / "fc_guarded_call" / "fc_guarded_call_B1_B2.log",
        "Result: UNKNOWN",
        _payload(
            "fc_guarded_call",
            None,
            unknown_reasons=[make_unknown_reason(UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING).to_dict()],
        ),
    )
    _write_log(
        raw_dir / "logs" / "loop" / "lmb_sum" / "lmb_sum_B1_B2.log",
        "Result: EQUIVALENT",
        _payload("lmb_sum", True),
    )
    return raw_dir


def _payload(function_name, is_equivalent, **extra):
    payload = {
        "function1_name": function_name,
        "function2_name": function_name,
        "binary1_name": "left.bin",
        "binary2_name": "right.bin",
        "is_equivalent": is_equivalent,
        "error_message": None,
        "unknown_reasons": [],
    }
    payload.update(extra)
    return payload


def _write_log(path: Path, human_result: str, payload):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "\n".join(
            [
                human_result,
                RESULT_JSON_BEGIN,
                json.dumps(payload),
                RESULT_JSON_END,
            ]
        ),
        encoding="utf-8",
    )
