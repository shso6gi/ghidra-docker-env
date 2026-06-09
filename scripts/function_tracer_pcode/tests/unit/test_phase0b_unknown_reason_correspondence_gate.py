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
        **_fixture_expected_classification_counts(),
    )
    gate = json.loads(path.read_text())

    assert gate["phase0b_unknown_reason_correspondence_ready"] is True
    assert gate["combined_blocking_classification_counts"] == {}
    assert gate["combined_classification_counts"] == {
        "proof_action_expansion": 2,
    }
    validate_phase0b_unknown_reason_correspondence_gate(gate)


def test_phase0b_unknown_reason_correspondence_gate_derives_combined_expected_for_selected_category(tmp_path):
    raw_dir = _write_fixture(tmp_path)

    path = build_phase0b_unknown_reason_correspondence_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        categories=("function_call",),
        expected_category_classification_counts={
            "function_call": {
                "proof_action_expansion": 2,
            },
            "loop": {
                "aggregation_difference": 99,
            },
        },
    )
    gate = json.loads(path.read_text())

    assert gate["phase0b_unknown_reason_correspondence_ready"] is True
    assert set(gate["categories"]) == {"function_call"}
    assert gate["expected"]["combined_classification_counts"] == {
        "proof_action_expansion": 2,
    }
    assert gate["combined_classification_counts"] == {
        "proof_action_expansion": 2,
    }
    validate_phase0b_unknown_reason_correspondence_gate(gate)


def test_phase0b_unknown_reason_correspondence_gate_rejects_unknown_selected_category(tmp_path):
    raw_dir = _write_fixture(tmp_path)

    with pytest.raises(ValueError, match="unknown --category value"):
        build_phase0b_unknown_reason_correspondence_gate(
            baseline_raw_dir=raw_dir,
            output_dir=tmp_path / "gate",
            categories=("functoin_call",),
        )


def test_phase0b_unknown_reason_correspondence_gate_rejects_duplicate_selected_category(tmp_path):
    raw_dir = _write_fixture(tmp_path)

    with pytest.raises(ValueError, match="duplicate --category value"):
        build_phase0b_unknown_reason_correspondence_gate(
            baseline_raw_dir=raw_dir,
            output_dir=tmp_path / "gate",
            categories=("function_call", "function_call"),
        )


def test_phase0b_validator_rejects_tampered_ready_summary(tmp_path):
    raw_dir = _write_fixture(tmp_path)

    path = build_phase0b_unknown_reason_correspondence_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        **_fixture_expected_classification_counts(),
    )
    gate = json.loads(path.read_text())
    gate["checks"][0]["status"] = "failed"
    gate["summary"]["failed"] = 0
    gate["summary"]["failed_kinds"] = []
    gate["phase0b_unknown_reason_correspondence_ready"] = True

    with pytest.raises(ValueError, match="summary_failed_mismatch"):
        validate_phase0b_unknown_reason_correspondence_gate(gate)


def test_phase0b_validator_rejects_tampered_combined_counts(tmp_path):
    raw_dir = _write_fixture(tmp_path)

    path = build_phase0b_unknown_reason_correspondence_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        **_fixture_expected_classification_counts(),
    )
    gate = json.loads(path.read_text())
    gate["combined_classification_counts"] = {}

    with pytest.raises(ValueError, match="combined_classification_counts_consistency"):
        validate_phase0b_unknown_reason_correspondence_gate(gate)


def test_phase0b_validator_rejects_tampered_ready_category_report(tmp_path):
    raw_dir = _write_fixture(tmp_path)

    path = build_phase0b_unknown_reason_correspondence_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        **_fixture_expected_classification_counts(),
    )
    gate = json.loads(path.read_text())
    assert gate["phase0b_unknown_reason_correspondence_ready"] is True
    gate["categories"]["function_call"]["typed_payload_count"] = 999
    gate["summary"]["failed"] = False

    with pytest.raises(ValueError, match="materialized_categories"):
        validate_phase0b_unknown_reason_correspondence_gate(gate)


def test_phase0b_validator_rejects_missing_materialized_context(tmp_path):
    raw_dir = _write_fixture(tmp_path)

    path = build_phase0b_unknown_reason_correspondence_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        **_fixture_expected_classification_counts(),
    )
    gate = json.loads(path.read_text())
    assert gate["phase0b_unknown_reason_correspondence_ready"] is True
    gate.pop("baseline_raw_artifact_ref")
    gate["categories"]["function_call"]["typed_payload_count"] = 999

    with pytest.raises(ValueError, match="materialized_context_missing"):
        validate_phase0b_unknown_reason_correspondence_gate(gate)


def test_phase0b_unknown_reason_correspondence_gate_rejects_unknown_log_without_typed_payload(tmp_path):
    raw_dir = _write_fixture(tmp_path)
    stale = raw_dir / "logs" / "function_call" / "fc_stale" / "fc_stale_B1_B2.log"
    stale.parent.mkdir(parents=True)
    stale.write_text("Result: UNKNOWN\nhuman-only diagnostic\n", encoding="utf-8")

    path = build_phase0b_unknown_reason_correspondence_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        **_fixture_expected_classification_counts(),
    )
    gate = json.loads(path.read_text())

    assert gate["phase0b_unknown_reason_correspondence_ready"] is False
    assert gate["combined_blocking_classification_counts"] == {"raw_log_missing": 1}
    with pytest.raises(ValueError, match="category_blocking_correspondence_absent"):
        validate_phase0b_unknown_reason_correspondence_gate(gate)


def test_phase0b_unknown_reason_correspondence_gate_uses_current_log_roots(tmp_path):
    raw_dir = _write_fixture(tmp_path)
    current_function = tmp_path / "current" / "function_call"
    current_loop = tmp_path / "current" / "loop"
    _copy_logs(raw_dir / "logs" / "function_call", current_function)
    _copy_logs(raw_dir / "logs" / "loop", current_loop)
    stale = current_function / "fc_stale" / "fc_stale_B1_B2.log"
    stale.parent.mkdir(parents=True)
    stale.write_text("Result: UNKNOWN\nhuman-only diagnostic\n", encoding="utf-8")

    path = build_phase0b_unknown_reason_correspondence_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_function, "loop": current_loop},
        **_fixture_expected_classification_counts(),
    )
    gate = json.loads(path.read_text())

    assert gate["phase0b_unknown_reason_correspondence_ready"] is False
    assert gate["current_log_roots"]["function_call"] == str(current_function)
    assert gate["combined_blocking_classification_counts"] == {"raw_log_missing": 1}


def test_phase0b_unknown_reason_correspondence_gate_rejects_unknown_current_log_root_category(tmp_path):
    raw_dir = _write_fixture(tmp_path)

    with pytest.raises(ValueError, match="unknown --current-log-root category"):
        build_phase0b_unknown_reason_correspondence_gate(
            baseline_raw_dir=raw_dir,
            output_dir=tmp_path / "gate",
            current_log_roots={"functoin_call": tmp_path / "does-not-exist"},
        )


def test_phase0b_unknown_reason_correspondence_gate_rejects_baseline_identity_drift(tmp_path):
    raw_dir = _write_fixture(tmp_path)
    manifest_path = raw_dir / "artifact_manifest.json"
    manifest = json.loads(manifest_path.read_text())
    manifest["git_head"] = "different"
    manifest_path.write_text(json.dumps(manifest), encoding="utf-8")

    path = build_phase0b_unknown_reason_correspondence_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        **_fixture_expected_classification_counts(),
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


def _fixture_expected_classification_counts():
    return {
        "expected_category_classification_counts": {
            "function_call": {
                "proof_action_expansion": 2,
            },
            "loop": {},
        },
        "expected_combined_classification_counts": {
            "proof_action_expansion": 2,
        },
    }


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


def _copy_logs(src: Path, dst: Path):
    for path in src.glob("*/*.log"):
        rel = path.relative_to(src)
        target = dst / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(path.read_text(encoding="utf-8"), encoding="utf-8")
