# -*- coding: utf-8 -*-

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.equivalence.unknown_reason import UnknownReasonId, make_unknown_reason
from scripts.function_tracer_pcode.validation.phase0c_observed_baseline_census_gate import (
    EXPECTED_COMBINED_UNKNOWN_BY_REASON,
    build_phase0c_observed_baseline_census_gate,
    validate_phase0c_observed_baseline_census_gate,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import RESULT_JSON_BEGIN, RESULT_JSON_END


def test_phase0c_observed_baseline_census_gate_accepts_fixture_counts(tmp_path):
    raw_dir = _write_fixture(tmp_path)

    path = build_phase0c_observed_baseline_census_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        expected_final_result_counts={
            "function_call": {"EQ": 1, "UNKNOWN": 1},
            "loop": {"NOT_EQ": 1, "TIMEOUT": 1},
        },
        expected_validation_unknown_units={"function_call": 1, "loop": 1},
        expected_category_pair_log_counts={"function_call": 2, "loop": 2},
        expected_combined_pair_log_count=4,
        expected_combined_final_result_counts={
            "EQ": 1,
            "NOT_EQ": 1,
            "UNKNOWN": 1,
            "TIMEOUT": 1,
        },
        expected_combined_validation_unknown_units=2,
        expected_combined_unknown_by_reason={
            "outcome_partition_unknown": 0,
            "return_coverage_gap": 1,
            "solver_unknown_timeout": 1,
        },
    )
    gate = json.loads(path.read_text())

    assert gate["phase0c_observed_baseline_census_ready"] is True
    assert gate["count_model"]["primary_census_count_kind"] == "validation_unknown_unit"
    assert gate["expected"]["combined_unknown_by_reason"]["outcome_partition_unknown"] == 0
    assert "outcome_partition_unknown" in gate["expected"]["known_unknown_reason_ids"]
    assert gate["observed"]["combined_pair_log_count"] == 4
    assert gate["observed"]["combined_validation_unknown_units"] == 2
    validate_phase0c_observed_baseline_census_gate(gate)


def test_phase0c_default_expected_reasons_include_outcome_partition_unknown():
    assert EXPECTED_COMBINED_UNKNOWN_BY_REASON["outcome_partition_unknown"] == 0


def test_phase0c_observed_baseline_census_gate_rejects_reason_drift(tmp_path):
    raw_dir = _write_fixture(tmp_path)

    path = build_phase0c_observed_baseline_census_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        expected_final_result_counts={
            "function_call": {"EQ": 1, "UNKNOWN": 1},
            "loop": {"NOT_EQ": 1, "TIMEOUT": 1},
        },
        expected_validation_unknown_units={"function_call": 1, "loop": 1},
        expected_category_pair_log_counts={"function_call": 2, "loop": 2},
        expected_combined_pair_log_count=4,
        expected_combined_final_result_counts={
            "EQ": 1,
            "NOT_EQ": 1,
            "UNKNOWN": 1,
            "TIMEOUT": 1,
        },
        expected_combined_validation_unknown_units=2,
        expected_combined_unknown_by_reason={"return_width_bridge_missing": 2},
    )
    gate = json.loads(path.read_text())

    assert gate["phase0c_observed_baseline_census_ready"] is False
    with pytest.raises(ValueError, match="combined_unknown_by_reason_expected"):
        validate_phase0c_observed_baseline_census_gate(gate)


def test_phase0c_observed_baseline_census_gate_rejects_baseline_identity_drift(tmp_path):
    raw_dir = _write_fixture(tmp_path)
    manifest_path = raw_dir / "artifact_manifest.json"
    manifest = json.loads(manifest_path.read_text())
    manifest["baseline_id"] = "observed-v0@different"
    manifest_path.write_text(json.dumps(manifest), encoding="utf-8")

    path = build_phase0c_observed_baseline_census_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        expected_final_result_counts={
            "function_call": {"EQ": 1, "UNKNOWN": 1},
            "loop": {"NOT_EQ": 1, "TIMEOUT": 1},
        },
        expected_validation_unknown_units={"function_call": 1, "loop": 1},
        expected_category_pair_log_counts={"function_call": 2, "loop": 2},
        expected_combined_pair_log_count=4,
        expected_combined_final_result_counts={
            "EQ": 1,
            "NOT_EQ": 1,
            "UNKNOWN": 1,
            "TIMEOUT": 1,
        },
        expected_combined_validation_unknown_units=2,
        expected_combined_unknown_by_reason={
            "return_coverage_gap": 1,
            "solver_unknown_timeout": 1,
        },
    )
    gate = json.loads(path.read_text())

    assert gate["phase0c_observed_baseline_census_ready"] is False
    with pytest.raises(ValueError, match="baseline_id_expected"):
        validate_phase0c_observed_baseline_census_gate(gate)


def test_phase0c_observed_baseline_census_gate_rejects_duplicate_pair_identity(tmp_path):
    raw_dir = _write_fixture(tmp_path)
    duplicate = raw_dir / "logs" / "function_call" / "fc_demo_alias" / "fc_demo_alias_B2_B1.log"
    _write_log(
        duplicate,
        "Result: EQUIVALENT",
        _payload("fc_guarded_call", True),
    )

    path = build_phase0c_observed_baseline_census_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        expected_final_result_counts={
            "function_call": {"EQ": 2, "UNKNOWN": 1},
            "loop": {"NOT_EQ": 1, "TIMEOUT": 1},
        },
        expected_validation_unknown_units={"function_call": 1, "loop": 1},
        expected_category_pair_log_counts={"function_call": 3, "loop": 2},
        expected_combined_pair_log_count=5,
        expected_combined_final_result_counts={
            "EQ": 2,
            "NOT_EQ": 1,
            "UNKNOWN": 1,
            "TIMEOUT": 1,
        },
        expected_combined_validation_unknown_units=2,
        expected_combined_unknown_by_reason={
            "return_coverage_gap": 1,
            "solver_unknown_timeout": 1,
        },
    )
    gate = json.loads(path.read_text())

    assert gate["phase0c_observed_baseline_census_ready"] is False
    with pytest.raises(ValueError, match="category_pair_identities_unique"):
        validate_phase0c_observed_baseline_census_gate(gate)


def test_phase0c_observed_baseline_census_gate_rejects_tampered_ready_observed_counts(tmp_path):
    raw_dir = _write_fixture(tmp_path)

    path = build_phase0c_observed_baseline_census_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        expected_final_result_counts={
            "function_call": {"EQ": 1, "UNKNOWN": 1},
            "loop": {"NOT_EQ": 1, "TIMEOUT": 1},
        },
        expected_validation_unknown_units={"function_call": 1, "loop": 1},
        expected_category_pair_log_counts={"function_call": 2, "loop": 2},
        expected_combined_pair_log_count=4,
        expected_combined_final_result_counts={
            "EQ": 1,
            "NOT_EQ": 1,
            "UNKNOWN": 1,
            "TIMEOUT": 1,
        },
        expected_combined_validation_unknown_units=2,
        expected_combined_unknown_by_reason={
            "return_coverage_gap": 1,
            "solver_unknown_timeout": 1,
        },
    )
    gate = json.loads(path.read_text())
    assert gate["phase0c_observed_baseline_census_ready"] is True

    gate["observed"]["combined_pair_log_count"] = 999
    gate["summary"]["failed"] = False

    with pytest.raises(ValueError, match="materialized_observed"):
        validate_phase0c_observed_baseline_census_gate(gate)


def test_phase0c_observed_baseline_census_gate_rejects_missing_materialized_context(tmp_path):
    raw_dir = _write_fixture(tmp_path)

    path = build_phase0c_observed_baseline_census_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        expected_final_result_counts={
            "function_call": {"EQ": 1, "UNKNOWN": 1},
            "loop": {"NOT_EQ": 1, "TIMEOUT": 1},
        },
        expected_validation_unknown_units={"function_call": 1, "loop": 1},
        expected_category_pair_log_counts={"function_call": 2, "loop": 2},
        expected_combined_pair_log_count=4,
        expected_combined_final_result_counts={
            "EQ": 1,
            "NOT_EQ": 1,
            "UNKNOWN": 1,
            "TIMEOUT": 1,
        },
        expected_combined_validation_unknown_units=2,
        expected_combined_unknown_by_reason={
            "return_coverage_gap": 1,
            "solver_unknown_timeout": 1,
        },
    )
    gate = json.loads(path.read_text())
    assert gate["phase0c_observed_baseline_census_ready"] is True

    gate.pop("baseline_raw_artifact_ref")
    gate["observed"]["combined_pair_log_count"] = 999

    with pytest.raises(ValueError, match="materialized_context_missing"):
        validate_phase0c_observed_baseline_census_gate(gate)


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
            unknown_reasons=[make_unknown_reason(UnknownReasonId.RETURN_COVERAGE_GAP).to_dict()],
        ),
    )
    _write_log(
        raw_dir / "logs" / "function_call" / "fc_guarded_call" / "fc_guarded_call_B1_B3.log",
        "Result: EQUIVALENT",
        _payload("fc_guarded_call", True),
    )
    _write_log(
        raw_dir / "logs" / "loop" / "lmb_sum" / "lmb_sum_B1_B2.log",
        "Result: NOT EQUIVALENT",
        _payload("lmb_sum", False),
    )
    _write_log(
        raw_dir / "logs" / "loop" / "lmb_sum" / "lmb_sum_B1_B3.log",
        "Result: TIMEOUT",
        _payload(
            "lmb_sum",
            None,
            is_timeout=True,
            unknown_reasons=[make_unknown_reason(UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT).to_dict()],
        ),
    )
    _write_overall_summary(
        raw_dir / "logs" / "function_call" / "overall_summary.txt",
        {
            "return_coverage_gap": 1,
        },
    )
    _write_overall_summary(
        raw_dir / "logs" / "loop" / "overall_summary.txt",
        {
            "solver_unknown_timeout": 1,
        },
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


def _write_overall_summary(path: Path, unknown_by_reason):
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        "UNKNOWN reason summary:",
        "    UNKNOWN by reason:",
    ]
    for reason, count in sorted(unknown_by_reason.items()):
        lines.append(f"      - {reason}: {count}")
    lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")
