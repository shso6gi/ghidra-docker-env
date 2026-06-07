# -*- coding: utf-8 -*-

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.equivalence.unknown_reason import UnknownReasonId, make_unknown_reason
from scripts.function_tracer_pcode.validation.phase0c_canonical_reproduction_gate import (
    build_phase0c_canonical_reproduction_gate,
    validate_phase0c_canonical_reproduction_gate,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import RESULT_JSON_BEGIN, RESULT_JSON_END


def test_phase0c_canonical_reproduction_gate_accepts_exact_reproduction(tmp_path):
    raw_dir = _write_fixture(tmp_path)

    path = build_phase0c_canonical_reproduction_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={
            "function_call": raw_dir / "logs" / "function_call",
            "loop": raw_dir / "logs" / "loop",
        },
    )
    gate = json.loads(path.read_text())

    assert gate["phase0c_canonical_reproduction_ready"] is True
    assert gate["combined_comparison"]["before_total_results"] == 4
    validate_phase0c_canonical_reproduction_gate(gate)


def test_phase0c_canonical_reproduction_gate_rejects_final_result_drift(tmp_path):
    raw_dir = _write_fixture(tmp_path)
    current_function = tmp_path / "current" / "function_call"
    current_loop = tmp_path / "current" / "loop"
    _copy_logs(raw_dir / "logs" / "function_call", current_function)
    _copy_logs(raw_dir / "logs" / "loop", current_loop)
    _write_log(
        current_function / "fc_demo" / "fc_demo_B1_B2.log",
        "Result: EQUIVALENT",
        _payload("fc_demo", True),
    )

    path = build_phase0c_canonical_reproduction_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_function, "loop": current_loop},
    )
    gate = json.loads(path.read_text())

    assert gate["phase0c_canonical_reproduction_ready"] is False
    with pytest.raises(ValueError, match="canonical_reproduction_final_result_counts"):
        validate_phase0c_canonical_reproduction_gate(gate)


def test_phase0c_canonical_reproduction_gate_rejects_reason_tuple_drift(tmp_path):
    raw_dir = _write_fixture(tmp_path)
    current_function = tmp_path / "current" / "function_call"
    current_loop = tmp_path / "current" / "loop"
    _copy_logs(raw_dir / "logs" / "function_call", current_function)
    _copy_logs(raw_dir / "logs" / "loop", current_loop)
    _write_log(
        current_function / "fc_demo" / "fc_demo_B1_B2.log",
        "Result: UNKNOWN",
        _payload(
            "fc_demo",
            None,
            unknown_reasons=[make_unknown_reason(UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING).to_dict()],
        ),
    )

    path = build_phase0c_canonical_reproduction_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_function, "loop": current_loop},
    )
    gate = json.loads(path.read_text())

    assert gate["phase0c_canonical_reproduction_ready"] is False
    with pytest.raises(ValueError, match="canonical_reproduction_validation_unknown_unit_multiset"):
        validate_phase0c_canonical_reproduction_gate(gate)


def test_phase0c_canonical_reproduction_gate_rejects_missing_pair(tmp_path):
    raw_dir = _write_fixture(tmp_path)
    current_function = tmp_path / "current" / "function_call"
    current_loop = tmp_path / "current" / "loop"
    _copy_logs(raw_dir / "logs" / "function_call", current_function)
    _copy_logs(raw_dir / "logs" / "loop", current_loop)
    (current_loop / "lmb_demo" / "lmb_demo_B1_B3.log").unlink()

    path = build_phase0c_canonical_reproduction_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_function, "loop": current_loop},
    )
    gate = json.loads(path.read_text())

    assert gate["phase0c_canonical_reproduction_ready"] is False
    with pytest.raises(ValueError, match="canonical_reproduction_pair_identities"):
        validate_phase0c_canonical_reproduction_gate(gate)


def test_phase0c_canonical_reproduction_gate_rejects_unknown_current_log_root_category(tmp_path):
    raw_dir = _write_fixture(tmp_path)

    with pytest.raises(ValueError, match="unknown --current-log-root category"):
        build_phase0c_canonical_reproduction_gate(
            baseline_raw_dir=raw_dir,
            output_dir=tmp_path / "gate",
            current_log_roots={"functoin_call": tmp_path / "does-not-exist"},
        )


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
        raw_dir / "logs" / "function_call" / "fc_demo" / "fc_demo_B1_B2.log",
        "Result: UNKNOWN",
        _payload(
            "fc_demo",
            None,
            left_binary="B1",
            right_binary="B2",
            unknown_reasons=[make_unknown_reason(UnknownReasonId.RETURN_COVERAGE_GAP).to_dict()],
        ),
    )
    _write_log(
        raw_dir / "logs" / "function_call" / "fc_demo" / "fc_demo_B1_B3.log",
        "Result: EQUIVALENT",
        _payload("fc_demo", True, left_binary="B1", right_binary="B3"),
    )
    _write_log(
        raw_dir / "logs" / "loop" / "lmb_demo" / "lmb_demo_B1_B2.log",
        "Result: NOT EQUIVALENT",
        _payload("lmb_demo", False, left_binary="B1", right_binary="B2"),
    )
    _write_log(
        raw_dir / "logs" / "loop" / "lmb_demo" / "lmb_demo_B1_B3.log",
        "Result: TIMEOUT",
        _payload(
            "lmb_demo",
            None,
            left_binary="B1",
            right_binary="B3",
            is_timeout=True,
            timeout_class="solver_timeout",
            unknown_reasons=[make_unknown_reason(UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT).to_dict()],
        ),
    )
    return raw_dir


def _payload(function_name, is_equivalent, *, left_binary="left.bin", right_binary="right.bin", **extra):
    payload = {
        "function1_name": function_name,
        "function2_name": function_name,
        "binary1_name": left_binary,
        "binary2_name": right_binary,
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
