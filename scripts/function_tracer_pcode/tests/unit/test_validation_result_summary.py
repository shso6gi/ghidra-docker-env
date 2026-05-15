# -*- coding: utf-8 -*-

import json
import subprocess
import sys
from pathlib import Path

from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    UnknownReasonId,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.validation.result_summary import (
    STATUS_EQ,
    STATUS_ERROR,
    STATUS_INCOMPLETE,
    STATUS_NOT_EQ,
    STATUS_TIMEOUT,
    STATUS_UNKNOWN,
    aggregate_validation_logs,
    aggregate_validation_logs_by_function,
    assert_aggregation_invariant,
    classify_log_text,
    compare_validation_baseline_records,
    format_function_results_summary,
    format_overall_results_summary,
    format_validation_baseline_comparison,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
)


def _write_log(tmp_path, name, human_result, payload=None):
    path = tmp_path / name
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = [human_result]
    if payload is not None:
        lines.extend(
            [
                RESULT_JSON_BEGIN,
                json.dumps(payload),
                RESULT_JSON_END,
            ]
        )
    path.write_text("\n".join(lines))
    return path


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


def test_validation_classifier_prefers_typed_payload_over_human_text():
    payload = _payload("fc_read_after_void", None)

    text = "\n".join(
        [
            "Result: EQUIVALENT ✓",
            RESULT_JSON_BEGIN,
            json.dumps(payload),
            RESULT_JSON_END,
        ]
    )

    assert classify_log_text(text) == STATUS_UNKNOWN


def test_validation_classifier_marks_markerless_resultless_logs_incomplete():
    assert classify_log_text("debug output without final result") == STATUS_INCOMPLETE


def test_function_and_overall_summary_share_aggregator_invariant(tmp_path):
    logs = [
        _write_log(
            tmp_path,
            "fc_read_after_void_B1_B2.log",
            "Result: UNKNOWN (could not determine equivalence)",
            _payload(
                "fc_read_after_void",
                None,
                unknown_reasons=[
                    make_unknown_reason(UnknownReasonId.RETURN_COVERAGE_GAP).to_dict()
                ],
            ),
        ),
        _write_log(
            tmp_path,
            "fc_read_after_void_B1_B3.log",
            "Result: EQUIVALENT ✓",
            _payload("fc_read_after_void", True),
        ),
        _write_log(
            tmp_path,
            "ptr_call_and_store_B1_B2.log",
            "Result: NOT EQUIVALENT ✗",
            _payload("ptr_call_and_store", False),
        ),
        _write_log(
            tmp_path,
            "ptr_call_and_store_B1_B3.log",
            "Result: ERROR",
            _payload("ptr_call_and_store", None, error_message="boom"),
        ),
        _write_log(
            tmp_path,
            "ptr_call_and_store_B1_B4.log",
            "Result: TIMEOUT",
            _payload("ptr_call_and_store", None, is_timeout=True),
        ),
        _write_log(
            tmp_path,
            "ptr_call_and_store_B1_B5.log",
            "truncated before result",
        ),
    ]

    fc_summary = aggregate_validation_logs(logs[:2])
    ptr_summary = aggregate_validation_logs(logs[2:])
    overall = aggregate_validation_logs_by_function(logs)

    assert_aggregation_invariant(overall)
    assert fc_summary.count(STATUS_EQ) + ptr_summary.count(STATUS_EQ) == overall.overall.count(STATUS_EQ)
    assert fc_summary.count(STATUS_NOT_EQ) + ptr_summary.count(STATUS_NOT_EQ) == overall.overall.count(STATUS_NOT_EQ)
    assert fc_summary.count(STATUS_ERROR) + ptr_summary.count(STATUS_ERROR) == overall.overall.count(STATUS_ERROR)
    assert fc_summary.count(STATUS_UNKNOWN) + ptr_summary.count(STATUS_UNKNOWN) == overall.overall.count(STATUS_UNKNOWN)
    assert fc_summary.count(STATUS_TIMEOUT) + ptr_summary.count(STATUS_TIMEOUT) == overall.overall.count(STATUS_TIMEOUT)
    assert (
        fc_summary.count(STATUS_INCOMPLETE) + ptr_summary.count(STATUS_INCOMPLETE)
        == overall.overall.count(STATUS_INCOMPLETE)
    )
    assert overall.overall.count(STATUS_INCOMPLETE) == 1

    function_text = format_function_results_summary(
        "fc_read_after_void",
        fc_summary,
        elapsed_seconds=65.25,
    )
    overall_text = format_overall_results_summary(
        overall,
        function_wall_times={"fc_read_after_void": 65.25},
    )

    assert "Unknown        : 1" in function_text
    assert "INCOMPLETE" in overall_text
    assert "UNKNOWN by reason:" in function_text
    assert "return_coverage_gap" in function_text
    assert "UNKNOWN validation before/after delta:" in function_text
    assert "Baseline: unavailable" in function_text
    assert "fc_read_after_void" in overall_text
    assert "ptr_call_and_store" in overall_text
    assert "Overall totals" in overall_text
    assert "UNKNOWN by reason:" in overall_text
    assert "UNKNOWN validation before/after delta:" in overall_text


def test_result_summary_module_accepts_function_wall_time_option():
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "scripts.function_tracer_pcode.validation.result_summary",
            "--overall-summary",
            "--function-wall-time",
            "fc_read_after_void=1.25",
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    assert "RuntimeWarning" not in result.stderr
    assert "All functions processed" in result.stdout


def test_result_summary_require_before_dir_rejects_unavailable_baseline():
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "scripts.function_tracer_pcode.validation.result_summary",
            "--overall-summary",
            "--require-before-dir",
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode != 0
    assert "--require-before-dir requires --before-dir" in result.stderr


def test_result_summary_require_before_dir_emits_real_delta(tmp_path):
    before_dir = tmp_path / "before"
    before_dir.mkdir()
    after_log = tmp_path / "after" / "fc_read_after_void_B1_B2.log"
    after_log.parent.mkdir()
    _write_log(
        before_dir,
        "fc_read_after_void_B1_B2.log",
        "Result: UNKNOWN",
        _payload(
            "fc_read_after_void",
            None,
            unknown_reasons=[
                make_unknown_reason(UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING).to_dict()
            ],
        ),
    )
    _write_log(
        after_log.parent,
        after_log.name,
        "Result: UNKNOWN",
        _payload(
            "fc_read_after_void",
            None,
            unknown_reasons=[
                make_unknown_reason(UnknownReasonId.RETURN_COVERAGE_GAP).to_dict()
            ],
        ),
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "scripts.function_tracer_pcode.validation.result_summary",
            "--function-summary",
            "--function-name",
            "fc_read_after_void",
            "--before-dir",
            str(before_dir),
            "--require-before-dir",
            str(after_log),
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    assert "UNKNOWN validation before/after delta:" in result.stdout
    assert "Baseline: unavailable" not in result.stdout
    assert "- return_coverage_gap: 1" in result.stdout
    assert "- return_width_bridge_missing: -1" in result.stdout


def test_canonical_baseline_comparison_uses_sorted_binary_pair_and_reason_tuples(tmp_path):
    before_log = _write_log(
        tmp_path / "before",
        "fc_apply_indirect_B2_B1.log",
        "Result: UNKNOWN",
        _payload(
            "fc_apply_indirect",
            None,
            binary1_name="function_call_test-mips64-clang-O2",
            binary2_name="function_call_test-mips64-clang-O1",
            unknown_reasons=[
                make_unknown_reason(
                    UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY,
                    recovery_proof_kind=UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
                    proof_stage="object_evidence_collected",
                    action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
                ).to_dict()
            ],
        ),
    )
    after_log = _write_log(
        tmp_path / "after",
        "fc_apply_indirect_B1_B2.log",
        "Result: UNKNOWN",
        _payload(
            "fc_apply_indirect",
            None,
            binary1_name="function_call_test-mips64-clang-O1",
            binary2_name="function_call_test-mips64-clang-O2",
            unknown_reasons=[
                make_unknown_reason(
                    UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY,
                    recovery_proof_kind=UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
                    proof_stage="object_evidence_collected",
                    action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
                ).to_dict()
            ],
        ),
    )
    before = aggregate_validation_logs([before_log])
    after = aggregate_validation_logs([after_log])

    comparison = compare_validation_baseline_records(before.records, after.records)

    assert not comparison.has_differences()
    assert comparison.pair_result_multiset_delta == {}
    assert comparison.validation_unknown_unit_multiset_delta == {}
    assert comparison.proof_action_multiset_delta == {}


def test_canonical_baseline_comparison_reports_pair_and_timeout_deltas(tmp_path):
    before_log = _write_log(
        tmp_path / "before",
        "fc_apply_indirect_B1_B2.log",
        "Result: TIMEOUT",
        _payload(
            "fc_apply_indirect",
            None,
            binary1_name="function_call_test-mips64-clang-O1",
            binary2_name="function_call_test-mips64-clang-O2",
            is_timeout=True,
            timeout_class="solver_timeout",
        ),
    )
    after_log = _write_log(
        tmp_path / "after",
        "fc_apply_indirect_B1_B2.log",
        "Result: UNKNOWN",
        _payload(
            "fc_apply_indirect",
            None,
            binary1_name="function_call_test-mips64-clang-O1",
            binary2_name="function_call_test-mips64-clang-O2",
            unknown_reasons=[
                make_unknown_reason(UnknownReasonId.RETURN_COVERAGE_GAP).to_dict()
            ],
        ),
    )
    before = aggregate_validation_logs([before_log])
    after = aggregate_validation_logs([after_log])

    comparison = compare_validation_baseline_records(before.records, after.records)
    text = format_validation_baseline_comparison(comparison)

    assert comparison.has_differences()
    assert comparison.final_result_counts_delta == {
        STATUS_TIMEOUT: -1,
        STATUS_UNKNOWN: 1,
    }
    assert comparison.timeout_class_multiset_delta == {"solver_timeout": -1}
    assert comparison.timeout_final_results_delta == -1
    assert comparison.unknown_final_results_delta == 1
    assert any(
        key[0] == "fc_apply_indirect"
        and key[2] == STATUS_TIMEOUT
        and value == -1
        for key, value in comparison.pair_result_multiset_delta.items()
    )
    assert "Canonical baseline comparison:" in text
    assert "Pair result tuple delta:" in text
    assert "solver_timeout: -1" in text


def test_result_summary_require_baseline_match_rejects_canonical_mismatch(tmp_path):
    before_dir = tmp_path / "before"
    after_dir = tmp_path / "after"
    before_dir.mkdir()
    after_dir.mkdir()
    before_log = _write_log(
        before_dir,
        "fc_apply_indirect_B1_B2.log",
        "Result: UNKNOWN",
        _payload("fc_apply_indirect", None),
    )
    after_log = _write_log(
        after_dir,
        "fc_apply_indirect_B1_B2.log",
        "Result: EQUIVALENT",
        _payload("fc_apply_indirect", True),
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "scripts.function_tracer_pcode.validation.result_summary",
            "--function-summary",
            "--function-name",
            "fc_apply_indirect",
            "--before-dir",
            str(before_dir),
            "--require-before-dir",
            "--require-baseline-match",
            str(after_log),
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode != 0
    assert "Canonical baseline comparison:" in result.stdout
    assert "baseline comparison mismatch" in result.stderr
    assert before_log.is_file()


def test_matrix_runners_update_summary_outputs_only_after_success():
    script_paths = (
        "loop_run_matrix_all_parallel_multifunc.sh",
        "mem_run_matrix_all_parallel_multifunc.sh",
        "pointer_run_matrix_all_parallel_multifunc.sh",
        "run_matrix_all_parallel_multifunc.sh",
        "copy_run_matrix_all_parallel_multifunc.sh",
        "func_call_run_matrix_all_parallel_multifunc.sh",
    )

    for script_path in script_paths:
        script = Path(script_path).read_text()
        assert "VALIDATION_REQUIRE_BEFORE_DELTA=${VALIDATION_REQUIRE_BEFORE_DELTA:-0}" in script
        assert "VALIDATION_REQUIRE_BASELINE_MATCH=${VALIDATION_REQUIRE_BASELINE_MATCH:-0}" in script
        assert "write_summary_file()" in script
        assert "FUNCTION_SUMMARY_ARGS+=(--require-before-dir)" in script
        assert "OVERALL_SUMMARY_ARGS+=(--require-before-dir)" in script
        assert "FUNCTION_SUMMARY_ARGS+=(--require-baseline-match)" in script
        assert "OVERALL_SUMMARY_ARGS+=(--require-baseline-match)" in script
        assert '} | tee "$RESULT_FILE"' not in script
        assert '} | tee "$SUMMARY_FILE"' not in script


def test_function_call_runner_supports_full_phase2_parallel_mode():
    script = Path("func_call_run_matrix_all_parallel_multifunc.sh").read_text()

    assert "FUNCTION_CALL_TARGET_SET=${FUNCTION_CALL_TARGET_SET:-configured}" in script
    assert 'cd "$SCRIPT_DIR"' in script
    assert "FULL20_TARGET_FUNCS=(" in script
    assert '"fc_apply_indirect"' in script
    assert '"fc_dispatch_indirect"' in script
    assert '"fc_recursive_sum"' in script
    assert "PYTHON_BIN=${PYTHON_BIN:-python3}" in script
    assert "VALIDATION_SKIP_COMPLETED=${VALIDATION_SKIP_COMPLETED:-0}" in script
    assert "RUNNER_TMP_ROOT=${RUNNER_TMP_ROOT:-" in script
    assert 'TMPDIR="$PAIR_TMPDIR" "$PYTHON_BIN" -m scripts.function_tracer_pcode.cli.main' in script
    assert " | sort)" in script
    assert "local status=$?" in script


def test_phase2_full_function_call_wrapper_defaults_to_safe_full_run():
    script = Path("phase2_run_function_call_full_matrix_32jobs.sh").read_text()

    assert 'FUNCTION_CALL_TARGET_SET="${FUNCTION_CALL_TARGET_SET:-full20}"' in script
    assert 'cd "$SCRIPT_DIR"' in script
    assert 'PARALLEL_JOBS="${PARALLEL_JOBS:-32}"' in script
    assert "function_call_test_phase2_full_pre_producer" in script
    assert "artifacts/baselines/observed-v0@0a53352/raw/logs/function_call" in script
    assert 'VALIDATION_REQUIRE_BEFORE_DELTA="${VALIDATION_REQUIRE_BEFORE_DELTA:-1}"' in script
    assert 'VALIDATION_REQUIRE_BEFORE_DELTA="${VALIDATION_REQUIRE_BEFORE_DELTA:-0}"' in script
    assert 'VALIDATION_REQUIRE_BASELINE_MATCH="${VALIDATION_REQUIRE_BASELINE_MATCH:-0}"' in script
    assert 'VALIDATION_SKIP_COMPLETED="${VALIDATION_SKIP_COMPLETED:-1}"' in script
    assert "validation_before_dir=${VALIDATION_BEFORE_DIR:-}" in script
    assert "baseline_note=$BASELINE_NOTE" in script
    assert "Skipping Phase 2 gate:" in script
    assert "phase2_equivalence_blocking_unsafety" in script
    assert "files_to_copy_for_codex.txt" in script
