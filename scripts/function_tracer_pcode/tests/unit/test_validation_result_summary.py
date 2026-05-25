# -*- coding: utf-8 -*-

import json
import os
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
    assert "FUNCTION_CALL_MANIFEST=${FUNCTION_CALL_MANIFEST:-" in script
    assert "manifest_query functions" in script
    assert "manifest_query pairs" in script
    assert "VALIDATION_SKIP_COMPLETED=${VALIDATION_SKIP_COMPLETED:-0}" in script
    assert "VALIDATION_RUNNER_DRY_RUN=${VALIDATION_RUNNER_DRY_RUN:-0}" in script
    assert "FUNCTION_CALL_PAIR_FILTER=${FUNCTION_CALL_PAIR_FILTER:-}" in script
    assert "function_call_pair_filter_allows" in script
    assert "validate_function_call_pair_filter" in script
    assert "RUNNER_TMP_ROOT=${RUNNER_TMP_ROOT:-" in script
    assert 'TMPDIR="$PAIR_TMPDIR" "$PYTHON_BIN" -m scripts.function_tracer_pcode.cli.main' in script
    assert "BINARY_ID_ORDER=(" in script
    assert 'collect_expected_log_files "$OUTPUT_DIR" "$TARGET_FUNC"' in script
    assert "collect_all_expected_log_files" in script
    assert 'mapfile -t PAIR_SPECS < <(collect_pair_specs "$TARGET_FUNC")' in script
    assert " | sort)" not in script
    assert "local status=$?" in script


def test_function_call_runner_dry_run_uses_baseline_pair_order(tmp_path):
    env = os.environ.copy()
    env.update(
        {
            "FUNCTION_CALL_TARGET_SET": "fc_dummy",
            "OUTPUT_BASE_DIR": str(tmp_path / "function_call"),
            "VALIDATION_AUTO_BEFORE_SNAPSHOT": "0",
            "VALIDATION_RUNNER_DRY_RUN": "1",
        }
    )

    result = subprocess.run(
        ["bash", "func_call_run_matrix_all_parallel_multifunc.sh"],
        check=True,
        capture_output=True,
        text=True,
        env=env,
    )

    assert "Binary ID order: B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 B13 B14 B15 B16" in result.stdout
    assert "fc_dummy B1 B2 fc_dummy_B1_B2.log" in result.stdout
    assert "fc_dummy B8 B15 fc_dummy_B8_B15.log" in result.stdout
    assert "fc_dummy B15 B8 fc_dummy_B15_B8.log" not in result.stdout


def test_function_call_runner_dry_run_filters_concrete_pairs(tmp_path):
    env = os.environ.copy()
    env.update(
        {
            "FUNCTION_CALL_TARGET_SET": "fc_recursive_sum,fc_is_even",
            "FUNCTION_CALL_PAIR_FILTER": "fc_recursive_sum:B11_B15,fc_is_even:B11_B12",
            "OUTPUT_BASE_DIR": str(tmp_path / "function_call"),
            "VALIDATION_AUTO_BEFORE_SNAPSHOT": "0",
            "VALIDATION_RUNNER_DRY_RUN": "1",
        }
    )

    result = subprocess.run(
        ["bash", "func_call_run_matrix_all_parallel_multifunc.sh"],
        check=True,
        capture_output=True,
        text=True,
        env=env,
    )

    assert "Function/pair filter: fc_recursive_sum:B11_B15,fc_is_even:B11_B12" in result.stdout
    assert "fc_recursive_sum B11 B15 fc_recursive_sum_B11_B15.log" in result.stdout
    assert "fc_is_even B11 B12 fc_is_even_B11_B12.log" in result.stdout
    assert "fc_recursive_sum B1 B2 fc_recursive_sum_B1_B2.log" not in result.stdout
    assert "fc_is_even B1 B2 fc_is_even_B1_B2.log" not in result.stdout


def test_function_call_runner_dry_run_rejects_unmatched_pair_filter(tmp_path):
    env = os.environ.copy()
    env.update(
        {
            "FUNCTION_CALL_TARGET_SET": "fc_recursive_sum",
            "FUNCTION_CALL_PAIR_FILTER": "fc_recursive_sum:B99_B100",
            "OUTPUT_BASE_DIR": str(tmp_path / "function_call"),
            "VALIDATION_AUTO_BEFORE_SNAPSHOT": "0",
            "VALIDATION_RUNNER_DRY_RUN": "1",
        }
    )

    result = subprocess.run(
        ["bash", "func_call_run_matrix_all_parallel_multifunc.sh"],
        check=False,
        capture_output=True,
        text=True,
        env=env,
    )

    assert result.returncode != 0
    assert "FUNCTION_CALL_PAIR_FILTER selected zero pairs for target function: fc_recursive_sum" in result.stderr
    assert "fc_recursive_sum:B99_B100" in result.stderr


def test_function_call_runner_dry_run_rejects_partially_unmatched_pair_filter(tmp_path):
    env = os.environ.copy()
    env.update(
        {
            "FUNCTION_CALL_TARGET_SET": "fc_recursive_sum",
            "FUNCTION_CALL_PAIR_FILTER": "fc_recursive_sum:B11_B15,fc_recursive_sum:B99_B100",
            "OUTPUT_BASE_DIR": str(tmp_path / "function_call"),
            "VALIDATION_AUTO_BEFORE_SNAPSHOT": "0",
            "VALIDATION_RUNNER_DRY_RUN": "1",
        }
    )

    result = subprocess.run(
        ["bash", "func_call_run_matrix_all_parallel_multifunc.sh"],
        check=False,
        capture_output=True,
        text=True,
        env=env,
    )

    assert result.returncode != 0
    assert "FUNCTION_CALL_PAIR_FILTER entry did not match any selected target function pair: fc_recursive_sum:B99_B100" in result.stderr


def test_function_call_runner_moves_existing_logs_before_dry_run(tmp_path):
    output_dir = tmp_path / "function_call"
    old_log = output_dir / "fc_dummy" / "fc_dummy_B1_B2.log"
    old_log.parent.mkdir(parents=True)
    old_log.write_text("old\n")
    env = os.environ.copy()
    env.update(
        {
            "FUNCTION_CALL_TARGET_SET": "fc_dummy",
            "OUTPUT_BASE_DIR": str(output_dir),
            "VALIDATION_AUTO_BEFORE_SNAPSHOT": "1",
            "VALIDATION_RUNNER_DRY_RUN": "1",
        }
    )

    result = subprocess.run(
        ["bash", "func_call_run_matrix_all_parallel_multifunc.sh"],
        check=True,
        capture_output=True,
        text=True,
        env=env,
    )

    moved_line = next(
        line for line in result.stdout.splitlines() if line.startswith("Moved old output dir: ")
    )
    moved_dir = Path(moved_line.removeprefix("Moved old output dir: "))
    assert not old_log.exists()
    assert (moved_dir / "fc_dummy" / "fc_dummy_B1_B2.log").read_text() == "old\n"
    assert "Validation before dir:" in result.stdout
    assert "[auto moved old output]" in result.stdout


def test_loop_runner_supports_representative_pair_filter_dry_run(tmp_path):
    script = Path("loop_run_matrix_all_parallel_multifunc.sh").read_text()

    assert "LOOP_TARGET_SET=${LOOP_TARGET_SET:-configured}" in script
    assert "LOOP_PAIR_FILTER=${LOOP_PAIR_FILTER:-}" in script
    assert "VALIDATION_RUNNER_DRY_RUN=${VALIDATION_RUNNER_DRY_RUN:-0}" in script
    assert '"$PYTHON_BIN" -m scripts.function_tracer_pcode.cli.main' in script

    env = os.environ.copy()
    env.update(
        {
            "LOOP_TARGET_SET": "lmb_sum_even_index_step2",
            "LOOP_PAIR_FILTER": "lmb_sum_even_index_step2:B10_B13",
            "OUTPUT_BASE_DIR": str(tmp_path / "loop"),
            "VALIDATION_AUTO_BEFORE_SNAPSHOT": "0",
            "VALIDATION_RUNNER_DRY_RUN": "1",
        }
    )
    result = subprocess.run(
        ["bash", "loop_run_matrix_all_parallel_multifunc.sh"],
        check=True,
        capture_output=True,
        text=True,
        env=env,
    )

    assert "Dry run fixed pair order:" in result.stdout
    assert "Function: lmb_sum_even_index_step2" in result.stdout
    assert "B10_B13" in result.stdout


def test_loop_runner_rejects_unmatched_pair_filter(tmp_path):
    env = os.environ.copy()
    env.update(
        {
            "LOOP_TARGET_SET": "lmb_sum_even_index_step2",
            "LOOP_PAIR_FILTER": "lmb_sum_even_index_step2:B99_B100",
            "OUTPUT_BASE_DIR": str(tmp_path / "loop"),
            "VALIDATION_AUTO_BEFORE_SNAPSHOT": "0",
            "VALIDATION_RUNNER_DRY_RUN": "1",
        }
    )
    result = subprocess.run(
        ["bash", "loop_run_matrix_all_parallel_multifunc.sh"],
        check=False,
        capture_output=True,
        text=True,
        env=env,
    )

    assert result.returncode != 0
    assert "LOOP_PAIR_FILTER selected zero pairs" in result.stderr


def test_loop_runner_rejects_selected_pair_when_binary_is_missing(tmp_path):
    env = os.environ.copy()
    env.update(
        {
            "LOOP_TARGET_SET": "lmb_sum_even_index_step2",
            "LOOP_PAIR_FILTER": "lmb_sum_even_index_step2:B10_B13",
            "OUTPUT_BASE_DIR": str(tmp_path / "loop"),
            "BASE_PATH": str(tmp_path / "missing-binaries"),
            "VALIDATION_AUTO_BEFORE_SNAPSHOT": "0",
            "VALIDATION_RUNNER_DRY_RUN": "0",
        }
    )
    result = subprocess.run(
        ["bash", "loop_run_matrix_all_parallel_multifunc.sh"],
        check=False,
        capture_output=True,
        text=True,
        env=env,
    )

    assert result.returncode != 0
    assert "could not run because binaries were missing" in result.stderr
    assert "All compared pairs are EQUIVALENT" not in result.stdout


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
    assert 'VALIDATION_AUTO_BEFORE_SNAPSHOT="${VALIDATION_AUTO_BEFORE_SNAPSHOT:-1}"' in script
    assert "PHASE2_GATE_BASELINE_DIR=" in script
    assert "validation_before_dir=${VALIDATION_BEFORE_DIR:-}" in script
    assert "validation_moved_output_dir=${VALIDATION_MOVED_OUTPUT_DIR:-}" in script
    assert "baseline_note=$BASELINE_NOTE" in script
    assert "Skipping Phase 2 gate:" in script
    assert "phase2_equivalence_blocking_unsafety" in script
    assert "--baseline-log-root" in script
    assert "files_to_copy_for_codex.txt" in script


def test_phase3_lane1_representative_wrapper_pins_pairs_and_manifest_hash():
    script = Path("phase3_run_function_call_return_coverage_lane1_representatives.sh").read_text()

    assert 'FUNCTION_CALL_TARGET_SET="${FUNCTION_CALL_TARGET_SET:-fc_recursive_sum,fc_is_even,fc_is_odd}"' in script
    assert (
        'FUNCTION_CALL_PAIR_FILTER="${FUNCTION_CALL_PAIR_FILTER:-'
        'fc_recursive_sum:B11_B15,fc_is_even:B11_B12,'
        'fc_is_odd:B8_B15,fc_is_odd:B11_B16,fc_is_odd:B12_B16}"'
    ) in script
    assert ".venv-pyghidra/bin/python" in script
    assert "phase3_return_coverage_lane1_reclassification/return_coverage_lane1_representatives.json" in script
    assert "eec876a6473ac4ac344d846bdffb93d7bbcf23d55559d0c6d58ee890304e6f5a" in script
    assert 'VALIDATION_RUNNER_DRY_RUN="${VALIDATION_RUNNER_DRY_RUN:-0}"' in script
    assert "Phase 3 lane 1 dry run finished before post-fix gate." in script
    assert 'PHASE3_REQUIRE_READY="${PHASE3_REQUIRE_READY:-1}"' in script
    assert 'BASELINE_FUNCTION_CALL_LOG_ROOT="${BASELINE_FUNCTION_CALL_LOG_ROOT:-$BASELINE_RAW_DIR/logs/function_call}"' in script
    assert '--baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT"' in script
    assert "--phase3-manifest-sha256" in script
    assert "--gate-stage post-fix" in script
    assert "PHASE3_GATE_ARGS+=(--require-ready)" in script


def test_phase3_lane2_representative_wrapper_pins_pair_and_manifest_hash():
    script = Path("phase3_run_function_call_return_width_bridge_lane2_representatives.sh").read_text()

    assert 'FUNCTION_CALL_TARGET_SET="${FUNCTION_CALL_TARGET_SET:-fc_apply_indirect}"' in script
    assert 'FUNCTION_CALL_PAIR_FILTER="${FUNCTION_CALL_PAIR_FILTER:-fc_apply_indirect:B10_B13}"' in script
    assert ".venv-pyghidra/bin/python" in script
    assert "phase3_return_width_bridge_lane2/return_width_bridge_lane2_representatives.json" in script
    assert "93629d92cd8bfcf0431eb8fc6bbd8e1c36dd71d9e4aca97e70bdfd962edf90d0" in script
    assert 'VALIDATION_RUNNER_DRY_RUN="${VALIDATION_RUNNER_DRY_RUN:-0}"' in script
    assert "Phase 3 lane 2 dry run finished before post-fix gate." in script
    assert 'PHASE3_REQUIRE_READY="${PHASE3_REQUIRE_READY:-1}"' in script
    assert 'BASELINE_FUNCTION_CALL_LOG_ROOT="${BASELINE_FUNCTION_CALL_LOG_ROOT:-$BASELINE_RAW_DIR/logs/function_call}"' in script
    assert '--baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT"' in script
    assert "--phase3-manifest-sha256" in script
    assert "--gate-stage post-fix" in script
    assert "PHASE3_GATE_ARGS+=(--require-ready)" in script


def test_phase3_lane3_readonly_representative_wrapper_pins_pair_and_manifest_hash():
    script = Path("phase3_run_loop_readonly_identity_lane3_representatives.sh").read_text()

    assert 'LOOP_TARGET_SET="${LOOP_TARGET_SET:-lmb_sum_even_index_step2}"' in script
    assert 'LOOP_PAIR_FILTER="${LOOP_PAIR_FILTER:-lmb_sum_even_index_step2:B10_B13}"' in script
    assert ".venv-pyghidra/bin/python" in script
    assert "phase3_readonly_identity_lane3/readonly_identity_lane3_representatives.json" in script
    assert "bca1a298585a58a6b0e27467fc7025387b641cbc639bc9aec859c8269abdf570" in script
    assert 'VALIDATION_RUNNER_DRY_RUN="${VALIDATION_RUNNER_DRY_RUN:-0}"' in script
    assert "Phase 3 lane 3 dry run finished before post-fix gate." in script
    assert 'PHASE3_REQUIRE_READY="${PHASE3_REQUIRE_READY:-1}"' in script
    assert 'BASELINE_LOOP_LOG_ROOT="${BASELINE_LOOP_LOG_ROOT:-$BASELINE_RAW_DIR/logs/loop}"' in script
    assert '--baseline-log-root "loop=$BASELINE_LOOP_LOG_ROOT"' in script
    assert "--phase3-manifest-sha256" in script
    assert "--gate-stage post-fix" in script
    assert "PHASE3_GATE_ARGS+=(--require-ready)" in script


def test_phase3_lane5_sat_unsafety_representative_wrapper_pins_pair_and_manifest_hash():
    script = Path("phase3_run_function_call_sat_unsafety_lane5_representatives.sh").read_text()

    assert 'FUNCTION_CALL_TARGET_SET="${FUNCTION_CALL_TARGET_SET:-fc_is_even}"' in script
    assert 'FUNCTION_CALL_PAIR_FILTER="${FUNCTION_CALL_PAIR_FILTER:-fc_is_even:B9_B10}"' in script
    assert ".venv-pyghidra/bin/python" in script
    assert "phase3_sat_unsafety_lane5/sat_unsafety_lane5_representatives.json" in script
    assert "a04bd74b9e1f2ca78f983644199314bab318fbb9a6491e5cad23f0dc7670167a" in script
    assert 'VALIDATION_RUNNER_DRY_RUN="${VALIDATION_RUNNER_DRY_RUN:-0}"' in script
    assert "Phase 3 lane 5 dry run finished before post-fix gate." in script
    assert 'PHASE3_REQUIRE_READY="${PHASE3_REQUIRE_READY:-1}"' in script
    assert 'BASELINE_FUNCTION_CALL_LOG_ROOT="${BASELINE_FUNCTION_CALL_LOG_ROOT:-$BASELINE_RAW_DIR/logs/function_call}"' in script
    assert '--baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT"' in script
    assert "--phase3-manifest-sha256" in script
    assert "--gate-stage post-fix" in script
    assert "PHASE3_GATE_ARGS+=(--require-ready)" in script


def test_phase3_lane7_solver_rewrite_representative_wrapper_pins_pair_and_manifest_hash():
    script = Path("phase3_run_loop_solver_rewrite_lane7_representatives.sh").read_text()

    assert 'LOOP_TARGET_SET="${LOOP_TARGET_SET:-lmb_sum_prefix_loop}"' in script
    assert 'LOOP_PAIR_FILTER="${LOOP_PAIR_FILTER:-lmb_sum_prefix_loop:B12_B16}"' in script
    assert ".venv-pyghidra/bin/python" in script
    assert "phase3_solver_rewrite_lane7/solver_rewrite_lane7_representatives.json" in script
    assert "ca0c925863e6d80d5c455deb4b13bd42eddb5bd81afd7e1d1f14d56633cbe488" in script
    assert 'VALIDATION_RUNNER_DRY_RUN="${VALIDATION_RUNNER_DRY_RUN:-0}"' in script
    assert "Phase 3 lane 7 dry run finished before post-fix gate." in script
    assert 'PHASE3_REQUIRE_READY="${PHASE3_REQUIRE_READY:-1}"' in script
    assert 'BASELINE_LOOP_LOG_ROOT="${BASELINE_LOOP_LOG_ROOT:-$BASELINE_RAW_DIR/logs/loop}"' in script
    assert '--baseline-log-root "loop=$BASELINE_LOOP_LOG_ROOT"' in script
    assert "--phase3-manifest-sha256" in script
    assert "--gate-stage post-fix" in script
    assert "PHASE3_GATE_ARGS+=(--require-ready)" in script
