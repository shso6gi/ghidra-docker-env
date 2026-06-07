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
from scripts.function_tracer_pcode.validation.phase2_return_coverage_risk_preflight import (
    main as risk_preflight_main,
    select_risk_pair_infos,
    select_risk_pairs,
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
    assert "Final result movements by function:" in text
    assert "TIMEOUT->UNKNOWN | fc_apply_indirect: 1" in text
    assert "solver_timeout: -1" in text


def test_canonical_baseline_comparison_summarizes_eq_to_unknown_by_function(tmp_path):
    before_dir = tmp_path / "before"
    after_dir = tmp_path / "after"
    before_logs = [
        _write_log(
            before_dir,
            f"fc_dispatch_indirect_B{index}_B{index + 1}.log",
            "Result: EQUIVALENT",
            _payload(
                "fc_dispatch_indirect",
                True,
                binary1_name=f"left-{index}",
                binary2_name=f"right-{index}",
            ),
        )
        for index in (1, 2)
    ]
    after_logs = [
        _write_log(
            after_dir,
            f"fc_dispatch_indirect_B{index}_B{index + 1}.log",
            "Result: UNKNOWN",
            _payload(
                "fc_dispatch_indirect",
                None,
                binary1_name=f"left-{index}",
                binary2_name=f"right-{index}",
                unknown_reasons=[
                    make_unknown_reason(UnknownReasonId.RETURN_COVERAGE_GAP).to_dict()
                ],
            ),
        )
        for index in (1, 2)
    ]

    comparison = compare_validation_baseline_records(
        aggregate_validation_logs(before_logs).records,
        aggregate_validation_logs(after_logs).records,
    )
    text = format_validation_baseline_comparison(comparison)

    assert comparison.has_final_result_differences()
    assert "EQ->UNKNOWN | fc_dispatch_indirect: 2" in text


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
    assert "UNKNOWN->EQ | fc_apply_indirect: 1" in result.stderr
    assert before_log.is_file()


def test_result_summary_baseline_match_after_pairs_scope_ignores_unrun_pairs(tmp_path):
    before_dir = tmp_path / "before"
    after_dir = tmp_path / "after"
    before_dir.mkdir()
    after_dir.mkdir()
    _write_log(
        before_dir,
        "fc_apply_indirect_B1_B2.log",
        "Result: EQUIVALENT",
        _payload(
            "fc_apply_indirect",
            True,
            binary1_name="function_call_test-arm64-clang-O0",
            binary2_name="function_call_test-arm64-clang-O1",
        ),
    )
    _write_log(
        before_dir,
        "fc_apply_indirect_B1_B3.log",
        "Result: UNKNOWN",
        _payload(
            "fc_apply_indirect",
            None,
            binary1_name="function_call_test-arm64-clang-O0",
            binary2_name="function_call_test-arm64-clang-O2",
        ),
    )
    after_log = _write_log(
        after_dir,
        "fc_apply_indirect_B1_B2.log",
        "Result: EQUIVALENT",
        _payload(
            "fc_apply_indirect",
            True,
            binary1_name="function_call_test-arm64-clang-O0",
            binary2_name="function_call_test-arm64-clang-O1",
        ),
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
            "--baseline-match-scope",
            "after-pairs",
            str(after_log),
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0
    assert "Total results delta      : 0" in result.stdout
    assert "Missing pair identities:" in result.stdout
    assert "ok" in result.stdout


def test_result_summary_after_pairs_scope_still_rejects_empty_after_set(tmp_path):
    before_dir = tmp_path / "before"
    before_dir.mkdir()
    _write_log(
        before_dir,
        "fc_apply_indirect_B1_B2.log",
        "Result: EQUIVALENT",
        _payload(
            "fc_apply_indirect",
            True,
            binary1_name="B1",
            binary2_name="B2",
        ),
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
            "--baseline-match-scope",
            "after-pairs",
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode != 0
    assert "baseline comparison mismatch" in result.stderr


def test_result_summary_final_result_match_level_allows_reason_only_movement(tmp_path):
    before_dir = tmp_path / "before"
    before_dir.mkdir()
    after_dir = tmp_path / "after"
    after_dir.mkdir()
    before_reason = make_unknown_reason(
        reason_id=UnknownReasonId.RETURN_COVERAGE_GAP,
        decision_effect="blocks_equivalence",
        reason_scope="function",
        recovery_proof_kind=UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION,
        action_status=UnknownRecoveryActionStatus.PLANNED,
    )
    after_reason = make_unknown_reason(
        reason_id=UnknownReasonId.RETURN_COVERAGE_GAP,
        decision_effect="blocks_equivalence",
        reason_scope="function",
        recovery_proof_kind=UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION,
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
    )
    _write_log(
        before_dir,
        "fc_recursive_sum_B3_B7.log",
        "Result: UNKNOWN",
        _payload(
            "fc_recursive_sum",
            None,
            binary1_name="B3",
            binary2_name="B7",
            unknown_reasons=[before_reason.to_dict()],
        ),
    )
    after_log = _write_log(
        after_dir,
        "fc_recursive_sum_B3_B7.log",
        "Result: UNKNOWN",
        _payload(
            "fc_recursive_sum",
            None,
            binary1_name="B3",
            binary2_name="B7",
            unknown_reasons=[after_reason.to_dict()],
        ),
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "scripts.function_tracer_pcode.validation.result_summary",
            "--function-summary",
            "--function-name",
            "fc_recursive_sum",
            "--before-dir",
            str(before_dir),
            "--require-before-dir",
            "--require-baseline-match",
            "--baseline-match-scope",
            "after-pairs",
            "--baseline-match-level",
            "final-results",
            str(after_log),
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0
    assert "Final result count delta:" in result.stdout
    assert "Pair final result tuple delta:" in result.stdout
    assert "Pair result tuple delta:" in result.stdout


def test_result_summary_final_result_match_level_rejects_unknown_to_eq(tmp_path):
    before_dir = tmp_path / "before"
    before_dir.mkdir()
    after_dir = tmp_path / "after"
    after_dir.mkdir()
    _write_log(
        before_dir,
        "fc_recursive_sum_B3_B7.log",
        "Result: UNKNOWN",
        _payload("fc_recursive_sum", None, binary1_name="B3", binary2_name="B7"),
    )
    after_log = _write_log(
        after_dir,
        "fc_recursive_sum_B3_B7.log",
        "Result: EQUIVALENT",
        _payload("fc_recursive_sum", True, binary1_name="B3", binary2_name="B7"),
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "scripts.function_tracer_pcode.validation.result_summary",
            "--function-summary",
            "--function-name",
            "fc_recursive_sum",
            "--before-dir",
            str(before_dir),
            "--require-before-dir",
            "--require-baseline-match",
            "--baseline-match-scope",
            "after-pairs",
            "--baseline-match-level",
            "final-results",
            str(after_log),
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode != 0
    assert "baseline comparison mismatch" in result.stderr


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

    function_call_script = Path("func_call_run_matrix_all_parallel_multifunc.sh").read_text()
    assert "VALIDATION_BASELINE_MATCH_SCOPE=${VALIDATION_BASELINE_MATCH_SCOPE:-all}" in function_call_script
    assert "VALIDATION_BASELINE_MATCH_LEVEL=${VALIDATION_BASELINE_MATCH_LEVEL:-exact}" in function_call_script
    assert 'FUNCTION_SUMMARY_ARGS+=(--baseline-match-scope "$VALIDATION_BASELINE_MATCH_SCOPE")' in function_call_script
    assert 'FUNCTION_SUMMARY_ARGS+=(--baseline-match-level "$VALIDATION_BASELINE_MATCH_LEVEL")' in function_call_script
    assert 'OVERALL_SUMMARY_ARGS+=(--baseline-match-scope "$VALIDATION_BASELINE_MATCH_SCOPE")' in function_call_script
    assert 'OVERALL_SUMMARY_ARGS+=(--baseline-match-level "$VALIDATION_BASELINE_MATCH_LEVEL")' in function_call_script


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
    assert "function_call_test_phase2_full_current" in script
    assert "artifacts/baselines/observed-v0@0a53352/raw/logs/function_call" in script
    assert 'VALIDATION_REQUIRE_BEFORE_DELTA="${VALIDATION_REQUIRE_BEFORE_DELTA:-1}"' in script
    assert 'VALIDATION_REQUIRE_BEFORE_DELTA="${VALIDATION_REQUIRE_BEFORE_DELTA:-0}"' in script
    assert 'VALIDATION_REQUIRE_BASELINE_MATCH="${VALIDATION_REQUIRE_BASELINE_MATCH:-0}"' in script
    assert 'VALIDATION_BASELINE_MATCH_LEVEL="${VALIDATION_BASELINE_MATCH_LEVEL:-exact}"' in script
    assert 'VALIDATION_SKIP_COMPLETED="${VALIDATION_SKIP_COMPLETED:-1}"' in script
    assert 'VALIDATION_AUTO_BEFORE_SNAPSHOT="${VALIDATION_AUTO_BEFORE_SNAPSHOT:-1}"' in script
    assert 'VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS="${VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS:-0}"' in script
    assert 'FUNCTION_CALL_EXTRA_EQUIV_ARGS="${FUNCTION_CALL_EXTRA_EQUIV_ARGS:-}"' in script
    assert 'PHASE2_RUN_EXPECTED_MOVEMENT_GATE="${PHASE2_RUN_EXPECTED_MOVEMENT_GATE:-0}"' in script
    assert "--no-completed-recovery-proofs" not in script
    assert "Phase 2 full matrix dry run finished before expected-movement gate." in script
    assert "PHASE2_GATE_BASELINE_DIR=" in script
    assert "validation_before_dir=${VALIDATION_BEFORE_DIR:-}" in script
    assert "validation_moved_output_dir=${VALIDATION_MOVED_OUTPUT_DIR:-}" in script
    assert "baseline_note=$BASELINE_NOTE" in script
    assert "Skipping Phase 2 gate:" in script
    assert "phase2_equivalence_blocking_unsafety" in script
    assert "--baseline-log-root" in script
    assert '--baseline-match-scope "${PHASE2_GATE_BASELINE_MATCH_SCOPE:-all}"' in script
    assert "files_to_copy_for_codex.txt" in script


def test_phase2_pre_producer_wrapper_pins_producer_only_flags():
    script = Path("phase2_run_function_call_full_matrix_pre_producer_32jobs.sh").read_text()

    assert "function_call_test_phase2_full_pre_producer" in script
    assert 'VALIDATION_SKIP_COMPLETED="${VALIDATION_SKIP_COMPLETED:-0}"' in script
    assert 'VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS="${VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS:-1}"' in script
    assert (
        'FUNCTION_CALL_EXTRA_EQUIV_ARGS="${FUNCTION_CALL_EXTRA_EQUIV_ARGS:---no-completed-recovery-proofs}"'
    ) in script
    default_line = next(
        line for line in script.splitlines() if line.startswith("export FUNCTION_CALL_EXTRA_EQUIV_ARGS=")
    )
    assert "--no-retry-phases" not in default_line
    assert 'PHASE2_RUN_EXPECTED_MOVEMENT_GATE="${PHASE2_RUN_EXPECTED_MOVEMENT_GATE:-0}"' in script
    assert "phase2_run_function_call_pre_producer_gate_reduced_matrix.sh" in script
    assert "phase2_function_call_full_matrix_pre_producer" in script
    assert 'exec "$SCRIPT_DIR/phase2_run_function_call_full_matrix_32jobs.sh"' in script


def test_phase2_pre_producer_preflight_pins_target_pairs_and_filtered_baseline_scope():
    script = Path("phase2_run_function_call_pre_producer_preflight.sh").read_text()

    assert "function_call_test_phase2_pre_producer_preflight" in script
    assert "fc_select_simple:B1_B10" in script
    assert "fc_widen_then_bias:B1_B14" in script
    assert "fc_long_branch_dispatch:B1_B10" in script
    assert "fc_guarded_call:B5_B13" in script
    assert "fc_recursive_sum:B3_B7" not in script
    assert 'VALIDATION_REQUIRE_BASELINE_MATCH="${VALIDATION_REQUIRE_BASELINE_MATCH:-1}"' in script
    assert 'VALIDATION_BASELINE_MATCH_SCOPE="${VALIDATION_BASELINE_MATCH_SCOPE:-after-pairs}"' in script
    assert 'PHASE2_RUN_EXPECTED_MOVEMENT_GATE="${PHASE2_RUN_EXPECTED_MOVEMENT_GATE:-0}"' in script
    assert 'exec "$SCRIPT_DIR/phase2_run_function_call_full_matrix_pre_producer_32jobs.sh"' in script


def test_phase2_pre_producer_final_result_preflight_pins_recursive_sum_pair():
    script = Path("phase2_run_function_call_pre_producer_final_result_preflight.sh").read_text()

    assert "function_call_test_phase2_pre_producer_final_result_preflight" in script
    assert "phase2_return_coverage_risk_preflight" in script
    assert 'RISK_CURRENT_LOG_ROOT="${RISK_CURRENT_LOG_ROOT:-$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase2_full_current}"' in script
    assert 'RISK_BASELINE_LOG_ROOT="${RISK_BASELINE_LOG_ROOT:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/raw/logs/function_call}"' in script
    assert "--max-evidence-only-per-stratum" in script
    assert "RISK_PREFLIGHT_MAX_EVIDENCE_ONLY_PER_STRATUM" in script
    assert "--max-pairs" in script
    assert "RISK_PREFLIGHT_MAX_PAIRS" in script
    assert "--sample-seed" in script
    assert "RISK_PREFLIGHT_SAMPLE_SEED" in script
    assert "--manifest-path" in script
    assert "RISK_PREFLIGHT_MANIFEST" in script
    assert 'fc_recursive_sum:B1_B7' in script or 'fc_recursive_sum:B1_B7' in Path(
        "scripts/function_tracer_pcode/validation/phase2_return_coverage_risk_preflight.py"
    ).read_text()
    assert 'FUNCTION_CALL_TARGET_SET="${FUNCTION_CALL_TARGET_SET:-fc_recursive_sum,fc_is_odd,fc_dispatch_indirect}"' in script
    assert (
        'fc_recursive_sum:B1_B7,fc_recursive_sum:B3_B7,'
        'fc_is_odd:B1_B7,fc_dispatch_indirect:B1_B2,fc_dispatch_indirect:B3_B4'
    ) in script
    assert 'VALIDATION_REQUIRE_BASELINE_MATCH="${VALIDATION_REQUIRE_BASELINE_MATCH:-1}"' in script
    assert 'VALIDATION_BASELINE_MATCH_SCOPE="${VALIDATION_BASELINE_MATCH_SCOPE:-after-pairs}"' in script
    assert 'VALIDATION_BASELINE_MATCH_LEVEL="${VALIDATION_BASELINE_MATCH_LEVEL:-exact}"' in script
    assert 'PHASE2_RUN_EXPECTED_MOVEMENT_GATE="${PHASE2_RUN_EXPECTED_MOVEMENT_GATE:-0}"' in script
    assert "phase2_function_call_pre_producer_final_result_preflight" in script
    assert 'exec "$SCRIPT_DIR/phase2_run_function_call_full_matrix_pre_producer_32jobs.sh"' in script


def test_phase2_reduced_pre_producer_matrix_pins_failure_contributor_functions():
    script = Path("phase2_run_function_call_pre_producer_reduced_matrix.sh").read_text()

    assert "function_call_test_phase2_reduced_pre_producer" in script
    assert (
        'FUNCTION_CALL_TARGET_SET="${FUNCTION_CALL_TARGET_SET:-'
        'fc_recursive_sum,fc_is_even,fc_is_odd,fc_read_after_void}"'
    ) in script
    assert 'VALIDATION_REQUIRE_BASELINE_MATCH="${VALIDATION_REQUIRE_BASELINE_MATCH:-1}"' in script
    assert 'VALIDATION_BASELINE_MATCH_SCOPE="${VALIDATION_BASELINE_MATCH_SCOPE:-after-pairs}"' in script
    assert 'VALIDATION_BASELINE_MATCH_LEVEL="${VALIDATION_BASELINE_MATCH_LEVEL:-final-results}"' in script
    assert 'PHASE2_RUN_EXPECTED_MOVEMENT_GATE="${PHASE2_RUN_EXPECTED_MOVEMENT_GATE:-0}"' in script
    assert "phase2_function_call_reduced_matrix_pre_producer" in script
    assert 'exec "$SCRIPT_DIR/phase2_run_function_call_full_matrix_pre_producer_32jobs.sh"' in script


def test_phase2_gate_reduced_pre_producer_matrix_pins_gate_contributor_pairs():
    script = Path("phase2_run_function_call_pre_producer_gate_reduced_matrix.sh").read_text()

    assert "function_call_test_phase2_gate_reduced_pre_producer" in script
    assert (
        'FUNCTION_CALL_TARGET_SET="${FUNCTION_CALL_TARGET_SET:-'
        'fc_apply_indirect,fc_dispatch_indirect,fc_recursive_sum,fc_is_even,fc_is_odd}"'
    ) in script
    assert (
        'fc_apply_indirect:B10_B11,fc_dispatch_indirect:B10_B11,'
        'fc_recursive_sum:B10_B14,fc_apply_indirect:B1_B2,'
        'fc_apply_indirect:B1_B14,fc_is_even:B1_B10,fc_is_odd:B1_B10'
    ) in script
    assert 'VALIDATION_BASELINE_MATCH_SCOPE="${VALIDATION_BASELINE_MATCH_SCOPE:-after-pairs}"' in script
    assert 'VALIDATION_BASELINE_MATCH_LEVEL="${VALIDATION_BASELINE_MATCH_LEVEL:-final-results}"' in script
    assert 'PHASE2_RUN_EXPECTED_MOVEMENT_GATE="${PHASE2_RUN_EXPECTED_MOVEMENT_GATE:-1}"' in script
    assert 'PHASE2_GATE_BASELINE_MATCH_SCOPE="${PHASE2_GATE_BASELINE_MATCH_SCOPE:-after-pairs}"' in script
    assert "phase2_function_call_full_matrix_pre_producer" in script
    assert 'exec "$SCRIPT_DIR/phase2_run_function_call_full_matrix_pre_producer_32jobs.sh"' in script


def test_rerun_full_analysis_runs_full_matrix_without_phase2_preflight():
    script = Path("rerun_full_analysis.sh").read_text()

    phase0a_gate = script.index("./phase0a_validate_observed_baseline_integrity_gate.sh")
    phase0c_gate = script.index("./phase0c_validate_observed_baseline_census_gate.sh")
    phase0c_reproduction_gate = script.index("./phase0c_validate_canonical_reproduction_gate.sh")
    phase0d_gate = script.index("./phase0d_validate_not_eq_audit_gate.sh")
    phase1_gate = script.index("./phase1_validate_concrete_manifest_gate.sh")
    phase15_gate = script.index("./phase15_validate_regression_gates.sh")
    normal_full_matrix = script.index("./phase2_run_function_call_full_matrix_32jobs.sh")
    producer_full_matrix = script.index(
        "./phase2_run_function_call_full_matrix_pre_producer_32jobs.sh"
    )

    assert phase0a_gate < phase0c_gate
    assert phase0c_gate < phase0c_reproduction_gate
    assert phase0c_reproduction_gate < phase0d_gate
    assert phase0d_gate < phase1_gate
    assert phase1_gate < phase15_gate
    assert phase15_gate < normal_full_matrix
    assert "phase0a_observed_baseline_integrity_gate_stdout.log" in script
    assert "phase0c_observed_baseline_census_gate_stdout.log" in script
    assert "phase0c_canonical_reproduction_gate_stdout.log" in script
    assert "phase0d_not_eq_audit_gate_stdout.log" in script
    assert "phase1_concrete_manifest_gate_stdout.log" in script
    assert "phase1_5_regression_gates_stdout.log" in script
    assert normal_full_matrix < producer_full_matrix
    assert "./phase2_run_function_call_pre_producer_final_result_preflight.sh" not in script
    assert "./phase2_run_function_call_pre_producer_preflight.sh" not in script
    assert "RERUN_FULL_ANALYSIS_SKIP_NORMAL_FULL" in script


def test_phase0d_not_eq_audit_gate_wrapper_validates_frozen_audit():
    script_path = Path("phase0d_validate_not_eq_audit_gate.sh")
    script = script_path.read_text()

    assert os.access(script_path, os.X_OK)
    assert "set -euo pipefail" in script
    assert 'cd "$SCRIPT_DIR"' in script
    assert 'PYTHON_BIN="${PYTHON_BIN:-$DEFAULT_PYTHON_BIN}"' in script
    assert 'BASELINE_ROOT="${BASELINE_ROOT:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352}"' in script
    assert (
        'OUTPUT_DIR="${OUTPUT_DIR:-$SCRIPT_DIR/logs/equivalence_all/'
        'phase0d_not_eq_audit_gate}"'
    ) in script
    assert (
        '"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.'
        'phase0d_not_eq_audit_gate'
    ) in script
    assert '--baseline-raw-dir "$BASELINE_ROOT/raw"' in script
    assert '--audit-manifest "$BASELINE_ROOT/audit/not_eq_audit_manifest.json"' in script
    assert '--oracle-manifest "$BASELINE_ROOT/derived_oracle/oracle_manifest_draft.json"' in script
    assert "--require-ready" in script


def test_phase0c_observed_baseline_census_gate_wrapper_validates_frozen_raw_logs():
    script_path = Path("phase0c_validate_observed_baseline_census_gate.sh")
    script = script_path.read_text()

    assert os.access(script_path, os.X_OK)
    assert "set -euo pipefail" in script
    assert 'cd "$SCRIPT_DIR"' in script
    assert 'PYTHON_BIN="${PYTHON_BIN:-$DEFAULT_PYTHON_BIN}"' in script
    assert 'BASELINE_ROOT="${BASELINE_ROOT:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352}"' in script
    assert (
        'OUTPUT_DIR="${OUTPUT_DIR:-$SCRIPT_DIR/logs/equivalence_all/'
        'phase0c_observed_baseline_census_gate}"'
    ) in script
    assert (
        '"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.'
        'phase0c_observed_baseline_census_gate'
    ) in script
    assert '--baseline-raw-dir "$BASELINE_ROOT/raw"' in script
    assert "--require-ready" in script


def test_phase0c_canonical_reproduction_gate_wrapper_validates_exact_match():
    script_path = Path("phase0c_validate_canonical_reproduction_gate.sh")
    script = script_path.read_text()

    assert os.access(script_path, os.X_OK)
    assert "set -euo pipefail" in script
    assert 'cd "$SCRIPT_DIR"' in script
    assert 'PYTHON_BIN="${PYTHON_BIN:-$DEFAULT_PYTHON_BIN}"' in script
    assert 'BASELINE_ROOT="${BASELINE_ROOT:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352}"' in script
    assert 'FUNCTION_CALL_CURRENT_LOG_ROOT="${FUNCTION_CALL_CURRENT_LOG_ROOT:-$BASELINE_ROOT/raw/logs/function_call}"' in script
    assert 'LOOP_CURRENT_LOG_ROOT="${LOOP_CURRENT_LOG_ROOT:-$BASELINE_ROOT/raw/logs/loop}"' in script
    assert (
        'OUTPUT_DIR="${OUTPUT_DIR:-$SCRIPT_DIR/logs/equivalence_all/'
        'phase0c_canonical_reproduction_gate}"'
    ) in script
    assert (
        '"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.'
        'phase0c_canonical_reproduction_gate'
    ) in script
    assert '--current-log-root "function_call=$FUNCTION_CALL_CURRENT_LOG_ROOT"' in script
    assert '--current-log-root "loop=$LOOP_CURRENT_LOG_ROOT"' in script
    assert "--require-ready" in script


def test_phase0a_observed_baseline_integrity_gate_wrapper_validates_frozen_raw_hashes():
    script_path = Path("phase0a_validate_observed_baseline_integrity_gate.sh")
    script = script_path.read_text()

    assert os.access(script_path, os.X_OK)
    assert "set -euo pipefail" in script
    assert 'cd "$SCRIPT_DIR"' in script
    assert 'PYTHON_BIN="${PYTHON_BIN:-$DEFAULT_PYTHON_BIN}"' in script
    assert 'BASELINE_ROOT="${BASELINE_ROOT:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352}"' in script
    assert (
        'OUTPUT_DIR="${OUTPUT_DIR:-$SCRIPT_DIR/logs/equivalence_all/'
        'phase0a_observed_baseline_integrity_gate}"'
    ) in script
    assert 'PHASE0A_VALIDATE_FILE_CONTENT_HASHES="${PHASE0A_VALIDATE_FILE_CONTENT_HASHES:-1}"' in script
    assert (
        '"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.'
        'phase0a_observed_baseline_integrity_gate "${ARGS[@]}"'
    ) in script
    assert '--baseline-raw-dir "$BASELINE_ROOT/raw"' in script
    assert "--require-ready" in script
    assert "ARGS+=(--skip-file-content-hashes)" in script


def test_phase0_observed_baseline_gate_wrapper_runs_all_lightweight_gates():
    script_path = Path("phase0_validate_observed_baseline_gates.sh")
    script = script_path.read_text()

    assert os.access(script_path, os.X_OK)
    assert "set -euo pipefail" in script
    assert 'cd "$SCRIPT_DIR"' in script
    assert "./phase0a_validate_observed_baseline_integrity_gate.sh" in script
    assert "./phase0c_validate_observed_baseline_census_gate.sh" in script
    assert "./phase0c_validate_canonical_reproduction_gate.sh" in script
    assert "./phase0d_validate_not_eq_audit_gate.sh" in script
    assert script.index("./phase0a_validate_observed_baseline_integrity_gate.sh") < script.index(
        "./phase0c_validate_observed_baseline_census_gate.sh"
    )
    assert script.index("./phase0c_validate_observed_baseline_census_gate.sh") < script.index(
        "./phase0c_validate_canonical_reproduction_gate.sh"
    )
    assert script.index("./phase0c_validate_canonical_reproduction_gate.sh") < script.index(
        "./phase0d_validate_not_eq_audit_gate.sh"
    )


def test_phase1_concrete_manifest_gate_wrapper_validates_frozen_manifests():
    script_path = Path("phase1_validate_concrete_manifest_gate.sh")
    script = script_path.read_text()

    assert os.access(script_path, os.X_OK)
    assert "set -euo pipefail" in script
    assert 'cd "$SCRIPT_DIR"' in script
    assert 'BASELINE_ROOT="${BASELINE_ROOT:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352}"' in script
    assert 'PHASE1_DIR="${PHASE1_DIR:-$BASELINE_ROOT/phase1}"' in script
    assert 'BASELINE_RAW_DIR="${BASELINE_RAW_DIR:-$BASELINE_ROOT/raw}"' in script
    assert (
        'OUTPUT_DIR="${OUTPUT_DIR:-$SCRIPT_DIR/logs/equivalence_all/'
        'phase1_concrete_manifest_gate}"'
    ) in script
    assert (
        '"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.'
        'phase1_concrete_manifest_gate'
    ) in script
    assert '--phase1-dir "$PHASE1_DIR"' in script
    assert '--baseline-raw-dir "$BASELINE_RAW_DIR"' in script
    assert "--require-ready" in script


def test_phase15_regression_gate_wrapper_validates_exact_pre_semantic_fix_match():
    script_path = Path("phase15_validate_regression_gates.sh")
    script = script_path.read_text()

    assert os.access(script_path, os.X_OK)
    assert "set -euo pipefail" in script
    assert 'cd "$SCRIPT_DIR"' in script
    assert 'BASELINE_ROOT="${BASELINE_ROOT:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352}"' in script
    assert 'BASELINE_RAW_DIR="${BASELINE_RAW_DIR:-$BASELINE_ROOT/raw}"' in script
    assert 'PHASE1_DIR="${PHASE1_DIR:-$BASELINE_ROOT/phase1}"' in script
    assert 'FUNCTION_CALL_CURRENT_LOG_ROOT="${FUNCTION_CALL_CURRENT_LOG_ROOT:-$BASELINE_RAW_DIR/logs/function_call}"' in script
    assert 'LOOP_CURRENT_LOG_ROOT="${LOOP_CURRENT_LOG_ROOT:-$BASELINE_RAW_DIR/logs/loop}"' in script
    assert (
        'OUTPUT_DIR="${OUTPUT_DIR:-$SCRIPT_DIR/logs/equivalence_all/'
        'phase1_5_regression_gates}"'
    ) in script
    assert (
        '"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.'
        'phase15_regression_gates'
    ) in script
    assert '--baseline-raw-dir "$BASELINE_RAW_DIR"' in script
    assert '--phase1-dir "$PHASE1_DIR"' in script
    assert '--current-log-root "function_call=$FUNCTION_CALL_CURRENT_LOG_ROOT"' in script
    assert '--current-log-root "loop=$LOOP_CURRENT_LOG_ROOT"' in script
    assert "--require-ready" in script


def test_phase2_equivalence_blocking_unsafety_reduced_log_gate_wrapper_validates_existing_logs():
    script_path = Path("phase2_validate_equivalence_blocking_unsafety_reduced_log_gate.sh")
    script = script_path.read_text()

    assert os.access(script_path, os.X_OK)
    assert "set -euo pipefail" in script
    assert 'cd "$SCRIPT_DIR"' in script
    assert 'BASELINE_ROOT="${BASELINE_ROOT:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352}"' in script
    assert 'PHASE1_DIR="${PHASE1_DIR:-$BASELINE_ROOT/phase1}"' in script
    assert (
        'BASELINE_FUNCTION_CALL_LOG_ROOT="${BASELINE_FUNCTION_CALL_LOG_ROOT:-'
        '$BASELINE_ROOT/raw/logs/function_call}"'
    ) in script
    assert (
        'PHASE2_FUNCTION_CALL_LOG_ROOT="${PHASE2_FUNCTION_CALL_LOG_ROOT:-'
        '$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase2_gate_reduced_pre_producer}"'
    ) in script
    assert (
        'OUTPUT_DIR="${OUTPUT_DIR:-$SCRIPT_DIR/logs/equivalence_all/'
        'phase2_equivalence_blocking_unsafety_reduced_log_gate}"'
    ) in script
    assert (
        '"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.'
        'phase2_equivalence_blocking_unsafety'
    ) in script
    assert '--current-log-root "function_call=$PHASE2_FUNCTION_CALL_LOG_ROOT"' in script
    assert '--baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT"' in script
    assert "--baseline-match-scope after-pairs" in script
    assert "--require-ready" in script


def test_log_only_pre_full_gate_wrapper_runs_phase0_phase1_phase15_phase2_then_phase3_log_only_gates():
    script_path = Path("validate_log_only_pre_full_gates.sh")
    script = script_path.read_text()

    assert os.access(script_path, os.X_OK)
    assert "set -euo pipefail" in script
    assert 'cd "$SCRIPT_DIR"' in script
    assert "./phase0_validate_observed_baseline_gates.sh" in script
    assert "./phase1_validate_concrete_manifest_gate.sh" in script
    assert "./phase15_validate_regression_gates.sh" in script
    assert "./phase2_validate_equivalence_blocking_unsafety_reduced_log_gate.sh" in script
    assert "./phase3_rebuild_all_post_fix_gates_from_logs.sh" in script
    assert script.index("./phase0_validate_observed_baseline_gates.sh") < script.index(
        "./phase1_validate_concrete_manifest_gate.sh"
    )
    assert script.index("./phase1_validate_concrete_manifest_gate.sh") < script.index(
        "./phase15_validate_regression_gates.sh"
    )
    assert script.index("./phase15_validate_regression_gates.sh") < script.index(
        "./phase2_validate_equivalence_blocking_unsafety_reduced_log_gate.sh"
    )
    assert script.index("./phase2_validate_equivalence_blocking_unsafety_reduced_log_gate.sh") < script.index(
        "./phase3_rebuild_all_post_fix_gates_from_logs.sh"
    )


def test_phase2_return_coverage_risk_preflight_selects_eq_pairs_by_note_strata(tmp_path):
    current = tmp_path / "current"
    baseline = tmp_path / "baseline"
    payload = _payload(
        "fc_dispatch_indirect",
        True,
        binary1_name="function_call_test-arm64-clang-O0",
        binary2_name="function_call_test-arm64-clang-O1",
    )
    _write_log(
        baseline / "fc_dispatch_indirect",
        "fc_dispatch_indirect_B1_B2.log",
        "Result: EQUIVALENT",
        payload,
    )
    risky_current = _write_log(
        current / "fc_dispatch_indirect",
        "fc_dispatch_indirect_B1_B2.log",
        "Result: EQUIVALENT",
        payload,
    )
    risky_current.write_text(
        risky_current.read_text()
        + "\n[ReturnAnalyzer] Analysis notes: ['switch_return_recovery', 'control_region_return_recovery']"
    )
    plain_current = _write_log(
        current / "fc_plain",
        "fc_plain_B1_B2.log",
        "Result: EQUIVALENT",
        _payload("fc_plain", True),
    )
    plain_current.write_text(
        plain_current.read_text()
        + "\n[ReturnAnalyzer] Analysis notes: ['ordinary_note']"
    )

    selected = select_risk_pairs(
        current,
        baseline_log_root=baseline,
        fallback_pairs=("fc_recursive_sum:B3_B7",),
    )

    assert selected == ("fc_dispatch_indirect:B1_B2", "fc_recursive_sum:B3_B7")


def test_phase2_return_coverage_risk_preflight_reads_gitignored_logs(tmp_path):
    (tmp_path / ".gitignore").write_text("logs/\n")
    current = tmp_path / "logs" / "current"
    risky_current = _write_log(
        current / "fc_dispatch_indirect",
        "fc_dispatch_indirect_B1_B2.log",
        "Result: EQUIVALENT",
        _payload("fc_dispatch_indirect", True),
    )
    risky_current.write_text(
        risky_current.read_text()
        + "\n[ReturnAnalyzer] Analysis notes: ['switch_return_recovery']"
    )

    selected = select_risk_pairs(tmp_path, fallback_pairs=())

    assert selected == ("fc_dispatch_indirect:B1_B2",)


def test_phase2_return_coverage_risk_preflight_caps_evidence_only_strata(tmp_path):
    current = tmp_path / "current"
    for pair in ("B1_B2", "B1_B3"):
        note_log = _write_log(
            current / "fc_note_risk",
            f"fc_note_risk_{pair}.log",
            "Result: EQUIVALENT",
            _payload("fc_note_risk", True),
        )
        note_log.write_text(
            note_log.read_text()
            + "\n[ReturnAnalyzer] Analysis notes: ['state_transition_loop_summary']"
        )
    for pair in ("B1_B2", "B1_B3"):
        evidence_log = _write_log(
            current / "fc_evidence_only",
            f"fc_evidence_only_{pair}.log",
            "Result: EQUIVALENT",
            _payload("fc_evidence_only", True),
        )
        evidence_log.write_text(
            evidence_log.read_text()
            + "\ncompleted_recovery_proof_evidence: [{\"proof_stage\": \"return_guard_coverage\"}]"
        )

    selected = select_risk_pairs(
        current,
        max_per_stratum=2,
        max_evidence_only_per_stratum=1,
        fallback_pairs=(),
    )

    assert sum(entry.startswith("fc_note_risk:") for entry in selected) == 2
    assert sum(entry.startswith("fc_evidence_only:") for entry in selected) == 1


def test_phase2_return_coverage_risk_preflight_extracts_json_payload_shapes(tmp_path):
    current = tmp_path / "current"
    log_path = _write_log(
        current / "fc_evidence_only",
        "fc_evidence_only_B9_B16.log",
        "Result: EQUIVALENT",
        _payload(
            "fc_evidence_only",
            True,
            binary1_name="function_call_test-mips64-clang-O0",
            binary2_name="function_call_test-mips64-gcc-O3",
            completed_recovery_proof_evidence=[
                {
                    "evidence": {
                        "proof_stage": "return_partition_extraction",
                        "object_target_key": [
                            "return_coverage",
                            "function1",
                            ["function_ref", ["function", "B9", 1053512]],
                            "return_coverage_gap",
                            ["return_storage", "return_value", 32, None, "int"],
                        ]
                    },
                },
                {
                    "evidence": {
                        "proof_stage": "return_guard_coverage",
                        "object_target_key": [
                            "return_coverage",
                            "function2",
                            ["function_ref", ["function", "B16", 4831841344]],
                            "return_coverage_gap",
                            ["return_storage", "return_value", 32, None, "int"],
                        ]
                    },
                },
            ],
        ),
    )

    selected_infos = select_risk_pair_infos(
        current,
        max_evidence_only_per_stratum=1,
        fallback_pairs=(),
    )

    assert log_path.exists()
    assert len(selected_infos) == 1
    selected = selected_infos[0]
    assert selected.entry == "fc_evidence_only:B9_B16"
    assert selected.side_shape == "mips64/clang/O0 -> mips64/gcc/O3"
    assert selected.proof_stages == (
        "return_guard_coverage",
        "return_partition_extraction",
    )
    assert selected.object_target_shapes != ("unknown",)
    assert any("function1" in shape for shape in selected.object_target_shapes)
    assert any("function2" in shape for shape in selected.object_target_shapes)


def test_phase2_return_coverage_risk_preflight_reuses_duplicate_fallback_capacity(tmp_path):
    current = tmp_path / "current"
    for function_name in ("fc_a", "fc_b", "fc_c"):
        log_path = _write_log(
            current / function_name,
            f"{function_name}_B1_B2.log",
            "Result: EQUIVALENT",
            _payload(
                function_name,
                True,
                completed_recovery_proof_evidence=[
                    {
                        "proof_stage": "return_guard_coverage",
                        "evidence": {
                            "object_target_key": [
                                "return_coverage",
                                "function1",
                                ["function_ref", ["function", "B1", 1]],
                            ]
                        },
                    }
                ],
            ),
        )
        assert log_path.exists()

    selected = select_risk_pairs(
        current,
        max_pairs=3,
        max_evidence_only_per_stratum=1,
        fallback_pairs=("fc_a:B1_B2", "fc_fallback:B3_B4"),
    )

    assert len(selected) == 3
    assert "fc_a:B1_B2" in selected
    assert "fc_fallback:B3_B4" in selected


def test_phase2_return_coverage_risk_preflight_stratifies_binary_side_shape(tmp_path):
    current = tmp_path / "current"
    for pair, left, right in (
        ("B1_B2", "function_call_test-arm64-clang-O0", "function_call_test-arm64-clang-O1"),
        ("B3_B4", "function_call_test-mips64-gcc-O0", "function_call_test-mips64-gcc-O2"),
    ):
        log_path = _write_log(
            current / "fc_dispatch_indirect",
            f"fc_dispatch_indirect_{pair}.log",
            "Result: EQUIVALENT",
            _payload(
                "fc_dispatch_indirect",
                True,
                binary1_name=left,
                binary2_name=right,
            ),
        )
        log_path.write_text(
            log_path.read_text()
            + "\n[ReturnAnalyzer] Analysis notes: ['switch_return_recovery']"
        )

    selected_infos = select_risk_pair_infos(
        current,
        max_per_stratum=1,
        fallback_pairs=(),
    )

    assert {info.entry for info in selected_infos} == {
        "fc_dispatch_indirect:B1_B2",
        "fc_dispatch_indirect:B3_B4",
    }
    assert {info.side_shape for info in selected_infos} == {
        "arm64/clang/O0 -> arm64/clang/O1",
        "mips64/gcc/O0 -> mips64/gcc/O2",
    }


def test_phase2_return_coverage_risk_preflight_writes_manifest_and_summary(tmp_path, capsys):
    current = tmp_path / "current"
    manifest = tmp_path / "selection.json"
    log_path = _write_log(
        current / "fc_recursive_sum",
        "fc_recursive_sum_B3_B7.log",
        "Result: EQUIVALENT",
        _payload(
            "fc_recursive_sum",
            True,
            binary1_name="function_call_test-arm64-clang-O0",
            binary2_name="function_call_test-arm64-clang-O1",
        ),
    )
    log_path.write_text(
        log_path.read_text()
        + "\n[ReturnAnalyzer] Analysis notes: ['state_transition_loop_summary']"
    )

    exit_code = risk_preflight_main(
        [
            "--current-log-root",
            str(current),
            "--max-pairs",
            "1",
            "--sample-seed",
            "7",
            "--manifest-path",
            str(manifest),
            "--fallback-pair",
            "fc_dispatch_indirect:B1_B2",
        ]
    )

    captured = capsys.readouterr()
    payload = json.loads(manifest.read_text())
    assert exit_code == 0
    assert "export RISK_PREFLIGHT_SELECTED_COUNT=1" in captured.out
    assert "Phase 2 return coverage risk preflight selection:" in captured.err
    assert "fc_recursive_sum:B3_B7 | reason=risk-stratum" in captured.err
    assert payload["selected_count"] == 1
    assert payload["sample_seed"] == 7
    assert payload["selected_pairs"][0]["entry"] == "fc_recursive_sum:B3_B7"
    assert payload["selected_pairs"][0]["selection_reason"] == "risk-stratum"


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
    assert 'PHASE1_FUNCTION_CALL_LOG_ROOT="${PHASE1_FUNCTION_CALL_LOG_ROOT:-$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase2_full_current}"' in script
    assert 'PHASE1_LOOP_LOG_ROOT="${PHASE1_LOOP_LOG_ROOT:-$BASELINE_RAW_DIR/logs/loop}"' in script
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


def test_phase3_lane4_method_b_closure_representative_wrapper_pins_pair_and_manifest_hash():
    script = Path("phase3_run_loop_method_b_closure_lane4_representatives.sh").read_text()

    assert 'LOOP_TARGET_SET="${LOOP_TARGET_SET:-lmb_sum_even_index_step2}"' in script
    assert 'LOOP_PAIR_FILTER="${LOOP_PAIR_FILTER:-lmb_sum_even_index_step2:B10_B13}"' in script
    assert ".venv-pyghidra/bin/python" in script
    assert "phase3_method_b_closure_lane4/method_b_closure_lane4_representatives.json" in script
    assert "925d7614fa46b74c4cf2378182cf701a47fe771fc8a9b445b90509fdb92ae9e1" in script
    assert 'VALIDATION_RUNNER_DRY_RUN="${VALIDATION_RUNNER_DRY_RUN:-0}"' in script
    assert "Phase 3 lane 4 dry run finished before post-fix gate." in script
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


def test_phase3_lane6_unresolved_expression_representative_wrapper_pins_pair_and_manifest_hash():
    script = Path("phase3_run_function_call_unresolved_expression_lane6_representatives.sh").read_text()

    assert 'FUNCTION_CALL_TARGET_SET="${FUNCTION_CALL_TARGET_SET:-fc_is_even}"' in script
    assert 'FUNCTION_CALL_PAIR_FILTER="${FUNCTION_CALL_PAIR_FILTER:-fc_is_even:B11_B12}"' in script
    assert ".venv-pyghidra/bin/python" in script
    assert "phase3_unresolved_expression_lane6/unresolved_expression_lane6_representatives.json" in script
    assert "44e90da602bf10a0f3fa4387f3ef426eab474d181c62ac0a442382a15472c6ea" in script
    assert 'VALIDATION_RUNNER_DRY_RUN="${VALIDATION_RUNNER_DRY_RUN:-0}"' in script
    assert "Phase 3 lane 6 dry run finished before post-fix gate." in script
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


def test_phase3_lane8_solver_rewrite_proof_representative_wrapper_pins_pair_and_manifest_hash():
    script = Path("phase3_run_function_call_solver_rewrite_proof_lane8_representatives.sh").read_text()

    assert 'FUNCTION_CALL_TARGET_SET="${FUNCTION_CALL_TARGET_SET:-fc_recursive_sum}"' in script
    assert 'FUNCTION_CALL_PAIR_FILTER="${FUNCTION_CALL_PAIR_FILTER:-fc_recursive_sum:B8_B10}"' in script
    assert ".venv-pyghidra/bin/python" in script
    assert "phase3_solver_rewrite_proof_lane8/solver_rewrite_proof_lane8_representatives.json" in script
    assert "36af8ab79a23375db0a2bad49679b90e035a2fb7d99a994f0396eaaeb4742c43" in script
    assert 'VALIDATION_RUNNER_DRY_RUN="${VALIDATION_RUNNER_DRY_RUN:-0}"' in script
    assert "Phase 3 lane 8 dry run finished before post-fix gate." in script
    assert 'PHASE3_REQUIRE_READY="${PHASE3_REQUIRE_READY:-1}"' in script
    assert 'BASELINE_FUNCTION_CALL_LOG_ROOT="${BASELINE_FUNCTION_CALL_LOG_ROOT:-$BASELINE_RAW_DIR/logs/function_call}"' in script
    assert '--baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT"' in script
    assert "--phase3-manifest-sha256" in script
    assert "--gate-stage post-fix" in script
    assert "PHASE3_GATE_ARGS+=(--require-ready)" in script


def test_phase3_lane9_solver_timeout_representative_wrapper_pins_pair_and_manifest_hash():
    script = Path("phase3_run_function_call_solver_timeout_lane9_representatives.sh").read_text()

    assert 'FUNCTION_CALL_TARGET_SET="${FUNCTION_CALL_TARGET_SET:-fc_long_branch_dispatch}"' in script
    assert 'FUNCTION_CALL_PAIR_FILTER="${FUNCTION_CALL_PAIR_FILTER:-fc_long_branch_dispatch:B8_B9}"' in script
    assert ".venv-pyghidra/bin/python" in script
    assert "phase3_solver_timeout_lane9/solver_timeout_lane9_representatives.json" in script
    assert "ceb30318fa56f5255d115f0ac53320ad349b7133c69dc2e1c05ee8c1afdb3f06" in script
    assert 'VALIDATION_RUNNER_DRY_RUN="${VALIDATION_RUNNER_DRY_RUN:-0}"' in script
    assert "Phase 3 lane 9 dry run finished before post-fix gate." in script
    assert 'PHASE3_REQUIRE_READY="${PHASE3_REQUIRE_READY:-1}"' in script
    assert 'BASELINE_FUNCTION_CALL_LOG_ROOT="${BASELINE_FUNCTION_CALL_LOG_ROOT:-$BASELINE_RAW_DIR/logs/function_call}"' in script
    assert '--baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT"' in script
    assert "--phase3-manifest-sha256" in script
    assert "--gate-stage post-fix" in script
    assert "PHASE3_GATE_ARGS+=(--require-ready)" in script


def test_phase3_post_fix_gate_index_wrapper_validates_all_gates():
    script_path = Path("phase3_validate_all_post_fix_gates.sh")
    script = script_path.read_text()

    assert os.access(script_path, os.X_OK)
    assert "set -euo pipefail" in script
    assert 'cd "$SCRIPT_DIR"' in script
    assert 'PYTHON_BIN="${PYTHON_BIN:-$DEFAULT_PYTHON_BIN}"' in script
    assert (
        'OUTPUT_DIR="${OUTPUT_DIR:-$SCRIPT_DIR/logs/equivalence_all/'
        'phase3_post_fix_gate_index}"'
    ) in script
    assert 'PHASE3_REQUIRE_READY="${PHASE3_REQUIRE_READY:-1}"' in script
    assert '--repo-root "$SCRIPT_DIR"' in script
    assert '--output-dir "$OUTPUT_DIR"' in script
    assert 'ARGS+=(--require-ready)' in script
    assert (
        '"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.'
        'phase3_post_fix_gate_index "${ARGS[@]}"'
    ) in script
