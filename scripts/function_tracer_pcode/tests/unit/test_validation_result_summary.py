# -*- coding: utf-8 -*-

import json
import subprocess
import sys

from scripts.function_tracer_pcode.equivalence.unknown_reason import (
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
    format_function_results_summary,
    format_overall_results_summary,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
)


def _write_log(tmp_path, name, human_result, payload=None):
    path = tmp_path / name
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
    assert "fc_read_after_void" in overall_text
    assert "ptr_call_and_store" in overall_text
    assert "Overall totals" in overall_text
    assert "UNKNOWN by reason:" in overall_text


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
