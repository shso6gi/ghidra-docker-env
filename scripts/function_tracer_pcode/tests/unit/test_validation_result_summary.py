# -*- coding: utf-8 -*-

import json
import base64
import os
import re
import shutil
import subprocess
import sys
import tarfile
import time
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.authority.decision.pair_status_authority import (
    PAIR_STATUS_PUBLIC_KEY_FILE,
    generate_pair_status_keypair,
    pair_status_operational_diagnostic,
    seal_pair_status,
)
from scripts.function_tracer_pcode.authority.contracts import authority_digest

from scripts.function_tracer_pcode.checker.unknown_reason import (
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    UnknownReasonId,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.reporting.result_summary import (
    STATUS_EQ,
    STATUS_ERROR,
    STATUS_INCOMPLETE,
    STATUS_NOT_EQ,
    STATUS_TIMEOUT,
    STATUS_UNKNOWN,
    aggregate_validation_logs,
    aggregate_validation_logs_by_function,
    assert_aggregation_invariant,
    build_run_health_summary,
    canonical_validation_surface,
    canonical_validation_surface_hash,
    classify_log_text,
    compare_validation_baseline_records,
    error_pairs_from_summary,
    format_function_results_summary,
    format_overall_results_summary,
    format_run_health_summary,
    format_validation_baseline_comparison,
    parse_log_identity,
    read_validation_log_record,
)
from scripts.function_tracer_pcode.reporting.run_health_summary import parse_overall_summary_health
from scripts.function_tracer_pcode.reporting.unknown_reason_summary import (
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


def _write_pair_status(log_path, outcome):
    path = log_path.with_suffix(".pair-status.json")
    private_key = log_path.parent / ".pair-status-test.key"
    public_key = log_path.parent / PAIR_STATUS_PUBLIC_KEY_FILE
    if not private_key.exists():
        generate_pair_status_keypair(private_key, public_key)
    digest = "a" * 64
    status = {
        "authority_kind": "DurableTimeoutFinalizationBundle",
        "supervisor_authority_kind": "DurableTimeoutFinalizationBundle",
        "supervisor_final_authority_digest": digest,
        "launch_receipt_digest": digest,
        "canonical_outcome": outcome,
        "decision_receipt_digest": digest,
        "result_occurrence_id": "result-occurrence",
        "result_entry_occurrence_receipt_digest": digest,
        "execution_identity_digest": digest,
        "execution_nonce": "execution-nonce",
        "stream_id": "stream-id",
        "source_snapshot_fingerprint": digest,
        "canonical_result_bundle_digest": digest,
        "canonical_result_bundle_kind": "CanonicalResultFinalizationBundle",
        "canonical_result_payload_preimage_digest": digest,
        "semantic_projection_digest": digest,
        "error_kind": None,
        "child_returncode": 143,
        "supervisor_status": "TIMEOUT",
        "supervisor_projection_digest": digest,
        "classification_valid": True,
        "pair_execution_target": {
            "schema": "eqbench-pair-execution-target-v1",
            "authority_kind": "PairExecutionTargetReceipt",
            "sample_identity": "sample/Eq/newV",
            "output_sample_relative_path": "sample/Eq/newV",
            "function_name": "client", "left_binary_id": "B7",
            "right_binary_id": "B13", "source_path": "source.c",
            "source_sha256": digest, "left_binary_path": "left.bin",
            "left_binary_sha256": digest, "right_binary_path": "right.bin",
            "right_binary_sha256": digest, "analysis_source_digest": digest,
            "analysis_config_digest": digest,
        },
        "finalization_bundle_digest": digest,
        "event_stream_authority_digest": digest,
        "child_exit_disposition": "EXITED_143_AFTER_SIGTERM",
        "child_returncode_observation_kind": "LIVE_PROCESS_WAIT",
    }
    status["pair_execution_target"]["target_digest"] = authority_digest(
        status["pair_execution_target"]
    )
    sealed = seal_pair_status(
        status, private_key_path=private_key, public_key_path=public_key
    )
    path.write_text(json.dumps(sealed))
    return path


def test_parse_log_identity_handles_neqbench_axis_filename() -> None:
    assert parse_log_identity(Path("f_N_B10_O_B11.log")) == (
        "f",
        "B10 ↔ B11",
    )


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


def _bash_validation_classify(path):
    repo_root = Path(__file__).resolve().parents[4]
    result = subprocess.run(
        [
            "bash",
            "-lc",
            'source scripts/validation_matrix_common.sh; validation_classify_log_result "$1"',
            "bash",
            str(path),
        ],
        cwd=repo_root,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return result.stdout.strip()


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


def test_canonical_pair_status_overrides_obsolete_log_only_error(tmp_path):
    path = _write_log(
        tmp_path,
        "client_B7_B13.log",
        "\n".join((
            "Result: TIMEOUT (pair process exceeded wall-clock time limit)",
            "Result: ERROR (pair process exited before emitting a final result)",
        )),
    )
    _write_pair_status(path, "TIMEOUT")

    record = read_validation_log_record(path, canonical_only=True)
    assert record.status == STATUS_TIMEOUT
    assert record.payloads == ()
    assert _bash_validation_classify(path) == STATUS_TIMEOUT


def test_canonical_pair_status_rejects_outcome_tampering(tmp_path):
    path = _write_log(tmp_path, "client_B7_B13.log", "Result: TIMEOUT")
    status_path = _write_pair_status(path, "TIMEOUT")
    payload = json.loads(status_path.read_text())
    payload["canonical_outcome"] = "EQUIVALENT"
    status_path.write_text(json.dumps(payload))

    with pytest.raises(ValueError, match="pair-status seal metadata is invalid"):
        read_validation_log_record(path, canonical_only=True)


def test_canonical_only_missing_pair_status_is_incomplete(tmp_path):
    path = _write_log(tmp_path, "client_B1_B2.log", "Result: EQUIVALENT")

    record = read_validation_log_record(path, canonical_only=True)

    assert record.status == STATUS_INCOMPLETE
    assert record.payloads == ()
    assert record.pair_status_metadata is None


def test_classify_log_cli_can_explicitly_reuse_legacy_terminal_line(tmp_path):
    path = _write_log(tmp_path, "client_B1_B2.log", "Result: EQUIVALENT")
    strict = subprocess.run(
        [sys.executable, "-m", "scripts.function_tracer_pcode.reporting.result_summary",
         "--classify-log", str(path)],
        check=True, text=True, capture_output=True,
    )
    legacy = subprocess.run(
        [sys.executable, "-m", "scripts.function_tracer_pcode.reporting.result_summary",
         "--classify-log", "--allow-legacy-log", str(path)],
        check=True, text=True, capture_output=True,
    )
    assert strict.stdout.strip() == STATUS_INCOMPLETE
    assert legacy.stdout.strip() == STATUS_EQ


def test_error_pairs_from_summary_returns_only_error_pairs(tmp_path):
    summary = tmp_path / "results_summary.txt"
    summary.write_text("\n".join((
        "  Error          : 2",
        "  ERROR pairs:",
        "    - B3 ↔ B9",
        "    - B10 ↔ B11",
        "",
        "  TIMEOUT pairs:",
        "    - B1 ↔ B2",
    )))
    assert error_pairs_from_summary(summary, matrix="EQ") == ("B3_B9", "B10_B11")

    summary.write_text("\n".join((
        "  Error          : 1",
        "  ERROR pairs:",
        "    - N_B3 ↔ O_B9",
    )))
    assert error_pairs_from_summary(summary, matrix="NEQ") == ("N_B3_O_B9",)


def test_signed_pair_status_rejects_semantically_inconsistent_status(tmp_path):
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

    path = _write_log(tmp_path, "client_B7_B13.log", "Result: TIMEOUT")
    status_path = _write_pair_status(path, "TIMEOUT")
    payload = json.loads(status_path.read_text())
    payload["canonical_outcome"] = "EQUIVALENT"
    seal_fields = {
        key for key in payload if key.startswith("pair_status_")
    }
    body = {key: value for key, value in payload.items() if key not in seal_fields}
    digest = authority_digest(body)
    private_key = Ed25519PrivateKey.from_private_bytes(
        (tmp_path / ".pair-status-test.key").read_bytes()
    )
    payload["pair_status_body_digest"] = digest
    payload["pair_status_signature"] = base64.b64encode(
        private_key.sign(bytes.fromhex(digest))
    ).decode("ascii")
    status_path.write_text(json.dumps(payload))

    with pytest.raises(ValueError, match="durable status/outcome join"):
        read_validation_log_record(path, canonical_only=True)


def test_run_health_counts_verified_pair_status_metadata(tmp_path):
    path = _write_log(tmp_path, "client_B7_B13.log", "Result: TIMEOUT")
    _write_pair_status(path, "TIMEOUT")
    summary = aggregate_validation_logs_by_function((path,), canonical_only=True)

    health = build_run_health_summary(summary)

    assert health["error_kind_counts"] == {"<none>": 1}
    assert health["child_returncode_counts"] == {"143": 1}
    assert health["supervisor_status_counts"] == {"TIMEOUT": 1}


def test_canonical_summary_aggregates_operational_invalid_pair_status(tmp_path):
    path = _write_log(tmp_path, "client_B7_B13.log", "Result: TIMEOUT")
    path.with_suffix(".pair-status.json").write_text(json.dumps({
        "classification_valid": False,
        "error_kind": "PAIR_STATUS_AUTHORITY_INVALID",
        "detail": "ValueError: durable restart authority is invalid",
    }))

    record = read_validation_log_record(path, canonical_only=True)
    summary = aggregate_validation_logs_by_function((path,), canonical_only=True)
    health = build_run_health_summary(summary)

    assert record.status == STATUS_ERROR
    assert record.payloads == ()
    assert record.pair_status_metadata == {
        "error_kind": "PAIR_STATUS_AUTHORITY_INVALID",
        "child_returncode": None,
        "supervisor_status": "INVALID",
        "classification_valid": False,
        "detail": "ValueError: durable restart authority is invalid",
    }
    assert summary.overall.count(STATUS_ERROR) == 1
    assert health["error_kind_counts"] == {"PAIR_STATUS_AUTHORITY_INVALID": 1}
    assert health["supervisor_status_counts"] == {"INVALID": 1}


def test_pair_status_operational_diagnostic_requires_exact_schema():
    diagnostic = {
        "classification_valid": False,
        "error_kind": "PAIR_STATUS_AUTHORITY_INVALID",
        "detail": "ValueError: primary classification failure",
    }

    assert pair_status_operational_diagnostic(diagnostic) == diagnostic
    assert pair_status_operational_diagnostic({**diagnostic, "extra": True}) is None
    assert pair_status_operational_diagnostic({**diagnostic, "detail": ""}) is None
    assert pair_status_operational_diagnostic({
        **diagnostic, "error_kind": "DIFFERENT_ERROR_KIND",
    }) is None


def test_pair_status_validation_classifies_operational_diagnostic_as_error(tmp_path):
    status_path = tmp_path / "pair-status.json"
    status_path.write_text(json.dumps({
        "classification_valid": False,
        "error_kind": "PAIR_STATUS_AUTHORITY_INVALID",
        "detail": "ValueError: primary classification failure",
    }))

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "scripts.function_tracer_pcode.authority.decision.pair_status_authority",
            "--validate-pair-status",
            str(status_path),
            "--allow-operational-diagnostic",
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0
    assert result.stdout.strip() == "ERROR"
    assert "signed pair-status schema differs" not in result.stderr


def test_operational_diagnostic_mode_still_verifies_signed_status(tmp_path):
    log_path = _write_log(tmp_path, "client_B7_B13.log", "Result: TIMEOUT")
    status_path = _write_pair_status(log_path, "TIMEOUT")

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "scripts.function_tracer_pcode.authority.decision.pair_status_authority",
            "--validate-pair-status",
            str(status_path),
            "--public-key",
            str(tmp_path / PAIR_STATUS_PUBLIC_KEY_FILE),
            "--allow-operational-diagnostic",
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0
    assert result.stdout.strip() == "TIMEOUT"


def test_runner_canonical_result_subprocess_persists_primary_classification_error(
    tmp_path,
):
    paths = [tmp_path / f"input-{index}" for index in range(8)]
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "scripts.function_tracer_pcode.authority.decision.canonical_result",
            "--classify-pair-log", str(paths[0]),
            "--supervisor-projection", str(paths[1]),
            "--checkpoint-root", str(paths[2]),
            "--execution-nonce", "execution-nonce",
            "--supervisor-signing-key-id", "supervisor-key",
            "--supervisor-signing-key-file", str(paths[3]),
            "--worker-signing-key-id", "worker-key",
            "--worker-signing-key-file", str(paths[4]),
            "--pair-status-signing-private-key-file", str(paths[5]),
            "--pair-status-verification-key-file", str(paths[6]),
            "--pair-execution-target-file", str(paths[7]),
            "--classification-diagnostic-log", str(paths[0]),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    payload = json.loads(result.stdout)
    message = f"Primary pair classification error: {payload['detail']}"

    assert result.returncode == 2
    assert result.stderr.strip() == message
    assert paths[0].read_text(encoding="utf-8").strip() == message
    assert payload == {
        "classification_valid": False,
        "error_kind": "PAIR_STATUS_AUTHORITY_INVALID",
        "detail": payload["detail"],
    }


@pytest.mark.parametrize(
    "diagnostic",
    (
        {
            "classification_valid": False,
            "error_kind": "PAIR_STATUS_AUTHORITY_INVALID",
            "detail": "invalid",
            "extra": "unsealed",
        },
        {
            "classification_valid": False,
            "error_kind": "PAIR_STATUS_AUTHORITY_INVALID",
            "detail": "",
        },
        {
            "classification_valid": False,
            "error_kind": "DIFFERENT_ERROR_KIND",
            "detail": "invalid",
        },
    ),
)
def test_canonical_summary_rejects_other_unsigned_diagnostics(
    tmp_path, diagnostic,
):
    path = _write_log(tmp_path, "client_B7_B13.log", "Result: TIMEOUT")
    _write_pair_status(path, "TIMEOUT")
    path.with_suffix(".pair-status.json").write_text(json.dumps(diagnostic))

    with pytest.raises(ValueError, match="signed pair-status schema differs"):
        read_validation_log_record(path, canonical_only=True)


def test_canonical_pair_status_rejects_schema_extension(tmp_path):
    path = _write_log(tmp_path, "client_B7_B13.log", "Result: TIMEOUT")
    status_path = _write_pair_status(path, "TIMEOUT")
    payload = json.loads(status_path.read_text())
    payload["unsealed_claim"] = True
    status_path.write_text(json.dumps(payload))

    with pytest.raises(ValueError, match="signed pair-status schema differs"):
        read_validation_log_record(path, canonical_only=True)


def test_canonical_pair_status_remains_verifiable_after_private_key_removal(
    tmp_path,
):
    path = _write_log(tmp_path, "client_B7_B13.log", "Result: TIMEOUT")
    _write_pair_status(path, "TIMEOUT")
    (tmp_path / ".pair-status-test.key").unlink()

    record = read_validation_log_record(path, canonical_only=True)
    assert record.status == STATUS_TIMEOUT


def test_canonical_pair_status_rejects_replacement_public_key(tmp_path):
    path = _write_log(tmp_path, "client_B7_B13.log", "Result: TIMEOUT")
    _write_pair_status(path, "TIMEOUT")
    replacement_private = tmp_path / "replacement.key"
    generate_pair_status_keypair(
        replacement_private, tmp_path / PAIR_STATUS_PUBLIC_KEY_FILE
    )

    with pytest.raises(ValueError, match="pair-status seal metadata is invalid"):
        read_validation_log_record(path, canonical_only=True)


def test_validation_classifier_uses_trailing_timeout_result_after_error_json():
    error_payload = _payload(
        "fc_read_after_void",
        None,
        error_message="Function 'fc_read_after_void' not found",
        failure_status="function_lookup_miss",
    )
    text = "\n".join(
        [
            "Result: ERROR",
            RESULT_JSON_BEGIN,
            json.dumps(error_payload),
            RESULT_JSON_END,
            "Result: TIMEOUT (pair process exceeded wall-clock time limit)",
        ]
    )

    assert classify_log_text(text) == STATUS_TIMEOUT


def test_validation_classifier_uses_trailing_timeout_payload_after_error_json():
    error_payload = _payload(
        "fc_read_after_void",
        None,
        error_message="boom",
    )
    timeout_payload = {
        "is_equivalent": None,
        "is_timeout": True,
        "timeout_class": "pair_process_timeout",
    }
    text = "\n".join(
        [
            "Result: ERROR",
            RESULT_JSON_BEGIN,
            json.dumps(error_payload),
            RESULT_JSON_END,
            "Result: TIMEOUT (pair process exceeded wall-clock time limit)",
            RESULT_JSON_BEGIN,
            json.dumps(timeout_payload),
            RESULT_JSON_END,
        ]
    )

    assert classify_log_text(text) == STATUS_TIMEOUT


def test_matrix_validation_classifies_function_lookup_miss_as_incomplete(tmp_path):
    path = _write_log(
        tmp_path,
        "fc_missing_B1_B2.log",
        "Result: ERROR",
        _payload(
            "fc_missing",
            None,
            error_message="Function 'fc_missing' not found",
            failure_status="function_lookup_miss",
        ),
    )

    assert classify_log_text(path.read_text()) == STATUS_ERROR
    assert read_validation_log_record(path).status == STATUS_INCOMPLETE


def test_bash_validation_classifier_rejects_legacy_json_and_result_lines(tmp_path):
    path = tmp_path / "stale_lookup_then_real_error.log"
    path.write_text(
        "\n".join(
            [
                "Result: ERROR",
                RESULT_JSON_BEGIN,
                json.dumps(
                    _payload(
                        "fc_missing",
                        None,
                        error_message="Function 'fc_missing' not found",
                        failure_status="function_lookup_miss",
                    )
                ),
                RESULT_JSON_END,
                "debug from rerun",
                "Result: ERROR",
            ]
        )
    )

    assert _bash_validation_classify(path) == STATUS_INCOMPLETE


def test_bash_validation_classifier_maps_final_lookup_miss_json_to_incomplete(tmp_path):
    path = _write_log(
        tmp_path,
        "final_lookup_miss.log",
        "Result: ERROR",
        _payload(
            "fc_missing",
            None,
            error_message="Function 'fc_missing' not found",
            failure_status="function_lookup_miss",
        ),
    )

    assert _bash_validation_classify(path) == STATUS_INCOMPLETE


def test_canonical_validation_surface_hash_is_stable_for_sorted_multisets(tmp_path):
    log_a = _write_log(
        tmp_path,
        "fc_demo/fc_demo_B1_B2.log",
        "Result: UNKNOWN",
        _payload(
            "fc_demo",
            None,
            binary1_name="B1",
            binary2_name="B2",
            unknown_reasons=[make_unknown_reason(UnknownReasonId.RETURN_COVERAGE_GAP).to_dict()],
        ),
    )
    log_b = _write_log(
        tmp_path,
        "fc_demo/fc_demo_B1_B3.log",
        "Result: EQUIVALENT",
        _payload("fc_demo", True, binary1_name="B1", binary2_name="B3"),
    )
    forward = aggregate_validation_logs([log_a, log_b]).records
    reversed_order = aggregate_validation_logs([log_b, log_a]).records

    surface = canonical_validation_surface(forward)

    assert surface["total_results"] == 2
    assert surface["pair_identities"] == [["fc_demo", "B1 ↔ B2"], ["fc_demo", "B1 ↔ B3"]]
    assert canonical_validation_surface_hash(forward) == canonical_validation_surface_hash(reversed_order)


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


def test_overall_summary_compact_suppresses_large_tuple_sections(tmp_path):
    logs = [
        _write_log(
            tmp_path,
            "fc_read_after_void/fc_read_after_void_B1_B2.log",
            "Result: UNKNOWN",
            _payload(
                "fc_read_after_void",
                None,
                unknown_reasons=[
                    make_unknown_reason(UnknownReasonId.RETURN_COVERAGE_GAP).to_dict()
                ],
            ),
        )
    ]
    overall = aggregate_validation_logs_by_function(logs)

    text = format_overall_results_summary(overall, compact=True, max_items=1)

    assert "UNKNOWN by reason:" in text
    assert "Reason record tuples:" not in text
    assert "Proof action tuples:" not in text
    assert "Canonical baseline comparison:" not in text


def test_result_summary_cli_writes_health_summary_artifacts(tmp_path):
    log_path = _write_log(
        tmp_path,
        "after/fc_read_after_void/fc_read_after_void_B1_B2.log",
        "Result: UNKNOWN",
        _payload(
            "fc_read_after_void",
            None,
            unknown_reasons=[
                make_unknown_reason(UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING).to_dict()
            ],
        ),
    )
    health_json = tmp_path / "health.json"
    health_text = tmp_path / "health.txt"

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "scripts.function_tracer_pcode.reporting.result_summary",
            "--overall-summary",
            "--summary-level",
            "compact",
            "--health-summary-json",
            str(health_json),
            "--health-summary-text",
            str(health_text),
            str(log_path),
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    payload = json.loads(health_json.read_text())
    assert "Reason record tuples:" not in result.stdout
    assert payload["final_result_counts"]["UNKNOWN"] == 1
    assert payload["unknown_units"] == 1
    assert "Run health summary:" in health_text.read_text()
    assert "return_width_bridge_missing" in format_run_health_summary(payload)


def test_run_health_summary_parses_overall_summary_without_pair_logs(tmp_path):
    overall_summary = tmp_path / "overall_summary.txt"
    overall_summary.write_text(
        "\n".join(
            [
                "============================================================",
                "  All functions processed: 1 function(s)",
                "============================================================",
                "  fc_demo                       : TOTAL=  2, EQ=  1, NOT_EQ=  0, ERROR=  0, UNKNOWN=  1, TIMEOUT=  0, INCOMPLETE=  0, WALL=1.000s",
                "",
                "  Overall totals              : TOTAL=  2, EQ=  1, NOT_EQ=  0, ERROR=  0, UNKNOWN=  1, TIMEOUT=  0, INCOMPLETE=  0",
                "",
                "  UNKNOWN validation summary:",
                "    Total results : 2",
                "    Unknown results: 1",
                "    Unknown units  : 3",
                "    UNKNOWN by reason:",
                "      - unresolved_expression: 2",
                "      - sat_unsafety: 1",
                "    Proof backlog by reason:",
                "      - unresolved_expression: 2",
                "    Operational UNKNOWN by reason:",
                "      (none)",
            ]
        )
    )

    health = parse_overall_summary_health(overall_summary)

    assert health["source"] == "overall_summary_txt"
    assert health["total_results"] == 2
    assert health["final_result_counts"]["UNKNOWN"] == 1
    assert health["unknown_units"] == 3
    assert health["functions"]["fc_demo"]["EQ"] == 1
    assert health["unknown_by_reason"] == {"unresolved_expression": 2, "sat_unsafety": 1}


def test_result_summary_module_accepts_function_wall_time_option():
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "scripts.function_tracer_pcode.reporting.result_summary",
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
            "scripts.function_tracer_pcode.reporting.result_summary",
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
            "scripts.function_tracer_pcode.reporting.result_summary",
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
            "scripts.function_tracer_pcode.reporting.result_summary",
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
            "scripts.function_tracer_pcode.reporting.result_summary",
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
            "scripts.function_tracer_pcode.reporting.result_summary",
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
            "scripts.function_tracer_pcode.reporting.result_summary",
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
            "scripts.function_tracer_pcode.reporting.result_summary",
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


def test_result_summary_reads_large_nul_delimited_log_manifest(tmp_path):
    log_path = _write_log(
        tmp_path,
        "pair with spaces.log",
        "Result: EQUIVALENT",
    )
    manifest_path = tmp_path / "logs.list0"
    manifest_path.write_bytes((os.fsencode(log_path) + b"\0") * 20_000)

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "scripts.function_tracer_pcode.reporting.result_summary",
            "--overall-summary",
            "--summary-level",
            "compact",
            "--log-list0",
            str(manifest_path),
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stderr
    assert "TOTAL=20000" in result.stdout


def test_eqbench_runner_uses_bounded_summary_argv_and_excludes_stdout_log():
    script = Path("eqbench_run_all_32jobs.sh").read_text()

    assert 'EQBENCH_RUN_TMPDIR="$(mktemp -d "$EQBENCH_TMPDIR/eqbench-run.XXXXXX")"' in script
    assert 'pair_tmpdir="$(mktemp -d "$EQBENCH_RUN_TMPDIR/pair.XXXXXX")"' in script
    assert 'checkpoint_root="${EQBENCH_RUN_TMPDIR}/process-authority"' in script
    assert 'checkpoint_root="${output_dir}/.process-authority"' not in script
    assert 'env "TMPDIR=$pair_tmpdir" "TEMP=$pair_tmpdir" "TMP=$pair_tmpdir"' in script
    assert 'trap cleanup_eqbench_run_tmpdir EXIT' in script
    assert 'rm -rf -- "$pair_tmpdir"' in script
    assert "write_log_list0()" in script
    assert '--log-list0 "$function_log_list"' in script
    assert '--log-list0 "$overall_log_list"' in script
    assert '! -name "run_stdout.log"' in script
    assert "--emit-process-timeout-json" not in script
    assert "UNKNOWN_TAXONOMY_V2_DISABLE_PROCESS_WORKER_RUNTIME" not in script
    assert 'PAIR_PROCESS_TIMEOUT="${PAIR_PROCESS_TIMEOUT:-600s}"' in script
    assert "--classify-pair-log" in script
    assert "validation_result_log_is_complete" not in script
    assert "pair_status_is_skippable_for_run_mode" in script
    assert '--resume-skip-mode "$mode"' in script
    assert "results_summary.txt" in script
    assert "function_summary_all_pairs_reusable" in script
    assert "Summary shortcut: skipped" in script
    assert "validate_current_pair_status" in script
    assert "remove_pair_process_authority" in script
    assert "reporting.process_authority_cleanup" in script
    assert "EQBENCH_PRIVATE_AUTHORITY_ROOT" in script
    # Issue #170: 鍵の具体化は共通 helper が唯一の owner で、keyset の lock の中で呼ぶ。
    assert "--validate-private-key" not in script
    assert 'validation_lock_authority_keyset "$PROCESS_AUTHORITY_ROOT" "$OUTPUT_BASE_DIR" || exit 1' in script
    assert "validation_materialize_pair_status_keypair" in script
    assert "validation_unlock_authority_keyset" in script
    assert "expected_pair_status_paths.txt" in script
    failure_decision = script.index("FINAL_RUN_EXIT_STATUS=0")
    receipt_issue = script.rindex("reporting.execution_receipt")
    assert failure_decision < receipt_issue
    assert 'FINAL_RUN_EXIT_STATUS=1' in script[failure_decision:receipt_issue]
    assert '--exit-status "$FINAL_RUN_EXIT_STATUS"' in script
    assert 'exit "$FINAL_RUN_EXIT_STATUS"' in script[receipt_issue:]
    overall_summary_call = script.split(
        'write_summary_file "$OUTPUT_BASE_DIR/overall_summary.txt"', 1
    )[1].split("\nfi", 1)[0]
    assert '"${ALL_LOG_FILES[@]}"' not in overall_summary_call


def test_eqbench_runner_clamps_parallelism_and_records_pair_progress_contract(
    tmp_path,
):
    script = Path("eqbench_run_all_32jobs.sh").read_text()
    assert 'EQBENCH_CPU_TOKENS=' in script
    assert 'EQBENCH_PAIR_CPU_TOKENS=' in script
    assert 'RESOURCE_ADMISSION_JOBS=$((EQBENCH_CPU_TOKENS / EQBENCH_PAIR_CPU_TOKENS))' in script
    # Issue #160: the receipt writer is shared with the Neq runner; the schema
    # lives in reporting/pair_runtime_receipt.py, the shell entry in the common file.
    common = Path("scripts/validation_matrix_common.sh").read_text()
    receipt_module = Path(
        "scripts/function_tracer_pcode/reporting/pair_runtime_receipt.py"
    ).read_text()
    assert 'validation_write_pair_runtime_receipt() {' in common
    assert 'write_pair_progress_receipt' not in script
    assert 'validation_write_pair_runtime_receipt "$PYTHON_BIN" --state COMPLETED' in script
    assert 'eqbench-pair-progress-receipt-v2' in receipt_module
    assert "/usr/bin/time -f 'elapsed_seconds=%e\\nmax_rss_kb=%M'" in script
    assert '"writer_pid": os.getpid()' in receipt_module
    assert '"timed_command_pid"' in receipt_module
    assert '"supervisor_pid"' not in receipt_module
    assert '"pid": os.getpid()' not in receipt_module

    output_dir = tmp_path / "eqbench"
    env = os.environ.copy()
    env.update({
        "OUTPUT_BASE_DIR": str(output_dir),
        "EQBENCH_TMPDIR": str(tmp_path / "tmp"),
        "EQBENCH_PRIVATE_AUTHORITY_ROOT": str(tmp_path / "authority"),
        "EQBENCH_RUN_SCOPE": "REPRESENTATIVE",
        "EQBENCH_BUILD_POLICY": "PREBUILT_ONLY",
        "EQBENCH_SAMPLE_FILTER": r"REVE/inlining/Eq/newV[.]c$",
        "EQBENCH_MAX_SAMPLES": "1",
        "EQBENCH_PAIR_FILTER": "B10_B11",
        "PARALLEL_JOBS": "9",
        "EQBENCH_CPU_TOKENS": "16",
        "EQBENCH_PAIR_CPU_TOKENS": "8",
        "DRY_RUN": "1",
    })
    result = subprocess.run(
        ["bash", "eqbench_run_all_32jobs.sh"],
        check=False,
        capture_output=True,
        text=True,
        env=env,
    )
    assert result.returncode == 0, result.stderr
    manifest = (output_dir / "run_manifest.txt").read_text()
    assert "parallel_jobs=2" in manifest
    assert "parallel_jobs_requested=9" in manifest
    assert "resource_admission_enabled=1" in manifest
    assert "cpu_tokens=16" in manifest
    assert "pair_cpu_tokens=8" in manifest


def _run_ps_ppid(parent_pid):
    return subprocess.run(
        ["ps", "-o", "pid=", "--ppid", str(parent_pid)],
        check=False,
        capture_output=True,
        text=True,
    )


def _observe_child_pids(
    parent_pid,
    *,
    run_ps=_run_ps_ppid,
    attempts=100,
    sleep_seconds=0.01,
    sleep=time.sleep,
):
    """Return the PIDs ``ps --ppid`` reports for ``parent_pid``.

    procps ``ps`` exits 1 with empty output when nothing matches, and also
    exits 1 on a usage error (with a message on stderr), so only "no child
    yet" is retried; every other observation fails. Rules, first match wins:

    1. ``run_ps`` raises -> propagate
    2. stderr non-empty -> fail
    3. rc 0 and every non-empty line is a positive PID -> those PIDs
    4. rc 0 and no non-empty line -> retry
    5. rc 1 and empty stdout -> retry
    6. anything else -> fail
    7. ``attempts`` observations without a PID -> fail

    Every retried observation is followed by one ``sleep(sleep_seconds)``,
    exactly as in the loop this helper replaced, so the wait is unchanged.
    """
    for _ in range(attempts):
        result = run_ps(parent_pid)
        if result.stderr:
            pytest.fail(
                f"ps --ppid {parent_pid} wrote to stderr "
                f"(rc={result.returncode}): {result.stderr!r}"
            )
        lines = [line.strip() for line in result.stdout.splitlines()]
        lines = [line for line in lines if line]
        if result.returncode == 0 and lines:
            if not all(
                re.fullmatch(r"[0-9]+", line) and int(line) > 0
                for line in lines
            ):
                pytest.fail(
                    f"ps --ppid {parent_pid} printed a non-PID line: "
                    f"{result.stdout!r}"
                )
            return {int(line) for line in lines}
        if not (
            result.returncode == 0
            or (result.returncode == 1 and not result.stdout)
        ):
            pytest.fail(
                f"ps --ppid {parent_pid} failed (rc={result.returncode}): "
                f"stdout={result.stdout!r}"
            )
        sleep(sleep_seconds)
    pytest.fail(
        f"ps --ppid {parent_pid} reported no child after {attempts} attempts"
    )


def _scripted_ps(*results):
    calls = []
    remaining = list(results)

    def run_ps(parent_pid):
        calls.append(parent_pid)
        result = remaining.pop(0) if len(remaining) > 1 else remaining[0]
        if isinstance(result, BaseException):
            raise result
        returncode, stdout, stderr = result
        return subprocess.CompletedProcess(
            ["ps"], returncode, stdout=stdout, stderr=stderr
        )

    return run_ps, calls


def _no_sleep(seconds):
    pass


def test_observe_child_pids_retries_ps_exit_1_until_the_child_appears():
    run_ps, calls = _scripted_ps(
        (1, "", ""), (1, "", ""), (1, "", ""), (0, "   1234\n", "")
    )

    assert _observe_child_pids(42, run_ps=run_ps, sleep=_no_sleep) == {1234}
    assert calls == [42] * 4


def test_observe_child_pids_retries_ps_exit_0_with_empty_output():
    run_ps, calls = _scripted_ps((0, "", ""), (0, "\n", ""), (0, "7\n", ""))

    assert _observe_child_pids(42, run_ps=run_ps, sleep=_no_sleep) == {7}
    assert len(calls) == 3


def test_observe_child_pids_fails_when_no_child_appears_within_budget():
    run_ps, calls = _scripted_ps((1, "", ""))
    sleeps = []

    with pytest.raises(pytest.fail.Exception, match="no child after 100 attempts"):
        _observe_child_pids(42, run_ps=run_ps, sleep=sleeps.append)
    # The default budget is the replaced loop's: 100 observations, each
    # followed by a 10 ms sleep. A longer wait would hide the race.
    assert len(calls) == 100
    assert sleeps == [0.01] * 100


@pytest.mark.parametrize(
    "result",
    [
        (1, "", "error: unsupported option (BSD syntax)\n"),
        (0, "1234\n", "warning\n"),
    ],
)
def test_observe_child_pids_fails_at_once_on_stderr(result):
    run_ps, calls = _scripted_ps(result, (0, "1234\n", ""))

    with pytest.raises(pytest.fail.Exception, match="stderr"):
        _observe_child_pids(42, run_ps=run_ps, sleep=_no_sleep)
    assert len(calls) == 1


@pytest.mark.parametrize("result", [(2, "", ""), (1, "1234\n", "")])
def test_observe_child_pids_fails_at_once_on_other_exit(result):
    run_ps, calls = _scripted_ps(result, (0, "1234\n", ""))

    with pytest.raises(pytest.fail.Exception, match="failed"):
        _observe_child_pids(42, run_ps=run_ps, sleep=_no_sleep)
    assert len(calls) == 1


@pytest.mark.parametrize(
    "stdout", ["abc\n", "0\n", "-5\n", "1234\nabc\n", "12 34\n"]
)
def test_observe_child_pids_fails_on_a_non_pid_line(stdout):
    run_ps, calls = _scripted_ps((0, stdout, ""))

    with pytest.raises(pytest.fail.Exception, match="non-PID"):
        _observe_child_pids(42, run_ps=run_ps, sleep=_no_sleep)
    assert len(calls) == 1


def test_observe_child_pids_propagates_a_failure_to_run_ps():
    run_ps, calls = _scripted_ps(FileNotFoundError("ps"))

    with pytest.raises(FileNotFoundError):
        _observe_child_pids(42, run_ps=run_ps, sleep=_no_sleep)
    assert len(calls) == 1


_PS_NO_MATCH_FIXTURE = (
    Path(__file__).resolve().parents[1] / "fixtures" / "ps_no_match"
)


def _start_timed_wrapper():
    return subprocess.Popen(
        [
            "/usr/bin/time",
            "-f",
            "elapsed_seconds=%e",
            sys.executable,
            "-c",
            "import time; time.sleep(2)",
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )


def test_timed_command_pid_is_distinct_from_timed_child_process():
    """The PID captured by ``$!`` identifies GNU time, not its child."""
    wrapper = _start_timed_wrapper()
    try:
        child_pids = _observe_child_pids(wrapper.pid)
        assert wrapper.pid not in child_pids
        assert child_pids
    finally:
        wrapper.terminate()
        wrapper.wait(timeout=5)


def test_timed_command_pid_contract_survives_ps_no_match_exits(
    tmp_path, monkeypatch,
):
    """Issue #157: the real ``ps`` path retries ``ps`` exiting 1 on no match.

    The fixture ``ps`` answers the first three calls the way procps does
    before GNU time has forked its child (exit 1, no output) and runs the
    real ``ps`` afterwards.
    """
    real_ps = shutil.which("ps")
    assert real_ps
    calls = tmp_path / "ps-calls"
    monkeypatch.setenv(
        "PATH", f"{_PS_NO_MATCH_FIXTURE}{os.pathsep}{os.environ['PATH']}"
    )
    monkeypatch.setenv("PS_NO_MATCH_REAL_PS", real_ps)
    monkeypatch.setenv("PS_NO_MATCH_CALLS", str(calls))
    monkeypatch.setenv("PS_NO_MATCH_COUNT", "3")
    wrapper = _start_timed_wrapper()
    try:
        child_pids = _observe_child_pids(wrapper.pid)
        assert int(calls.read_text()) >= 4
        assert wrapper.pid not in child_pids
        assert child_pids
    finally:
        wrapper.terminate()
        wrapper.wait(timeout=5)


def test_eqbench_runner_cleans_authority_after_validation_diagnostics():
    script = Path("eqbench_run_all_32jobs.sh").read_text()
    validation_call = script.index(
        'if pair_status_validation_detail="$(validate_current_pair_status'
    )
    cleanup_call = script.index(
        "if cleanup_pair_process_authority_with_run_health",
        validation_call,
    )
    validation_failure = script.index(
        "generated pair status failed authority validation",
        validation_call,
    )
    log_copy = script.index(
        "Pair-status authority validation failed:",
        validation_failure,
    )
    assert validation_call < validation_failure < log_copy < cleanup_call


def test_eqbench_runner_reports_primary_diagnostic_before_signature_validation():
    script = Path("eqbench_run_all_32jobs.sh").read_text()
    validation_start = script.index("validate_current_pair_status() {")
    validation_end = script.index(
        "remove_pair_process_authority() {", validation_start
    )
    validation_block = script[validation_start:validation_end]

    assert "--allow-operational-diagnostic" in validation_block
    assert '--classification-diagnostic-log "$log_file"' in script
    assert "Primary pair classification error:" in Path(
        "scripts/function_tracer_pcode/authority/decision/canonical_result.py"
    ).read_text()


def test_eqbench_runner_reports_cleanup_failure_as_independent_run_health_error():
    script = Path("eqbench_run_all_32jobs.sh").read_text()
    cleanup_start = script.index("cleanup_pair_process_authority_with_run_health() {")
    cleanup_end = script.index(
        "pair_is_selected() {",
        cleanup_start,
    )
    cleanup_block = script[cleanup_start:cleanup_end]

    assert "PAIR_STATUS_AUTHORITY_INVALID" not in cleanup_block
    assert "Process-authority cleanup run-health failure:" in cleanup_block
    assert '>> "$PROCESS_AUTHORITY_CLEANUP_FAILURES_FILE"' in cleanup_block
    assert '> "$PROCESS_AUTHORITY_CLEANUP_STOP_FILE"' in cleanup_block
    assert "Stopping new pair scheduling after process-authority cleanup failure." in script
    assert "process_authority_cleanup_failure_count=" in script
    assert "process-authority cleanup run-health failure(s)" in script


def test_eqbench_cleanup_failure_preserves_pair_classification_and_records_run_health(
    tmp_path,
):
    script = Path("eqbench_run_all_32jobs.sh").read_text()
    function_source = script[
        script.index("cleanup_pair_process_authority_with_run_health() {"):
        script.index("pair_is_selected() {")
    ]
    log_file = tmp_path / "pair.log"
    failure_file = tmp_path / "cleanup-failures.txt"

    result = subprocess.run(
        [
            "bash",
            "-c",
            "remove_pair_process_authority() { "
            + 'echo "injected cleanup failure" >&2; return 23; }\n'
            + function_source
            + '\nPROCESS_AUTHORITY_CLEANUP_FAILURES_FILE="$1"\n'
            + 'PROCESS_AUTHORITY_CLEANUP_STOP_FILE="$8"\n'
            + "cleanup_pair_process_authority_with_run_health "
            + '"$2" "$3" "$4" "$5" "$6" "$7"',
            "bash",
            str(failure_file),
            str(tmp_path / "checkpoint"),
            "0123456789abcdef01234567",
            str(log_file),
            str(tmp_path / "pair-status.json"),
            "sample",
            "foo_B1_B2",
            str(tmp_path / "cleanup-stop"),
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 23
    assert "PAIR_STATUS_AUTHORITY_INVALID" not in result.stdout + result.stderr
    assert "injected cleanup failure" in log_file.read_text()
    assert failure_file.read_text().strip().split("\t") == [
        "sample",
        "foo_B1_B2",
        "0123456789abcdef01234567",
    ]
    assert (tmp_path / "cleanup-stop").is_file()


def test_eqbench_summary_failure_preserves_actual_exit_status(tmp_path):
    script = Path("eqbench_run_all_32jobs.sh").read_text()
    function_source = script[
        script.index("write_summary_file() {"):script.index("write_log_list0() {")
    ]
    output_path = tmp_path / "summary.txt"
    result = subprocess.run(
        [
            "bash",
            "-c",
            function_source
            + '\nwrite_summary_file "$1" bash -c "exit 23"',
            "bash",
            str(output_path),
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 23
    assert f"summary generation failed for {output_path} (exit=23)" in result.stderr
    assert not output_path.exists()


