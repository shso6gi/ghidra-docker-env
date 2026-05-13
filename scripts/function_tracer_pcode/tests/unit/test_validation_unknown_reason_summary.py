# -*- coding: utf-8 -*-

import subprocess
import sys

from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownDecisionEffect,
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    UnknownReasonClass,
    UnknownReasonId,
    UnknownReasonScope,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
    compare_validation_unknowns,
    extract_result_payloads_from_text,
    format_validation_unknown_diff,
    format_validation_unknown_summary,
    summarize_validation_unknowns,
)


def _payload(function_name, *, is_equivalent=None, reasons=(), debug_trace=None):
    payload = {
        "is_equivalent": is_equivalent,
        "function1_name": function_name,
        "function2_name": function_name,
        "binary1_name": "before.bin",
        "binary2_name": "after.bin",
        "error_message": None,
        "unknown_reasons": [
            reason.to_dict() if hasattr(reason, "to_dict") else reason
            for reason in reasons
        ],
    }
    if debug_trace is not None:
        payload["debug_trace"] = debug_trace
    return payload


def test_validation_unknown_summary_tracks_plan16_dimensions_for_target_cases():
    summary = summarize_validation_unknowns(
        [
            _payload(
                "fc_read_after_void",
                reasons=[
                    make_unknown_reason(
                        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING,
                        pair_or_case="B1-B2",
                    )
                ],
            ),
            _payload(
                "ptr_call_and_store",
                reasons=[
                    make_unknown_reason(
                        UnknownReasonId.RECOVERABLE_PARTIAL,
                        pair_or_case="B1-B3",
                    )
                ],
            ),
            _payload(
                "loop_method_b_test:lmb_sum_prefix_peeled3_tail",
                is_equivalent=True,
            ),
            _payload(
                "unrelated",
                reasons=[make_unknown_reason(UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT)],
            ),
        ],
        target_cases=(
            "fc_read_after_void",
            "ptr_call_and_store",
            "loop_method_b_test",
        ),
    )

    assert summary.total_results == 3
    assert summary.unknown_results == 2
    assert summary.unknown_by_reason == {
        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value: 1,
        UnknownReasonId.RECOVERABLE_PARTIAL.value: 1,
    }
    assert summary.unknown_by_decision_effect == {
        UnknownDecisionEffect.BLOCKS_EQUIVALENCE.value: 1,
        UnknownDecisionEffect.RETRYABLE.value: 1,
    }
    assert summary.unknown_by_reason_scope == {
        UnknownReasonScope.QUERY.value: 1,
        UnknownReasonScope.FUNCTION.value: 1,
    }
    assert summary.proof_backlog_by_reason == {
        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value: 1,
    }
    assert summary.proof_backlog_by_proof_kind == {
        "abi_relation_proof": 1,
        "high_bit_proof": 1,
    }
    assert summary.proof_backlog_by_action_status == {
        UnknownRecoveryActionStatus.PLANNED.value: 2,
    }
    assert summary.proof_backlog_by_recovery_action == {
        "return_width_bridge_missing | abi_relation_proof | abi_relation | planned": 1,
        "return_width_bridge_missing | high_bit_proof | high_bit_relation | planned": 1,
    }
    assert summary.operational_unknown_by_reason == {
        UnknownReasonId.RECOVERABLE_PARTIAL.value: 1,
    }
    assert summary.operational_unknown_by_class == {
        UnknownReasonClass.OPERATIONAL_GAP.value: 1,
    }


def test_validation_unknown_diff_reports_before_after_reason_effect_scope_changes():
    before = [
        _payload(
            "fc_read_after_void",
            reasons=[make_unknown_reason(UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING)],
        ),
        _payload(
            "ptr_call_and_store",
            reasons=[make_unknown_reason(UnknownReasonId.RECOVERABLE_PARTIAL)],
        ),
        _payload(
            "loop_method_b_test:lmb_sum_even_index_step2",
            reasons=[make_unknown_reason(UnknownReasonId.METHOD_B_CLOSURE_BLOCKED)],
        ),
    ]
    after = [
        _payload("fc_read_after_void", is_equivalent=True),
        _payload(
            "ptr_call_and_store",
            reasons=[make_unknown_reason(UnknownReasonId.RECOVERABLE_PARTIAL)],
        ),
        _payload(
            "loop_method_b_test:lmb_sum_even_index_step2",
            reasons=[make_unknown_reason(UnknownReasonId.READONLY_IDENTITY_MISSING)],
        ),
    ]

    diff = compare_validation_unknowns(
        before,
        after,
        target_cases=(
            "fc_read_after_void",
            "ptr_call_and_store",
            "loop_method_b_test",
        ),
    )

    assert diff.delta_unknown_results == -1
    assert diff.unknown_by_reason_delta == {
        UnknownReasonId.METHOD_B_CLOSURE_BLOCKED.value: -1,
        UnknownReasonId.READONLY_IDENTITY_MISSING.value: 1,
        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value: -1,
    }
    assert diff.unknown_by_decision_effect_delta == {
        UnknownDecisionEffect.BLOCKS_EQUIVALENCE.value: -1,
    }
    assert diff.unknown_by_reason_scope_delta == {
        UnknownReasonScope.EXPRESSION.value: 1,
        UnknownReasonScope.QUERY.value: -1,
        UnknownReasonScope.STAGE.value: -1,
    }
    assert diff.proof_backlog_by_reason_delta == {
        UnknownReasonId.METHOD_B_CLOSURE_BLOCKED.value: -1,
        UnknownReasonId.READONLY_IDENTITY_MISSING.value: 1,
        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value: -1,
    }
    assert diff.operational_unknown_by_reason_delta == {}


def test_validation_summary_uses_final_unknown_contributor_from_debug_trace():
    payload = _payload(
        "loop_method_b_test:lmb_sum_prefix_peeled3_tail",
        reasons=[
            make_unknown_reason(
                UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING,
                pair_or_case="root",
            )
        ],
        debug_trace={
            "final_result": None,
            "attempts": [
                {
                    "result": None,
                    "transition_reason": "UNKNOWN",
                    "unknown_reasons": [
                        make_unknown_reason(
                            UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING,
                            pair_or_case="B1-B2",
                        ).to_dict()
                    ],
                },
                {
                    "result": None,
                    "transition_reason": "UNKNOWN",
                    "unknown_reasons": [
                        make_unknown_reason(
                            UnknownReasonId.METHOD_B_CLOSURE_BLOCKED,
                            pair_or_case="B1-B2",
                        ).to_dict()
                    ],
                },
            ],
        },
    )

    summary = summarize_validation_unknowns([payload], target_cases=("loop_method_b_test",))

    assert summary.unknown_by_reason == {
        UnknownReasonId.METHOD_B_CLOSURE_BLOCKED.value: 1,
    }
    assert summary.proof_backlog_by_proof_kind == {
        "proof_backed_covering_case": 1,
        "guard_partition_completion": 1,
    }
    assert summary.proof_backlog_by_action_status == {
        UnknownRecoveryActionStatus.PLANNED.value: 2,
    }


def test_validation_unknown_summary_formatters_include_plan16_sections():
    before = [
        _payload(
            "fc_read_after_void",
            reasons=[make_unknown_reason(UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING)],
        )
    ]
    after = [
        _payload(
            "fc_read_after_void",
            reasons=[make_unknown_reason(UnknownReasonId.RECOVERABLE_PARTIAL)],
        )
    ]

    summary_text = format_validation_unknown_summary(summarize_validation_unknowns(after))
    diff_text = format_validation_unknown_diff(compare_validation_unknowns(before, after))

    assert "UNKNOWN by reason:" in summary_text
    assert "UNKNOWN by decision_effect:" in summary_text
    assert "UNKNOWN by reason_scope:" in summary_text
    assert "Proof backlog by reason:" in summary_text
    assert "Proof backlog by recovery_action:" in summary_text
    assert "Proof backlog by action_status:" in summary_text
    assert "Operational UNKNOWN by reason:" in summary_text
    assert "UNKNOWN by reason delta:" in diff_text
    assert "UNKNOWN by decision_effect delta:" in diff_text
    assert "UNKNOWN by reason_scope delta:" in diff_text
    assert "Proof backlog by proof_kind delta:" in diff_text
    assert "Proof backlog by recovery_action delta:" in diff_text
    assert "Proof backlog by action_status delta:" in diff_text
    assert "Operational UNKNOWN by class delta:" in diff_text


def test_validation_unknown_summary_makes_return_coverage_gap_actionable():
    summary = summarize_validation_unknowns(
        [
            _payload(
                "loop_method_b_test:lmb_sum_prefix_peeled3_tail",
                reasons=[make_unknown_reason(UnknownReasonId.RETURN_COVERAGE_GAP)],
            ),
            _payload(
                "loop_method_b_test:lmb_solver_rewrite",
                reasons=[make_unknown_reason(UnknownReasonId.SOLVER_PROVEN_REWRITE_PROOF_FAILED)],
            ),
        ]
    )

    assert summary.proof_backlog_by_reason == {
        UnknownReasonId.RETURN_COVERAGE_GAP.value: 1,
        UnknownReasonId.SOLVER_PROVEN_REWRITE_PROOF_FAILED.value: 1,
    }
    assert summary.proof_backlog_by_proof_kind == {
        UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION.value: 2,
        UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION.value: 2,
    }
    assert summary.proof_backlog_by_action_status == {
        UnknownRecoveryActionStatus.PLANNED.value: 4,
    }
    assert (
        "return_coverage_gap | return_coverage_completion | return_partition_extraction | planned"
        in summary.proof_backlog_by_recovery_action
    )
    assert (
        "solver_proven_rewrite_proof_failed | solver_retry_or_normalization | "
        "rewrite_proof_recheck | planned"
        in summary.proof_backlog_by_recovery_action
    )


def test_validation_summary_extracts_typed_result_json_from_log_text():
    payload = _payload(
        "fc_read_after_void",
        reasons=[make_unknown_reason(UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING)],
    )
    log_text = "\n".join(
        [
            "human diagnostic before",
            RESULT_JSON_BEGIN,
            __import__("json").dumps(payload),
            RESULT_JSON_END,
            "human diagnostic after",
        ]
    )

    payloads = extract_result_payloads_from_text(log_text)
    summary = summarize_validation_unknowns(payloads, target_cases=("fc_read_after_void",))

    assert len(payloads) == 1
    assert summary.unknown_by_reason == {
        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value: 1,
    }


def test_validation_summary_module_execution_has_no_runtime_warning():
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "scripts.function_tracer_pcode.validation.unknown_reason_summary",
            "--summary",
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    assert "RuntimeWarning" not in result.stderr
    assert "UNKNOWN validation summary:" in result.stdout
