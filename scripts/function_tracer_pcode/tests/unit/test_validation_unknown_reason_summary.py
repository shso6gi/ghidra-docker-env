# -*- coding: utf-8 -*-

import subprocess
import sys

from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UNKNOWN_TUPLE_MISSING,
    UnknownCountKind,
    UnknownDecisionEffect,
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofObligation,
    UnknownRecoveryProofKind,
    UnknownReasonClass,
    UnknownReasonId,
    UnknownReasonScope,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
    UnknownValidationSummary,
    compare_validation_unknowns,
    diagnose_unknown_reason_correspondence,
    extract_result_payloads_from_text,
    format_validation_unknown_diff,
    format_validation_unknown_summary,
    summarize_validation_unknowns,
)


def _payload(function_name, *, is_equivalent=None, reasons=(), debug_trace=None, **extra):
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
    payload.update(extra)
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
    assert summary.final_result_counts == {
        "UNKNOWN": 2,
        "EQUIVALENT": 1,
    }
    assert summary.reason_record_multiset[
        (
            UnknownCountKind.REASON_RECORD.value,
            UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value,
            UnknownDecisionEffect.BLOCKS_EQUIVALENCE.value,
            UnknownReasonScope.QUERY.value,
            UnknownRecoveryProofKind.ABI_RELATION_HIGH_BIT_PROOF.value,
            UNKNOWN_TUPLE_MISSING,
            UNKNOWN_TUPLE_MISSING,
        )
    ] == 1


def test_validation_unknown_summary_treats_planned_action_as_proof_backlog():
    summary = summarize_validation_unknowns(
        [
            _payload(
                "fc_is_even",
                reasons=[
                    make_unknown_reason(
                        UnknownReasonId.UNRESOLVED_VALUE_EXPRESSION,
                        pair_or_case="(5,1)",
                        action_status=UnknownRecoveryActionStatus.PLANNED,
                        object_target_key=("unresolved_expression", ("pair", "(5,1)")),
                        recovery_proof_obligations=(
                            UnknownRecoveryProofObligation(
                                proof_kind=UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                                proof_stage="phi_circular_guard_condition_lowering",
                            ),
                            UnknownRecoveryProofObligation(
                                proof_kind=UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                                proof_stage="recursive_summary_guard_equivalence",
                            ),
                        ),
                    )
                ],
            )
        ]
    )

    assert summary.proof_backlog_by_reason == {
        UnknownReasonId.UNRESOLVED_VALUE_EXPRESSION.value: 1,
    }
    assert summary.proof_backlog_by_action_status == {
        UnknownRecoveryActionStatus.PLANNED.value: 2,
    }
    assert summary.operational_unknown_by_reason == {}


def test_validation_unknown_summary_treats_object_target_planned_actions_as_backlog():
    summary = summarize_validation_unknowns(
        [
            _payload(
                "fc_is_even",
                reasons=[
                    make_unknown_reason(
                        UnknownReasonId.UNRESOLVED_VALUE_EXPRESSION,
                        pair_or_case="(5,1)",
                        object_target_key=("unresolved_expression", ("pair", "(5,1)")),
                        recovery_proof_obligations=(
                            UnknownRecoveryProofObligation(
                                proof_kind=UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                                proof_stage="phi_circular_guard_condition_lowering",
                            ),
                        ),
                    ),
                    make_unknown_reason(
                        UnknownReasonId.RECOVERABLE_PARTIAL,
                        pair_or_case="operational",
                    ),
                ],
            )
        ]
    )

    assert summary.proof_backlog_by_reason == {
        UnknownReasonId.UNRESOLVED_VALUE_EXPRESSION.value: 1,
    }
    assert summary.operational_unknown_by_reason == {
        UnknownReasonId.RECOVERABLE_PARTIAL.value: 1,
    }


def test_validation_summary_normalizes_bool_debug_trace_final_result_counts():
    summary = summarize_validation_unknowns(
        [
            _payload("eq", debug_trace={"final_result": True}),
            _payload("not_eq", debug_trace={"final_result": False}),
            _payload("unknown", debug_trace={"final_result": None}),
        ],
    )

    assert summary.final_result_counts == {
        "EQUIVALENT": 1,
        "NOT_EQ": 1,
        "UNKNOWN": 1,
    }


def test_validation_summary_keeps_timeout_final_result_separate_from_unknown():
    summary = summarize_validation_unknowns(
        [
            _payload(
                "timeout_flag",
                is_timeout=True,
                reasons=[make_unknown_reason(UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT)],
            ),
            _payload(
                "timeout_solver",
                solver_results={"all_results": [{"status": "TIMEOUT"}]},
                reasons=[make_unknown_reason(UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT)],
            ),
            _payload(
                "unknown",
                reasons=[make_unknown_reason(UnknownReasonId.UNRESOLVED_EXPRESSION)],
            ),
        ],
    )

    assert summary.unknown_results == 3
    assert summary.final_result_counts == {
        "TIMEOUT": 2,
        "UNKNOWN": 1,
    }
    assert summary.unknown_by_reason == {
        UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT.value: 2,
        UnknownReasonId.UNRESOLVED_EXPRESSION.value: 1,
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


def test_validation_summary_separates_reason_units_from_proof_actions_by_count_kind():
    record = make_unknown_reason(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY,
        recovery_proof_kind=UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
        recovery_proof_obligations=(
            UnknownRecoveryProofObligation.create(
                UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
                "object_evidence_collected",
                required_evidence=(
                    "call_effect_summary",
                    "runtime_ref",
                    "callsite_storage",
                ),
            ),
        ),
        evidence_kind="runtime_ref",
        object_target_key=("deferred_call_site", 7),
        recovery_action="call_effect_summary_proof_required",
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
    )

    summary = summarize_validation_unknowns(
        [
            _payload("fc_apply_indirect", reasons=[record]),
            _payload("fc_no_call", is_equivalent=True),
        ],
    )

    assert summary.final_result_counts == {
        "UNKNOWN": 1,
        "EQUIVALENT": 1,
    }
    assert summary.validation_unknown_unit_multiset == {
        (
            UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value,
            UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
            UnknownDecisionEffect.BLOCKS_EQUIVALENCE.value,
            UnknownReasonScope.FUNCTION.value,
            UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value,
            "object_evidence_collected",
            UnknownRecoveryActionStatus.PENDING_PROOF.value,
        ): 1,
    }
    assert summary.reason_record_multiset == {
        (
            UnknownCountKind.REASON_RECORD.value,
            UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
            UnknownDecisionEffect.BLOCKS_EQUIVALENCE.value,
            UnknownReasonScope.FUNCTION.value,
            UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value,
            "object_evidence_collected",
            UnknownRecoveryActionStatus.PENDING_PROOF.value,
        ): 1,
    }
    assert summary.proof_action_multiset == {
        (
            UnknownCountKind.PROOF_ACTION.value,
            UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
            UnknownDecisionEffect.BLOCKS_EQUIVALENCE.value,
            UnknownReasonScope.FUNCTION.value,
            UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value,
            "object_evidence_collected",
            UnknownRecoveryActionStatus.PENDING_PROOF.value,
        ): 1,
    }


def test_validation_summary_classifies_reason_record_aggregation_difference():
    summary = summarize_validation_unknowns(
        [
            _payload(
                "fc_apply_indirect",
                reasons=[
                    make_unknown_reason(
                        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY,
                        pair_or_case="B10-B11",
                        aggregation_unit="pair",
                    ),
                    make_unknown_reason(
                        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING,
                        pair_or_case="B10-B11",
                        aggregation_unit="pair",
                    ),
                ],
            ),
        ]
    )

    diagnostics = diagnose_unknown_reason_correspondence(summary)

    assert any(
        diagnostic.classification == "aggregation_difference"
        and diagnostic.reason_records == 1
        and diagnostic.validation_unknown_units == 0
        and UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value in diagnostic.tuple_key
        for diagnostic in diagnostics
    )


def test_validation_summary_selects_primary_function_reason_without_order_dependency():
    gap = make_unknown_reason(
        UnknownReasonId.RETURN_COVERAGE_GAP,
        aggregation_unit="function",
        stage="S_PAIRWISE",
        detail="function1:return_coverage_gap",
        evidence_refs=("function1:return_coverage_gap",),
    )
    inconclusive = make_unknown_reason(
        UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
        aggregation_unit="function",
        stage="S_PAIRWISE",
        detail="function2:return_coverage_inconclusive",
        evidence_refs=("function2:return_coverage_inconclusive",),
    )

    forward = summarize_validation_unknowns(
        [_payload("fc_is_odd", reasons=[gap, inconclusive])]
    )
    reversed_order = summarize_validation_unknowns(
        [_payload("fc_is_odd", reasons=[inconclusive, gap])]
    )

    expected_unit_tuple = (
        UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value,
        UnknownReasonId.RETURN_COVERAGE_GAP.value,
        UnknownDecisionEffect.BLOCKS_EQUIVALENCE.value,
        UnknownReasonScope.FUNCTION.value,
        UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION.value,
        UNKNOWN_TUPLE_MISSING,
        UNKNOWN_TUPLE_MISSING,
    )
    assert forward.validation_unknown_unit_multiset == {expected_unit_tuple: 1}
    assert reversed_order.validation_unknown_unit_multiset == {expected_unit_tuple: 1}
    assert forward.reason_record_multiset == reversed_order.reason_record_multiset


def test_validation_summary_classifies_proof_action_expansion():
    summary = summarize_validation_unknowns(
        [
            _payload(
                "fc_apply_indirect",
                reasons=[
                    make_unknown_reason(
                        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING,
                        pair_or_case="B10-B11",
                    )
                ],
            ),
        ]
    )

    diagnostics = diagnose_unknown_reason_correspondence(summary)
    proof_action_diagnostics = [
        diagnostic
        for diagnostic in diagnostics
        if diagnostic.classification == "proof_action_expansion"
    ]

    assert len(proof_action_diagnostics) == 2
    assert {diagnostic.proof_actions for diagnostic in proof_action_diagnostics} == {1}
    assert {
        diagnostic.tuple_key[4] for diagnostic in proof_action_diagnostics
    } == {"abi_relation_proof", "high_bit_proof"}


def test_validation_summary_classifies_missing_detail_and_parser_bug_correspondence():
    unit_tuple = (
        UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value,
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
        UnknownDecisionEffect.BLOCKS_EQUIVALENCE.value,
        UnknownReasonScope.FUNCTION.value,
        UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value,
        "object_evidence_collected",
        UnknownRecoveryActionStatus.PENDING_PROOF.value,
    )
    reason_tuple = (
        UnknownCountKind.REASON_RECORD.value,
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
        UnknownDecisionEffect.BLOCKS_EQUIVALENCE.value,
        UnknownReasonScope.FUNCTION.value,
        UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value,
        "object_evidence_collected",
        UnknownRecoveryActionStatus.PENDING_PROOF.value,
    )

    detail_missing = diagnose_unknown_reason_correspondence(
        UnknownValidationSummary(
            total_results=1,
            unknown_results=1,
            unknown_units=1,
            validation_unknown_unit_multiset={unit_tuple: 1},
            reason_record_multiset={},
        )
    )
    parser_bug = diagnose_unknown_reason_correspondence(
        UnknownValidationSummary(
            total_results=1,
            unknown_results=1,
            unknown_units=2,
            validation_unknown_unit_multiset={unit_tuple: 2},
            reason_record_multiset={reason_tuple: 1},
        )
    )
    raw_missing = diagnose_unknown_reason_correspondence(
        UnknownValidationSummary(
            total_results=1,
            unknown_results=1,
            unknown_units=0,
            validation_unknown_unit_multiset={},
            reason_record_multiset={},
        )
    )

    assert {diagnostic.classification for diagnostic in detail_missing} == {"detail_missing"}
    assert {diagnostic.classification for diagnostic in parser_bug} == {"parser_bug"}
    assert {diagnostic.classification for diagnostic in raw_missing} == {"raw_log_missing"}


def test_validation_unknown_summary_formats_correspondence_diagnostics():
    summary = summarize_validation_unknowns(
        [
            _payload(
                "fc_apply_indirect",
                reasons=[
                    make_unknown_reason(
                        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING,
                        pair_or_case="B10-B11",
                    )
                ],
            ),
        ]
    )

    text = format_validation_unknown_summary(summary)

    assert "Validation UNKNOWN unit / reason record correspondence:" in text
    assert "proof_action_expansion" in text


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
