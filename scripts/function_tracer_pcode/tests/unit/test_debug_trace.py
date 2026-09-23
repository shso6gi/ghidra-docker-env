# -*- coding: utf-8 -*-
"""デバッグトレース機能のテスト"""

import pytest
import json
from types import SimpleNamespace
from scripts.function_tracer_pcode.checker.debug_trace import (
    DebugTrace,
    Attempt,
    AttemptIdentity,
    CompletionApplicabilityStatus,
    ReasonCompletionEvent,
    TransitionReason,
    PairwiseDecisiveInfo,
    NormalizationRuleApplication,
)
from scripts.function_tracer_pcode.checker.attempts import _record_explicit_proof_completions
from scripts.function_tracer_pcode.checker.unknown_reason import make_unknown_reason
from scripts.function_tracer_pcode.core.evidence_authority import mark_function_unary
from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import (
    bound_to,
    comparison_frame,
    fixed_test_comparison,
)


def test_normalization_rule_application():
    """正規化ルール適用の記録"""
    rule = NormalizationRuleApplication(
        rule_name="double_negation",
        reason="Removed double negation",
        applied_to="value1",
        before="(NOT (NOT x))",
        after="x"
    )
    
    assert rule.rule_name == "double_negation"
    assert rule.reason == "Removed double negation"
    
    rule_dict = rule.to_dict()
    assert rule_dict["rule_name"] == "double_negation"
    assert rule_dict["before"] == "(NOT (NOT x))"
    assert rule_dict["after"] == "x"


def test_reason_completion_validates_exact_occurrence_and_premise():
    requirement = {
        "schema_version": 1,
        "proof_kind": "unary_return_width_relation",
        "proof_target_key": ("return-member", 1),
        "proof_contract_key": (1, "return width"),
    }
    trace = DebugTrace()
    trace.add_attempt(Attempt(
        attempt_id=0,
        retry_count=0,
        phase="P0_BASE",
        stage_path=["S_PAIRWISE"],
        strategy="pairwise",
        result=None,
        transition_reason=TransitionReason.UNKNOWN.value,
        unknown_reasons=[make_unknown_reason(
            "return_width_bridge_missing",
            object_target_key=("return-member", 1),
            proof_requirement_ids=(requirement,),
        )],
    ))
    occurrence = trace.attempts[0].reason_occurrences[0].occurrence_id
    proposed = ReasonCompletionEvent(
        completion_event_id=("width-completion", 1),
        completed_occurrence_id=occurrence,
        exact_target_id=("return-member", 1),
        exact_missing_fact_or_proof_slot="unary_return_width_relation",
        source_snapshot_fingerprint="snapshot-sha",
        semantic_seed_or_premise_digest="premise-sha",
        evidence_or_artifact_digest="artifact-sha",
        recognizing_stage="return_width_canonicalization",
        completed_at_attempt=AttemptIdentity("pairwise", 1),
        applicability_status="unvalidated",
    )

    completed = trace.add_reason_completion(
        proposed,
        current_snapshot_fingerprint="snapshot-sha",
        current_semantic_seed_or_premise_digest="premise-sha",
        artifact_is_valid=True,
    )
    duplicate = trace.add_reason_completion(
        proposed,
        current_snapshot_fingerprint="snapshot-sha",
        current_semantic_seed_or_premise_digest="premise-sha",
        artifact_is_valid=True,
    )

    assert completed.applicability_status == CompletionApplicabilityStatus.APPLICABLE.value
    assert duplicate.applicability_status == (
        CompletionApplicabilityStatus.OCCURRENCE_ALREADY_COMPLETED.value
    )


def test_pairwise_decisive_info():
    """Pairwise decisive情報の記録"""
    decisive = PairwiseDecisiveInfo(
        decisive_result="SAT",
        total_pairs=10,
        unsat_pairs=8,
        sat_pairs=1,
        unknown_pairs=1,
        decisive_pair=(2, 3),
        pair_stage="with-ineq",
        case1_summary="x > 0",
        case2_summary="y > 0",
        value1_expr="x + 1",
        value2_expr="y + 1",
        final_query_excerpt="(assert (not (= (bvadd x 1) (bvadd y 1))))"
    )
    
    assert decisive.decisive_result == "SAT"
    assert decisive.total_pairs == 10
    assert decisive.decisive_pair == (2, 3)
    assert decisive.pair_stage == "with-ineq"
    
    decisive_dict = decisive.to_dict()
    assert decisive_dict["decisive_result"] == "SAT"
    assert decisive_dict["decisive_pair"]["i"] == 2
    assert decisive_dict["decisive_pair"]["j"] == 3
    assert decisive_dict["case1_summary"] == "x > 0"


def test_attempt():
    """Attempt記録"""
    attempt = Attempt(
        attempt_id=0,
        retry_count=0,
        phase="P0_BASE",
        stage_path=["S_PAIRWISE"],
        strategy="pairwise",
        result=None,
        transition_reason=TransitionReason.UNKNOWN.value,
        elapsed_time=1.5
    )
    
    assert attempt.attempt_id == 0
    assert attempt.retry_count == 0
    assert attempt.phase == "P0_BASE"
    assert attempt.stage_path == ["S_PAIRWISE"]
    assert attempt.transition_reason == "UNKNOWN"
    
    attempt_dict = attempt.to_dict()
    assert attempt_dict["attempt_id"] == 0
    assert attempt_dict["phase"] == "P0_BASE"
    assert attempt_dict["transition_reason"] == "UNKNOWN"
    assert attempt_dict["elapsed_time"] == 1.5


def test_later_independent_unknown_does_not_supersede_prior_blockers():
    trace = DebugTrace()
    first = Attempt(
        attempt_id=0,
        retry_count=0,
        phase="P0_BASE",
        stage_path=["S_PAIRWISE"],
        strategy="pairwise",
        result=None,
        transition_reason=TransitionReason.UNKNOWN.value,
        unknown_reasons=[
            make_unknown_reason("return_coverage_gap"),
            make_unknown_reason("equivalence_blocking_unsafety"),
        ],
    )
    second = Attempt(
        attempt_id=1,
        retry_count=1,
        phase="P1_RETRY",
        stage_path=["S_MONOLITHIC"],
        strategy="monolithic",
        result=None,
        transition_reason=TransitionReason.UNKNOWN.value,
        unknown_reasons=[make_unknown_reason("solver_unknown_timeout")],
    )

    trace.add_attempt(first)
    trace.add_attempt(second)

    assert trace.causal_transitions == []


def test_explicit_matching_proof_completion_requires_runtime_applicability():
    requirement = {
        "schema_version": 1,
        "proof_kind": "return_coverage_completion",
        "proof_target_key": ("function", "f"),
        "proof_contract_key": (1, "all inputs classified"),
    }
    trace = DebugTrace()
    trace.add_attempt(
        Attempt(
            attempt_id=0,
            retry_count=0,
            phase="P0_BASE",
            stage_path=["S_PAIRWISE"],
            strategy="pairwise",
            result=None,
            transition_reason=TransitionReason.UNKNOWN.value,
            unknown_reasons=[
                make_unknown_reason(
                    "return_coverage_gap",
                    object_target_key=("function", "f"),
                    proof_requirement_ids=(requirement,),
                )
            ],
        )
    )
    trace.add_attempt(
        Attempt(
            attempt_id=1,
            retry_count=1,
            phase="P1_COVERAGE",
            stage_path=["S_PAIRWISE"],
            strategy="pairwise",
            result=True,
            transition_reason=TransitionReason.UNSAT.value,
        )
    )
    result = SimpleNamespace(
        completed_recovery_proof_evidence=[
            {
                "side": "function1",
                # unary artifact（関数単体の return partition）を指す完了証拠。
                "evidence": mark_function_unary({
                    "proof_requirement_id": requirement,
                    "proof_status": "verified",
                    "proof_artifact_ref": ("return_partition", "f", "v1"),
                    "source_snapshot_fingerprint": "snapshot-current",
                    "semantic_seed_or_premise_digest": "premise-current",
                    "evidence_or_artifact_digest": "artifact-current",
                    "recognizing_stage": "return_coverage",
                }),
            }
        ],
        reason_completion_applicability_contexts=[{
            "proof_requirement_id": requirement,
            "proof_artifact_ref": ("return_partition", "f", "v1"),
            "current_snapshot_fingerprint": "snapshot-current",
            "current_semantic_seed_or_premise_digest": "premise-current",
            "current_evidence_or_artifact_digest": "artifact-current",
            "artifact_is_valid": True,
        }],
    )

    _record_explicit_proof_completions(trace, result)

    assert len(trace.proof_completion_events) == 1
    assert trace.causal_transitions == []
    assert len(trace.reason_completion_events) == 1
    assert trace.reason_completion_events[0].applicability_status == "APPLICABLE"


def test_stale_runtime_completion_is_diagnostic_and_cannot_use_legacy_transition():
    requirement = {
        "schema_version": 1,
        "proof_kind": "return_coverage_completion",
        "proof_target_key": ("function", "f"),
        "proof_contract_key": (1, "all inputs classified"),
    }
    trace = DebugTrace()
    trace.add_attempt(Attempt(
        attempt_id=0,
        retry_count=0,
        phase="P0_BASE",
        stage_path=["S_PAIRWISE"],
        strategy="pairwise",
        result=None,
        transition_reason=TransitionReason.UNKNOWN.value,
        unknown_reasons=[make_unknown_reason(
            "return_coverage_gap",
            object_target_key=("function", "f"),
            proof_requirement_ids=(requirement,),
        )],
    ))
    trace.add_attempt(Attempt(
        attempt_id=1,
        retry_count=1,
        phase="P1_COVERAGE",
        stage_path=["S_PAIRWISE"],
        strategy="pairwise",
        result=True,
        transition_reason=TransitionReason.UNSAT.value,
    ))
    result = SimpleNamespace(
        completed_recovery_proof_evidence=[{"evidence": mark_function_unary({
            "proof_requirement_id": requirement,
            "proof_status": "verified",
            "proof_artifact_ref": ("return_partition", "f", "v1"),
            "source_snapshot_fingerprint": "snapshot-old",
            "semantic_seed_or_premise_digest": "premise-current",
            "evidence_or_artifact_digest": "artifact-current",
            "recognizing_stage": "return_coverage",
        })}],
        reason_completion_applicability_contexts=[{
            "proof_requirement_id": requirement,
            "proof_artifact_ref": ("return_partition", "f", "v1"),
            "current_snapshot_fingerprint": "snapshot-current",
            "current_semantic_seed_or_premise_digest": "premise-current",
            "current_evidence_or_artifact_digest": "artifact-current",
            "artifact_is_valid": True,
        }],
    )

    _record_explicit_proof_completions(trace, result)

    assert trace.causal_transitions == []
    assert trace.reason_completion_events[0].applicability_status == "STALE_SNAPSHOT"


def test_proof_evidence_without_exact_requirement_does_not_discharge():
    trace = DebugTrace()
    trace.add_attempt(
        Attempt(
            attempt_id=0,
            retry_count=0,
            phase="P0_BASE",
            stage_path=[],
            strategy="pairwise",
            result=None,
            transition_reason=TransitionReason.UNKNOWN.value,
            unknown_reasons=[make_unknown_reason("return_coverage_gap")],
        )
    )
    result = SimpleNamespace(
        completed_recovery_proof_evidence=[
            {"evidence": {"proof_status": "verified", "proof_artifact_ref": ("x",)}}
        ]
    )

    _record_explicit_proof_completions(trace, result)

    assert trace.proof_completion_events == []
    assert trace.causal_transitions == []


def test_production_proof_obligation_links_unique_typed_requirement():
    requirement = {
        "schema_version": 1,
        "proof_kind": "return_coverage_completion",
        "proof_target_key": ("function", "f"),
        "proof_contract_key": (1, "all inputs classified"),
    }
    legacy_obligation = (
        "proof_obligation",
        "return_coverage_gap",
        "return_guard_coverage",
        ("return_partition", "f"),
    )
    trace = DebugTrace()
    trace.add_attempt(
        Attempt(
            attempt_id=0,
            retry_count=0,
            phase="P0_BASE",
            stage_path=[],
            strategy="pairwise",
            result=None,
            transition_reason=TransitionReason.UNKNOWN.value,
            unknown_reasons=[
                make_unknown_reason(
                    "return_coverage_gap",
                    proof_obligation_id=legacy_obligation,
                    proof_requirement_ids=(requirement,),
                )
            ],
        )
    )
    trace.add_attempt(
        Attempt(
            attempt_id=1,
            retry_count=1,
            phase="P1_COVERAGE",
            stage_path=[],
            strategy="pairwise",
            result=True,
            transition_reason=TransitionReason.UNSAT.value,
        )
    )
    # attempt 1 の比較で作った証拠（その比較の frame が結果に付く）。
    comparison = fixed_test_comparison()
    result = SimpleNamespace(
        _prepared_dispatch_frame=comparison_frame(comparison),
        completed_recovery_proof_evidence=[
            {
                "side": "function1",
                "evidence": bound_to(comparison, {
                    "proof_obligation_id": legacy_obligation,
                    "status": "complete",
                }),
            }
        ],
    )

    _record_explicit_proof_completions(trace, result)

    assert len(trace.proof_completion_events) == 1
    assert trace.proof_completion_events[0].proof_requirement_id == requirement
    assert trace.proof_completion_events[0].proof_status == "proven"
    assert trace.causal_transitions == []
    assert trace.reason_completion_events == []


def test_ambiguous_legacy_obligation_does_not_guess_typed_requirement():
    legacy_obligation = ("proof_obligation", "shared")
    trace = DebugTrace()
    reasons = []
    for suffix in ("left", "right"):
        reasons.append(
            make_unknown_reason(
                "return_coverage_gap",
                proof_obligation_id=legacy_obligation,
                proof_requirement_ids=(
                    {
                        "schema_version": 1,
                        "proof_kind": "return_coverage_completion",
                        "proof_target_key": ("function", suffix),
                        "proof_contract_key": (1, "all inputs classified"),
                    },
                ),
            )
        )
    trace.add_attempt(
        Attempt(
            attempt_id=0,
            retry_count=0,
            phase="P0_BASE",
            stage_path=[],
            strategy="pairwise",
            result=None,
            transition_reason=TransitionReason.UNKNOWN.value,
            unknown_reasons=reasons,
        )
    )
    trace.add_attempt(
        Attempt(
            attempt_id=1,
            retry_count=1,
            phase="P1_COVERAGE",
            stage_path=[],
            strategy="pairwise",
            result=True,
            transition_reason=TransitionReason.UNSAT.value,
        )
    )
    result = SimpleNamespace(
        completed_recovery_proof_evidence=[
            {
                "evidence": {
                    "proof_obligation_id": legacy_obligation,
                    "status": "complete",
                }
            }
        ]
    )

    _record_explicit_proof_completions(trace, result)

    assert trace.proof_completion_events == []
    assert trace.causal_transitions == []


def test_debug_trace():
    """DebugTrace全体の記録"""
    trace = DebugTrace(
        planned_phases=["P0_BASE", "P1_SIGNEDNESS", "P2_PATTERN_INT"],
        known_phases=[
            "P0_BASE",
            "P1_SIGNEDNESS",
            "P2_PATTERN_INT",
            "P4A_MIPS64_ABI",
            "P4B_MIPS64_SPURIOUS",
            "P4C_RETURN_TYPE_FIX",
        ],
    )
    
    # Attempt 1: P0 UNKNOWN
    attempt1 = Attempt(
        attempt_id=0,
        retry_count=0,
        phase="P0_BASE",
        stage_path=["S_PAIRWISE", "S_MONOLITHIC_FALLBACK"],
        strategy="pairwise",
        result=None,
        transition_reason=TransitionReason.UNKNOWN.value,
        elapsed_time=2.0
    )
    trace.add_attempt(attempt1)
    
    # Attempt 2: P1 UNSAT
    attempt2 = Attempt(
        attempt_id=1,
        retry_count=1,
        phase="P1_SIGNEDNESS",
        stage_path=["S_PAIRWISE"],
        strategy="pairwise",
        result=True,
        transition_reason=TransitionReason.UNSAT.value,
        elapsed_time=1.0
    )
    trace.add_attempt(attempt2)
    
    trace.final_result = True
    trace.total_time = 3.0
    
    # to_dict 検証
    trace_dict = trace.to_dict()
    assert trace_dict["attempt_count"] == 2
    assert trace_dict["final_result"] is True
    assert trace_dict["total_time"] == 3.0
    assert len(trace_dict["attempts"]) == 2
    
    assert trace_dict["attempts"][0]["phase"] == "P0_BASE"
    assert trace_dict["attempts"][0]["result"] is None
    assert trace_dict["attempts"][0]["transition_reason"] == "UNKNOWN"
    
    assert trace_dict["attempts"][1]["phase"] == "P1_SIGNEDNESS"
    assert trace_dict["attempts"][1]["result"] is True
    assert trace_dict["attempts"][1]["transition_reason"] == "UNSAT"
    
    # JSON シリアライズ可能性確認
    json_str = json.dumps(trace_dict)
    assert isinstance(json_str, str)
    
    parsed = json.loads(json_str)
    assert parsed["attempt_count"] == 2
    assert parsed["final_result"] is True
    assert parsed["used_phases"] == ["P0_BASE", "P1_SIGNEDNESS"]


def test_debug_trace_phase_usage_summary():
    """Phase利用状況の集約が取れることを確認"""
    trace = DebugTrace(
        planned_phases=["P0_BASE", "P1_SIGNEDNESS", "P2_PATTERN_INT"],
        known_phases=[
            "P0_BASE",
            "P1_SIGNEDNESS",
            "P2_PATTERN_INT",
            "P4A_MIPS64_ABI",
            "P4B_MIPS64_SPURIOUS",
            "P4C_RETURN_TYPE_FIX",
        ],
    )

    trace.add_attempt(
        Attempt(
            attempt_id=0,
            retry_count=0,
            phase="P0_BASE",
            stage_path=["S_PAIRWISE"],
            strategy="pairwise",
            result=None,
            transition_reason=TransitionReason.UNKNOWN.value,
            elapsed_time=0.3,
        )
    )
    trace.add_attempt(
        Attempt(
            attempt_id=1,
            retry_count=1,
            phase="P1_SIGNEDNESS",
            stage_path=[],
            strategy="pairwise",
            result=None,
            transition_reason=TransitionReason.NO_CHANGES.value,
            elapsed_time=0.0,
        )
    )

    usage = {entry["phase"]: entry for entry in trace.get_phase_usage()}

    assert usage["P0_BASE"]["planned"] is True
    assert usage["P0_BASE"]["reached"] is True
    assert usage["P0_BASE"]["used"] is True
    assert usage["P0_BASE"]["result_attempt_count"] == 1

    assert usage["P1_SIGNEDNESS"]["reached"] is True
    assert usage["P1_SIGNEDNESS"]["used"] is False
    assert usage["P1_SIGNEDNESS"]["no_change_skip_count"] == 1
    assert usage["P1_SIGNEDNESS"]["last_transition_reason"] == "no_changes"
    assert usage["P0_BASE"]["transition_counts"]["UNKNOWN"] == 1
    assert usage["P1_SIGNEDNESS"]["transition_counts"]["no_changes"] == 1

    assert usage["P2_PATTERN_INT"]["reached"] is False
    assert usage["P4B_MIPS64_SPURIOUS"]["planned"] is False
    assert usage["P4B_MIPS64_SPURIOUS"]["reached"] is False

    assert trace.get_used_phases() == ["P0_BASE"]

    summary = trace.format_phase_usage_summary()
    assert "P0_BASE: USED" in summary
    assert "P1_SIGNEDNESS: NO_CHANGES" in summary
    assert "P2_PATTERN_INT: NOT_REACHED" in summary


def test_debug_trace_phase_usage_tracks_sat_phase4b():
    """SAT->Phase4B 遷移が phase usage に集約されることを確認"""
    trace = DebugTrace(
        planned_phases=["P0_BASE"],
        known_phases=["P0_BASE", "P4A_MIPS64_ABI"],
    )

    trace.add_attempt(
        Attempt(
            attempt_id=0,
            retry_count=0,
            phase="P4A_MIPS64_ABI",
            stage_path=["S_PAIRWISE"],
            strategy="pairwise",
            result=False,
            transition_reason=TransitionReason.SAT_PHASE4B.value,
            elapsed_time=0.2,
        )
    )

    usage = {entry["phase"]: entry for entry in trace.get_phase_usage()}
    assert usage["P4A_MIPS64_ABI"]["transition_counts"]["SAT->Phase4B"] == 1

    summary = trace.format_phase_usage_summary()
    assert "sat_phase4b=1" in summary


def test_debug_trace_with_pairwise_decisive():
    """Pairwise decisive情報を含むDebugTrace"""
    trace = DebugTrace()
    
    decisive = PairwiseDecisiveInfo(
        decisive_result="SAT",
        total_pairs=4,
        unsat_pairs=3,
        sat_pairs=1,
        unknown_pairs=0,
        decisive_pair=(1, 2),
        pair_stage="norm-ineq",
        case1_summary="x > 0 AND x < 10",
        case2_summary="unconditional",
        value1_expr="(bvadd x (_ bv1 32))",
        value2_expr="(bvadd y (_ bv2 32))",
        final_query_excerpt="(assert (not (= ...)))"
    )
    
    attempt = Attempt(
        attempt_id=0,
        retry_count=0,
        phase="P0_BASE",
        stage_path=["S_PAIRWISE"],
        strategy="pairwise",
        result=False,
        transition_reason=TransitionReason.SAT.value,
        pairwise_decisive=decisive,
        elapsed_time=1.5
    )
    
    trace.add_attempt(attempt)
    trace.final_result = False
    trace.total_time = 1.5
    
    trace_dict = trace.to_dict()
    assert trace_dict["attempts"][0]["pairwise_decisive"]["decisive_result"] == "SAT"
    assert trace_dict["attempts"][0]["pairwise_decisive"]["decisive_pair"]["i"] == 1
    assert trace_dict["attempts"][0]["pairwise_decisive"]["decisive_pair"]["j"] == 2
    assert trace_dict["attempts"][0]["pairwise_decisive"]["pair_stage"] == "norm-ineq"


def test_debug_trace_with_normalization_rules():
    """正規化ルール適用履歴を含むDebugTrace"""
    trace = DebugTrace()
    
    rules = [
        NormalizationRuleApplication(
            rule_name="double_negation",
            reason="Removed double negation",
            applied_to="pair_(1,2)"
        ),
        NormalizationRuleApplication(
            rule_name="division_sign_normalize",
            reason="Normalized division signs",
            applied_to="pair_(1,2)"
        )
    ]
    
    attempt = Attempt(
        attempt_id=0,
        retry_count=0,
        phase="P0_BASE",
        stage_path=["S_PAIRWISE"],
        strategy="pairwise",
        result=True,
        transition_reason=TransitionReason.UNSAT.value,
        normalization_rules=rules,
        elapsed_time=1.0
    )
    
    trace.add_attempt(attempt)
    trace.final_result = True
    trace.total_time = 1.0
    
    trace_dict = trace.to_dict()
    norm_rules = trace_dict["attempts"][0]["normalization_rules"]
    assert len(norm_rules) == 2
    assert norm_rules[0]["rule_name"] == "double_negation"
    assert norm_rules[1]["rule_name"] == "division_sign_normalize"


def test_debug_trace_with_mips64_abi_constraints():
    """MIPS64 ABI制約を含むDebugTrace"""
    trace = DebugTrace()
    
    abi_constraints = {
        "param_0_2": {"signedness": "signed", "narrow_bits": 32}
    }
    
    attempt = Attempt(
        attempt_id=1,
        retry_count=1,
        phase="P4B_MIPS64_SPURIOUS",
        stage_path=["S_PAIRWISE"],
        strategy="pairwise",
        result=True,
        transition_reason=TransitionReason.UNSAT.value,
        mips64_abi_constraints=abi_constraints,
        elapsed_time=0.5
    )
    
    trace.add_attempt(attempt)
    trace.final_result = True
    trace.total_time = 1.5
    
    trace_dict = trace.to_dict()
    mips64_abi = trace_dict["attempts"][0]["mips64_abi_constraints"]
    assert "param_0_2" in mips64_abi
    assert mips64_abi["param_0_2"]["signedness"] == "signed"
    assert mips64_abi["param_0_2"]["narrow_bits"] == 32
