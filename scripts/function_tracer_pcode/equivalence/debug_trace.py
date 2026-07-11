# -*- coding: utf-8 -*-
"""等価性判定のデバッグトレース（機械可読）"""

from typing import List, Dict, Any, Mapping, Optional, Tuple
from dataclasses import dataclass, field, asdict
from enum import Enum

from .unknown_reason import (
    UnknownReasonRecord,
    build_unknown_recovery_actions,
    coerce_unknown_reason_records,
    summarize_unknown_recovery_backlog,
    summarize_unknown_reason_counts,
)


class TransitionReason(Enum):
    """Phase/Stage遷移理由"""
    UNSAT = "UNSAT"  # 等価確定 → 終了
    SAT = "SAT"  # 非等価確定 → 終了
    SAT_PHASE4B = "SAT->Phase4B"  # SAT だが Phase 4-B 試行
    UNKNOWN = "UNKNOWN"  # 不明 → 次Phase
    TIMEOUT = "TIMEOUT"  # タイムアウト → 次Phase
    NO_CHANGES = "no_changes"  # Phase適用されず → スキップ
    CRITICAL_ERROR = "critical_error"  # 致命的エラー → 終了
    STAGE_FALLBACK = "stage_fallback"  # Pairwise UNKNOWN → Monolithic


class CausalStatus(str, Enum):
    ACTIVE_FINAL_BLOCKER = "active_final_blocker"
    CONTRIBUTING_BLOCKER = "contributing_blocker"
    DIAGNOSTIC_ONLY = "diagnostic_only"
    UNCLASSIFIED = "unclassified"


@dataclass(frozen=True)
class AttemptIdentity:
    strategy_identity: str
    attempt_ordinal: int
    trace_schema_version: int = 1

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class ReasonOccurrenceId:
    attempt_identity: AttemptIdentity
    reason_ordinal: int
    occurrence_schema_version: int = 1

    def to_dict(self) -> Dict[str, Any]:
        return {
            "occurrence_schema_version": self.occurrence_schema_version,
            "attempt_identity": self.attempt_identity.to_dict(),
            "reason_ordinal": self.reason_ordinal,
        }


@dataclass(frozen=True)
class ReasonOccurrence:
    occurrence_id: ReasonOccurrenceId
    reason_record: UnknownReasonRecord
    initial_causal_status: str = CausalStatus.UNCLASSIFIED.value

    def to_dict(self) -> Dict[str, Any]:
        return {
            "occurrence_id": self.occurrence_id.to_dict(),
            "reason_record": self.reason_record.to_dict(),
            "attempt_identity": self.occurrence_id.attempt_identity.to_dict(),
            "initial_causal_status": self.initial_causal_status,
        }


@dataclass(frozen=True)
class ProofCompletionEvent:
    completion_id: Tuple[Any, ...]
    proof_requirement_id: Mapping[str, Any]
    proof_artifact_ref: Tuple[Any, ...]
    proof_status: str
    completed_at_attempt: AttemptIdentity

    def to_dict(self) -> Dict[str, Any]:
        return {
            "completion_id": self.completion_id,
            "proof_requirement_id": dict(self.proof_requirement_id),
            "proof_artifact_ref": self.proof_artifact_ref,
            "proof_status": self.proof_status,
            "completed_at_attempt": self.completed_at_attempt.to_dict(),
        }


@dataclass(frozen=True)
class ReasonCausalTransition:
    transition_id: Tuple[Any, ...]
    target_occurrence_id: ReasonOccurrenceId
    transition_kind: str
    cause_kind: str
    cause_ref: Any
    emitted_at_attempt: AttemptIdentity
    transition_ordinal: int

    def to_dict(self) -> Dict[str, Any]:
        cause_ref = self.cause_ref
        if hasattr(cause_ref, "to_dict"):
            cause_ref = cause_ref.to_dict()
        return {
            "transition_id": self.transition_id,
            "target_occurrence_id": self.target_occurrence_id.to_dict(),
            "transition_kind": self.transition_kind,
            "cause_kind": self.cause_kind,
            "cause_ref": cause_ref,
            "emitted_at_attempt": self.emitted_at_attempt.to_dict(),
            "transition_ordinal": self.transition_ordinal,
        }


@dataclass
class NormalizationRuleApplication:
    """正規化ルール適用記録"""
    rule_name: str
    reason: str
    applied_to: str  # "value1" or "value2" or "both" or "case_i_j"
    before: Optional[str] = None
    after: Optional[str] = None
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "rule_name": self.rule_name,
            "reason": self.reason,
            "applied_to": self.applied_to,
            "before": self.before,
            "after": self.after,
        }


@dataclass
class PairwiseDecisiveInfo:
    """Pairwise戦略の決定的情報（どのペアが結果を決定したか）"""
    decisive_result: str  # "SAT" or "UNSAT" or "UNKNOWN"
    total_pairs: int
    unsat_pairs: int
    sat_pairs: int
    unknown_pairs: int
    
    # SAT時の decisive ペア情報
    decisive_pair: Optional[Tuple[int, int]] = None  # (i, j)
    pair_stage: Optional[str] = None  # "conds-only", "with-ineq", "norm-ineq"
    case1_summary: Optional[str] = None
    case2_summary: Optional[str] = None
    value1_expr: Optional[str] = None
    value2_expr: Optional[str] = None
    final_query_excerpt: Optional[str] = None  # ★ 互換性のため残す（先頭200文字）
    final_query: Optional[str] = None  # ★ 新規追加: 完全なクエリ
    
    def to_dict(self) -> Dict[str, Any]:
        result = {
            "decisive_result": self.decisive_result,
            "total_pairs": self.total_pairs,
            "unsat_pairs": self.unsat_pairs,
            "sat_pairs": self.sat_pairs,
            "unknown_pairs": self.unknown_pairs,
        }
        
        if self.decisive_pair is not None:
            result["decisive_pair"] = {
                "i": self.decisive_pair[0],
                "j": self.decisive_pair[1],
            }
            result["pair_stage"] = self.pair_stage
            result["case1_summary"] = self.case1_summary
            result["case2_summary"] = self.case2_summary
            result["value1_expr"] = self.value1_expr
            result["value2_expr"] = self.value2_expr
            result["final_query_excerpt"] = self.final_query_excerpt
            result["final_query"] = self.final_query  # ★ 追加
        
        return result


@dataclass
class Attempt:
    """1回の等価性判定試行（1つのPhase/Stageセット）"""
    attempt_id: int
    retry_count: int
    phase: str
    stage_path: List[str]
    strategy: str
    result: Optional[bool]
    transition_reason: str
    
    # 詳細情報
    type_fix_result: Optional[Dict[str, Any]] = None
    rewrite_info: Optional[Dict[str, Any]] = None
    original_function1_signature: Optional[Dict[str, Any]] = None
    original_function2_signature: Optional[Dict[str, Any]] = None
    effective_function1_signature: Optional[Dict[str, Any]] = None
    effective_function2_signature: Optional[Dict[str, Any]] = None
    function1_signature_hypotheses: List[Dict[str, Any]] = field(default_factory=list)
    function2_signature_hypotheses: List[Dict[str, Any]] = field(default_factory=list)
    solver_results: Optional[Dict[str, Any]] = None
    final_smt_excerpt: Optional[str] = None  # SMT式の先頭500文字（互換性のため残す）
    final_smt: Optional[str] = None  # ★ 新規: 完全なSMT式
    counterexample: Optional[Dict[str, Any]] = None
    pairwise_decisive: Optional[PairwiseDecisiveInfo] = None
    normalization_rules: List[NormalizationRuleApplication] = field(default_factory=list)
    unknown_reasons: List[UnknownReasonRecord] = field(default_factory=list)
    reason_occurrences: List[ReasonOccurrence] = field(default_factory=list)
    mips64_abi_constraints: Optional[Dict[str, Any]] = None
    elapsed_time: float = 0.0

    def __post_init__(self) -> None:
        self.unknown_reasons = list(coerce_unknown_reason_records(self.unknown_reasons))
        if not self.reason_occurrences:
            identity = AttemptIdentity(self.strategy, self.attempt_id)
            self.reason_occurrences = [
                ReasonOccurrence(
                    occurrence_id=ReasonOccurrenceId(identity, ordinal),
                    reason_record=reason,
                )
                for ordinal, reason in enumerate(self.unknown_reasons)
            ]
    
    def to_dict(self) -> Dict[str, Any]:
        result = {
            "attempt_id": self.attempt_id,
            "retry_count": self.retry_count,
            "phase": self.phase,
            "stage_path": self.stage_path,
            "strategy": self.strategy,
            "result": self.result,
            "transition_reason": self.transition_reason,
            "type_fix_result": self.type_fix_result,
            "rewrite_info": self.rewrite_info,
            "original_function1_signature": self.original_function1_signature,
            "original_function2_signature": self.original_function2_signature,
            "effective_function1_signature": self.effective_function1_signature,
            "effective_function2_signature": self.effective_function2_signature,
            "function1_signature_hypotheses": list(self.function1_signature_hypotheses),
            "function2_signature_hypotheses": list(self.function2_signature_hypotheses),
            "solver_results": self.solver_results,
            "final_smt_excerpt": self.final_smt_excerpt,
            "final_smt": self.final_smt,  # ★ 追加
            "counterexample": self.counterexample,
            "pairwise_decisive": self.pairwise_decisive.to_dict() if self.pairwise_decisive else None,
            "normalization_rules": [rule.to_dict() for rule in self.normalization_rules],
            "unknown_reasons": [reason.to_dict() for reason in self.unknown_reasons],
            "reason_occurrences": [item.to_dict() for item in self.reason_occurrences],
            "mips64_abi_constraints": self.mips64_abi_constraints,
            "elapsed_time": self.elapsed_time,
        }
        return result


@dataclass
class DebugTrace:
    """デバッグトレース（機械可読）"""
    attempts: List[Attempt] = field(default_factory=list)
    planned_phases: List[str] = field(default_factory=list)
    known_phases: List[str] = field(default_factory=list)
    final_result: Optional[bool] = None
    total_time: float = 0.0
    error_message: Optional[str] = None
    causal_transitions: List[ReasonCausalTransition] = field(default_factory=list)
    proof_completion_events: List[ProofCompletionEvent] = field(default_factory=list)
    
    def add_attempt(self, attempt: Attempt):
        """試行を追加"""
        self.attempts.append(attempt)

    def add_reason_replacement(
        self,
        old_occurrence_id: ReasonOccurrenceId,
        replacement_occurrence_id: ReasonOccurrenceId,
        replacement_stage: str,
    ) -> None:
        """Record an orchestration-proven logical reason replacement."""
        occurrence_ids = {
            occurrence.occurrence_id
            for attempt in self.attempts
            for occurrence in attempt.reason_occurrences
        }
        if old_occurrence_id not in occurrence_ids:
            raise ValueError("replacement source occurrence is not present in this trace")
        if replacement_occurrence_id not in occurrence_ids:
            raise ValueError("replacement target occurrence is not present in this trace")
        if (
            replacement_occurrence_id.attempt_identity.attempt_ordinal
            <= old_occurrence_id.attempt_identity.attempt_ordinal
        ):
            raise ValueError("replacement occurrence must belong to a later attempt")
        stage = str(replacement_stage or "").strip()
        if not stage:
            raise ValueError("reason replacement requires the recognizing stage")
        self.causal_transitions.append(
            ReasonCausalTransition(
                transition_id=(
                    "explicit_reason_replacement",
                    old_occurrence_id.attempt_identity.strategy_identity,
                    old_occurrence_id.attempt_identity.attempt_ordinal,
                    old_occurrence_id.reason_ordinal,
                    replacement_occurrence_id.attempt_identity.strategy_identity,
                    replacement_occurrence_id.attempt_identity.attempt_ordinal,
                    replacement_occurrence_id.reason_ordinal,
                    stage,
                ),
                target_occurrence_id=old_occurrence_id,
                transition_kind="superseded",
                cause_kind="reason_occurrence",
                cause_ref=replacement_occurrence_id,
                emitted_at_attempt=replacement_occurrence_id.attempt_identity,
                transition_ordinal=len(self.causal_transitions),
            )
        )

    def add_causal_transition(self, transition: ReasonCausalTransition) -> None:
        self.causal_transitions.append(transition)

    def add_proof_completion(self, completion: ProofCompletionEvent) -> None:
        self.proof_completion_events.append(completion)

    def get_phase_usage(self) -> List[Dict[str, Any]]:
        """Phase 利用状況を集約して返す。"""
        ordered_phases: List[str] = []
        seen_phases = set()

        for phase in self.known_phases:
            if phase not in seen_phases:
                ordered_phases.append(phase)
                seen_phases.add(phase)

        for attempt in self.attempts:
            if attempt.phase not in seen_phases:
                ordered_phases.append(attempt.phase)
                seen_phases.add(attempt.phase)

        usage_by_phase: Dict[str, Dict[str, Any]] = {}
        for phase in ordered_phases:
            usage_by_phase[phase] = {
                "phase": phase,
                "planned": phase in self.planned_phases,
                "reached": False,
                "used": False,
                "attempt_count": 0,
                "result_attempt_count": 0,
                "no_change_skip_count": 0,
                "transition_counts": {
                    TransitionReason.UNSAT.value: 0,
                    TransitionReason.SAT.value: 0,
                    TransitionReason.SAT_PHASE4B.value: 0,
                    TransitionReason.UNKNOWN.value: 0,
                    TransitionReason.TIMEOUT.value: 0,
                    TransitionReason.CRITICAL_ERROR.value: 0,
                    TransitionReason.NO_CHANGES.value: 0,
                },
                "last_transition_reason": None,
                "last_result": None,
            }

        for attempt in self.attempts:
            phase_usage = usage_by_phase.setdefault(
                attempt.phase,
                {
                    "phase": attempt.phase,
                    "planned": attempt.phase in self.planned_phases,
                    "reached": False,
                    "used": False,
                    "attempt_count": 0,
                    "result_attempt_count": 0,
                    "no_change_skip_count": 0,
                    "transition_counts": {
                        TransitionReason.UNSAT.value: 0,
                        TransitionReason.SAT.value: 0,
                        TransitionReason.SAT_PHASE4B.value: 0,
                        TransitionReason.UNKNOWN.value: 0,
                        TransitionReason.TIMEOUT.value: 0,
                        TransitionReason.CRITICAL_ERROR.value: 0,
                        TransitionReason.NO_CHANGES.value: 0,
                    },
                    "last_transition_reason": None,
                    "last_result": None,
                }
            )
            phase_usage["reached"] = True
            phase_usage["attempt_count"] += 1
            transition_counts = phase_usage["transition_counts"]
            transition_counts[attempt.transition_reason] = (
                transition_counts.get(attempt.transition_reason, 0) + 1
            )
            if attempt.transition_reason == TransitionReason.NO_CHANGES.value:
                phase_usage["no_change_skip_count"] += 1
            else:
                phase_usage["result_attempt_count"] += 1
                phase_usage["used"] = True
            phase_usage["last_transition_reason"] = attempt.transition_reason
            phase_usage["last_result"] = attempt.result

        return [usage_by_phase[phase] for phase in ordered_phases]

    def get_used_phases(self) -> List[str]:
        """実際に再解析・再判定まで進んだ Phase の一覧を返す。"""
        return [entry["phase"] for entry in self.get_phase_usage() if entry["used"]]

    def format_phase_usage_summary(self) -> str:
        """人間向けの Phase 利用状況サマリを返す。"""
        usage = self.get_phase_usage()
        if not usage:
            return "Phase Usage Summary:\n  (none)"

        lines = ["Phase Usage Summary:"]
        for entry in usage:
            if not entry["reached"]:
                status = "NOT_REACHED"
            elif entry["used"]:
                status = "USED"
            else:
                status = "NO_CHANGES"

            scope = "planned" if entry["planned"] else "aux"
            details = [f"scope={scope}"]
            if entry["attempt_count"] > 0:
                details.append(f"attempts={entry['attempt_count']}")
            if entry["result_attempt_count"] > 0:
                details.append(f"rechecks={entry['result_attempt_count']}")
            if entry["no_change_skip_count"] > 0:
                details.append(f"no_changes={entry['no_change_skip_count']}")
            transition_counts = entry["transition_counts"]
            details.append(f"unsat={transition_counts.get(TransitionReason.UNSAT.value, 0)}")
            details.append(f"sat={transition_counts.get(TransitionReason.SAT.value, 0)}")
            details.append(
                f"sat_phase4b={transition_counts.get(TransitionReason.SAT_PHASE4B.value, 0)}"
            )
            details.append(f"unknown={transition_counts.get(TransitionReason.UNKNOWN.value, 0)}")
            details.append(f"timeout={transition_counts.get(TransitionReason.TIMEOUT.value, 0)}")
            details.append(
                f"critical={transition_counts.get(TransitionReason.CRITICAL_ERROR.value, 0)}"
            )
            if entry["last_transition_reason"] is not None:
                details.append(f"last={entry['last_transition_reason']}")

            lines.append(f"  {entry['phase']}: {status} ({', '.join(details)})")
        return "\n".join(lines)
    
    def to_dict(self) -> Dict[str, Any]:
        observed_unknown_reasons = [
            reason
            for attempt in self.attempts
            for reason in getattr(attempt, "unknown_reasons", []) or []
        ]
        final_unknown_reasons = []
        if self.final_result is None:
            final_transition_reasons = {
                TransitionReason.UNKNOWN.value,
                TransitionReason.TIMEOUT.value,
            }
            for attempt in reversed(self.attempts):
                if (
                    attempt.result is None
                    and attempt.transition_reason in final_transition_reasons
                ):
                    final_unknown_reasons = list(getattr(attempt, "unknown_reasons", []) or [])
                    break
        return {
            "attempts": [attempt.to_dict() for attempt in self.attempts],
            "causal_transitions": [item.to_dict() for item in self.causal_transitions],
            "proof_completion_events": [item.to_dict() for item in self.proof_completion_events],
            "planned_phases": self.planned_phases,
            "known_phases": self.known_phases,
            "used_phases": self.get_used_phases(),
            "phase_usage": self.get_phase_usage(),
            "unknown_reason_counts": summarize_unknown_reason_counts(
                final_unknown_reasons,
                primary_by_aggregation_unit=True,
            ),
            "observed_unknown_reason_counts": summarize_unknown_reason_counts(observed_unknown_reasons),
            "unknown_recovery_backlog": summarize_unknown_recovery_backlog(
                final_unknown_reasons,
                primary_by_aggregation_unit=True,
            ),
            "unknown_recovery_actions": [
                action.to_dict()
                for action in build_unknown_recovery_actions(
                    final_unknown_reasons,
                    primary_by_aggregation_unit=True,
                )
            ],
            "observed_unknown_recovery_backlog": summarize_unknown_recovery_backlog(
                observed_unknown_reasons
            ),
            "observed_unknown_recovery_actions": [
                action.to_dict()
                for action in build_unknown_recovery_actions(observed_unknown_reasons)
            ],
            "final_result": self.final_result,
            "total_time": self.total_time,
            "error_message": self.error_message,
            "attempt_count": len(self.attempts),
        }
    
    def to_json_string(self, indent: int = 2) -> str:
        """JSON文字列として出力"""
        import json
        return json.dumps(self.to_dict(), indent=indent)
