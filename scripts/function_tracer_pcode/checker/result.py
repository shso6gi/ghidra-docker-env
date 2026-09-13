# -*- coding: utf-8 -*-
"""等価性判定結果のデータモデル"""

from typing import Optional, Dict, Any, List, Mapping, Tuple
from dataclasses import dataclass, field

from scripts.function_tracer_pcode.core import FunctionSignature
from scripts.function_tracer_pcode.smt import ParallelResult, SolverStatus
from scripts.function_tracer_pcode.checker.counterexample import FormattedCounterexample
from scripts.function_tracer_pcode.semantics.typing.fixer import TypeFixResult
from scripts.function_tracer_pcode.checker.debug_trace import DebugTrace
from scripts.function_tracer_pcode.checker.unknown_reason import (
    UnknownReasonRecord,
    UnknownRecoveryAction,
    build_unknown_recovery_actions,
    coerce_unknown_reason_records,
    coerce_unknown_recovery_actions,
    summarize_unknown_recovery_backlog,
)
from scripts.function_tracer_pcode.proof.unknown_reason import (
    UnknownRecoveryActionStatus,
)


def _format_stage_seconds(diagnostics: Any) -> str:
    """診断ブロックの段階別時間を 1 行に整形する（無ければ空文字）。"""
    try:
        stages = (diagnostics or {}).get("stages") or {}
        seconds = stages.get("seconds") or {}
        if not seconds:
            return ""
        parts = [f"{stage}={float(value):.3f}" for stage, value in seconds.items()]
        age = stages.get("process_age_at_start_seconds")
        if age is not None:
            parts.insert(0, f"process_startup={float(age):.3f}")
        boundary = (diagnostics or {}).get("boundary_seconds") or {}
        for key, value in boundary.items():
            parts.append(f"boundary.{key}={float(value):.3f}")
        return "Stage seconds: " + " ".join(parts)
    except Exception:
        return ""


@dataclass
class EquivalenceResult:
    """等価性判定の結果"""
    is_equivalent: Optional[bool]
    function1_name: str
    function2_name: str
    binary1_name: str
    binary2_name: str
    solver_results: ParallelResult
    counterexample: Optional[FormattedCounterexample] = None
    counterexample_raw: Optional[Dict[str, Any]] = field(
        default=None,
        repr=False,
        compare=False,
    )
    smt_formula: Optional[str] = None
    total_time: float = 0.0
    error_message: Optional[str] = None
    type_fix_result: Optional[TypeFixResult] = None
    retry_count: int = 0
    function1_signature: Optional[FunctionSignature] = None
    function2_signature: Optional[FunctionSignature] = None
    effective_function1_signature: Optional[FunctionSignature] = None
    effective_function2_signature: Optional[FunctionSignature] = None
    function1_signature_hypotheses: List[Dict[str, Any]] = field(default_factory=list)
    function2_signature_hypotheses: List[Dict[str, Any]] = field(default_factory=list)
    constrained_fragments: List[str] = field(default_factory=list)
    mips64_abi_constraints: Optional[Dict[str, Tuple[str, int]]] = None
    pairwise_stats: Optional[Dict[str, int]] = None
    pairwise_debug_stats: Optional[Dict[str, int]] = None
    unknown_reasons: List[UnknownReasonRecord] = field(default_factory=list)
    unknown_recovery_actions: List[UnknownRecoveryAction] = field(default_factory=list)
    failure_status: Optional[str] = None
    failure_message: Optional[str] = None
    sat_pair_info: Optional[Dict[str, Any]] = None
    stage_path: List[str] = field(default_factory=list)
    debug_trace: Optional[DebugTrace] = None
    decision_gated_by_pending_proof: bool = False
    
    # ★ 新規追加: 正規化ルール適用履歴
    normalization_rules: List[Any] = field(default_factory=list)  # List[NormalizationRuleApplication]
    completed_recovery_proof_evidence: List[Dict[str, Any]] = field(default_factory=list)
    reason_completion_applicability_contexts: List[Dict[str, Any]] = field(default_factory=list)
    call_effect_shadow_manifest: Optional[Dict[str, Any]] = None
    call_proof_terminal_provenance: Optional[Dict[str, Any]] = None
    recurrence_promotion_receipt: Optional[Dict[str, Any]] = None
    binary1_content_identity: Optional[Tuple[Any, ...]] = None
    binary2_content_identity: Optional[Tuple[Any, ...]] = None
    function1_identity: Optional[Tuple[Any, ...]] = None
    function2_identity: Optional[Tuple[Any, ...]] = None
    decision_receipt: Optional[Any] = field(default=None, repr=False, compare=False)
    final_outcome: Optional[str] = None
    # 条件付き（仮定依存）判定の列。無条件 authority とは別に保持し、
    # is_equivalent / final_outcome / exit code には決して影響させない（#20 PR-A）。
    conditional_decision_receipt: Optional[Any] = field(
        default=None, repr=False, compare=False
    )
    conditional_outcome: Optional[str] = None
    canonical_decision_required: bool = False
    canonical_c_active_base: Tuple[Mapping[str, Any], ...] = ()
    canonical_q_open_base: Tuple[Mapping[str, Any], ...] = ()
    canonical_result_finalization_bundle: Optional[Mapping[str, Any]] = field(
        default=None, repr=False, compare=False
    )
    # 非署名の診断（Issue #17）: 解析時間・式サイズ。to_dict で結果統計と合成する。
    diagnostics: Optional[Dict[str, Any]] = field(default=None, repr=False, compare=False)
    # Issue #128 PR-128-A: `debug_trace` を省いても原因分析を失わないための
    # lossless な compact 集計。canonical bundle を組む前に確定させる
    # （`checker.cause_aggregate.attach_cause_aggregate`）。未設定なら to_dict が
    # その場で組むので、この field が None でも JSON には必ず出る。
    unknown_cause_aggregate: Optional[Dict[str, Any]] = field(
        default=None, repr=False, compare=False
    )

    def __post_init__(self) -> None:
        self.unknown_reasons = list(coerce_unknown_reason_records(self.unknown_reasons))
        if self.unknown_recovery_actions:
            self.unknown_recovery_actions = list(
                coerce_unknown_recovery_actions(self.unknown_recovery_actions)
            )
        else:
            self.unknown_recovery_actions = list(
                build_unknown_recovery_actions(self.unknown_reasons)
            )
        if self.is_equivalent is True and self._has_pending_proof_gate():
            self.is_equivalent = None
            self.decision_gated_by_pending_proof = True

    def _has_pending_proof_gate(self) -> bool:
        for action in self.unknown_recovery_actions:
            if action.status != UnknownRecoveryActionStatus.PENDING_PROOF.value:
                continue
            if action.proof_obligation_id is not None or action.object_target_key is not None:
                return True
        return False
    
    def is_timeout(self) -> bool:
        """タイムアウトで結果が不明かどうかを判定"""
        if self.decision_receipt is not None:
            from scripts.function_tracer_pcode.authority.decision.production_cutover import (
                outcome_from_result,
            )
            from scripts.function_tracer_pcode.authority.contracts import Outcome

            return outcome_from_result(self) is Outcome.TIMEOUT
        if self.canonical_decision_required:
            raise ValueError("canonical result lacks DecisionReceipt")
        if self.is_equivalent is not None:
            return False
        if not self.solver_results or not self.solver_results.results:
            return False
        for sr in self.solver_results.results:
            if sr.status == SolverStatus.TIMEOUT:
                return True
        return False
    
    def is_unknown(self) -> bool:
        """結果がsemantic UNKNOWNかどうかを判定（TIMEOUTは含めない）。"""
        if self.decision_receipt is not None:
            from scripts.function_tracer_pcode.authority.decision.production_cutover import (
                outcome_from_result,
            )
            from scripts.function_tracer_pcode.authority.contracts import Outcome

            return outcome_from_result(self) is Outcome.UNKNOWN
        if self.canonical_decision_required:
            raise ValueError("canonical result lacks DecisionReceipt")
        return self.is_equivalent is None and self.error_message is None
    
    def has_critical_error(self) -> bool:
        """致命的なエラー（リトライ不可能）があるかどうかを判定"""
        if self.error_message is None:
            return False
        critical_keywords = ["not found", "not available", "No SMT solvers"]
        return any(kw in self.error_message for kw in critical_keywords)

    def get_effective_function1_signature(self) -> Optional[FunctionSignature]:
        """判定時に有効だった binary1 側シグネチャを返す。"""
        return self.effective_function1_signature or self.function1_signature

    def get_effective_function2_signature(self) -> Optional[FunctionSignature]:
        """判定時に有効だった binary2 側シグネチャを返す。"""
        return self.effective_function2_signature or self.function2_signature
    
    def to_dict(self) -> Dict[str, Any]:
        """機械可読な辞書に変換（JSON シリアライズ可能）"""
        decision_receipt = None
        if self.decision_receipt is not None:
            from scripts.function_tracer_pcode.authority.decision.production_cutover import (
                decision_receipt_payload,
                outcome_from_result,
            )

            outcome_from_result(self)
            decision_receipt = decision_receipt_payload(self.decision_receipt)
        elif self.canonical_decision_required:
            raise ValueError("canonical serialization lacks DecisionReceipt")
        conditional_decision_receipt = None
        if self.conditional_decision_receipt is not None:
            from scripts.function_tracer_pcode.authority.decision.production_cutover import (
                conditional_decision_receipt_payload,
            )

            conditional_decision_receipt = conditional_decision_receipt_payload(
                self.conditional_decision_receipt
            )
        elif self.conditional_outcome is not None:
            raise ValueError("conditional outcome without its ConditionalDecisionReceipt")
        result = {
            "is_equivalent": self.is_equivalent,
            "function1_name": self.function1_name,
            "function2_name": self.function2_name,
            "binary1_name": self.binary1_name,
            "binary2_name": self.binary2_name,
            "binary1_content_identity": self.binary1_content_identity,
            "binary2_content_identity": self.binary2_content_identity,
            "function1_identity": self.function1_identity,
            "function2_identity": self.function2_identity,
            "function1_signature": self.function1_signature.to_dict() if self.function1_signature else None,
            "function2_signature": self.function2_signature.to_dict() if self.function2_signature else None,
            "effective_function1_signature": self.get_effective_function1_signature().to_dict() if self.get_effective_function1_signature() else None,
            "effective_function2_signature": self.get_effective_function2_signature().to_dict() if self.get_effective_function2_signature() else None,
            "function1_signature_hypotheses": list(self.function1_signature_hypotheses),
            "function2_signature_hypotheses": list(self.function2_signature_hypotheses),
            "solver_results": self.solver_results.to_dict() if self.solver_results else None,
            "counterexample": self.counterexample.to_dict() if self.counterexample else None,
            "total_time": self.total_time,
            "error_message": self.error_message,
            "failure_status": self.failure_status,
            "failure_message": self.failure_message,
            "type_fix_result": self.type_fix_result.to_dict() if self.type_fix_result else None,
            "retry_count": self.retry_count,
            "is_timeout": self.is_timeout(),
            "final_outcome": self.final_outcome,
            "decision_receipt": decision_receipt,
            "conditional_outcome": self.conditional_outcome,
            "conditional_decision_receipt": conditional_decision_receipt,
            "c_active_base": [dict(row) for row in self.canonical_c_active_base],
            "q_open_base": [dict(row) for row in self.canonical_q_open_base],
            "constrained_fragments": self.constrained_fragments,
            "pairwise_stats": self.pairwise_stats,
            "pairwise_debug_stats": self.pairwise_debug_stats,
            "unknown_reasons": [reason.to_dict() for reason in self.unknown_reasons],
            "unknown_recovery_actions": [
                action.to_dict() for action in self.unknown_recovery_actions
            ],
            "unknown_recovery_backlog": summarize_unknown_recovery_backlog(self.unknown_reasons),
            "decision_gated_by_pending_proof": self.decision_gated_by_pending_proof,
            "sat_pair_info": self.sat_pair_info,
            "stage_path": self.stage_path,
        }
        from scripts.function_tracer_pcode.checker.diagnostics import result_diagnostics_payload

        result["diagnostics"] = result_diagnostics_payload(self)
        # Issue #128: 原因分析の compact 集計は常時出す。既に確定していれば
        # それを使い、ここで作り直さない（preimage 確定前に固定するため）。
        if self.unknown_cause_aggregate is None:
            from scripts.function_tracer_pcode.checker.cause_aggregate import (
                build_unknown_cause_aggregate,
            )

            self.unknown_cause_aggregate = build_unknown_cause_aggregate(self)
        result["unknown_cause_aggregate"] = self.unknown_cause_aggregate
        if self.canonical_result_finalization_bundle is not None:
            result["canonical_result_finalization_bundle"] = dict(
                self.canonical_result_finalization_bundle
            )
        if self.completed_recovery_proof_evidence:
            result["completed_recovery_proof_evidence"] = list(self.completed_recovery_proof_evidence)
        if self.reason_completion_applicability_contexts:
            result["reason_completion_applicability_contexts"] = list(
                self.reason_completion_applicability_contexts
            )
        if self.call_effect_shadow_manifest is not None:
            result["call_effect_shadow_manifest"] = dict(self.call_effect_shadow_manifest)
        if self.call_proof_terminal_provenance is not None:
            result["call_proof_terminal_provenance"] = dict(
                self.call_proof_terminal_provenance
            )
        if self.recurrence_promotion_receipt is not None:
            result["recurrence_promotion_receipt"] = dict(
                self.recurrence_promotion_receipt
            )
        
        # ★ 新規追加: mips64_abi_constraints
        if self.mips64_abi_constraints:
            # Dict[str, Tuple[str, int]] を JSON可能な形式に変換
            result["mips64_abi_constraints"] = {
                k: {"signedness": v[0], "narrow_bits": v[1]}
                for k, v in self.mips64_abi_constraints.items()
            }
        
        # ★ 新規追加: デバッグトレース
        if self.debug_trace:
            result["debug_trace"] = self.debug_trace.to_dict()
        
        return result
    
    def to_string(self, verbose: bool = False, show_phase_usage: bool = False) -> str:
        lines = []
        lines.append("=" * 70)
        lines.append("EQUIVALENCE CHECK RESULT")
        lines.append("=" * 70)
        
        # Binary 1 の情報
        lines.append(f"Binary 1: {self.binary1_name}")
        lines.append(f"Function 1: {self.function1_name}")
        if self.function1_signature:
            lines.append(f"  Original signature: {self.function1_signature.format_full(self.function1_name)}")
        effective_signature1 = self.get_effective_function1_signature()
        if (
            effective_signature1
            and self.function1_signature
            and effective_signature1.to_dict() != self.function1_signature.to_dict()
        ):
            lines.append(f"  Effective signature: {effective_signature1.format_full(self.function1_name)}")
        elif effective_signature1 and self.function1_signature is None:
            lines.append(f"  Effective signature: {effective_signature1.format_full(self.function1_name)}")
        if self.function1_signature_hypotheses:
            lines.append(f"  Hypotheses: {self.function1_signature_hypotheses}")

        lines.append("")
        
        # Binary 2 の情報
        lines.append(f"Binary 2: {self.binary2_name}")
        lines.append(f"Function 2: {self.function2_name}")
        if self.function2_signature:
            lines.append(f"  Original signature: {self.function2_signature.format_full(self.function2_name)}")
        effective_signature2 = self.get_effective_function2_signature()
        if (
            effective_signature2
            and self.function2_signature
            and effective_signature2.to_dict() != self.function2_signature.to_dict()
        ):
            lines.append(f"  Effective signature: {effective_signature2.format_full(self.function2_name)}")
        elif effective_signature2 and self.function2_signature is None:
            lines.append(f"  Effective signature: {effective_signature2.format_full(self.function2_name)}")
        if self.function2_signature_hypotheses:
            lines.append(f"  Hypotheses: {self.function2_signature_hypotheses}")

        lines.append("")

        # Pairwise統計情報を追加
        if self.pairwise_stats:
            lines.append("")
            lines.append("Pairwise Statistics:")
            stats = self.pairwise_stats
            lines.append(f"  Total pairs: {stats['total_pairs']}")
            lines.append(f"  UNSAT: {stats['unsat_pairs']}, SAT: {stats['sat_pairs']}, "
                        f"UNKNOWN: {stats['unknown_pairs']}, ERROR: {stats['error_pairs']}")
            
            if self.sat_pair_info:
                info = self.sat_pair_info
                lines.append(f"  First SAT pair: ({info['i']}, {info['j']})")
                lines.append(f"    Case1: {info['case1_summary']}")
                lines.append(f"    Case2: {info['case2_summary']}")

        if self.pairwise_debug_stats:
            stats = self.pairwise_debug_stats
            lines.append("")
            lines.append("Pairwise Final Solver Disposition Summary:")
            lines.append(
                "  unsat={unsat}, sat={sat}, unknown={unknown}".format(
                    unsat=stats.get("unsat_results", 0),
                    sat=stats.get("sat_results", 0),
                    unknown=stats.get("unknown_results", 0),
                )
            )
            lines.append("Pairwise Timeout Normalization Summary:")
            lines.append(
                "  attempts={attempts}, changed={changed}, no_change={no_change}, "
                "unsat={unsat}, sat={sat}, unknown={unknown}".format(
                    attempts=stats.get("timeout_fallback_attempts", 0),
                    changed=stats.get("changed_pairs", 0),
                    no_change=stats.get("no_change_pairs", 0),
                    unsat=stats.get(
                        "normalization_unsat_results",
                        stats.get("unsat_results", 0),
                    ),
                    sat=stats.get(
                        "normalization_sat_results",
                        stats.get("sat_results", 0),
                    ),
                    unknown=stats.get(
                        "normalization_unknown_results",
                        stats.get("unknown_results", 0),
                    ),
                )
            )
            if (
                "exact_query_attempt_cache_hits" in stats
                or "exact_query_attempt_cache_misses" in stats
            ):
                lines.append(
                    "  exact_query_cache_hits={hits}, exact_query_cache_misses={misses}".format(
                        hits=stats.get("exact_query_attempt_cache_hits", 0),
                        misses=stats.get("exact_query_attempt_cache_misses", 0),
                    )
                )
            if (
                "obligation_pair_cache_hits" in stats
                or "obligation_pair_cache_misses" in stats
            ):
                lines.append(
                    "  obligation_pair_cache_hits={hits}, obligation_pair_cache_misses={misses}".format(
                        hits=stats.get("obligation_pair_cache_hits", 0),
                        misses=stats.get("obligation_pair_cache_misses", 0),
                    )
                )
            if "guard_overlap_graph_hits" in stats or "guard_overlap_graph_misses" in stats:
                lines.append(
                    "  guard_overlap_graph_hits={hits}, guard_overlap_graph_misses={misses}".format(
                        hits=stats.get("guard_overlap_graph_hits", 0),
                        misses=stats.get("guard_overlap_graph_misses", 0),
                    )
                )
            if "guard_overlap_prepass_node_hits" in stats:
                lines.append(
                    "  guard_overlap_prepass_node_hits={hits}, value_candidates={candidates}".format(
                        hits=stats.get("guard_overlap_prepass_node_hits", 0),
                        candidates=stats.get("guard_overlap_value_candidates", 0),
                    )
                )
            if stats.get("pair_ledger_sealed"):
                lines.append(
                    "  pair_ledger=sealed, skipped_after_terminal={skipped}".format(
                        skipped=stats.get("pair_ledger_skipped_after_terminal", 0),
                    )
                )

        if self.unknown_reasons:
            lines.append("")
            lines.append("UNKNOWN Reasons:")
            for reason in self.unknown_reasons[:10]:
                scope = reason.pair_or_case or reason.stage or reason.reason_scope
                recovery = self._reason_recovery_display(reason)
                lines.append(
                    f"  {reason.reason_id}: class={reason.reason_class}, "
                    f"effect={reason.decision_effect}, scope={scope}, recovery={recovery}"
                )
            if len(self.unknown_reasons) > 10:
                lines.append(f"  ... ({len(self.unknown_reasons) - 10} more)")

            recovery_backlog = summarize_unknown_recovery_backlog(self.unknown_reasons)
            if recovery_backlog:
                lines.append("")
                lines.append("UNKNOWN Recovery Proof Backlog:")
                for reason_id, entry in recovery_backlog.items():
                    proof_kinds = ", ".join(entry.get("proof_obligation_counts", {}).keys())
                    if not proof_kinds:
                        proof_kinds = entry.get("recovery_proof_kind") or "none"
                    lines.append(
                        f"  {reason_id}: count={entry.get('count', 0)}, proofs={proof_kinds}"
                    )
        if self.decision_gated_by_pending_proof:
            lines.append("")
            lines.append("Decision gated: pending proof obligation blocks EQUIVALENT recovery")
                
        lines.append("")
        
        # パラメータ断片として制約された変数を表示
        if self.constrained_fragments:
            vars_str = ", ".join(self.constrained_fragments)
            lines.append(f"Derived fragments: {vars_str}")
            lines.append("  (upper-bits variables constrained via sign/zero extension from parameters)")
        
        if self.type_fix_result and self.type_fix_result.any_fix_applied():
            lines.append(f"Type fix applied: {self.type_fix_result}")
        if self.retry_count > 0:
            lines.append(f"Retry count: {self.retry_count}")
        
        lines.append("-" * 70)
        
        canonical_outcome = None
        if self.decision_receipt is not None:
            from scripts.function_tracer_pcode.authority.decision.production_cutover import (
                outcome_from_result,
            )

            canonical_outcome = outcome_from_result(self).value
        elif self.canonical_decision_required:
            raise ValueError("canonical rendering lacks DecisionReceipt")
        if canonical_outcome == "ERROR" or (
            canonical_outcome is None and self.error_message
        ):
            lines.append("Result: ERROR")
            if self.error_message:
                lines.append(f"ERROR: {self.error_message}")
            if self.failure_status:
                lines.append(f"Failure status: {self.failure_status}")
        elif canonical_outcome in {"UNKNOWN", "TIMEOUT"} or (
            canonical_outcome is None and self.is_equivalent is None
        ):
            if canonical_outcome == "TIMEOUT" or (
                canonical_outcome is None and self.is_timeout()
            ):
                lines.append("Result: TIMEOUT (could not determine equivalence within time limit)")
            else:
                lines.append("Result: UNKNOWN (could not determine equivalence)")
            if self.failure_status:
                lines.append(f"Failure status: {self.failure_status}")
            if self.failure_message:
                lines.append(f"Failure detail: {self.failure_message}")
        elif canonical_outcome == "EQUIVALENT" or (
            canonical_outcome is None and self.is_equivalent
        ):
            lines.append("Result: EQUIVALENT ✓")
        else:
            lines.append("Result: NOT EQUIVALENT ✗")
            if self.counterexample:
                lines.append("")
                lines.append(self.counterexample.to_string())
            else:
                lines.append("")
                lines.append("(No counterexample available)")
        
        lines.append("-" * 70)
        lines.append(f"Total time: {self.total_time:.3f} seconds")
        stage_line = _format_stage_seconds(getattr(self, "diagnostics", None))
        if stage_line:
            lines.append(stage_line)
        
        if verbose and self.solver_results:
            lines.append("")
            lines.append("Solver Results:")
            for sr in self.solver_results.results:
                status_str = sr.status.name
                lines.append(f"  {sr.solver_name}: {status_str} ({sr.elapsed_time:.3f}s)")
                if sr.error_message:
                    lines.append(f"    Error: {sr.error_message}")
                if sr.model:
                    lines.append(f"    Model: {sr.model}")

        if show_phase_usage and self.debug_trace:
            lines.append("")
            lines.append(self.debug_trace.format_phase_usage_summary())
        
        lines.append("=" * 70)
        return "\n".join(lines)

    def _reason_recovery_display(self, reason: UnknownReasonRecord) -> str:
        matching_actions = [
            action
            for action in self.unknown_recovery_actions
            if action.reason_id == reason.reason_id
            and (reason.pair_or_case is None or action.pair_or_case == reason.pair_or_case)
        ]
        if not matching_actions:
            return reason.recovery_proof_kind
        proof_kinds = sorted({action.proof_kind for action in matching_actions if action.proof_kind})
        statuses = sorted({action.status for action in matching_actions if action.status})
        if not proof_kinds:
            proof_kinds = [reason.recovery_proof_kind]
        proof_text = ",".join(proof_kinds)
        if statuses:
            return f"{proof_text} ({','.join(statuses)})"
        return proof_text
