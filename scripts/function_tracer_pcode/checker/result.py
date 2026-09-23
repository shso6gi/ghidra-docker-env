# -*- coding: utf-8 -*-
"""等価性判定結果のデータモデル"""

from typing import Optional, Dict, Any, List, Mapping, Tuple
from dataclasses import dataclass, field

from scripts.function_tracer_pcode.core import FunctionSignature
from scripts.function_tracer_pcode.smt import ParallelResult, SolverStatus
from scripts.function_tracer_pcode.checker.counterexample import FormattedCounterexample
from scripts.function_tracer_pcode.semantics.typing.fixer import TypeFixResult
from scripts.function_tracer_pcode.checker.debug_trace import DebugTrace
from scripts.function_tracer_pcode.checker.output_preparation import (
    PREPARED_SOURCE_ATTRIBUTES,
    PreparedPayloadStale,
)
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


def _reason_recovery_display(reason: Mapping[str, Any], actions: List[Mapping[str, Any]]) -> str:
    matching_actions = [
        action
        for action in actions
        if action.get("reason_id") == reason.get("reason_id")
        and (reason.get("pair_or_case") is None or action.get("pair_or_case") == reason.get("pair_or_case"))
    ]
    if not matching_actions:
        return reason.get("recovery_proof_kind")
    proof_kinds = sorted({str(action.get("proof_kind")) for action in matching_actions if action.get("proof_kind")})
    statuses = sorted({str(action.get("status")) for action in matching_actions if action.get("status")})
    if not proof_kinds:
        proof_kinds = [str(reason.get("recovery_proof_kind"))]
    proof_text = ",".join(proof_kinds)
    if statuses:
        return f"{proof_text} ({','.join(statuses)})"
    return proof_text


def _format_pairwise_debug_stats(stats: Mapping[str, Any]) -> List[str]:
    lines = ["Pairwise Final Solver Disposition Summary:"]
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
            unsat=stats.get("normalization_unsat_results", stats.get("unsat_results", 0)),
            sat=stats.get("normalization_sat_results", stats.get("sat_results", 0)),
            unknown=stats.get("normalization_unknown_results", stats.get("unknown_results", 0)),
        )
    )
    for hits_key, misses_key, label_hits, label_misses in (
        ("exact_query_attempt_cache_hits", "exact_query_attempt_cache_misses",
         "exact_query_cache_hits", "exact_query_cache_misses"),
        ("obligation_pair_cache_hits", "obligation_pair_cache_misses",
         "obligation_pair_cache_hits", "obligation_pair_cache_misses"),
        ("guard_overlap_graph_hits", "guard_overlap_graph_misses",
         "guard_overlap_graph_hits", "guard_overlap_graph_misses"),
    ):
        if hits_key in stats or misses_key in stats:
            lines.append(
                f"  {label_hits}={stats.get(hits_key, 0)}, {label_misses}={stats.get(misses_key, 0)}"
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
    return lines


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
    # Issue #15: 同一バイナリ・同一関数の identity proof で確定したときの provenance
    # と、その評価の顛末（適用可否と理由）。どちらも判定の authority ではなく、
    # authority は `decision_receipt` / `final_outcome` のまま。値が無い pair では
    # `to_dict()` に key ごと出さないので、非 identical pair の JSON は変わらない。
    decisive_proof_provenance: Optional[Mapping[str, Any]] = field(
        default=None, repr=False, compare=False
    )
    identical_fast_path_disposition: Optional[Mapping[str, Any]] = field(
        default=None, repr=False, compare=False
    )
    # Issue #15 PR-15-B: 左右の Program から観測した同一性そのもの。
    # `function*_identity`（= 解析由来の stable result key）とは別の key に置く。
    # 前者は「この pair のこの側を他と区別する識別子」、こちらは「左右が同じ
    # 関数だと言える観測」で、役割が違う。混ぜると同じ binary を共有する複数の
    # pair が 1 つの結果に潰れる（`reporting/root_blocker_summary`）。
    identical_function_identity_evidence: Optional[Mapping[str, Any]] = field(
        default=None, repr=False, compare=False
    )
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
    # Issue #106 PR-106-0: pair 1 件を打ち切った理由（`PairStopState` の値）。
    # 台帳（`core.errors.PairFailureLedger`）が所有する stop state を、境界で
    # 1 度だけ結果へ写したもの。**判定 authority の入力ではない**（UNKNOWN /
    # ERROR を決めるのは既存の attribution と authority）。打ち切っていない
    # pair では `None` のままで、JSON にも出ない。
    pair_stop_state: Optional[str] = field(default=None, repr=False, compare=False)
    # Issue #128 PR-128-A: `debug_trace` を省いても原因分析を失わないための
    # lossless な compact 集計。canonical bundle を組む前に確定させる
    # （`checker.cause_aggregate.attach_cause_aggregate`）。未設定なら to_dict が
    # その場で組むので、この field が None でも JSON には必ず出る。
    unknown_cause_aggregate: Optional[Dict[str, Any]] = field(
        default=None, repr=False, compare=False
    )
    # Issue #128 PR-128-B: `debug_trace` **object の生成は止めない**。この flag は
    # `to_dict()` が JSON へ添付するかだけを決める（trace object は結果に残る）。
    # Issue #22 PR-22-D: 出力を準備した結果では、diagnostics / to_string /
    # 原因集計は authority 前に準備した値（`PreparedSemanticPayload.trace_timings` /
    # `cause_evidence`）だけを読み、trace を読み直さない。準備していない結果
    # （直接組んだ `EquivalenceResult`）では従来どおり trace から作る。既定 True なので
    # `EquivalenceResult` を直接組む呼び出し元の挙動は変わらず、production では
    # `checker/workflow.py` が既存の debug 伝播（`--debug` / `-d` /
    # `EQBENCH_DEBUG=1`）をそのまま入れる。
    emit_debug_trace: bool = True
    # Issue #22 PR-22-D: authority 確定 **前** に準備した解析由来の payload
    # （`checker.output_preparation.PreparedSemanticPayload`）。pair 境界が 1 回
    # だけ設定し、`to_dict()` はその値を使う（解析 object を読み直さない）。
    # 判定 authority の入力ではない。境界を通らずに組んだ結果では `None` のままで、
    # `to_dict()` はその場で準備する。
    prepared_semantic_payload: Optional[Any] = field(
        default=None, repr=False, compare=False
    )

    def __setattr__(self, name: str, value: Any) -> None:
        # Issue #22 PR-22-D: 準備した A（解析由来の payload）は authority 確定前に
        # 1 回だけ作り、以後 live な属性を読み直さない。準備の後でその元になる属性を
        # 差し替えるのは、出力に現れない更新なので内部バグとして拒む。
        if name in PREPARED_SOURCE_ATTRIBUTES and (
            self.__dict__.get("prepared_semantic_payload") is not None
        ):
            raise PreparedPayloadStale(
                f"result.{name} cannot be replaced after the output was prepared"
            )
        object.__setattr__(self, name, value)

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
        """機械可読な辞書に変換（JSON シリアライズ可能）。

        Issue #22 PR-22-D: field ごとの所有者（解析由来 = 準備済み payload /
        authority / 診断）と key 順は `checker.output_preparation.RESULT_FIELDS` が
        唯一の定義。ここは合成を呼ぶだけ。
        """
        from scripts.function_tracer_pcode.checker.output_preparation import (
            result_payload,
        )

        return result_payload(self)
    
    def to_string(self, verbose: bool = False, show_phase_usage: bool = False) -> str:
        """人間向けの text。**出力と同じ有界な表現**（`to_dict()` の値）から作る。

        Issue #22 PR-22-D: authority 確定後に live な解析・結果 object（signature の
        Ghidra 型・反例・solver model・debug trace）を読み直さない。A は authority 前に
        準備した値、B / C は出力と同じ上限で準備した値を読む。
        """

        from scripts.function_tracer_pcode.checker.counterexample import format_counterexample_text
        from scripts.function_tracer_pcode.checker.debug_trace import format_phase_usage_rows
        from scripts.function_tracer_pcode.core.signature import format_signature_text
        from scripts.function_tracer_pcode.semantics.typing.fixer import (
            describe_type_fix,
            type_fix_applied,
        )

        payload = self.to_dict()
        lines = []
        lines.append("=" * 70)
        lines.append("EQUIVALENCE CHECK RESULT")
        lines.append("=" * 70)

        for side in ("1", "2"):
            name = payload.get(f"function{side}_name")
            lines.append(f"Binary {side}: {payload.get(f'binary{side}_name')}")
            lines.append(f"Function {side}: {name}")
            original = payload.get(f"function{side}_signature")
            effective = payload.get(f"effective_function{side}_signature")
            if original:
                lines.append(f"  Original signature: {format_signature_text(original, name)}")
            if effective and (original is None or effective != original):
                lines.append(f"  Effective signature: {format_signature_text(effective, name)}")
            hypotheses = payload.get(f"function{side}_signature_hypotheses")
            if hypotheses:
                lines.append(f"  Hypotheses: {hypotheses}")
            lines.append("")

        # Pairwise統計情報を追加
        stats = payload.get("pairwise_stats")
        if isinstance(stats, dict) and stats and not stats.get("truncated"):
            lines.append("")
            lines.append("Pairwise Statistics:")
            lines.append(f"  Total pairs: {stats.get('total_pairs')}")
            lines.append(f"  UNSAT: {stats.get('unsat_pairs')}, SAT: {stats.get('sat_pairs')}, "
                        f"UNKNOWN: {stats.get('unknown_pairs')}, ERROR: {stats.get('error_pairs')}")

            info = payload.get("sat_pair_info")
            if isinstance(info, dict) and info:
                lines.append(f"  First SAT pair: ({info.get('i')}, {info.get('j')})")
                lines.append(f"    Case1: {info.get('case1_summary')}")
                lines.append(f"    Case2: {info.get('case2_summary')}")

        stats = payload.get("pairwise_debug_stats")
        if isinstance(stats, dict) and stats and not stats.get("truncated"):
            lines.append("")
            lines.extend(_format_pairwise_debug_stats(stats))

        reasons = [row for row in (payload.get("unknown_reasons") or ()) if isinstance(row, dict)]
        if reasons:
            actions = [
                row for row in (payload.get("unknown_recovery_actions") or ())
                if isinstance(row, dict)
            ]
            lines.append("")
            lines.append("UNKNOWN Reasons:")
            for reason in reasons[:10]:
                scope = reason.get("pair_or_case") or reason.get("stage") or reason.get("reason_scope")
                recovery = _reason_recovery_display(reason, actions)
                lines.append(
                    f"  {reason.get('reason_id')}: class={reason.get('reason_class')}, "
                    f"effect={reason.get('decision_effect')}, scope={scope}, recovery={recovery}"
                )
            if len(reasons) > 10:
                lines.append(f"  ... ({len(reasons) - 10} more)")

            recovery_backlog = payload.get("unknown_recovery_backlog") or {}
            if recovery_backlog:
                lines.append("")
                lines.append("UNKNOWN Recovery Proof Backlog:")
                for reason_id, entry in recovery_backlog.items():
                    counts = entry.get("proof_obligation_counts") if isinstance(entry, dict) else None
                    proof_kinds = (
                        ", ".join(counts.keys())
                        if isinstance(counts, dict) and "bounded_evidence" not in counts else ""
                    )
                    if not proof_kinds:
                        proof_kinds = (entry.get("recovery_proof_kind") if isinstance(entry, dict) else None) or "none"
                    lines.append(
                        f"  {reason_id}: count={entry.get('count', 0) if isinstance(entry, dict) else 0}, "
                        f"proofs={proof_kinds}"
                    )
        if payload.get("decision_gated_by_pending_proof"):
            lines.append("")
            lines.append("Decision gated: pending proof obligation blocks EQUIVALENT recovery")
        disposition = payload.get("identical_fast_path_disposition")
        if isinstance(disposition, dict):
            lines.append("")
            lines.append(
                "Identical function identity: applicable={applicable}, "
                "applied={applied}, reason={reason}".format(
                    applicable=disposition.get("applicable"),
                    applied=disposition.get("applied"),
                    reason=disposition.get("reason"),
                )
            )

        lines.append("")

        # パラメータ断片として制約された変数を表示
        fragments = payload.get("constrained_fragments")
        if isinstance(fragments, list) and fragments:
            vars_str = ", ".join(str(item) for item in fragments)
            lines.append(f"Derived fragments: {vars_str}")
            lines.append("  (upper-bits variables constrained via sign/zero extension from parameters)")

        type_fix = payload.get("type_fix_result")
        if isinstance(type_fix, dict) and type_fix_applied(type_fix):
            lines.append(f"Type fix applied: {describe_type_fix(type_fix)}")
        if (payload.get("retry_count") or 0) > 0:
            lines.append(f"Retry count: {payload.get('retry_count')}")

        lines.append("-" * 70)

        canonical_outcome = None
        if self.decision_receipt is not None:
            from scripts.function_tracer_pcode.authority.decision.production_cutover import (
                outcome_from_result,
            )

            canonical_outcome = outcome_from_result(self).value
        elif self.canonical_decision_required:
            raise ValueError("canonical rendering lacks DecisionReceipt")
        error_message = payload.get("error_message")
        failure_status = payload.get("failure_status")
        failure_message = payload.get("failure_message")
        if canonical_outcome == "ERROR" or (
            canonical_outcome is None and error_message
        ):
            lines.append("Result: ERROR")
            if error_message:
                lines.append(f"ERROR: {error_message}")
            if failure_status:
                lines.append(f"Failure status: {failure_status}")
        elif canonical_outcome in {"UNKNOWN", "TIMEOUT"} or (
            canonical_outcome is None and payload.get("is_equivalent") is None
        ):
            if canonical_outcome == "TIMEOUT" or (
                canonical_outcome is None and payload.get("is_timeout")
            ):
                lines.append("Result: TIMEOUT (could not determine equivalence within time limit)")
            else:
                lines.append("Result: UNKNOWN (could not determine equivalence)")
            if failure_status:
                lines.append(f"Failure status: {failure_status}")
            if failure_message:
                lines.append(f"Failure detail: {failure_message}")
        elif canonical_outcome == "EQUIVALENT" or (
            canonical_outcome is None and payload.get("is_equivalent")
        ):
            lines.append("Result: EQUIVALENT ✓")
        else:
            lines.append("Result: NOT EQUIVALENT ✗")
            counterexample = payload.get("counterexample")
            if isinstance(counterexample, dict) and counterexample:
                lines.append("")
                lines.append(format_counterexample_text(counterexample))
            else:
                lines.append("")
                lines.append("(No counterexample available)")

        lines.append("-" * 70)
        lines.append(f"Total time: {float(payload.get('total_time') or 0.0):.3f} seconds")
        stage_line = _format_stage_seconds(getattr(self, "diagnostics", None))
        if stage_line:
            lines.append(stage_line)

        solver_results = payload.get("solver_results")
        if verbose and isinstance(solver_results, dict):
            lines.append("")
            lines.append("Solver Results:")
            for row in solver_results.get("all_results") or ():
                if not isinstance(row, dict):
                    continue
                lines.append(
                    f"  {row.get('solver_name')}: {row.get('status')} "
                    f"({float(row.get('elapsed_time') or 0.0):.3f}s)"
                )
                if row.get("error_message"):
                    lines.append(f"    Error: {row.get('error_message')}")
                if row.get("model"):
                    lines.append(f"    Model: {row.get('model')}")

        if show_phase_usage:
            from scripts.function_tracer_pcode.checker.diagnostics import trace_timings_payload

            phase_rows = trace_timings_payload(self).get("phase_usage")
            if isinstance(phase_rows, list):
                lines.append("")
                lines.append(format_phase_usage_rows(phase_rows))

        lines.append("=" * 70)
        return "\n".join(lines)

