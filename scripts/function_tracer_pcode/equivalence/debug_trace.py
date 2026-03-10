# -*- coding: utf-8 -*-
"""等価性判定のデバッグトレース（機械可読）"""

from typing import List, Dict, Any, Optional, Tuple
from dataclasses import dataclass, field, asdict
from enum import Enum


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
    solver_results: Optional[Dict[str, Any]] = None
    final_smt_excerpt: Optional[str] = None  # SMT式の先頭500文字（互換性のため残す）
    final_smt: Optional[str] = None  # ★ 新規: 完全なSMT式
    counterexample: Optional[Dict[str, Any]] = None
    pairwise_decisive: Optional[PairwiseDecisiveInfo] = None
    normalization_rules: List[NormalizationRuleApplication] = field(default_factory=list)
    mips64_abi_constraints: Optional[Dict[str, Any]] = None
    elapsed_time: float = 0.0
    
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
            "solver_results": self.solver_results,
            "final_smt_excerpt": self.final_smt_excerpt,
            "final_smt": self.final_smt,  # ★ 追加
            "counterexample": self.counterexample,
            "pairwise_decisive": self.pairwise_decisive.to_dict() if self.pairwise_decisive else None,
            "normalization_rules": [rule.to_dict() for rule in self.normalization_rules],
            "mips64_abi_constraints": self.mips64_abi_constraints,
            "elapsed_time": self.elapsed_time,
        }
        return result


@dataclass
class DebugTrace:
    """デバッグトレース（機械可読）"""
    attempts: List[Attempt] = field(default_factory=list)
    final_result: Optional[bool] = None
    total_time: float = 0.0
    error_message: Optional[str] = None
    
    def add_attempt(self, attempt: Attempt):
        """試行を追加"""
        self.attempts.append(attempt)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "attempts": [attempt.to_dict() for attempt in self.attempts],
            "final_result": self.final_result,
            "total_time": self.total_time,
            "error_message": self.error_message,
            "attempt_count": len(self.attempts),
        }
    
    def to_json_string(self, indent: int = 2) -> str:
        """JSON文字列として出力"""
        import json
        return json.dumps(self.to_dict(), indent=indent)