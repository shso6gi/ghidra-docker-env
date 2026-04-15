# -*- coding: utf-8 -*-
"""関数解析結果のデータモデル"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Any, TYPE_CHECKING

if TYPE_CHECKING:
    from .condition import Condition
    from .expression import Expression
    from ..analysis.signedness import SignednessEvidence
    from ..analysis.effect_summary import EffectSummary

@dataclass
class ReturnInfo:
    """単一のreturn文の情報"""
    address: str
    value: Expression
    conditions: List[Condition] = field(default_factory=list)
    branch_index: Optional[int] = None
    pcode_identity: Optional[str] = None
    pcode_order: Optional[int] = None
    pcode_time: Optional[int] = None

    def site_key(self) -> str:
        """return site の安定識別子を返す。"""
        return self.pcode_identity or self.address
    
    def to_dict(self) -> Dict:
        result = {
            "address": self.address,
            "value": self.value.to_dict(),
            "conditions": [c.to_dict() for c in self.conditions],
            "branch_index": self.branch_index,
        }
        if self.pcode_identity is not None:
            result["pcode_identity"] = self.pcode_identity
        if self.pcode_order is not None:
            result["pcode_order"] = self.pcode_order
        if self.pcode_time is not None:
            result["pcode_time"] = self.pcode_time
        return result


@dataclass
class DeferredCallInfo:
    """解析時に展開できなかった呼び出しサイトの情報。"""

    placeholder_name: str
    target_name: str
    arguments: List["Expression"] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "placeholder_name": self.placeholder_name,
            "target_name": self.target_name,
            "arguments": [arg.to_dict() for arg in self.arguments],
        }

@dataclass
class SignednessResult:
    """符号性推定の結果（軽量版）"""
    signedness: str = "unknown"  # "signed", "unsigned", "unknown"
    evidence_summary: Dict[str, int] = field(default_factory=dict)
    opcode_counts: Dict[str, int] = field(default_factory=dict)
    excluded_fastpath_count: int = 0
    excluded_opcode_counts: Dict[str, int] = field(default_factory=dict)
    
    def is_signed(self) -> bool:
        return self.signedness == "signed"
    
    def is_unsigned(self) -> bool:
        return self.signedness == "unsigned"
    
    def is_unknown(self) -> bool:
        return self.signedness == "unknown"
    
    def should_fix_to_signed(self) -> bool:
        """
        unsigned型をsigned型に修正すべきかどうか
        
        Returns:
            True: signed証拠があるため修正すべき
            False: 修正すべきでない
        """
        return self.is_signed()
    
    def to_dict(self) -> Dict[str, Any]:
        result = {
            "signedness": self.signedness,
            "evidence_summary": self.evidence_summary,
            "opcode_counts": self.opcode_counts,
        }
        if self.excluded_fastpath_count > 0:
            result["excluded_fastpath_count"] = self.excluded_fastpath_count
            result["excluded_opcode_counts"] = self.excluded_opcode_counts
        return result
    
    @classmethod
    def from_evidence(cls, evidence: 'SignednessEvidence') -> 'SignednessResult':
        """SignednessEvidenceから生成（Phase 2対応）"""
        return cls(
            signedness=evidence.result.value,
            evidence_summary=evidence.get_summary(),
            opcode_counts=evidence.get_opcode_counts(),
            excluded_fastpath_count=len(evidence.excluded_fastpath),
            excluded_opcode_counts=evidence.get_excluded_opcode_counts(),
        )

@dataclass
class FunctionReturnAnalysis:
    """関数のreturn値解析結果"""
    function_name: str
    entry_point: str
    parameters: List[Dict]
    returns: List[ReturnInfo]
    return_type: Optional[str] = None
    signedness_result: Optional[SignednessResult] = None
    unknown_event_count: int = 0
    unknown_event_reasons: List[str] = field(default_factory=list)
    analysis_notes: List[str] = field(default_factory=list)
    recovered_from_decompiler: bool = False
    incomplete_control_flow: bool = False
    deferred_calls: Dict[str, DeferredCallInfo] = field(default_factory=dict)
    effect_summary: Optional["EffectSummary"] = None

    def to_dict(self) -> Dict:
        result = {
            "function_name": self.function_name,
            "entry_point": self.entry_point,
            "parameters": self.parameters,
            "returns": [r.to_dict() for r in self.returns],
            "return_type": self.return_type,
            "unknown_event_count": self.unknown_event_count,
            "unknown_event_reasons": list(self.unknown_event_reasons),
            "analysis_notes": list(self.analysis_notes),
            "recovered_from_decompiler": self.recovered_from_decompiler,
            "incomplete_control_flow": self.incomplete_control_flow,
            "deferred_calls": {
                name: info.to_dict()
                for name, info in self.deferred_calls.items()
            },
        }
        
        if self.signedness_result:
            result["signedness"] = self.signedness_result.to_dict()
        
        return result
    
    def get_inferred_signedness(self) -> str:
        """推定された符号性を取得"""
        if self.signedness_result:
            return self.signedness_result.signedness
        return "unknown"
    
    def should_fix_return_to_signed(self) -> bool:
        """
        戻り値の型をsignedに修正すべきかどうか
        
        Returns:
            True: unsigned型だがsigned証拠があるため修正すべき
            False: 修正不要
        """
        if self.signedness_result is None:
            return False
        
        # 戻り値の型がunsigned系の場合のみ修正対象
        if self.return_type:
            type_lower = self.return_type.lower()
            is_unsigned_type = (
                "ulong" in type_lower or
                "uint" in type_lower or
                "unsigned" in type_lower
            )
            if is_unsigned_type and self.signedness_result.should_fix_to_signed():
                return True
        
        return False

    def has_unknown_return(self) -> bool:
        """UNKNOWN 式を含む戻り値候補があるか。"""
        return any(
            getattr(ret.value, "expr_type", None) is not None
            and ret.value.expr_type.name == "UNKNOWN"
            for ret in self.returns
        )

    def _expression_contains_unresolved_value(self, expr) -> bool:
        """式木に solver へ流せない未解決値が残っているかを判定する。"""
        if expr is None:
            return True

        expr_type = getattr(expr, "expr_type", None)
        expr_kind = getattr(expr_type, "__class__", None)
        if expr_type is None or expr_kind is None:
            return True

        if expr_type in {expr_kind.UNKNOWN, expr_kind.CALL}:
            return True

        if expr_type == expr_kind.PHI and expr.value:
            for cond, value in expr.value:
                cond_expr = getattr(cond, "expression", None) if cond is not None else None
                if cond_expr is not None and self._expression_contains_unresolved_value(cond_expr):
                    return True
                if self._expression_contains_unresolved_value(value):
                    return True
            return False

        for operand in getattr(expr, "operands", []) or []:
            if self._expression_contains_unresolved_value(operand):
                return True

        return False

    def has_unresolved_return_value(self) -> bool:
        """ネストした UNKNOWN/CALL を含む戻り値・ガードがあるか。"""
        for ret in self.returns:
            if self._expression_contains_unresolved_value(ret.value):
                return True
            for cond in ret.conditions:
                cond_expr = getattr(cond, "expression", None)
                if cond_expr is not None and self._expression_contains_unresolved_value(cond_expr):
                    return True
        return False

    def _expression_contains_symbolic_post_state_reads(self, expr) -> bool:
        """式木に synthetic post-state read が残っているか。"""
        if expr is None:
            return False

        from ..analysis.effect_summary import (
            expression_contains_synthetic_location_reads,
        )

        return expression_contains_synthetic_location_reads(expr)

    def has_symbolic_post_state_reads(self) -> bool:
        """戻り値・ガードに __locread__ 由来の symbolic post-state read が残っているか。"""
        for ret in self.returns:
            if self._expression_contains_symbolic_post_state_reads(ret.value):
                return True
            for cond in ret.conditions:
                cond_expr = getattr(cond, "expression", None)
                if cond_expr is not None and self._expression_contains_symbolic_post_state_reads(cond_expr):
                    return True
        return False

    def count_unconditional_returns(self) -> int:
        """条件なしの return 候補数を返す。"""
        return sum(1 for ret in self.returns if not ret.conditions)

    def has_overlapping_unconditional_returns(self) -> bool:
        """条件なし return が複数あり、monolithic 化が危険か。"""
        return self.count_unconditional_returns() > 1

    def should_skip_monolithic_fallback(self) -> bool:
        """解析が不完全で monolithic fallback を避けるべきか。"""
        if "return_case_coverage_gap" in self.analysis_notes:
            return True
        if self.recovered_from_decompiler:
            return False
        if not self.incomplete_control_flow:
            return "return_case_coverage_gap" in self.analysis_notes
        return self.has_unresolved_return_value() or self.has_overlapping_unconditional_returns()

    def get_decisive_sat_unsafety_reasons(self) -> List[str]:
        """
        SAT を「非等価の決め手」として扱うには危険な要因を列挙する。

        UNKNOWN へ倒すべき保守条件のみを返し、UNSAT 証明の利用は妨げない。
        """
        reasons: List[str] = []

        if self.has_unresolved_return_value():
            reasons.append("unresolved_return_value")
        if self.has_symbolic_post_state_reads():
            reasons.append("symbolic_post_state_reads")
        if self.has_overlapping_unconditional_returns():
            reasons.append("overlapping_unconditional_returns")
        if self.incomplete_control_flow and not self.recovered_from_decompiler:
            reasons.append("incomplete_control_flow")

        for note in self.analysis_notes:
            if note in {
                "indirect_control_flow_unresolved",
                "symbolic_post_state_reads",
                "return_case_coverage_gap",
            } and note not in reasons:
                reasons.append(note)

        return reasons
