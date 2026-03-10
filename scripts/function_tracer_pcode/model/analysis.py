# -*- coding: utf-8 -*-
"""関数解析結果のデータモデル"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Any, TYPE_CHECKING

if TYPE_CHECKING:
    from .condition import Condition
    from .expression import Expression
    from ..analysis.signedness import SignednessEvidence


@dataclass
class ReturnInfo:
    """単一のreturn文の情報"""
    address: str
    value: Expression
    conditions: List[Condition] = field(default_factory=list)
    branch_index: Optional[int] = None
    
    def to_dict(self) -> Dict:
        return {
            "address": self.address,
            "value": self.value.to_dict(),
            "conditions": [c.to_dict() for c in self.conditions],
            "branch_index": self.branch_index
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
    
    def to_dict(self) -> Dict:
        result = {
            "function_name": self.function_name,
            "entry_point": self.entry_point,
            "parameters": self.parameters,
            "returns": [r.to_dict() for r in self.returns],
            "return_type": self.return_type,
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
