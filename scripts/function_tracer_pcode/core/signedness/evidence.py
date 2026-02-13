# -*- coding: utf-8 -*-
"""符号性証拠データモデル"""

from dataclasses import dataclass, field
from enum import Enum
from typing import List, Dict, Optional, Any


class SignednessType(Enum):
    """符号性の種類"""
    SIGNED = "signed"
    UNSIGNED = "unsigned"
    UNKNOWN = "unknown"


class EvidenceCategory(Enum):
    """証拠のカテゴリ"""
    SIGNED_STRONG = "signed_strong"      # Signed強証拠
    SIGNED_MEDIUM = "signed_medium"      # Signed中証拠
    UNSIGNED = "unsigned"                 # Unsigned証拠
    IGNORED = "ignored"                   # 無視する証拠


# P-codeオペコードと証拠カテゴリのマッピング
OPCODE_EVIDENCE_MAP: Dict[str, EvidenceCategory] = {
    # Signed強証拠
    "INT_SDIV": EvidenceCategory.SIGNED_STRONG,
    "INT_SREM": EvidenceCategory.SIGNED_STRONG,
    "INT_SRIGHT": EvidenceCategory.SIGNED_STRONG,
    "INT_SEXT": EvidenceCategory.SIGNED_STRONG,
    
    # Signed中証拠
    "INT_SLESS": EvidenceCategory.SIGNED_MEDIUM,
    "INT_SLESSEQUAL": EvidenceCategory.SIGNED_MEDIUM,
    
    # Unsigned証拠
    "INT_DIV": EvidenceCategory.UNSIGNED,
    "INT_REM": EvidenceCategory.UNSIGNED,
    "INT_RIGHT": EvidenceCategory.UNSIGNED,
    "INT_LESS": EvidenceCategory.UNSIGNED,
    "INT_LESSEQUAL": EvidenceCategory.UNSIGNED,
    
    # 無視
    "INT_ZEXT": EvidenceCategory.IGNORED,
}

# Phase 2: fast-path 除外対象のオペコード
FASTPATH_UNSIGNED_OPCODES = frozenset({"INT_DIV", "INT_REM", "INT_RIGHT"})


@dataclass
class PcodeEvidence:
    """単一のP-code証拠"""
    opcode: str
    category: EvidenceCategory
    address: Optional[str] = None
    context: Optional[str] = None  # 追加コンテキスト情報
    excluded: bool = False  # Phase 2: fast-path として除外されたか
    exclusion_reason: Optional[str] = None  # Phase 2: 除外理由
    
    def to_dict(self) -> Dict[str, Any]:
        result = {
            "opcode": self.opcode,
            "category": self.category.value,
            "address": self.address,
            "context": self.context,
        }
        if self.excluded:
            result["excluded"] = True
            result["exclusion_reason"] = self.exclusion_reason
        return result


@dataclass
class SignednessEvidence:
    """符号性判定の証拠コレクション（Phase 2対応）"""
    
    # 各カテゴリの証拠リスト
    signed_strong: List[PcodeEvidence] = field(default_factory=list)
    signed_medium: List[PcodeEvidence] = field(default_factory=list)
    unsigned: List[PcodeEvidence] = field(default_factory=list)
    ignored: List[PcodeEvidence] = field(default_factory=list)
    
    # Phase 2: fast-path として除外された証拠
    excluded_fastpath: List[PcodeEvidence] = field(default_factory=list)
    
    # 判定結果
    result: SignednessType = SignednessType.UNKNOWN
    
    def add_evidence(self, evidence: PcodeEvidence) -> None:
        """証拠を追加"""
        if evidence.category == EvidenceCategory.SIGNED_STRONG:
            self.signed_strong.append(evidence)
        elif evidence.category == EvidenceCategory.SIGNED_MEDIUM:
            self.signed_medium.append(evidence)
        elif evidence.category == EvidenceCategory.UNSIGNED:
            self.unsigned.append(evidence)
        elif evidence.category == EvidenceCategory.IGNORED:
            self.ignored.append(evidence)
    
    def add_excluded_fastpath(self, evidence: PcodeEvidence, reason: str) -> None:
        """
        Phase 2: fast-path として除外された証拠を追加
        
        Args:
            evidence: 除外する証拠
            reason: 除外理由
        """
        evidence.excluded = True
        evidence.exclusion_reason = reason
        self.excluded_fastpath.append(evidence)
    
    def determine_signedness(self) -> SignednessType:
        """
        収集した証拠から符号性を判定
        
        Phase 2 判定ルール:
        1. Signed強証拠が1つでもあれば signed
        2. Signed強証拠がなく、fast-path除外後のUnsigned証拠が1つ以上あれば unsigned
        3. それ以外は unknown
        """
        if len(self.signed_strong) > 0:
            self.result = SignednessType.SIGNED
        elif len(self.unsigned) > 0:
            # Phase 2: unsigned証拠があっても、除外されていないものがあるか確認
            # unsigned リストには除外されていない証拠のみ追加されるので、そのまま使用
            self.result = SignednessType.UNSIGNED
        else:
            self.result = SignednessType.UNKNOWN
        
        return self.result
    
    def get_summary(self) -> Dict[str, int]:
        """証拠の件数サマリを取得"""
        return {
            "signed_strong": len(self.signed_strong),
            "signed_medium": len(self.signed_medium),
            "unsigned": len(self.unsigned),
            "ignored": len(self.ignored),
            "excluded_fastpath": len(self.excluded_fastpath),
        }
    
    def get_opcode_counts(self) -> Dict[str, int]:
        """オペコード別の件数を取得"""
        counts: Dict[str, int] = {}
        
        all_evidences = (
            self.signed_strong + 
            self.signed_medium + 
            self.unsigned
        )
        
        for ev in all_evidences:
            counts[ev.opcode] = counts.get(ev.opcode, 0) + 1
        
        return counts
    
    def get_excluded_opcode_counts(self) -> Dict[str, int]:
        """Phase 2: 除外されたオペコード別の件数を取得"""
        counts: Dict[str, int] = {}
        for ev in self.excluded_fastpath:
            counts[ev.opcode] = counts.get(ev.opcode, 0) + 1
        return counts
    
    def has_any_evidence(self) -> bool:
        """何らかの証拠があるかどうか"""
        return (
            len(self.signed_strong) > 0 or
            len(self.signed_medium) > 0 or
            len(self.unsigned) > 0
        )
    
    def to_dict(self) -> Dict[str, Any]:
        """辞書形式に変換"""
        result = {
            "result": self.result.value,
            "summary": self.get_summary(),
            "opcode_counts": self.get_opcode_counts(),
            "signed_strong": [e.to_dict() for e in self.signed_strong],
            "signed_medium": [e.to_dict() for e in self.signed_medium],
            "unsigned": [e.to_dict() for e in self.unsigned],
        }
        
        # Phase 2: 除外情報を追加
        if self.excluded_fastpath:
            result["excluded_fastpath"] = [e.to_dict() for e in self.excluded_fastpath]
            result["excluded_opcode_counts"] = self.get_excluded_opcode_counts()
        
        return result
    
    def format_debug_string(self) -> str:
        """デバッグ用の文字列を生成"""
        lines = []
        lines.append(f"Signedness Result: {self.result.value}")
        lines.append(f"Evidence Summary: {self.get_summary()}")
        
        if self.signed_strong:
            lines.append("  Signed Strong Evidence:")
            for ev in self.signed_strong:
                lines.append(f"    - {ev.opcode} at {ev.address}")
        
        if self.signed_medium:
            lines.append("  Signed Medium Evidence:")
            for ev in self.signed_medium:
                lines.append(f"    - {ev.opcode} at {ev.address}")
        
        if self.unsigned:
            lines.append("  Unsigned Evidence:")
            for ev in self.unsigned:
                lines.append(f"    - {ev.opcode} at {ev.address}")
        
        # Phase 2: 除外された証拠
        if self.excluded_fastpath:
            lines.append("  Excluded Fast-path Evidence:")
            for ev in self.excluded_fastpath:
                lines.append(f"    - {ev.opcode} at {ev.address}: {ev.exclusion_reason}")
        
        return "\n".join(lines)