# -*- coding: utf-8 -*-
"""符号性証拠データモデル（Phase 2対応）"""

from dataclasses import dataclass, field
from enum import Enum
from typing import List, Dict, Optional, Any, FrozenSet
from itertools import chain

from scripts.function_tracer_pcode.core.json_encoding import Tally, each, inline, materialize, scan


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

# fast-path 除外対象のオペコード（FastPathDetector.TARGET_OPCODESと同期）
FASTPATH_UNSIGNED_OPCODES: FrozenSet[str] = frozenset({
    "INT_DIV", 
    "INT_REM", 
    "INT_RIGHT"
})


@dataclass
class PcodeEvidence:
    """単一のP-code証拠"""
    opcode: str
    category: EvidenceCategory
    address: Optional[str] = None
    context: Optional[str] = None  # 追加コンテキスト情報
    excluded: bool = False  # fast-path として除外されたか
    exclusion_reason: Optional[str] = None  # 除外理由
    
    def json_items(self):
        yield "opcode", self.opcode
        yield "category", self.category.value
        yield "address", self.address
        if self.context:
            yield "context", self.context
        if self.excluded:
            yield "excluded", True
            yield "exclusion_reason", self.exclusion_reason

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass
class SignednessEvidence:
    """符号性判定の証拠コレクション（Phase 2対応）"""
    
    # 各カテゴリの証拠リスト
    signed_strong: List[PcodeEvidence] = field(default_factory=list)
    signed_medium: List[PcodeEvidence] = field(default_factory=list)
    unsigned: List[PcodeEvidence] = field(default_factory=list)
    ignored: List[PcodeEvidence] = field(default_factory=list)
    
    # fast-path として除外された証拠
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
        """fast-path として除外された証拠を追加"""
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
        """オペコード別の件数を取得（除外分は含まない）"""
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
        """除外されたオペコード別の件数を取得"""
        counts: Dict[str, int] = {}
        for ev in self.excluded_fastpath:
            counts[ev.opcode] = counts.get(ev.opcode, 0) + 1
        return counts
    
    def json_items(self):
        # 件数は list の長さ（固定個数）。opcode 別件数は walker が証拠を 1 つずつ数えながら
        # 集計する（`scan`。列を連結・複製しない）
        yield "result", self.result.value
        yield "summary", inline(
            ("signed_strong", len(self.signed_strong)),
            ("signed_medium", len(self.signed_medium)),
            ("unsigned", len(self.unsigned)),
            ("ignored", len(self.ignored)),
            ("excluded_fastpath", len(self.excluded_fastpath)),
        )
        yield "opcode_counts", scan(
            chain(self.signed_strong, self.signed_medium, self.unsigned), Tally("opcode"),
        )
        yield "signed_strong", each(self.signed_strong)
        yield "signed_medium", each(self.signed_medium)
        yield "unsigned", each(self.unsigned)
        if self.excluded_fastpath:
            yield "excluded_fastpath", each(self.excluded_fastpath)
            yield "excluded_opcode_counts", scan(iter(self.excluded_fastpath), Tally("opcode"))

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)
    