# -*- coding: utf-8 -*-
"""Unknown発生イベントの追跡・記録モジュール"""

from dataclasses import dataclass
from typing import Optional, List, Any
from enum import Enum, auto


class UnknownReason(Enum):
    """Unknown発生理由の分類"""
    # トレース制限
    MAX_DEPTH_EXCEEDED = auto()
    CIRCULAR_REFERENCE = auto()
    
    # PHI関連
    PHI_SELF_REFERENCE = auto()
    PHI_CIRCULAR = auto()
    PHI_NO_PARENT = auto()
    PHI_NO_VALID_BRANCH = auto()
    
    # Varnode関連
    NULL_VARNODE = auto()
    UNIQUE_UNTRACED = auto()
    UNTRACED_VARNODE = auto()
    
    # PcodeOp関連
    UNSUPPORTED_OPCODE = auto()
    INSUFFICIENT_INPUTS = auto()
    NO_OUTPUT = auto()
    
    # その他
    OTHER = auto()
    
    @classmethod
    def from_string(cls, reason: str) -> 'UnknownReason':
        """文字列から列挙型に変換"""
        mapping = {
            "null": cls.NULL_VARNODE,
            "max_depth_exceeded": cls.MAX_DEPTH_EXCEEDED,
            "circular_reference": cls.CIRCULAR_REFERENCE,
            "phi_self_reference": cls.PHI_SELF_REFERENCE,
            "phi_circular": cls.PHI_CIRCULAR,
            "phi_no_parent": cls.PHI_NO_PARENT,
            "phi_no_valid_branch": cls.PHI_NO_VALID_BRANCH,
        }
        
        # 部分一致でチェック
        reason_lower = reason.lower()
        for key, value in mapping.items():
            if key in reason_lower:
                return value
        
        if "unique_" in reason_lower:
            return cls.UNIQUE_UNTRACED
        if "untraced_" in reason_lower:
            return cls.UNTRACED_VARNODE
        if "_no_input" in reason_lower or "_insufficient_inputs" in reason_lower:
            return cls.INSUFFICIENT_INPUTS
        if "_no_output" in reason_lower:
            return cls.NO_OUTPUT
        if "unhandled_" in reason_lower:
            return cls.UNSUPPORTED_OPCODE
        
        return cls.OTHER


@dataclass
class VarnodeInfo:
    """Varnode情報のスナップショット"""
    space: str
    offset: int
    size: int
    is_constant: bool
    is_register: bool
    is_unique: bool
    is_input: bool
    high_var_name: Optional[str] = None
    
    def __str__(self):
        parts = [f"{self.space}:0x{self.offset:x}"]
        if self.size:
            parts.append(f"size={self.size}")
        
        flags = []
        if self.is_constant:
            flags.append("const")
        if self.is_register:
            flags.append("reg")
        if self.is_unique:
            flags.append("unique")
        if self.is_input:
            flags.append("input")
        
        if flags:
            parts.append(f"({','.join(flags)})")
        
        if self.high_var_name:
            parts.append(f"'{self.high_var_name}'")
        
        return " ".join(parts)
    
    @classmethod
    def from_varnode(cls, varnode) -> Optional['VarnodeInfo']:
        """GhidraのVarnodeから情報を抽出"""
        if varnode is None:
            return None
        
        try:
            addr = varnode.getAddress()
            high_var = varnode.getHigh()
            high_name = high_var.getName() if high_var else None
            
            return cls(
                space=str(addr.getAddressSpace().getName()),
                offset=varnode.getOffset(),
                size=varnode.getSize(),
                is_constant=varnode.isConstant(),
                is_register=varnode.isRegister(),
                is_unique=varnode.isUnique(),
                is_input=varnode.isInput(),
                high_var_name=high_name if high_name != "UNNAMED" else None
            )
        except Exception:
            return None


@dataclass
class PcodeOpInfo:
    """PcodeOp情報のスナップショット"""
    mnemonic: str
    seqnum_addr: Optional[str]
    seqnum_order: Optional[int]
    num_inputs: int
    
    def __str__(self):
        if self.seqnum_addr and self.seqnum_order is not None:
            return f"{self.mnemonic} @{self.seqnum_addr}:{self.seqnum_order}"
        return f"{self.mnemonic} (inputs={self.num_inputs})"
    
    @classmethod
    def from_pcodeop(cls, pcode_op) -> Optional['PcodeOpInfo']:
        """GhidraのPcodeOpから情報を抽出"""
        if pcode_op is None:
            return None
        
        try:
            seq = pcode_op.getSeqnum()
            seq_addr = str(seq.getTarget()) if seq else None
            seq_order = seq.getOrder() if seq else None
            
            return cls(
                mnemonic=pcode_op.getMnemonic(),
                seqnum_addr=seq_addr,
                seqnum_order=seq_order,
                num_inputs=pcode_op.getNumInputs()
            )
        except Exception:
            return None


@dataclass
class UnknownEvent:
    """Unknown発生イベント"""
    reason: UnknownReason
    reason_str: str
    depth: int
    varnode: Optional[VarnodeInfo]
    def_op: Optional[PcodeOpInfo]
    note: Optional[str] = None
    context: Optional[str] = None  # "tracer" / "phi_handler" など
    
    def format_detail(self, indent: int = 0) -> str:
        """詳細を整形"""
        prefix = "  " * indent
        lines = [
            f"{prefix}[UNKNOWN EVENT] {self.reason.name}",
            f"{prefix}  Reason: {self.reason_str}",
            f"{prefix}  Depth: {self.depth}",
        ]
        
        if self.context:
            lines.append(f"{prefix}  Context: {self.context}")
        
        if self.varnode:
            lines.append(f"{prefix}  Varnode: {self.varnode}")
        
        if self.def_op:
            lines.append(f"{prefix}  Def Op: {self.def_op}")
        
        if self.note:
            lines.append(f"{prefix}  Note: {self.note}")
        
        return "\n".join(lines)


class UnknownTracker:
    """Unknown発生を追跡・集計"""
    
    def __init__(self):
        self.events: List[UnknownEvent] = []
        self.enabled = False
    
    def enable(self):
        self.enabled = True
    
    def disable(self):
        self.enabled = False
    
    def record(self, event: UnknownEvent):
        """イベントを記録"""
        if self.enabled:
            self.events.append(event)
    
    def clear(self):
        """記録をクリア"""
        self.events.clear()
    
    def get_summary(self) -> str:
        """サマリーを取得"""
        if not self.events:
            return "No unknown events recorded."
        
        # 理由別に集計
        reason_counts = {}
        for event in self.events:
            key = event.reason
            reason_counts[key] = reason_counts.get(key, 0) + 1
        
        lines = [
            f"Total unknown events: {len(self.events)}",
            "Breakdown by reason:"
        ]
        
        for reason, count in sorted(reason_counts.items(), key=lambda x: -x[1]):
            lines.append(f"  {reason.name}: {count}")
        
        return "\n".join(lines)
    
    def get_detailed_report(self) -> str:
        """詳細レポートを取得"""
        if not self.events:
            return "No unknown events recorded."
        
        lines = [
            "=" * 70,
            f"UNKNOWN EVENT DETAILED REPORT ({len(self.events)} events)",
            "=" * 70,
        ]
        
        for i, event in enumerate(self.events):
            lines.append(f"\n--- Event {i + 1}/{len(self.events)} ---")
            lines.append(event.format_detail(indent=0))
        
        lines.append("\n" + "=" * 70)
        lines.append(self.get_summary())
        lines.append("=" * 70)
        
        return "\n".join(lines)
    
    def filter_by_reason(self, reason: UnknownReason) -> List[UnknownEvent]:
        """特定の理由のイベントのみ抽出"""
        return [e for e in self.events if e.reason == reason]
    
    def filter_phi_related(self) -> List[UnknownEvent]:
        """PHI関連のイベントのみ抽出"""
        phi_reasons = {
            UnknownReason.PHI_SELF_REFERENCE,
            UnknownReason.PHI_CIRCULAR,
            UnknownReason.PHI_NO_PARENT,
            UnknownReason.PHI_NO_VALID_BRANCH,
        }
        return [e for e in self.events if e.reason in phi_reasons]