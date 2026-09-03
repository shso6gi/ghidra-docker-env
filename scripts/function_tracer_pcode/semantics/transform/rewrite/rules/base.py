# -*- coding: utf-8 -*-
"""リライトルールの基底クラスとデータ構造"""

from typing import List, Tuple, TYPE_CHECKING
from abc import ABC, abstractmethod
from dataclasses import dataclass, field

if TYPE_CHECKING:
    from scripts.function_tracer_pcode.core import Expression


@dataclass
class RewriteResult:
    """リライト結果"""
    expression: 'Expression'
    was_rewritten: bool
    history: List[Tuple[str, str, str]] = field(default_factory=list)
    
    def get_summary(self) -> str:
        """リライトの概要を取得"""
        if not self.was_rewritten:
            return "No rewrite applied"
        
        lines = [f"Applied {len(self.history)} rewrite(s):"]
        for rule_name, before, after in self.history:
            lines.append(f"  [{rule_name}] {before} -> {after}")
        return "\n".join(lines)


class RewriteRule(ABC):
    """リライトルールの抽象基底クラス"""
    
    def __init__(self, name: str, description: str):
        self.name = name
        self.description = description
    
    @abstractmethod
    def matches(self, expr: 'Expression') -> bool:
        """式がこのルールにマッチするかチェック"""
        pass
    
    @abstractmethod
    def apply(self, expr: 'Expression') -> 'Expression':
        """ルールを適用して新しい式を返す"""
        pass