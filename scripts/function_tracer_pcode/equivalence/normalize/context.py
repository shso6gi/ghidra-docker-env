# -*- coding: utf-8 -*-
"""正規化コンテキスト（安全性チェック・監査用）"""

from dataclasses import dataclass, field
from typing import Set, List, Optional
from ...model import Expression


@dataclass
class AppliedRule:
    """適用されたルールの記録"""
    rule_name: str
    before_expr: str  # 適用前の式（短縮表示用）
    after_expr: str   # 適用後の式（短縮表示用）
    reason: str       # 適用理由・根拠


@dataclass
class NormalizationContext:
    """
    正規化のコンテキスト（安全性チェック・監査用）
    
    Attributes:
        debug: デバッグモード
        min_excluded_params: MIN除外制約があるパラメータ名のセット
        applied_rules: 適用されたルールのリスト（監査用）
        allow_unsafe: 安全性チェックを無視するか（デフォルト: False）
    """
    debug: bool = False
    min_excluded_params: Set[str] = field(default_factory=set)
    applied_rules: List[AppliedRule] = field(default_factory=list)
    allow_unsafe: bool = False
    
    def is_min_excluded(self, param_name: str) -> bool:
        """パラメータがMIN除外制約を持つか確認"""
        return param_name in self.min_excluded_params
    
    def record_rule(
        self,
        rule_name: str,
        before_expr: Expression,
        after_expr: Expression,
        reason: str
    ) -> None:
        """ルール適用を記録"""
        self.applied_rules.append(AppliedRule(
            rule_name=rule_name,
            before_expr=self._truncate(before_expr.to_smt()),
            after_expr=self._truncate(after_expr.to_smt()),
            reason=reason
        ))
        
        if self.debug:
            print(f"[NormalizationContext] Applied rule: {rule_name}")
            print(f"  Before: {self._truncate(before_expr.to_smt())}")
            print(f"  After:  {self._truncate(after_expr.to_smt())}")
            print(f"  Reason: {reason}")
    
    def _truncate(self, text: str, max_len: int = 100) -> str:
        """文字列を切り詰め"""
        if len(text) <= max_len:
            return text
        return text[:max_len] + "..."
    
    def get_summary(self) -> str:
        """適用されたルールのサマリー"""
        if not self.applied_rules:
            return "No rules applied"
        
        lines = [f"Applied {len(self.applied_rules)} normalization rule(s):"]
        for i, rule in enumerate(self.applied_rules, 1):
            lines.append(f"  {i}. {rule.rule_name}: {rule.reason}")
        return "\n".join(lines)