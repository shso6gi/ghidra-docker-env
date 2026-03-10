# -*- coding: utf-8 -*-
"""正規化コンテキスト"""

from typing import Set, Optional, List
from dataclasses import dataclass, field


@dataclass
class RuleApplication:
    """正規化ルール適用記録"""
    rule_name: str
    reason: str
    before_expr: Optional[str] = None
    after_expr: Optional[str] = None


@dataclass
class NormalizationContext:
    """
    正規化コンテキスト
    
    正規化時の安全性チェック情報と監査ログを保持
    """
    debug: bool = False
    min_excluded_params: Set[str] = field(default_factory=set)
    nonneg_vars: Set[str] = field(default_factory=set)
    pos_vars: Set[str] = field(default_factory=set)
    neg_vars: Set[str] = field(default_factory=set)
    nonzero_vars: Set[str] = field(default_factory=set)
    allow_unsafe: bool = False
    
    # ★ 新規追加: 適用されたルールを記録
    applied_rules: List[RuleApplication] = field(default_factory=list)
    
    def record_rule(
        self,
        rule_name: str,
        reason: str,
        before_expr: Optional[str] = None,
        after_expr: Optional[str] = None
    ):
        """ルール適用を記録"""
        self.applied_rules.append(RuleApplication(
            rule_name=rule_name,
            reason=reason,
            before_expr=before_expr,
            after_expr=after_expr
        ))
        
        if self.debug:
            print(f"[Normalize] Applied: {rule_name} ({reason})")