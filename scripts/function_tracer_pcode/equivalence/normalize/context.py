# -*- coding: utf-8 -*-
"""正規化コンテキスト"""

from typing import Dict, Set, Optional, List, Union
from dataclasses import dataclass, field

from ...model import Expression, StructuralKey, expression_key_or_identity


ExpressionAuditValue = Optional[Union[str, Expression]]


@dataclass
class RuleApplication:
    """正規化ルール適用記録"""
    rule_name: str
    reason: str
    before_expr: ExpressionAuditValue = None
    after_expr: ExpressionAuditValue = None


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
    nonneg_exprs: Set[StructuralKey] = field(default_factory=set)
    pos_exprs: Set[StructuralKey] = field(default_factory=set)
    neg_exprs: Set[StructuralKey] = field(default_factory=set)
    nonzero_exprs: Set[StructuralKey] = field(default_factory=set)
    upper_bounds: Dict[str, int] = field(default_factory=dict)
    allow_unsafe: bool = False
    
    # ★ 新規追加: 適用されたルールを記録
    applied_rules: List[RuleApplication] = field(default_factory=list)

    def is_min_excluded(self, var_name: str) -> bool:
        """MIN値除外制約があるか"""
        return var_name in self.min_excluded_params

    def is_nonneg(self, var_name: str) -> bool:
        """非負が保証されるか"""
        return var_name in self.nonneg_vars or var_name in self.pos_vars

    def is_pos(self, var_name: str) -> bool:
        """正が保証されるか"""
        return var_name in self.pos_vars

    def is_neg(self, var_name: str) -> bool:
        """負が保証されるか"""
        return var_name in self.neg_vars

    def is_nonzero(self, var_name: str) -> bool:
        """ゼロでないことが保証されるか"""
        return (
            var_name in self.nonzero_vars
            or var_name in self.pos_vars
            or var_name in self.neg_vars
        )

    def is_expr_nonneg(self, expr) -> bool:
        """式が非負と保証されるか"""
        key = self._expr_key(expr)
        if key in self.nonneg_exprs or key in self.pos_exprs:
            return True
        var_name = getattr(expr, "name", None)
        return bool(var_name) and self.is_nonneg(var_name)

    def is_expr_pos(self, expr) -> bool:
        """式が正と保証されるか"""
        key = self._expr_key(expr)
        if key in self.pos_exprs:
            return True
        var_name = getattr(expr, "name", None)
        return bool(var_name) and self.is_pos(var_name)

    def is_expr_neg(self, expr) -> bool:
        """式が負と保証されるか"""
        key = self._expr_key(expr)
        if key in self.neg_exprs:
            return True
        var_name = getattr(expr, "name", None)
        return bool(var_name) and self.is_neg(var_name)

    def is_expr_nonzero(self, expr) -> bool:
        """式が非ゼロと保証されるか"""
        key = self._expr_key(expr)
        if key in self.nonzero_exprs or key in self.pos_exprs or key in self.neg_exprs:
            return True
        var_name = getattr(expr, "name", None)
        return bool(var_name) and self.is_nonzero(var_name)

    def get_upper_bound(self, var_name: str) -> Optional[int]:
        """変数の既知の上限（排他的）を取得"""
        return self.upper_bounds.get(var_name)

    def has_upper_bound_le(self, var_name: str, bound: int) -> bool:
        """変数の上限が指定値以下と分かっているか"""
        actual = self.get_upper_bound(var_name)
        return actual is not None and actual <= bound

    def record_rule(
        self,
        rule_name: str,
        reason: str,
        before_expr: ExpressionAuditValue = None,
        after_expr: ExpressionAuditValue = None
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

    def _expr_key(self, expr) -> StructuralKey:
        if expr is None:
            return ("none",)
        return expression_key_or_identity(
            expr,
            normalize_commutative=True,
            strip_width_adapters=True,
            collapse_full_masks=True,
            include_memory_read_order=False,
        )
