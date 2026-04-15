# -*- coding: utf-8 -*-
"""Condition model separated from Expression."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, TYPE_CHECKING, Mapping

from .storage import StorageInfo

if TYPE_CHECKING:
    from .expression import Expression


class Condition:
    """条件式を表現するクラス"""

    def __init__(self, expression: Optional["Expression"], negated: bool = False):
        if expression is None:
            raise ValueError("Condition expression must not be None")
        self.expression = expression
        self.negated = negated

    def negate(self) -> "Condition":
        return Condition(self.expression, not self.negated)

    def to_string(self) -> str:
        expr_str = self.expression.to_string()
        if self.negated:
            return f"(not {expr_str})"
        return expr_str

    def to_smt(
        self,
        *,
        symbol_name_mapping: Optional[Mapping[str, str]] = None,
    ) -> str:
        expr_smt = self.expression.to_smt(
            symbol_name_mapping=symbol_name_mapping,
        )
        if self.negated:
            return f"(not {expr_smt})"
        return expr_smt

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Condition):
            return False
        return self.equals(other)

    def __hash__(self) -> int:
        return hash(self.structural_key())

    def equals(self, other: "Condition") -> bool:
        """条件が等価かどうかを判定"""
        if not isinstance(other, Condition):
            return False
        return self.structural_key() == other.structural_key()

    def structural_key(self, *, budget: int = 256):
        from .structural import condition_key

        return condition_key(self, budget=budget)

    @classmethod
    def combine_and(cls, conditions: List[Optional["Condition"]]) -> Optional["Condition"]:
        """複数の条件を AND で結合する。"""
        if not conditions:
            return None

        unique: List[Condition] = []
        for cond in conditions:
            if cond is None:
                continue
            is_dup = False
            for existing in unique:
                if cond.equals(existing):
                    is_dup = True
                    break
            if not is_dup:
                unique.append(cond)

        if len(unique) == 0:
            return None
        if len(unique) == 1:
            return unique[0]

        from .expression import Expression

        def to_expr(condition: Condition) -> "Expression":
            if condition.negated:
                return Expression.unary_op("BOOL_NEGATE", condition.expression)
            return condition.expression

        combined = Expression.binary_op("BOOL_AND", to_expr(unique[0]), to_expr(unique[1]))
        for cond in unique[2:]:
            combined = Expression.binary_op("BOOL_AND", combined, to_expr(cond))

        return Condition(combined, False)

    def get_all_variables(self):
        """条件式に含まれる全ての変数名を取得"""
        return self.expression.get_all_variables()

    def get_all_variables_with_storage(self) -> Dict[str, Optional[StorageInfo]]:
        """条件式に含まれる全ての変数名とストレージ情報を取得"""
        return self.expression.get_all_variables_with_storage()

    def to_dict(self) -> Dict[str, Any]:
        """辞書形式に変換"""
        return {
            "expression": self.expression.to_dict(),
            "negated": self.negated,
        }
