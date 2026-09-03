# -*- coding: utf-8 -*-
"""式の正規化ルール

SMTソルバーの負荷を軽減するため、構文的に異なるが意味的に等価な式を
統一的な形式に変換する
"""

from typing import Any, List, TYPE_CHECKING
from scripts.function_tracer_pcode.semantics.transform.rewrite.rules.base import RewriteRule

if TYPE_CHECKING:
    from scripts.function_tracer_pcode.core import Expression


class CommutativeNormalizationRule(RewriteRule):
    """
    可換・結合演算の正規化ルール
    
    目的：
        式の構文差を吸収してSMTソルバーの負荷を軽減
        - 加算の順序差: (a+b)+c vs (a+c)+b
        - 乗算の順序差: (x*y)*z vs (y*x)*z
        - ビット演算の順序差: (a&b)&c vs (a&c)&b
    
    方法：
        1. 同じ演算子のネストをフラット化 → [a, b, c, ...]
        2. オペランドをSMT表現の辞書順でソート
        3. 左結合の二分木として再構築 → ((a+b)+c)+...
    
    根拠：
        可換律・結合律より、演算結果は順序に依存しない
        SMT-LIBでは構文的に異なる式は異なるものとして扱われるため、
        事前に正規化することでソルバーの証明が容易になる
    """
    
    COMMUTATIVE_ASSOCIATIVE_OPS = frozenset([
        "INT_ADD", "ADD", "+",
        "INT_MULT", "MULT", "*",
        "INT_AND", "AND", "&",
        "INT_OR", "OR", "|",
        "INT_XOR", "XOR", "^"
    ])
    
    def __init__(self):
        super().__init__(
            "commutative_normalization",
            "Normalize commutative operations by sorting operands"
        )
    
    def matches(self, expr: 'Expression') -> bool:
        from scripts.function_tracer_pcode.core import ExpressionType
        
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False
        if expr.operator is None or expr.operator not in self.COMMUTATIVE_ASSOCIATIVE_OPS:
            return False
        if not expr.operands or len(expr.operands) != 2:
            return False
        
        return True
    
    def apply(self, expr: 'Expression') -> 'Expression':
        from scripts.function_tracer_pcode.core import Expression
        
        if expr.operator is None:
            return expr
        
        operator: str = expr.operator
        
        # 1. フラット化
        operands = self._flatten(expr, operator)
        
        # 2. ソート
        sorted_operands = sorted(operands, key=self._get_sort_key)
        
        # 3. 変更不要かチェック
        if sorted_operands == operands:
            return expr
        
        # 4. 再構築
        if len(sorted_operands) == 0:
            return expr
        elif len(sorted_operands) == 1:
            return sorted_operands[0]
        else:
            result = sorted_operands[0]
            for operand in sorted_operands[1:]:
                result = Expression.binary_op(operator, result, operand)
                result.size = expr.size
            return result
    
    def _get_sort_key(self, expr: 'Expression'):
        """ソート用の structural key を取得する。"""
        from scripts.function_tracer_pcode.core import expression_key_or_identity

        if hasattr(expr, "structural_key") and callable(getattr(expr, "structural_key")):
            try:
                return expression_key_or_identity(
                    expr,
                    normalize_commutative=True,
                    strip_width_adapters=True,
                    collapse_full_masks=True,
                    include_memory_read_order=False,
                )
            except Exception:
                pass
        return self._opaque_structural_sort_key(expr)

    def _opaque_structural_sort_key(self, expr: 'Expression'):
        expr_type = getattr(getattr(expr, "expr_type", None), "name", None)
        operands = tuple(self._opaque_structural_sort_key(op) for op in (getattr(expr, "operands", None) or []))
        return (
            "opaque_expr",
            expr_type,
            getattr(expr, "operator", None),
            int(getattr(expr, "size", 0) or 0),
            self._opaque_atom_key(getattr(expr, "value", None)),
            getattr(expr, "name", None),
            operands,
        )

    @staticmethod
    def _opaque_atom_key(value: Any):
        if value is None:
            return ("none",)
        if isinstance(value, bool):
            return ("bool", int(value))
        if isinstance(value, int):
            return ("int", value)
        if isinstance(value, str):
            return ("str", value)
        return ("object_type", type(value).__name__)
    
    def _flatten(self, expr: 'Expression', target_op: str) -> List['Expression']:
        """同じ演算子のネストをフラット化"""
        from scripts.function_tracer_pcode.core import ExpressionType
        
        if expr.expr_type != ExpressionType.BINARY_OP:
            return [expr]
        if expr.operator != target_op:
            return [expr]
        if not expr.operands or len(expr.operands) != 2:
            return [expr]
        
        result: List['Expression'] = []
        for operand in expr.operands:
            result.extend(self._flatten(operand, target_op))
        
        return result


class ShiftConstantNormalizationRule(RewriteRule):
    """
    シフト演算の右辺定数のビット幅を正規化
    
    目的：
        シフト量の表現差を吸収
        - clang: x >> (_ bv63 64)  # 64-bit定数
        - gcc:   x >> (_ zero_extend 32) (_ bv63 32)  # 32-bit定数を拡張
    
    方法：
        右オペランドが定数の場合、左オペランドと同じビット幅に統一
    
    根拠：
        シフト量は通常、元のビット幅内の値（0～n-1）
        定数のビット幅が異なってもセマンティクスは同じ
        SMT-LIBでは型が厳密なため、事前に統一する
    """
    
    SHIFT_OPS = frozenset(["INT_LEFT", "INT_RIGHT", "INT_SRIGHT"])
    
    def __init__(self):
        super().__init__(
            "shift_constant_normalization",
            "Normalize shift amount constant to match operand bit width"
        )
    
    def matches(self, expr: 'Expression') -> bool:
        from scripts.function_tracer_pcode.core import ExpressionType
        
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False
        if expr.operator is None or expr.operator not in self.SHIFT_OPS:
            return False
        if not expr.operands or len(expr.operands) != 2:
            return False
        
        left = expr.operands[0]
        right = expr.operands[1]
        
        if right.expr_type != ExpressionType.CONSTANT:
            return False
        
        return left.size != right.size
    
    def apply(self, expr: 'Expression') -> 'Expression':
        from scripts.function_tracer_pcode.core import Expression
        
        if expr.operator is None:
            return expr
        
        left = expr.operands[0]
        right = expr.operands[1]
        
        normalized_right = Expression.constant(right.value, size=left.size)
        
        result = Expression.binary_op(expr.operator, left, normalized_right)
        result.size = expr.size
        
        return result
