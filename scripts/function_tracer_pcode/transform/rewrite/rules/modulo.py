# -*- coding: utf-8 -*-
"""剰余演算の正規化ルール"""

from typing import Optional, Tuple, TYPE_CHECKING
from .base import RewriteRule

if TYPE_CHECKING:
    from ....model import Expression


class ModuloExpansionRule(RewriteRule):
    """
    剰余の展開形式を剰余演算子に変換するルール
    
    パターン: (a - ((a / b) * b))
    変換先: (a % b)
    
    数学的根拠:
        整数除算の定義より、a = (a / b) * b + (a % b)
        したがって、a % b = a - (a / b) * b
    
    注意点:
        - 符号付き除算(SDIV/INT_SDIV)の場合は符号付き剰余(SREM/INT_SREM)に変換
        - 符号なし除算(DIV/INT_DIV)の場合は符号なし剰余(REM/INT_REM)に変換
        - オーバーフローの挙動は除算と剰余で一致するため変換は安全
    """
    
    def __init__(self):
        super().__init__(
            "modulo_expansion",
            "Convert (a - ((a / b) * b)) to (a % b)"
        )
        
        self.signed_div_ops = frozenset({"INT_SDIV", "SDIV", "//"})
        self.unsigned_div_ops = frozenset({"INT_DIV", "DIV", "/"})
        self.all_div_ops = self.signed_div_ops | self.unsigned_div_ops
        self.mult_ops = frozenset({"INT_MULT", "MULT", "*"})
        self.sub_ops = frozenset({"INT_SUB", "SUB", "-"})
    
    def matches(self, expr: 'Expression') -> bool:
        from ....model import ExpressionType
        
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False
        if expr.operator is None or expr.operator not in self.sub_ops:
            return False
        if not expr.operands or len(expr.operands) != 2:
            return False
        
        a = expr.operands[0]
        mult_expr = expr.operands[1]
        
        if mult_expr.expr_type != ExpressionType.BINARY_OP:
            return False
        if mult_expr.operator is None or mult_expr.operator not in self.mult_ops:
            return False
        if not mult_expr.operands or len(mult_expr.operands) != 2:
            return False
        
        div_expr, b_in_mult = self._extract_div_and_operand(mult_expr)
        
        if div_expr is None or b_in_mult is None:
            return False
        if not div_expr.operands or len(div_expr.operands) != 2:
            return False
        
        a_in_div = div_expr.operands[0]
        b_in_div = div_expr.operands[1]
        
        if not self._expressions_structurally_equal(a, a_in_div):
            return False
        if not self._expressions_structurally_equal(b_in_mult, b_in_div):
            return False
        
        return True
    
    def _extract_div_and_operand(self, mult_expr: 'Expression') -> Tuple[Optional['Expression'], Optional['Expression']]:
        from ....model import ExpressionType
        
        for i, op in enumerate(mult_expr.operands):
            if (
                op.expr_type == ExpressionType.BINARY_OP
                and op.operator is not None
                and op.operator in self.all_div_ops
            ):
                return op, mult_expr.operands[1 - i]
        return None, None
    
    def _expressions_structurally_equal(self, expr1: 'Expression', expr2: 'Expression') -> bool:
        try:
            return expr1.to_smt() == expr2.to_smt()
        except:
            return expr1.to_string() == expr2.to_string()
    
    def apply(self, expr: 'Expression') -> 'Expression':
        from ....model import Expression
        
        a = expr.operands[0]
        mult_expr = expr.operands[1]
        
        div_expr, b = self._extract_div_and_operand(mult_expr)
        
        if div_expr is None or b is None or div_expr.operator is None:
            return expr
        
        if div_expr.operator in self.signed_div_ops:
            mod_operator = "INT_SREM"
        else:
            mod_operator = "INT_REM"
        
        result = Expression.binary_op(mod_operator, a, b)
        result.size = expr.size if hasattr(expr, 'size') else 4
        return result


class ModuloToExpansionRule(RewriteRule):
    """
    剰余演算子を展開形式に変換するルール（逆方向）
    
    パターン: (a % b) または INT_SREM(a, b) / INT_REM(a, b)
    変換先: (a - ((a / b) * b))
    
    用途: G3形式をG1形式に変換する場合に使用
    
    注意: 通常はModuloExpansionRule（逆方向）を使用するため、
          このルールはデフォルトでは無効
    """
    
    def __init__(self):
        super().__init__(
            "modulo_to_expansion",
            "Convert (a % b) to (a - ((a / b) * b))"
        )
        
        self.signed_mod_ops = frozenset({"INT_SREM", "SREM"})
        self.unsigned_mod_ops = frozenset({"INT_REM", "REM", "%"})
        self.all_mod_ops = self.signed_mod_ops | self.unsigned_mod_ops
    
    def matches(self, expr: 'Expression') -> bool:
        from ....model import ExpressionType
        
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False
        if expr.operator not in self.all_mod_ops:
            return False
        if not expr.operands or len(expr.operands) != 2:
            return False
        
        return True
    
    def apply(self, expr: 'Expression') -> 'Expression':
        from ....model import Expression
        
        a = expr.operands[0]
        b = expr.operands[1]
        
        if expr.operator in self.signed_mod_ops:
            div_operator = "INT_SDIV"
        else:
            div_operator = "INT_DIV"
        
        div_expr = Expression.binary_op(div_operator, a, b)
        div_expr.size = expr.size if hasattr(expr, 'size') else 4
        
        mult_expr = Expression.binary_op("INT_MULT", div_expr, b)
        mult_expr.size = expr.size if hasattr(expr, 'size') else 4
        
        result = Expression.binary_op("INT_SUB", a, mult_expr)
        result.size = expr.size if hasattr(expr, 'size') else 4
        
        return result