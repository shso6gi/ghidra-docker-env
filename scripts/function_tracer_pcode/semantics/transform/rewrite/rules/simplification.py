# -*- coding: utf-8 -*-
"""式の簡約ルール"""

from typing import TYPE_CHECKING
from scripts.function_tracer_pcode.semantics.transform.rewrite.rules.base import RewriteRule

if TYPE_CHECKING:
    from scripts.function_tracer_pcode.core import Expression


class DivSimplificationRule(RewriteRule):
    """
    除算の簡約
    - x / 1 → x
    - x / -1 → -x
    """
    
    def __init__(self):
        super().__init__(
            "div_simplification",
            "Simplify x/1 and x/(-1)"
        )
        self.all_div_ops = frozenset(["INT_DIV", "DIV", "INT_SDIV", "SDIV"])
    
    def matches(self, expr: 'Expression') -> bool:
        from scripts.function_tracer_pcode.core import ExpressionType
        
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False
        if expr.operator not in self.all_div_ops:
            return False
        if not expr.operands or len(expr.operands) != 2:
            return False
        
        right = expr.operands[1]
        if right.expr_type != ExpressionType.CONSTANT:
            return False
        
        return right.value == 1 or right.value == -1
    
    def apply(self, expr: 'Expression') -> 'Expression':
        from scripts.function_tracer_pcode.core import Expression
        
        x = expr.operands[0]
        divisor = expr.operands[1].value
        
        if divisor == 1:
            return x
        else:  # divisor == -1
            result = Expression.unary_op("INT_2COMP", x)
            result.size = x.size
            return result