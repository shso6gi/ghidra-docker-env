# -*- coding: utf-8 -*-
"""否定関連の正規化ルール"""

from scripts.function_tracer_pcode.core import Expression, ExpressionType


def normalize_double_negation(expr: Expression) -> Expression:
    """
    二重否定を除去
    
    変形ルール:
        bvneg(bvneg(x)) -> x
    
    これは常に安全な変形（意味論保存）
    
    Args:
        expr: 正規化対象の式
    
    Returns:
        正規化された式
    """
    if expr.expr_type != ExpressionType.UNARY_OP:
        return expr
    
    if expr.operator != "INT_2COMP":
        return expr
    
    if not expr.operands:
        return expr
    
    inner = expr.operands[0]
    
    # 内側も INT_2COMP (bvneg) かチェック
    if inner.expr_type == ExpressionType.UNARY_OP and inner.operator == "INT_2COMP":
        if inner.operands:
            # bvneg(bvneg(x)) -> x
            return inner.operands[0]
    
    return expr