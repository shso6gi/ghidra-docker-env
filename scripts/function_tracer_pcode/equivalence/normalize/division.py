# -*- coding: utf-8 -*-
"""除算関連の正規化ルール"""

from ...model import Expression, ExpressionType


def normalize_division_signs(expr: Expression) -> Expression:
    """
    除算の符号を正規化
    
    変形ルール（UB除���制約が前提）：
        1. bvneg(bvsdiv(bvneg(a), b)) -> bvsdiv(a, b)
        2. bvneg(bvsdiv(a, bvneg(b))) -> bvsdiv(a, b)
        3. bvsdiv(bvneg(a), bvneg(b)) -> bvsdiv(a, b)
    
    数学的根拠：
        -((-a)/b) = a/b
        -(a/(-b)) = a/b
        (-a)/(-b) = a/b
    
    注意：
        - a == MIN または b == MIN の場合、Cでは未定義動作
        - しかし、SMTではUB除外制約（param != MIN）が既に入っているため安全
    
    Args:
        expr: 正規化対象の式
    
    Returns:
        正規化された式
    """
    # Case 1 & 2: bvneg(bvsdiv(...)) パターン
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "INT_2COMP":
        result = _normalize_negated_division(expr)
        if result is not expr:
            return result
    
    # Case 3: bvsdiv(bvneg(a), bvneg(b)) パターン
    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_SDIV":
        result = _normalize_double_negated_division(expr)
        if result is not expr:
            return result
    
    return expr


def _normalize_negated_division(expr: Expression) -> Expression:
    """
    bvneg(bvsdiv(...)) の正規化
    
    Case 1: bvneg(bvsdiv(bvneg(a), b)) -> bvsdiv(a, b)
    Case 2: bvneg(bvsdiv(a, bvneg(b))) -> bvsdiv(a, b)
    """
    if not expr.operands:
        return expr
    
    inner = expr.operands[0]
    
    # 内側が bvsdiv かチェック
    if inner.expr_type != ExpressionType.BINARY_OP or inner.operator != "INT_SDIV":
        return expr
    
    if len(inner.operands) < 2:
        return expr
    
    dividend = inner.operands[0]
    divisor = inner.operands[1]
    
    # Case 1: bvneg(bvsdiv(bvneg(a), b)) -> bvsdiv(a, b)
    if _is_negation(dividend):
        if dividend.operands:
            unwrapped_dividend = dividend.operands[0]
            return Expression(
                expr_type=ExpressionType.BINARY_OP,
                operator="INT_SDIV",
                operands=[unwrapped_dividend, divisor],
                size=expr.size
            )
    
    # Case 2: bvneg(bvsdiv(a, bvneg(b))) -> bvsdiv(a, b)
    if _is_negation(divisor):
        if divisor.operands:
            unwrapped_divisor = divisor.operands[0]
            return Expression(
                expr_type=ExpressionType.BINARY_OP,
                operator="INT_SDIV",
                operands=[dividend, unwrapped_divisor],
                size=expr.size
            )
    
    return expr


def _normalize_double_negated_division(expr: Expression) -> Expression:
    """
    bvsdiv(bvneg(a), bvneg(b)) -> bvsdiv(a, b)
    """
    if len(expr.operands) < 2:
        return expr
    
    dividend = expr.operands[0]
    divisor = expr.operands[1]
    
    # 両方が bvneg かチェック
    if _is_negation(dividend) and _is_negation(divisor):
        if dividend.operands and divisor.operands:
            unwrapped_dividend = dividend.operands[0]
            unwrapped_divisor = divisor.operands[0]
            return Expression(
                expr_type=ExpressionType.BINARY_OP,
                operator="INT_SDIV",
                operands=[unwrapped_dividend, unwrapped_divisor],
                size=expr.size
            )
    
    return expr


def _is_negation(expr: Expression) -> bool:
    """式が INT_2COMP (bvneg) かチェック"""
    return (expr.expr_type == ExpressionType.UNARY_OP and 
            expr.operator == "INT_2COMP")