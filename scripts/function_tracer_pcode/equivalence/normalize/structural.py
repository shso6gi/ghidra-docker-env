# -*- coding: utf-8 -*-
"""構造的同一性チェック（Stage3ショートカット用）"""

from typing import Tuple
from ...model import Expression, ExpressionType


def are_structurally_equivalent(
    expr1: Expression,
    expr2: Expression,
    debug: bool = False
) -> Tuple[bool, str]:
    """
    2つの式が構造的に同一か判定（サフィックス非依存版）
    
    判定条件（保守的）:
    - expr_type, operator が一致
    - PARAMETER/VARIABLE は name が完全一致
    - CONSTANT は value が一致
    - UNARY/BINARY は再帰的にオペランドも一致
    
    注意:
        Expression レベルでは param_1 のような元名のみが存在。
        param_1_1 / param_1_2 はSMT生成時の置換結果であり、
        構造的比較では関知しない。
    
    Args:
        expr1: 式1
        expr2: 式2
        debug: デバッグ出力
    
    Returns:
        (is_equivalent, reason)
    """
    # 型が異なれば不一致
    if expr1.expr_type != expr2.expr_type:
        return False, f"Different expr_type: {expr1.expr_type} vs {expr2.expr_type}"
    
    # CONSTANT: 値が一致すればOK
    if expr1.expr_type == ExpressionType.CONSTANT:
        if expr1.value == expr2.value:
            return True, f"Same constant: {expr1.value}"
        else:
            return False, f"Different constant: {expr1.value} vs {expr2.value}"
    
    # PARAMETER/VARIABLE: 名前が完全一致すればOK
    if expr1.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE):
        name1 = expr1.name or ""
        name2 = expr2.name or ""
        
        if name1 == name2:
            return True, f"Same param/var: {name1}"
        else:
            return False, f"Different param/var: {name1} vs {name2}"
    
    # UNARY_OP: operator一致 + operand再帰チェック
    if expr1.expr_type == ExpressionType.UNARY_OP:
        if expr1.operator != expr2.operator:
            return False, f"Different unary operator: {expr1.operator} vs {expr2.operator}"
        
        if not expr1.operands or not expr2.operands:
            return False, "Missing operands in unary op"
        
        is_eq, reason = are_structurally_equivalent(
            expr1.operands[0], 
            expr2.operands[0],
            debug
        )
        
        if is_eq:
            return True, f"Same unary structure: {expr1.operator}({reason})"
        else:
            return False, f"Different unary operand: {reason}"
    
    # BINARY_OP: operator一致 + 両operand再帰チェック
    if expr1.expr_type == ExpressionType.BINARY_OP:
        if expr1.operator != expr2.operator:
            return False, f"Different binary operator: {expr1.operator} vs {expr2.operator}"
        
        if len(expr1.operands) != len(expr2.operands):
            return False, f"Different operand count: {len(expr1.operands)} vs {len(expr2.operands)}"
        
        if len(expr1.operands) < 2:
            return False, "Insufficient operands in binary op"
        
        # 左辺チェック
        left_eq, left_reason = are_structurally_equivalent(
            expr1.operands[0],
            expr2.operands[0],
            debug
        )
        if not left_eq:
            return False, f"Different left operand: {left_reason}"
        
        # 右辺チェック
        right_eq, right_reason = are_structurally_equivalent(
            expr1.operands[1],
            expr2.operands[1],
            debug
        )
        if not right_eq:
            return False, f"Different right operand: {right_reason}"
        
        return True, f"Same binary structure: {expr1.operator}({left_reason}, {right_reason})"
    
    # その他の型は保守的に不一致扱い
    return False, f"Unsupported expr_type for structural comparison: {expr1.expr_type}"


def get_structural_summary(expr: Expression, max_depth: int = 3) -> str:
    """
    式の構造サマリーを取得（デバッグ用）
    
    Args:
        expr: 対象の式
        max_depth: 最大深さ
    
    Returns:
        構造サマリー文字列
    """
    if max_depth <= 0:
        return "..."
    
    if expr.expr_type == ExpressionType.CONSTANT:
        return f"CONST({expr.value})"
    
    if expr.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE):
        return f"PARAM({expr.name})"
    
    if expr.expr_type == ExpressionType.UNARY_OP:
        if expr.operands:
            inner = get_structural_summary(expr.operands[0], max_depth - 1)
            return f"{expr.operator}({inner})"
        return f"{expr.operator}(?)"
    
    if expr.expr_type == ExpressionType.BINARY_OP:
        if len(expr.operands) >= 2:
            left = get_structural_summary(expr.operands[0], max_depth - 1)
            right = get_structural_summary(expr.operands[1], max_depth - 1)
            return f"{expr.operator}({left}, {right})"
        return f"{expr.operator}(?, ?)"
    
    return f"{expr.expr_type.name}"