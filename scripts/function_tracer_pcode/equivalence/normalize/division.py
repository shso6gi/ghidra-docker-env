# -*- coding: utf-8 -*-
"""除算関連の正規化ルール（安全性チェック付き）"""

from typing import Optional
from ...model import Expression, ExpressionType
from .context import NormalizationContext


def normalize_division_signs(
    expr: Expression,
    context: NormalizationContext
) -> Expression:
    """
    除算の符号を正規化（安全性チェック付き）
    
    変形ルール（条件付き）：
        1. bvneg(bvsdiv(bvneg(PARAM), X)) -> bvsdiv(PARAM, X)
        2. bvneg(bvsdiv(X, bvneg(PARAM))) -> bvsdiv(X, PARAM)
        3. bvsdiv(bvneg(PARAM), bvneg(PARAM)) -> bvsdiv(PARAM, PARAM)
    
    安全性条件：
        - bvnegの直下がPARAMETERまたはVARIABLEであること
        - （推奨）そのパラメータがMIN除外制約を持つこと
    
    Args:
        expr: 正規化対象の式
        context: 正規化コンテキスト
    
    Returns:
        正規化された式
    """
    # Case 1 & 2: bvneg(bvsdiv(...)) パターン
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "INT_2COMP":
        result = _normalize_negated_division(expr, context)
        if result is not expr:
            return result
    
    # Case 3: bvsdiv(bvneg(a), bvneg(b)) パターン
    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_SDIV":
        result = _normalize_double_negated_division(expr, context)
        if result is not expr:
            return result
    
    return expr


def _normalize_negated_division(
    expr: Expression,
    context: NormalizationContext
) -> Expression:
    """
    bvneg(bvsdiv(...)) の正規化（安全性チェック付き）
    
    Case 1: bvneg(bvsdiv(bvneg(PARAM), b)) -> bvsdiv(PARAM, b)
    Case 2: bvneg(bvsdiv(a, bvneg(PARAM))) -> bvsdiv(a, PARAM)
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
    
    # Case 1: bvneg(bvsdiv(bvneg(PARAM), b)) -> bvsdiv(PARAM, b)
    if _is_safe_negation(dividend, context):
        unwrapped = dividend.operands[0]
        reason = _get_safety_reason(unwrapped, context)
        
        normalized = Expression(
            expr_type=ExpressionType.BINARY_OP,
            operator="INT_SDIV",
            operands=[unwrapped, divisor],
            size=expr.size
        )
        
        context.record_rule(
            rule_name="NEG_DIV_NEG_PARAM",
            before_expr=expr,
            after_expr=normalized,
            reason=f"dividend is safe: {reason}"
        )
        
        return normalized
    
    # Case 2: bvneg(bvsdiv(a, bvneg(PARAM))) -> bvsdiv(a, PARAM)
    if _is_safe_negation(divisor, context):
        unwrapped = divisor.operands[0]
        reason = _get_safety_reason(unwrapped, context)
        
        normalized = Expression(
            expr_type=ExpressionType.BINARY_OP,
            operator="INT_SDIV",
            operands=[dividend, unwrapped],
            size=expr.size
        )
        
        context.record_rule(
            rule_name="NEG_DIV_PARAM_NEG",
            before_expr=expr,
            after_expr=normalized,
            reason=f"divisor is safe: {reason}"
        )
        
        return normalized
    
    # 安全性条件を満たさない場合はスキップ
    if context.debug:
        if _is_negation(dividend):
            print(f"[Division] Skipped NEG_DIV_NEG: dividend is not safe param")
        if _is_negation(divisor):
            print(f"[Division] Skipped NEG_DIV_PARAM_NEG: divisor is not safe param")
    
    return expr


def _normalize_double_negated_division(
    expr: Expression,
    context: NormalizationContext
) -> Expression:
    """
    bvsdiv(bvneg(PARAM), bvneg(PARAM)) -> bvsdiv(PARAM, PARAM)
    （安全性チェック付き）
    """
    if len(expr.operands) < 2:
        return expr
    
    dividend = expr.operands[0]
    divisor = expr.operands[1]
    
    # 両方が safe negation かチェック
    if _is_safe_negation(dividend, context) and _is_safe_negation(divisor, context):
        unwrapped_dividend = dividend.operands[0]
        unwrapped_divisor = divisor.operands[0]
        
        reason1 = _get_safety_reason(unwrapped_dividend, context)
        reason2 = _get_safety_reason(unwrapped_divisor, context)
        
        normalized = Expression(
            expr_type=ExpressionType.BINARY_OP,
            operator="INT_SDIV",
            operands=[unwrapped_dividend, unwrapped_divisor],
            size=expr.size
        )
        
        context.record_rule(
            rule_name="DIV_BOTH_NEG_PARAMS",
            before_expr=expr,
            after_expr=normalized,
            reason=f"both operands safe: dividend({reason1}), divisor({reason2})"
        )
        
        return normalized
    
    # 安全性条件を満たさない場合はスキップ
    if context.debug:
        if _is_negation(dividend) and _is_negation(divisor):
            print(f"[Division] Skipped DIV_BOTH_NEG: operands are not safe params")
    
    return expr


def _is_negation(expr: Expression) -> bool:
    """式が INT_2COMP (bvneg) かチェック"""
    return (expr.expr_type == ExpressionType.UNARY_OP and 
            expr.operator == "INT_2COMP")


def _is_safe_negation(expr: Expression, context: NormalizationContext) -> bool:
    """
    安全にunwrapできるbvneg式かチェック
    
    条件:
    1. bvnegである
    2. 内側がPARAMETERまたはVARIABLEである
    3. (推奨) そのパラメータがMIN除外制約を持つ、またはallow_unsafe=True
    """
    if not _is_negation(expr):
        return False
    
    if not expr.operands:
        return False
    
    inner = expr.operands[0]
    
    # 内側がPARAM/VARIABLEかチェック
    if inner.expr_type not in (ExpressionType.PARAMETER, ExpressionType.VARIABLE):
        return False
    
    # パラメータ名を取得
    param_name = inner.name if inner.name else None
    if param_name is None:
        return False
    
    # MIN除外制約チェック（推奨）
    # allow_unsafe=True なら制約なしでも適用
    if context.allow_unsafe:
        return True
    
    # MIN除外制約がある場合のみ安全
    if context.is_min_excluded(param_name):
        return True
    
    # MIN除外制約がない場合は安全でない
    if context.debug:
        print(f"[Division] Param {param_name} lacks MIN exclusion constraint")
    
    return False


def _get_safety_reason(expr: Expression, context: NormalizationContext) -> str:
    """安全性の根拠を文字列で取得"""
    if expr.expr_type == ExpressionType.PARAMETER:
        param_name = expr.name if expr.name else "unknown"
        if context.is_min_excluded(param_name):
            return f"PARAM({param_name}, MIN-excluded)"
        elif context.allow_unsafe:
            return f"PARAM({param_name}, allow_unsafe)"
        else:
            return f"PARAM({param_name})"
    
    elif expr.expr_type == ExpressionType.VARIABLE:
        var_name = expr.name if expr.name else "unknown"
        if context.is_min_excluded(var_name):
            return f"VAR({var_name}, MIN-excluded)"
        elif context.allow_unsafe:
            return f"VAR({var_name}, allow_unsafe)"
        else:
            return f"VAR({var_name})"
    
    else:
        return "unknown"