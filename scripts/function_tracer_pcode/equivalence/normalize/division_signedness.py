# -*- coding: utf-8 -*-
"""除算の符号性正規化（UDIV/SDIV統一、bvneg対応強化版）"""

from typing import Optional, Tuple
from ...model import Expression, ExpressionType
from .context import NormalizationContext


def normalize_division_signedness(
    expr: Expression,
    context: NormalizationContext
) -> Expression:
    """
    除算の符号性を正規化（条件付きでUDIV/SDIVを統一）
    
    変形ルール（条件付き）：
        bvudiv(a, b) -> bvsdiv(a, b)
            if: a は非負 AND b は正
    
    根拠：
        dividend >= 0 かつ divisor > 0 の場合、
        ビットベクタ意味論でも bvudiv(a, b) == bvsdiv(a, b)
    
    Args:
        expr: 正規化対象の式
        context: 正規化コンテキスト（sign facts を含む）
    
    Returns:
        正規化された式
    """
    # INT_DIV (bvudiv) のみ対象
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_DIV":
        return expr
    
    if len(expr.operands) < 2:
        return expr
    
    dividend = expr.operands[0]
    divisor = expr.operands[1]
    
    # 安全性チェック：dividend が非負 AND divisor が正
    safe, reason = _is_safe_for_sdiv_conversion(dividend, divisor, context)
    
    if safe:
        # UDIV -> SDIV に変換
        normalized = Expression(
            expr_type=ExpressionType.BINARY_OP,
            operator="INT_SDIV",
            operands=[dividend, divisor],
            size=expr.size
        )
        
        context.record_rule(
            rule_name="UDIV_TO_SDIV_NONNEG_POS",
            before_expr=expr,
            after_expr=normalized,
            reason=reason
        )
        
        return normalized
    else:
        if context.debug:
            print(f"[DivisionSignedness] Cannot convert UDIV to SDIV: {reason}")
    
    return expr


def _is_safe_for_sdiv_conversion(
    dividend: Expression,
    divisor: Expression,
    context: NormalizationContext
) -> Tuple[bool, str]:
    """
    UDIV -> SDIV 変換が安全か判定
    
    条件:
    1. dividend が非負であることが facts から保証される
    2. divisor が正であることが facts から保証される
    
    Returns:
        (is_safe, reason)
    """
    # dividend の分類と非負性チェック
    dividend_class, dividend_var = _classify_term(dividend)
    
    if dividend_class == "unknown":
        return False, f"Dividend is complex expression"
    
    if dividend_class == "var":
        # 単純な変数
        if not context.is_nonneg(dividend_var):
            return False, f"Dividend {dividend_var} is not known to be nonneg"
    
    elif dividend_class == "neg":
        # bvneg(var) の形
        # -x >= 0  <=>  x <= 0
        # ここでは扱わない（保守的）
        return False, f"Dividend is negation of {dividend_var}, not directly nonneg"
    
    # divisor の分類と正性チェック
    divisor_class, divisor_var = _classify_term(divisor)
    
    if divisor_class == "unknown":
        return False, f"Divisor is complex expression"
    
    if divisor_class == "var":
        # 単純な変数
        if not context.is_pos(divisor_var):
            return False, f"Divisor {divisor_var} is not known to be pos"
        
        dividend_reason = f"{dividend_var}(nonneg)" if dividend_class == "var" else "?"
        divisor_reason = f"{divisor_var}(pos)"
        return True, f"dividend={dividend_reason}, divisor={divisor_reason}"
    
    elif divisor_class == "neg":
        # bvneg(var) の形
        # -x > 0  <=>  x < 0
        if context.is_neg(divisor_var):
            # x < 0 が保証されている
            # さらに x != MIN (MIN除外制約) があれば -x > 0 が確実
            if context.is_min_excluded(divisor_var):
                dividend_reason = f"{dividend_var}(nonneg)" if dividend_class == "var" else "?"
                divisor_reason = f"-{divisor_var}(pos, because {divisor_var}<0 and MIN-excluded)"
                return True, f"dividend={dividend_reason}, divisor={divisor_reason}"
            else:
                # MIN除外がない場合でも、x < 0 なら -x > 0（x == MIN の場合 -MIN == MIN < 0 だが）
                # 保守的に、nonzero だけで許可するかどうか
                # ここでは MIN除外を要求する
                return False, f"Divisor -{divisor_var} requires MIN-exclusion (has {divisor_var}<0 but not MIN-excluded)"
        else:
            return False, f"Divisor -{divisor_var} requires {divisor_var}<0"
    
    return False, "Unknown classification"


def _classify_term(expr: Expression) -> Tuple[str, str]:
    """
    式を分類
    
    Returns:
        ("var", "param_name") - 単純な変数
        ("neg", "param_name") - bvneg(param)
        ("unknown", "") - その他
    """
    # 単純な PARAMETER/VARIABLE
    if expr.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE):
        if expr.name:
            return ("var", expr.name)
    
    # bvneg(PARAMETER/VARIABLE)
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "INT_2COMP":
        if expr.operands:
            inner = expr.operands[0]
            if inner.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE):
                if inner.name:
                    return ("neg", inner.name)
    
    return ("unknown", "")