# -*- coding: utf-8 -*-
"""UDIV→SDIV正規化（SMTガード証明版）"""

from typing import Optional, List, Tuple, Callable
from ...model import Expression, ExpressionType
from .context import NormalizationContext
from .guard_prover import prove_guard_condition


def normalize_udiv_with_guard(
    expr: Expression,
    base_ctx,
    case1_conditions_smt: List[str],
    case2_conditions_smt: List[str],
    solver_runner,
    context: NormalizationContext,
    symbol_replace_fn: Callable[[str], str]  # 追加
) -> Expression:
    """
    SMTガード証明を使ってUDIV→SDIV正規化を試行（再帰的）
    
    Args:
        expr: 正規化対象の式
        base_ctx: 共通SMT部分
        case1_conditions_smt: case1の条件SMT式リスト
        case2_conditions_smt: case2の条件SMT式リスト
        solver_runner: ソルバー実行器
        context: 正規化コンテキスト
        symbol_replace_fn: シンボル名置換関数（param_1 -> param_1_2 など）
    
    Returns:
        正規化された式
    """
    # 子要素を先に再帰的に正規化
    if expr.operands:
        normalized_operands = [
            normalize_udiv_with_guard(
                op, base_ctx,
                case1_conditions_smt, case2_conditions_smt,
                solver_runner, context,
                symbol_replace_fn  # 追加
            )
            for op in expr.operands
        ]
        
        expr = Expression(
            expr_type=expr.expr_type,
            value=expr.value,
            operator=expr.operator,
            operands=normalized_operands,
            size=expr.size,
            name=expr.name,
            data_type=expr.data_type,
            data_type_obj=getattr(expr, "data_type_obj", None),
            storage_info=expr.storage_info,
            runtime_ref=getattr(expr, "runtime_ref", None),
        )
    
    # トップレベルの変換を試行
    return _try_convert_udiv_to_sdiv(
        expr, base_ctx,
        case1_conditions_smt, case2_conditions_smt,
        solver_runner, context,
        symbol_replace_fn  # 追加
    )


def _try_convert_udiv_to_sdiv(
    expr: Expression,
    base_ctx,
    case1_conditions_smt: List[str],
    case2_conditions_smt: List[str],
    solver_runner,
    context: NormalizationContext,
    symbol_replace_fn: Callable[[str], str]  # 追加
) -> Expression:
    """UDIV→SDIV変換を試行（単一ノード）"""
    
    # INT_DIV (bvudiv) のみ対象
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_DIV":
        return expr
    
    if len(expr.operands) < 2:
        return expr
    
    dividend = expr.operands[0]
    divisor = expr.operands[1]
    
    # 簡単な形のみ対象（保守的）
    dividend_class, dividend_var = _classify_term(dividend)
    divisor_class, divisor_var = _classify_term(divisor)
    
    if dividend_class == "unknown" or divisor_class == "unknown":
        if context.debug:
            print(f"[DivisionSignednessGuarded] Complex expressions, skip")
        return expr
    
    # SMT式を生成（シンボル名置換を適用）
    dividend_smt_raw = dividend.to_smt()
    divisor_smt_raw = divisor.to_smt()
    
    # 置換を適用
    dividend_smt = symbol_replace_fn(dividend_smt_raw)
    divisor_smt = symbol_replace_fn(divisor_smt_raw)
    
    dividend_bits = dividend.get_bit_width()
    divisor_bits = divisor.get_bit_width()
    
    # Guard 1: dividend >= 0 (signed comparison)
    guard1_smt = f"(bvsle (_ bv0 {dividend_bits}) {dividend_smt})"
    
    # Guard 2: divisor > 0 (signed comparison)
    guard2_smt = f"(bvslt (_ bv0 {divisor_bits}) {divisor_smt})"
    
    if context.debug:
        print(f"[DivisionSignednessGuarded] Trying UDIV->SDIV conversion...")
        print(f"  Dividend: {dividend_smt[:80]}")
        print(f"  Divisor: {divisor_smt[:80]}")
    
    # ガード条件を証明
    guard1_proven, guard1_error = prove_guard_condition(
        base_ctx,
        case1_conditions_smt,
        case2_conditions_smt,
        guard1_smt,
        solver_runner,
        timeout=2,
        debug=context.debug
    )
    
    if guard1_error:
        if context.debug:
            print(f"[DivisionSignednessGuarded] Guard 1 ERROR: {guard1_error}")
        return expr
    
    if not guard1_proven:
        if context.debug:
            print(f"[DivisionSignednessGuarded] Guard 1 (dividend >= 0) NOT proven")
        return expr
    
    guard2_proven, guard2_error = prove_guard_condition(
        base_ctx,
        case1_conditions_smt,
        case2_conditions_smt,
        guard2_smt,
        solver_runner,
        timeout=2,
        debug=context.debug
    )
    
    if guard2_error:
        if context.debug:
            print(f"[DivisionSignednessGuarded] Guard 2 ERROR: {guard2_error}")
        return expr
    
    if not guard2_proven:
        if context.debug:
            print(f"[DivisionSignednessGuarded] Guard 2 (divisor > 0) NOT proven")
        return expr
    
    # 両方証明できた → 変換を適用
    normalized = Expression(
        expr_type=ExpressionType.BINARY_OP,
        operator="INT_SDIV",
        operands=[dividend, divisor],
        size=expr.size
    )
    
    reason = f"Guards proven via SMT: dividend>=0, divisor>0"
    
    context.record_rule(
        rule_name="UDIV_TO_SDIV_GUARD_PROVEN",
        before_expr=expr,
        after_expr=normalized,
        reason=reason
    )
    
    return normalized


def _classify_term(expr: Expression) -> Tuple[str, str]:
    """
    式を分類（division_signedness.py と同じ）
    
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


def contains_udiv(expr: Expression) -> bool:
    """
    式に INT_DIV (bvudiv) が含まれるか再帰的に検査
    
    Args:
        expr: 検査対象の式
    
    Returns:
        True if INT_DIV is found
    """
    # 自身がUDIVか
    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_DIV":
        return True
    
    # 子要素を再帰的に検査
    if expr.operands:
        for operand in expr.operands:
            if contains_udiv(operand):
                return True
    
    return False
