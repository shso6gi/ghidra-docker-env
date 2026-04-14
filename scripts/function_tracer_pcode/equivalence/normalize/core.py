# -*- coding: utf-8 -*-
"""正規化のコアロジック"""

from typing import Optional
from ...model import Condition, Expression, ExpressionType
from .negation import normalize_double_negation
from .modulo import normalize_modulo_patterns
from .arithmetic import normalize_arithmetic
from .shift import normalize_shift_amounts
from .abs import normalize_bitwise_abs
from .division import normalize_division_signs
from .division_signedness import normalize_division_signedness
from .context import NormalizationContext
from .width import normalize_width_adapters
from .bitmask import normalize_fact_mask_patterns
from .series import normalize_series_patterns


def normalize_expression(
    expr: Expression,
    context: Optional[NormalizationContext] = None
) -> Expression:
    """
    式を正規化（意味論保存変形）
    
    適用順序：
    1. 子要素の再帰的正規化（ボトムアップ）
    2. 二重否定の除去
    3. 剰余展開の正規化
    4. 加算・減算の正規形化（常に安全な bit-vector 恒等変形）
    5. shift amount の正規化（range/origin facts付き）
    6. abs ビットハックの簡約（facts付き）
    7. 除算の符号正規化（安全性チェック付き）
    8. 除算の符号性正規化（UDIV/SDIV統一、条件付き）
    
    Args:
        expr: 正規化対象の式
        context: 正規化コンテキスト（安全性チェック・監査用）
    
    Returns:
        正規化された式
    """
    # コンテキストがない場合はデフォルトを作成
    if context is None:
        context = NormalizationContext()
    
    # 子要素を先に正規化（ボトムアップ処理）
    if expr.expr_type == ExpressionType.PHI and expr.value:
        original_size = expr.size
        normalized_branches = []
        for condition, branch_expr in expr.value:
            normalized_condition_expr = normalize_expression(condition.expression, context)
            normalized_branch_expr = normalize_expression(branch_expr, context)
            normalized_branches.append(
                (
                    Condition(normalized_condition_expr, condition.negated),
                    normalized_branch_expr,
                )
            )
        expr = Expression.phi(normalized_branches)
        expr.size = original_size
    elif expr.operands:
        normalized_operands = [normalize_expression(op, context) for op in expr.operands]
        
        # 新しい Expression インスタンスを作成（元の式は変更しない）
        expr = Expression(
            expr_type=expr.expr_type,
            value=expr.value,
            operator=expr.operator,
            operands=normalized_operands,
            size=expr.size,
            name=expr.name,
            data_type=expr.data_type,
            storage_info=expr.storage_info
        )
    
    # トップレベルの正規化（順序重要）
    # 1. 二重否定の除去（最も基本的な変形、常に安全）
    expr_before = expr
    expr = normalize_double_negation(expr)
    if expr is not expr_before:
        context.record_rule(
            rule_name="double_negation",
            reason="Removed double negation"
        )

    # 2. 幅アダプタの簡約
    expr_before = expr
    expr = normalize_width_adapters(expr, context)

    # 3. fact-aware mask / constant folding
    expr_before = expr
    expr = normalize_fact_mask_patterns(expr, context)

    # 4. bitmask/byte reconstruction が新しい幅アダプタを作ることがあるので再度簡約
    expr_before = expr
    expr = normalize_width_adapters(expr, context)

    # 5. arithmetic-series の閉形式正規化
    expr_before = expr
    expr = normalize_series_patterns(expr, context)

    # 6. 剰余展開の正規化
    expr_before = expr
    expr = normalize_modulo_patterns(expr, context)

    # 7. 加算・減算の正規形化
    expr_before = expr
    expr = normalize_arithmetic(expr, context)

    # 8. shift amount の正規化
    expr_before = expr
    expr = normalize_shift_amounts(expr, context)

    # 9. abs ビットハックの簡約
    expr_before = expr
    expr = normalize_bitwise_abs(expr, context)

    # 10. 除算の符号正規化（安全性チェック付き）
    expr_before = expr
    expr = normalize_division_signs(expr, context)
    # ルール記録はnormalize_division_signs内で行われる
    
    # 11. 除算の符号性正規化（UDIV/SDIV統一、条件付き）
    expr_before = expr
    expr = normalize_division_signedness(expr, context)
    # ルール記録はnormalize_division_signedness内で行われる
    
    return expr
