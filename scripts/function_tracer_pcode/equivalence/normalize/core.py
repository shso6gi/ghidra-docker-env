# -*- coding: utf-8 -*-
"""正規化のコアロジック"""

from typing import Optional
from ...model import Expression, ExpressionType
from .negation import normalize_double_negation
from .division import normalize_division_signs
from .division_signedness import normalize_division_signedness
from .context import NormalizationContext


def normalize_expression(
    expr: Expression,
    context: Optional[NormalizationContext] = None
) -> Expression:
    """
    式を正規化（意味論保存変形）
    
    適用順序：
    1. 子要素の再帰的正規化（ボトムアップ）
    2. 二重否定の除去
    3. 除算の符号正規化（安全性チェック付き）
    4. 除算の符号性正規化（UDIV/SDIV統一、条件付き）
    
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
    if expr.operands:
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
    if expr is not expr_before and context.debug:
        print(f"[Normalize] Applied: double_negation")
    
    # 2. 除算の符号正規化（安全性チェック付き）
    expr_before = expr
    expr = normalize_division_signs(expr, context)
    # ルール記録はnormalize_division_signs内で行われる
    
    # 3. 除算の符号性正規化（UDIV/SDIV統一、条件付き）
    expr_before = expr
    expr = normalize_division_signedness(expr, context)
    # ルール記録はnormalize_division_signedness内で行われる
    
    return expr