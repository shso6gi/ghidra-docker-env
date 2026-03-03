# -*- coding: utf-8 -*-
"""正規化のコアロジック"""

from ...model import Expression, ExpressionType
from .negation import normalize_double_negation
from .division import normalize_division_signs


def normalize_expression(expr: Expression) -> Expression:
    """
    式を正規化（意味論保存変形）
    
    適用順序：
    1. 子要素の再帰的正規化（ボトムアップ）
    2. 二重否定の除去
    3. 除算の符号正規化
    
    Args:
        expr: 正規化対象の式
    
    Returns:
        正規化された式
    """
    # 子要素を先に正規化（ボトムアップ処理）
    if expr.operands:
        normalized_operands = [normalize_expression(op) for op in expr.operands]
        
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
    # 1. 二重否定の除去（最も基本的な変形）
    expr = normalize_double_negation(expr)
    
    # 2. 除算の符号正規化（UB除外制約が前提）
    expr = normalize_division_signs(expr)
    
    return expr