# -*- coding: utf-8 -*-
"""シンボル名置換ユーティリティ"""

import re
from typing import List, Callable


def build_symbol_replacer(
    params_info: List,
    extra_vars_info: List
) -> Callable[[str], str]:
    """
    パラメータと追加変数の両方を置換する関数を作成
    
    original_name -> smt_name の置換を行う。
    長い名前を先に置換することで、部分一致を防ぐ。
    
    Args:
        params_info: ParameterInfo のリスト（original_name, smt_name を持つ）
        extra_vars_info: ExtraVariableInfo のリスト（original_name, smt_name を持つ）
    
    Returns:
        置換関数（smt_expr: str -> str）
    
    Example:
        >>> replacer = build_symbol_replacer(params1, extra_vars1)
        >>> smt_expr = "(bvsrem (concat in_a0_hi param_1) param_2)"
        >>> replaced = replacer(smt_expr)
        >>> # -> "(bvsrem (concat in_a0_hi_1 param_1_1) param_2_1)"
    """
    # すべてのシンボル（original_name, smt_name）のペアを収集
    all_symbols = []
    
    # パラメータを追加
    for param in params_info:
        all_symbols.append((param.original_name, param.smt_name))
    
    # 追加変数を追加
    for var in extra_vars_info:
        all_symbols.append((var.original_name, var.smt_name))
    
    # 長い名前を先に置換（部分一致を防ぐため）
    all_symbols.sort(key=lambda x: -len(x[0]))
    
    def replacer(smt_expr: str) -> str:
        """SMT式内のシンボル名を置換"""
        result = smt_expr
        
        for original_name, smt_name in all_symbols:
            # 単語境界を考慮した置換（\b で囲む）
            pattern = r'\b' + re.escape(original_name) + r'\b'
            result = re.sub(pattern, smt_name, result)
        
        return result
    
    return replacer