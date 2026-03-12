# -*- coding: utf-8 -*-
"""FormulaBuilder の return 定義関連ヘルパー。"""

from __future__ import annotations

from typing import Dict, List

from ...model import Expression, FunctionReturnAnalysis
from ...model.render_smt import expression_returns_bool
from .params import replace_symbol_names
from .types import ParameterInfo


def get_return_size(analysis: FunctionReturnAnalysis) -> int:
    """return値のビット幅を取得する。"""
    if analysis.returns:
        first_ret = analysis.returns[0]
        if hasattr(first_ret.value, "size") and first_ret.value.size:
            return first_ret.value.size * 8
    return 32


def is_boolean_return_expr(expr: Expression) -> bool:
    """戻り値式が SMT 上で Bool sort を返すかを判定する。"""
    return expression_returns_bool(expr)


def coerce_return_value_to_bitvec(
    expr: Expression,
    value_smt: str,
    return_size: int,
) -> str:
    """Bool sort の戻り値を bitvector 0/1 に正規化する。"""
    if not is_boolean_return_expr(expr):
        return value_smt
    return f"(ite {value_smt} (_ bv1 {return_size}) (_ bv0 {return_size}))"


def build_ite_expression(return_defs: List[Dict[str, str]], return_size: int) -> str:
    """条件付き return 定義から ite 式を構築する。"""
    if not return_defs:
        return f"(_ bv0 {return_size})"

    result = f"(_ bv0 {return_size})"
    for ret_def in reversed(return_defs):
        cond = ret_def["condition"]
        value = ret_def["value"]
        if cond == "true":
            result = value
        else:
            result = f"(ite {cond} {value} {result})"
    return result


def build_return_definition(
    analysis: FunctionReturnAnalysis,
    return_var_name: str,
    param_infos: List[ParameterInfo],
) -> List[str]:
    """return 値の定義式を構築する。"""
    lines: List[str] = []
    return_size = get_return_size(analysis)

    return_defs: List[Dict[str, str]] = []
    for ret in analysis.returns:
        if ret.conditions:
            cond_parts = []
            for condition in ret.conditions:
                cond_smt = replace_symbol_names(condition.to_smt(), param_infos)
                cond_parts.append(cond_smt)
            cond_str = cond_parts[0] if len(cond_parts) == 1 else f"(and {' '.join(cond_parts)})"
        else:
            cond_str = "true"

        value_smt = replace_symbol_names(ret.value.to_smt(), param_infos)
        value_smt = coerce_return_value_to_bitvec(ret.value, value_smt, return_size)
        return_defs.append({"condition": cond_str, "value": value_smt})

    unified_return = build_ite_expression(return_defs, return_size)
    lines.append(f"(define-fun {return_var_name} () (_ BitVec {return_size})")
    lines.append(f"  {unified_return})")
    return lines
