# -*- coding: utf-8 -*-
"""FormulaBuilder の return 定義関連ヘルパー。"""

from __future__ import annotations

import re
from typing import Dict, List, Optional

from ...model import Expression, FunctionReturnAnalysis
from ...model.render_smt import (
    expression_contains_signed_comparison,
    expression_returns_bool,
    expression_smt_bit_width,
)
from ..typing.helpers import is_unsigned_type
from .params import replace_symbol_names
from .types import ParameterInfo


def get_return_size(analysis: FunctionReturnAnalysis) -> int:
    """return値のビット幅を取得する。"""
    declared_bits = get_declared_return_size_bits(analysis.return_type)
    if declared_bits is not None:
        return declared_bits

    expr_bits = [
        ret.value.get_bit_width()
        for ret in analysis.returns
        if ret.value is not None
    ]
    if expr_bits:
        return max(expr_bits)
    return 32


def get_declared_return_size_bits(return_type: Optional[str]) -> Optional[int]:
    """型名から戻り値のビット幅を推定する。"""
    return_type = (return_type or "").strip()
    if not return_type:
        return None

    type_lower = return_type.lower()

    undefined_match = re.fullmatch(r"undefined(\d+)", type_lower)
    if undefined_match:
        return int(undefined_match.group(1)) * 8

    if type_lower == "bool":
        return 8
    if any(token in type_lower for token in ["char", "byte"]):
        return 8
    if "short" in type_lower:
        return 16
    if "longlong" in type_lower or "long long" in type_lower:
        return 64
    if "long" in type_lower:
        return 64
    if "int" in type_lower:
        return 32

    return None


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


def should_sign_extend_to_return_size(analysis: FunctionReturnAnalysis) -> bool:
    """return値の幅補正で sign extension を使うべきか判定する。"""
    return should_sign_extend_return_type(analysis.return_type)


def should_sign_extend_return_type(return_type: Optional[str]) -> bool:
    """return型名から sign extension の要否を判定する。"""
    return_type = (return_type or "").strip()
    if not return_type:
        return False

    type_lower = return_type.lower()
    if "undefined" in type_lower or "unknown" in type_lower:
        return False
    if is_unsigned_type(return_type):
        return False
    return "int" in type_lower or "long" in type_lower


def has_signed_branch_evidence(expr: Expression, conditions) -> bool:
    """値式やガード条件に signed 比較の証拠があるか判定する。"""
    if expression_contains_signed_comparison(expr):
        return True

    for condition in conditions or []:
        condition_expr = getattr(condition, "expression", None)
        if condition_expr is not None and expression_contains_signed_comparison(condition_expr):
            return True

    return False


def should_sign_extend_value(
    return_type: Optional[str],
    expr: Expression,
    conditions,
) -> bool:
    """return_type だけでなく branch evidence も見て sign extension の要否を判定する。"""
    if should_sign_extend_return_type(return_type):
        return True
    return has_signed_branch_evidence(expr, conditions)


def expression_has_unresolved_value(expr: Optional[Expression]) -> bool:
    """ソルバへ流せない未解決値を含むか判定する。"""
    if expr is None:
        return True

    expr_type = getattr(expr, "expr_type", None)
    expr_kind = getattr(expr_type, "__class__", None)
    if expr_type is None or expr_kind is None:
        return True

    if expr_type in {expr_kind.UNKNOWN, expr_kind.CALL}:
        return True

    if expr_type == expr_kind.PHI and expr.value:
        for cond, value in expr.value:
            cond_expr = getattr(cond, "expression", None) if cond is not None else None
            if cond_expr is not None and expression_has_unresolved_value(cond_expr):
                return True
            if expression_has_unresolved_value(value):
                return True
        return False

    for operand in getattr(expr, "operands", []) or []:
        if expression_has_unresolved_value(operand):
            return True

    return False


def _rewrite_ambiguous_negative_constant(
    expr: Expression,
    value_smt: str,
    target_size: int,
    use_sign_extension: bool,
) -> str:
    """32bit 由来の負定数が 64bit で zero-extended されていたら sign-extended に補正する。"""
    if not use_sign_extension:
        return value_smt
    if expr.expr_type != expr.expr_type.__class__.CONSTANT:
        return value_smt
    if target_size <= 32:
        return value_smt
    if not isinstance(expr.value, int) or expr.value < 0 or expr.value > 0xffffffff:
        return value_smt
    if (expr.value & 0x80000000) == 0:
        return value_smt

    sign_extended = expr.value | (((1 << (target_size - 32)) - 1) << 32)
    return f"(_ bv{sign_extended} {target_size})"


def coerce_value_to_bitvec_width(
    expr: Expression,
    value_smt: str,
    target_size: int,
    use_sign_extension: bool = False,
) -> str:
    """値式を target_size の bitvector に揃える。"""
    value_smt = coerce_return_value_to_bitvec(expr, value_smt, target_size)
    value_smt = _rewrite_ambiguous_negative_constant(
        expr,
        value_smt,
        target_size,
        use_sign_extension,
    )

    expr_bits = expression_smt_bit_width(expr)
    if expr_bits == target_size:
        return value_smt

    if expr_bits < target_size:
        extend_bits = target_size - expr_bits
        op = "sign_extend" if use_sign_extension else "zero_extend"
        return f"((_ {op} {extend_bits}) {value_smt})"

    return f"((_ extract {target_size - 1} 0) {value_smt})"


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
        use_sign_extension = should_sign_extend_value(
            analysis.return_type,
            ret.value,
            ret.conditions,
        )
        value_smt = coerce_value_to_bitvec_width(
            ret.value,
            value_smt,
            return_size,
            use_sign_extension=use_sign_extension,
        )
        return_defs.append({"condition": cond_str, "value": value_smt})

    unified_return = build_ite_expression(return_defs, return_size)
    lines.append(f"(define-fun {return_var_name} () (_ BitVec {return_size})")
    lines.append(f"  {unified_return})")
    return lines
