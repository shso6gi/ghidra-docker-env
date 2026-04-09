# -*- coding: utf-8 -*-
"""Helper utilities shared across normalization fact extraction modules."""

from typing import Optional, Set

from ...model import Expression, ExpressionType
from .fact_types import SignFacts, expr_key


def is_zero(expr: Expression) -> bool:
    return expr.expr_type == ExpressionType.CONSTANT and expr.value == 0


def is_and_operation(expr: Expression) -> bool:
    return expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_AND"


def get_var_name(expr: Expression) -> Optional[str]:
    if expr.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE):
        return expr.name
    return None


def get_integral_var_name(expr: Expression) -> Optional[str]:
    var_name = get_var_name(expr)
    if not var_name:
        return None

    data_type = (expr.data_type or "").lower()
    if "float" in data_type or "double" in data_type:
        return None
    return var_name


def normalize_fact_expr(expr: Expression) -> Expression:
    from .core import normalize_expression
    from .context import NormalizationContext

    return normalize_expression(expr, NormalizationContext())


def record_expr_fact(
    target: Set[str],
    expr: Expression,
    debug: bool,
    message: str,
) -> None:
    key = expr_key(expr)
    if not key:
        return
    target.add(key)
    if debug:
        print(f"[Facts] {message}: {key}")


def is_integral_expression(expr: Expression) -> bool:
    data_type = (expr.data_type or "").lower()
    return "float" not in data_type and "double" not in data_type


def record_integral_expr_fact(
    target: Set[str],
    expr: Expression,
    debug: bool,
    message: str,
) -> None:
    if not is_integral_expression(expr):
        return
    record_expr_fact(target, expr, debug, message)


def record_upper_bound(
    facts: SignFacts,
    var_name: str,
    bound: int,
    debug: bool,
    source: str,
) -> None:
    current = facts.upper_bounds.get(var_name)
    if current is None or bound < current:
        facts.upper_bounds[var_name] = bound
        if debug:
            print(f"[Facts] {var_name} has upper bound {bound} (source {source})")
