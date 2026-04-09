# -*- coding: utf-8 -*-
"""Scalar constraint to normalization fact conversion."""

from ...analysis.condition.scalar import ScalarConstraint
from .fact_helpers import (
    get_integral_var_name,
    get_var_name,
    is_integral_expression,
    normalize_fact_expr,
    record_expr_fact,
    record_integral_expr_fact,
    record_upper_bound,
)
from .fact_types import SignFacts


def record_scalar_fact(
    facts: SignFacts,
    scalar_fact: ScalarConstraint,
    debug: bool,
) -> None:
    """ConditionSimplifier の scalar 制約を sign/range facts に変換する"""
    normalized_expr = normalize_fact_expr(scalar_fact.expr)
    var_name = get_var_name(normalized_expr)

    if scalar_fact.kind == "ne":
        if scalar_fact.raw_value == 0:
            if var_name:
                facts.nonzero_vars.add(var_name)
                if debug:
                    print(f"[Facts] {var_name} is nonzero ({var_name} != 0)")
            record_expr_fact(
                facts.nonzero_exprs,
                normalized_expr,
                debug,
                "expr is nonzero (expr != 0)",
            )
        return

    if scalar_fact.kind == "lower" and scalar_fact.signed:
        value = int(scalar_fact.value or 0)
        inclusive = bool(scalar_fact.inclusive)
        if value > 0 or (value == 0 and not inclusive):
            if var_name:
                facts.pos_vars.add(var_name)
                facts.nonneg_vars.add(var_name)
                facts.nonzero_vars.add(var_name)
                if debug:
                    print(f"[Facts] {var_name} is pos ({var_name} > 0)")
            record_expr_fact(facts.pos_exprs, normalized_expr, debug, "expr is pos (expr > 0)")
            record_expr_fact(
                facts.nonneg_exprs,
                normalized_expr,
                debug,
                "expr is nonneg (expr > 0)",
            )
            record_expr_fact(
                facts.nonzero_exprs,
                normalized_expr,
                debug,
                "expr is nonzero (expr > 0)",
            )
            return

        if value == 0 and inclusive:
            if var_name:
                facts.nonneg_vars.add(var_name)
                if debug:
                    print(f"[Facts] {var_name} is nonneg ({var_name} >= 0)")
            record_expr_fact(
                facts.nonneg_exprs,
                normalized_expr,
                debug,
                "expr is nonneg (expr >= 0)",
            )
            return

        if value == -1 and not inclusive and is_integral_expression(normalized_expr):
            if var_name:
                facts.nonneg_vars.add(var_name)
                if debug:
                    print(f"[Facts] {var_name} is nonneg (-1 < {var_name}, integral)")
            record_integral_expr_fact(
                facts.nonneg_exprs,
                normalized_expr,
                debug,
                "expr is nonneg (-1 < expr, integral)",
            )
            return

    if scalar_fact.kind != "upper":
        return

    value = int(scalar_fact.value or 0)
    inclusive = bool(scalar_fact.inclusive)
    if scalar_fact.signed and (value < 0 or (value == 0 and not inclusive)):
        if var_name:
            facts.neg_vars.add(var_name)
            facts.nonzero_vars.add(var_name)
            if debug:
                op_text = "<= -1" if inclusive else "< 0"
                print(f"[Facts] {var_name} is neg ({var_name} {op_text})")
        record_expr_fact(facts.neg_exprs, normalized_expr, debug, "expr is neg (expr < 0)")
        record_expr_fact(
            facts.nonzero_exprs,
            normalized_expr,
            debug,
            "expr is nonzero (expr < 0)",
        )
        if value != 0 or inclusive:
            return

    exclusive_bound = value + 1 if inclusive else value
    if exclusive_bound >= 0:
        integral_name = get_integral_var_name(normalized_expr)
        if integral_name:
            record_upper_bound(
                facts,
                integral_name,
                exclusive_bound,
                debug,
                "<=" if inclusive else "<",
            )
