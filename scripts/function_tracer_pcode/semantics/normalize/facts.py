# -*- coding: utf-8 -*-
"""条件式から符号・範囲 facts を抽出する入口モジュール。"""

from typing import List

from scripts.function_tracer_pcode.analysis.condition.simplifier import ConditionSimplifier
from scripts.function_tracer_pcode.core import Condition, ExpressionType
from scripts.function_tracer_pcode.semantics.normalize.fact_helpers import (
    is_integral_expression,
    normalize_fact_expr,
    record_integral_expr_fact,
)
from scripts.function_tracer_pcode.semantics.normalize.fact_patterns import (
    extract_and_comparison_facts,
)
from scripts.function_tracer_pcode.semantics.normalize.fact_scalar import record_scalar_fact
from scripts.function_tracer_pcode.semantics.normalize.fact_types import SignFacts


def extract_sign_facts(
    conditions: List[Condition],
    debug: bool = False,
) -> SignFacts:
    """
    条件式から符号・範囲 facts を抽出する。

    方針:
    - ConditionSimplifier で条件を簡約
    - scalar 比較由来の facts を抽出
    - 補助的に AND を含むビットパターンから facts を推論
    """
    facts = SignFacts()
    simplified_conditions = ConditionSimplifier.simplify_conditions_object_centric(conditions)

    for cond in simplified_conditions:
        expr = cond.expression
        if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) < 2:
            continue

        scalar_fact = ConditionSimplifier.extract_scalar_constraint(cond)
        if scalar_fact is not None:
            record_scalar_fact(facts, scalar_fact, debug)

        left = normalize_fact_expr(expr.operands[0])
        right = normalize_fact_expr(expr.operands[1])
        if (
            expr.operator == "INT_SLESS"
            and left.expr_type == ExpressionType.CONSTANT
            and int(left.value or 0) == -1
            and is_integral_expression(right)
        ):
            record_integral_expr_fact(
                facts.nonneg_exprs,
                right,
                debug,
                "expr is nonneg (-1 < expr, direct comparison)",
            )
        extract_and_comparison_facts(expr.operator, left, right, facts, debug)

    return facts


__all__ = ["SignFacts", "extract_sign_facts"]
