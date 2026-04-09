# -*- coding: utf-8 -*-
"""条件式から符号・範囲 facts を抽出する入口モジュール。"""

from typing import List

from ...analysis.condition.simplifier import ConditionSimplifier
from ...model import Condition, ExpressionType
from .fact_helpers import normalize_fact_expr
from .fact_patterns import extract_and_comparison_facts
from .fact_scalar import record_scalar_fact
from .fact_types import SignFacts


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
    simplified_conditions = ConditionSimplifier.simplify_conditions(conditions)

    for cond in simplified_conditions:
        expr = cond.expression
        if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) < 2:
            continue

        scalar_fact = ConditionSimplifier.extract_scalar_constraint(cond)
        if scalar_fact is not None:
            record_scalar_fact(facts, scalar_fact, debug)

        left = normalize_fact_expr(expr.operands[0])
        right = normalize_fact_expr(expr.operands[1])
        extract_and_comparison_facts(expr.operator, left, right, facts, debug)

    return facts


__all__ = ["SignFacts", "extract_sign_facts"]
