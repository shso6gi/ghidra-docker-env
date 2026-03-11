# -*- coding: utf-8 -*-
"""0 比較の条件正規化に関する回帰テスト"""

import sys
from pathlib import Path


workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

from scripts.function_tracer_pcode.analysis.condition.normalizer import (
    ConditionNormalizer,
)
from scripts.function_tracer_pcode.analysis.condition.simplifier import (
    ConditionSimplifier,
)
from scripts.function_tracer_pcode.model import Condition, Expression, ExpressionType


def _param(name: str) -> Expression:
    return Expression(ExpressionType.PARAMETER, name=name, size=8)


def _const(value: int) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=8)


def _neg(expr: Expression) -> Expression:
    return Expression(
        ExpressionType.UNARY_OP,
        operator="INT_2COMP",
        operands=[expr],
        size=8,
    )


def test_normalize_zero_comparison_accepts_constant_zero():
    cond = Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator="INT_EQUAL",
            operands=[_neg(_param("param_2")), _const(0)],
            size=1,
        )
    )

    left, op, right, polarity = ConditionNormalizer.normalize_for_contradiction(cond)

    assert (left, op, right, polarity) == ("param_2", "INT_EQUAL", "0", True)


def test_negated_zero_comparison_contradicts_nonzero_condition():
    conditions = [
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_NOTEQUAL",
                operands=[_param("param_2"), _const(0)],
                size=1,
            )
        ),
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_EQUAL",
                operands=[_neg(_param("param_2")), _const(0)],
                size=1,
            )
        ),
    ]

    assert ConditionSimplifier.is_contradiction(conditions) is True


def test_negated_zero_comparison_matches_zero_condition():
    conditions = [
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_EQUAL",
                operands=[_param("param_2"), _const(0)],
                size=1,
            )
        ),
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_EQUAL",
                operands=[_neg(_param("param_2")), _const(0)],
                size=1,
            )
        ),
    ]

    assert ConditionSimplifier.is_contradiction(conditions) is False
