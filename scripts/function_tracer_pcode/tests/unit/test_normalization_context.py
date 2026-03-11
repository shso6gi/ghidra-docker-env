# -*- coding: utf-8 -*-
"""NormalizationContext の回帰テスト"""

import sys
from pathlib import Path


workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

from scripts.function_tracer_pcode.model import Expression, ExpressionType
from scripts.function_tracer_pcode.equivalence.normalize.context import (
    NormalizationContext,
)
from scripts.function_tracer_pcode.equivalence.normalize.division import (
    normalize_division_signs,
)
from scripts.function_tracer_pcode.equivalence.normalize.division_signedness import (
    normalize_division_signedness,
)


def _param(name: str) -> Expression:
    return Expression(ExpressionType.PARAMETER, name=name, size=8)


def _neg(expr: Expression) -> Expression:
    return Expression(
        ExpressionType.UNARY_OP,
        operator="INT_2COMP",
        operands=[expr],
        size=8,
    )


def test_normalization_context_fact_queries():
    context = NormalizationContext(
        min_excluded_params={"param_1"},
        nonneg_vars={"param_2"},
        pos_vars={"param_3"},
        neg_vars={"param_4"},
        nonzero_vars={"param_5"},
    )

    assert context.is_min_excluded("param_1") is True
    assert context.is_min_excluded("param_x") is False
    assert context.is_nonneg("param_2") is True
    assert context.is_nonneg("param_3") is True
    assert context.is_nonneg("param_4") is False
    assert context.is_pos("param_3") is True
    assert context.is_pos("param_2") is False
    assert context.is_neg("param_4") is True
    assert context.is_neg("param_3") is False
    assert context.is_nonzero("param_3") is True
    assert context.is_nonzero("param_4") is True
    assert context.is_nonzero("param_5") is True
    assert context.is_nonzero("param_2") is False


def test_normalize_division_signs_uses_min_exclusion_safely():
    expr = Expression(
        ExpressionType.UNARY_OP,
        operator="INT_2COMP",
        operands=[
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SDIV",
                operands=[_neg(_param("param_1")), _param("param_2")],
                size=8,
            )
        ],
        size=8,
    )
    context = NormalizationContext(min_excluded_params={"param_1"})

    normalized = normalize_division_signs(expr, context)

    assert normalized is not expr
    assert normalized.operator == "INT_SDIV"
    assert normalized.operands[0].name == "param_1"
    assert normalized.operands[1].name == "param_2"
    assert [rule.rule_name for rule in context.applied_rules] == ["NEG_DIV_NEG_PARAM"]


def test_normalize_division_signedness_uses_sign_fact_helpers():
    expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_DIV",
        operands=[_param("param_1"), _param("param_2")],
        size=8,
    )
    context = NormalizationContext(nonneg_vars={"param_1"}, pos_vars={"param_2"})

    normalized = normalize_division_signedness(expr, context)

    assert normalized is not expr
    assert normalized.operator == "INT_SDIV"
    assert [rule.rule_name for rule in context.applied_rules] == [
        "UDIV_TO_SDIV_NONNEG_POS"
    ]
