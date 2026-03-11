# -*- coding: utf-8 -*-
"""`(-1) < x` 由来の sign facts に関する回帰テスト"""

import sys
from pathlib import Path
from typing import Optional


workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

from scripts.function_tracer_pcode.equivalence.normalize.facts import extract_sign_facts
from scripts.function_tracer_pcode.model import Condition, Expression, ExpressionType


def _const(value: int) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=8)


def _param(name: str, data_type: Optional[str] = None) -> Expression:
    return Expression(
        ExpressionType.PARAMETER,
        name=name,
        size=8,
        data_type=data_type,
    )


def test_minus_one_less_than_integer_param_implies_nonneg():
    conditions = [
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SLESS",
                operands=[_const(-1), _param("param_2", data_type="long")],
                size=1,
            )
        )
    ]

    facts = extract_sign_facts(conditions)

    assert facts.is_nonneg("param_2") is True
    assert facts.is_pos("param_2") is False


def test_minus_one_less_than_unknown_type_param_still_implies_nonneg():
    conditions = [
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SLESS",
                operands=[_const(-1), _param("param_2")],
                size=1,
            )
        )
    ]

    facts = extract_sign_facts(conditions)

    assert facts.is_nonneg("param_2") is True


def test_minus_one_less_than_float_like_param_is_ignored():
    conditions = [
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SLESS",
                operands=[_const(-1), _param("param_2", data_type="double")],
                size=1,
            )
        )
    ]

    facts = extract_sign_facts(conditions)

    assert facts.is_nonneg("param_2") is False
    assert facts.is_pos("param_2") is False
    assert facts.is_neg("param_2") is False


def test_less_than_constant_implies_upper_bound():
    conditions = [
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SLESS",
                operands=[_param("param_2", data_type="long"), _const(64)],
                size=1,
            )
        )
    ]

    facts = extract_sign_facts(conditions)

    assert facts.get_upper_bound("param_2") == 64


def test_less_equal_constant_implies_exclusive_upper_bound_plus_one():
    conditions = [
        Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_SLESSEQUAL",
                operands=[_param("param_2", data_type="long"), _const(62)],
                size=1,
            )
        )
    ]

    facts = extract_sign_facts(conditions)

    assert facts.get_upper_bound("param_2") == 63
