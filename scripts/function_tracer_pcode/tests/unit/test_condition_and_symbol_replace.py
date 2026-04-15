# -*- coding: utf-8 -*-
"""Condition 等価性とシンボル置換のリグレッションテスト."""

from scripts.function_tracer_pcode.equivalence.formula.symbol_replace import build_symbol_replacer
from scripts.function_tracer_pcode.equivalence.formula.types import ParameterInfo
from scripts.function_tracer_pcode.model import Condition, Expression


def test_condition_equality_uses_structural_key_not_to_string():
    left = Expression.binary_op(
        "INT_LESS",
        Expression.parameter("param_1", 0, size=4),
        Expression.constant(0, 4),
    )
    same_left = Expression.binary_op(
        "INT_LESS",
        Expression.parameter("param_1", 0, size=4),
        Expression.constant(0, 4),
    )

    cond1 = Condition(left, negated=True)
    cond2 = Condition(same_left, negated=True)

    # to_string の不安定化（将来の pretty-printer 変更を想定）
    left.to_string = lambda: "(BROKEN_STRING 1)"  # type: ignore[assignment]
    same_left.to_string = lambda: "(BROKEN_STRING 2)"  # type: ignore[assignment]

    assert cond1 == cond2
    assert hash(cond1) == hash(cond2)
    assert len({cond1, cond2}) == 1

    combined = Condition.combine_and([cond1, cond2])
    assert combined == cond1


def test_symbol_replacer_handles_ast_and_string_without_collision():
    params = [
        ParameterInfo(
            original_name="p",
            smt_name="p_1",
            bit_width=32,
            index=0,
            is_signed=True,
        ),
        ParameterInfo(
            original_name="p1",
            smt_name="p1_1",
            bit_width=32,
            index=1,
            is_signed=True,
        ),
    ]
    replace_symbol = build_symbol_replacer(params, [])

    expr = Expression.binary_op(
        "INT_ADD",
        Expression.parameter("p", 0, size=4),
        Expression.parameter("p1", 1, size=4),
    )

    assert replace_symbol(expr) == "(bvadd p_1 p1_1)"
    assert replace_symbol(Expression.parameter("p_abc", 0, size=4)) == "p_abc"
    assert replace_symbol(" (and p p1 p_1 p1_1)") == " (and p_1 p1_1 p_1 p1_1)"
