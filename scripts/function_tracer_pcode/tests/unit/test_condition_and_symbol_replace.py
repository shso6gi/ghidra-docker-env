# -*- coding: utf-8 -*-
"""Condition 等価性とシンボル置換のリグレッションテスト."""

from scripts.function_tracer_pcode.equivalence.formula.symbol_replace import build_symbol_replacer
from scripts.function_tracer_pcode.equivalence.formula.types import ParameterInfo
from scripts.function_tracer_pcode.model import CanonicalLocation, Condition, Expression


class _DummyRuntimeRef:
    def __init__(self, marker: str):
        self.marker = marker


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


def test_condition_equality_detects_truncated_keys_as_incomparable():
    # Make identical but deeply nested expressions so the default budget truncates.
    expr1 = Expression.unary_op("INT_ZEXT", Expression.constant(1, 4))
    for _ in range(300):
        expr1 = Expression.unary_op("INT_ZEXT", expr1)

    expr2 = Expression.unary_op("INT_ZEXT", Expression.constant(1, 4))
    for _ in range(300):
        expr2 = Expression.unary_op("INT_ZEXT", expr2)

    cond1 = Condition(Expression.binary_op("INT_EQUAL", expr1, Expression.constant(0, 4)))
    cond2 = Condition(Expression.binary_op("INT_EQUAL", expr2, Expression.constant(0, 4)))

    assert cond1 == cond1
    assert cond1 != cond2
    assert hash(cond1) != hash(cond2)
    assert len({cond1, cond2}) == 2


def test_condition_equality_ignores_nonsemantic_runtime_ref_by_default():
    left1 = Expression.parameter("param_x", 0, size=4, runtime_ref=_DummyRuntimeRef("same"))
    left2 = Expression.parameter("param_x", 0, size=4, runtime_ref=_DummyRuntimeRef("same"))

    cond1 = Condition(Expression.binary_op("INT_EQUAL", left1, Expression.constant(1, 4)))
    cond2 = Condition(Expression.binary_op("INT_EQUAL", left2, Expression.constant(1, 4)))

    assert cond1 == cond2
    assert cond1.structural_key() == cond2.structural_key()


def test_condition_equality_distinguishes_semantic_runtime_ref_by_default():
    addr = Expression.parameter("trace", 0, size=8)
    pre_state = Expression.memory(addr, size=4)
    post_state = Expression.memory(
        Expression.parameter("trace", 0, size=8),
        size=4,
        runtime_ref=CanonicalLocation("trace", 0, 4),
    )

    cond1 = Condition(Expression.binary_op("INT_EQUAL", pre_state, Expression.constant(1, 4)))
    cond2 = Condition(Expression.binary_op("INT_EQUAL", post_state, Expression.constant(1, 4)))

    assert cond1 != cond2
    assert cond1.structural_key() != cond2.structural_key()


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


def test_symbol_replacer_string_fallback_handles_comments_and_quoted_symbols():
    params = [
        ParameterInfo(
            original_name="p",
            smt_name="p_1",
            bit_width=32,
            index=0,
            is_signed=True,
        ),
        ParameterInfo(
            original_name="x",
            smt_name="x_1",
            bit_width=32,
            index=1,
            is_signed=True,
        ),
        ParameterInfo(
            original_name="y",
            smt_name="y_1",
            bit_width=32,
            index=2,
            is_signed=True,
        ),
        ParameterInfo(
            original_name="x y",
            smt_name="xy_1",
            bit_width=32,
            index=3,
            is_signed=True,
        ),
    ]
    replace_symbol = build_symbol_replacer(params, [])

    smt_expr = "(let ((|x y| 0)) (and p x y |x y| ; comment x y should stay untouched\n \"x y\"))"
    replaced = replace_symbol(smt_expr)

    expected = "(let ((|xy_1| 0)) (and p_1 x_1 y_1 |xy_1| ; comment x y should stay untouched\n \"x y\"))"
    assert replaced == expected
