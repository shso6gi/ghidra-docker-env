# -*- coding: utf-8 -*-
"""Condition 等価性とシンボル置換のリグレッションテスト."""

from scripts.function_tracer_pcode.proof.formula.symbol_replace import build_symbol_replacer
from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo
from scripts.function_tracer_pcode.core import CanonicalLocation, Condition, Expression
from scripts.function_tracer_pcode.tests.unit._publication import published


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


def _nested_zext(depth: int) -> Expression:
    expr = Expression.unary_op("INT_ZEXT", Expression.constant(1, 4))
    for _ in range(depth):
        expr = Expression.unary_op("INT_ZEXT", expr)
    return expr


def _shared_chain(depth: int, leaf: Expression) -> Expression:
    """各段を 2 回参照する DAG。distinct node は depth + 1、木換算は 2 ** depth。"""

    node = leaf
    for _ in range(depth):
        node = Expression.binary_op("INT_SUB", node, node)
    return node


def test_condition_equality_refuses_when_the_comparison_budget_runs_out():
    """予算切れは「同じ」ではなく「判定できない」（= 一致としない）。

    深さ 300 の鎖は既定予算（distinct な node 組 256）を超えるので、
    構造が同じでも一致とはしない。ここは Issue #22 PR-22-B の前後で変わらない
    契約で、変わったのは予算の数え方（木の位置 → distinct な node 組）だけ。
    """

    cond1 = Condition(
        Expression.binary_op("INT_EQUAL", _nested_zext(300), Expression.constant(0, 4))
    )
    cond2 = Condition(
        Expression.binary_op("INT_EQUAL", _nested_zext(300), Expression.constant(0, 4))
    )

    assert cond1 == cond1
    assert cond1 != cond2
    assert len({cond1, cond2}) == 2


def test_condition_equality_now_compares_shared_dags_the_old_budget_truncated():
    """Issue #22 PR-22-B の互換契約（判定能力の改善方向）。

    旧実装は木として走査していたので、distinct な node が 13 しかない DAG でも
    木換算 4096 node を数え切れず placeholder になり、同じ条件どうしが「判定
    できない」になっていた。予算を distinct で数えるようになって、同じものは
    同じと言えるようになった（逆向きの変化は起きない）。
    """

    left = _shared_chain(12, Expression.parameter("p", 0, size=4))
    right = _shared_chain(12, Expression.parameter("p", 0, size=4))
    cond1 = Condition(left)
    cond2 = Condition(right)

    assert left.freeze().tree_size() > 256
    assert cond1 == cond2
    assert hash(cond1) == hash(cond2)
    assert len({cond1, cond2}) == 1


def test_conditions_over_different_shared_dags_are_not_equal():
    cond1 = Condition(_shared_chain(12, Expression.parameter("p", 0, size=4)))
    cond2 = Condition(_shared_chain(12, Expression.parameter("q", 1, size=4)))

    assert cond1 != cond2
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

    assert replace_symbol(published(expr)) == "(bvadd p_1 p1_1)"
    assert replace_symbol(published(Expression.parameter("p_abc", 0, size=4))) == "p_abc"
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
