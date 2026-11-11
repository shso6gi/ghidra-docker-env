"""共有の SMT 描画: 比較・bool 演算の結果を整数として使う式（PR #303 レビュー 3）。

P-code では比較・bool 演算の出力は ``size`` byte（通常 1 byte）の 0 / 1。SMT ではこの式を Bool sort で描くが、
算術・シフト・結合・符号付き比較の被演算子としては ``boolean_value_bits`` の幅の 0 / 1 として読む。
"""

from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.analysis.recurrence import value_queries
from scripts.function_tracer_pcode.core import Condition, Expression
from scripts.function_tracer_pcode.core.render_smt import (
    boolean_value_bits,
    expression_smt_bit_width,
    expression_value_bit_width,
)


def _op(operator, *operands, size=1):
    expr = Expression.binary_op(operator, *operands) if len(operands) == 2 else Expression.unary_op(operator, operands[0])
    expr.size = size
    return expr


def _c(value, size=1):
    return Expression.constant(value, size=size)


TRUE = _op("INT_EQUAL", _c(0), _c(0))       # 1 byte の 1
FALSE = _op("INT_EQUAL", _c(1), _c(0))      # 1 byte の 0


@pytest.mark.parametrize("expr,expected,size", [
    (_op("INT_LEFT", TRUE, _c(1, 4)), 2, 1),                    # 修正前は 0（1 bit で 1 << 1）
    (_op("INT_ADD", TRUE, TRUE), 2, 1),                         # 修正前は 0
    (_op("INT_SRIGHT", TRUE, _c(1)), 0, 1),                     # 修正前は 1（1 bit の 1 は -1）
    (_op("INT_SLESS", TRUE, FALSE), 0, 1),                      # 1 <s 0 は偽（修正前は真）
    (_op("INT_SLESSEQUAL", FALSE, TRUE), 1, 1),
    (_op("PIECE", TRUE, _c(0xFF), size=2), 0x1FF, 2),           # t は上位の 1 byte
    (_op("PIECE", _c(0x81), TRUE, size=2), 0x8101, 2),
    (_op("INT_ZEXT", _op("INT_LEFT", TRUE, _c(1, 4)), size=4), 2, 4),
    (_op("INT_ZEXT", TRUE, size=4), 1, 4),                      # 正例の維持
    (_op("INT_SEXT", TRUE, size=4), 1, 4),
    (_op("INT_LESS", FALSE, TRUE), 1, 1),
    (_op("INT_AND", TRUE, _c(3)), 1, 1),
])
def test_comparison_result_is_a_zero_one_byte(expr, expected, size):
    assert value_queries.prove_values_equal_under(expr, _c(expected, size), ())


def test_symbolic_comparison_used_as_an_integer():
    b = Expression.parameter("param_1", index=0, size=4)
    t = _op("INT_EQUAL", b, _c(0, 4))
    shifted = _op("INT_ZEXT", _op("INT_LEFT", t, _c(1, 4)), size=4)
    assert value_queries.prove_values_equal_under(
        shifted, _op("INT_MULT", _op("INT_ZEXT", t, size=4), _c(2, 4), size=4), ())
    zero = _op("INT_EQUAL", b, _c(0, 4))
    assert value_queries.prove_values_equal_under(shifted, _c(2, 4), [Condition(zero, False)])
    assert not value_queries.prove_values_equal_under(shifted, _c(0, 4), ())


def test_boolean_sort_width_is_unchanged_and_the_value_width_is_its_bytes():
    # Bool sort の幅（1）を読む既存の利用（戻り値の幅など）は変えない。整数として読む幅だけが byte
    assert expression_smt_bit_width(TRUE) == 1
    assert boolean_value_bits(TRUE) == 8
    assert expression_value_bit_width(TRUE) == 8
    assert expression_value_bit_width(_c(5, 4)) == 32
    wide = _op("INT_EQUAL", _c(0), _c(0), size=4)
    assert boolean_value_bits(wide) == 32
