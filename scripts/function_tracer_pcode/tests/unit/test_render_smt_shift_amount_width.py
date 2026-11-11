"""共有の SMT 描画: シフト量の幅が値と違うときも P-code の意味（量 ≥ 値の bit 数なら 0、算術右シフトは符号）。

量を値の幅へ切り詰めると、上位の bit が消えて別のシフトになる（32 bit の値の 2^32 bit のシフトが
0 bit のシフトになる）。#303 のレビュー 2 で見つかった。
"""

from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.analysis.recurrence import value_queries
from scripts.function_tracer_pcode.core import Condition, Expression


def _shift(operator, value, value_size, amount, amount_size):
    left = value if isinstance(value, Expression) else Expression.constant(value, size=value_size)
    right = amount if isinstance(amount, Expression) else Expression.constant(amount, size=amount_size)
    expr = Expression.binary_op(operator, left, right)
    expr.size = value_size
    return expr


@pytest.mark.parametrize("operator,value,amount,amount_size,expected", [
    ("INT_LEFT", 1, 1 << 32, 8, 0),             # 修正前は 1（量が 0 に切り詰められた）
    ("INT_LEFT", 1, (1 << 32) + 1, 8, 0),       # 修正前は 2
    ("INT_RIGHT", 0x80000000, 1 << 32, 8, 0),
    ("INT_SRIGHT", 0x80000000, 1 << 32, 8, 0xFFFFFFFF),
    ("INT_SRIGHT", 0x7FFFFFFF, 1 << 40, 8, 0),
    ("INT_LEFT", 1, 31, 8, 1 << 31),            # 範囲内は量の幅が違っても同じシフト
    ("INT_LEFT", 1, 32, 8, 0),
    ("INT_LEFT", 1, 32, 4, 0),                  # 同幅: SMT-LIB の bvshl も 0
    ("INT_LEFT", 1, 3, 1, 8),                   # 狭い量は zero extend
])
def test_constant_shift_matches_pcode(operator, value, amount, amount_size, expected):
    shifted = _shift(operator, value, 4, amount, amount_size)
    assert value_queries.prove_values_equal_under(shifted, Expression.constant(expected, size=4), ())


def test_symbolic_wide_amount_is_compared_at_its_own_width():
    x = Expression.parameter("param_1", index=0, size=4)
    k = Expression.parameter("param_2", index=1, size=8)
    big = Expression.binary_op("INT_LESSEQUAL", Expression.constant(32, size=8), k)
    big.size = 1
    assert value_queries.prove_values_equal_under(_shift("INT_LEFT", x, 4, k, 8), Expression.constant(0, size=4),
                                                  [Condition(big, False)])
    # 切り詰めた量でのシフトとは一致しない（k = 2^32 で値が違う）
    low = Expression.binary_op("SUBPIECE", k, Expression.constant(0, size=4))
    low.size = 4
    assert not value_queries.prove_values_equal_under(_shift("INT_LEFT", x, 4, k, 8), _shift("INT_LEFT", x, 4, low, 4), ())
