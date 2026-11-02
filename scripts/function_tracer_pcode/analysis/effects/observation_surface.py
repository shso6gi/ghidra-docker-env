# -*- coding: utf-8 -*-
"""関数が書いた memory を比べる面（番地を量化した観測。Issue #282, I9）。

以前の面は、store の場所（`CanonicalLocation`）ごとに `concat(書いたか, 値)` を作り、場所の名前の順に並べていた。
左右は並び順で対応し、同じ側の中の場所どうしの alias・部分重なり・書き込みの順は見ていなかった:

* 左 `*p=1; *q=2` と右 `*q=2; *p=1` が同じ面になる（`p == q` のとき最終状態は 2 と 1 で違う）
* `*(u32*)p` と `*(u8*)(p+1)` の書き込みの順が違っても同じ面になる
* 左 `*(p+0)=5` と右 `*(p+8)=5`、左 `g_a=5` と右 `g_b=5` が同じ面になる（書いた場所が違う）

新しい面は、観測の番地 `a`（`core.observation_index`。左右で同じ記号）の 1 byte について、

    surface(a) = ite(c_n ∧ a ∈ [addr_n, addr_n+size_n), concat(1, byte_n(a)),
                 ite(... , concat(0, 0)))

（store を program の順の **後ろから** 見て、最初に `a` を覆う store の byte）。範囲の判定は
`(a - addr) <u size`（2^64 での回り込みも機械と同じ）。byte の位置は `program_is_big_endian` で決める。
これで書き込みの順（後ろの store が勝つ）・alias（`p == q` は範囲の判定で決まる）・部分重なり（byte 単位）が
構成から正しくなり、左右の比較は同じ数値の番地の書き込みだけを比べる。

**この段階で面に入れる store**: 番地が parameter を起点とする位置だけ。global の object への store は、左右の
object が同じである根拠（identity の証拠）が無く、側ごとの番地の記号になって面がどの番地でも一致しないので、
効果を不完全にする（`effect_global_store_identity_unproven`。F-2 の後続で回復する）。
"""

from __future__ import annotations

from typing import Dict, List, Optional, Sequence

from scripts.function_tracer_pcode.core import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.core.observation_index import observation_index_expression

EFFECT_GLOBAL_STORE_IDENTITY_REASON = "effect_global_store_identity_unproven"

_ADDRESS_BYTES = 8


def _store_address_expression(location, parameters: Sequence[Dict]) -> Optional[Expression]:
    from scripts.function_tracer_pcode.analysis.effects._api import _bind_location_to_parameter_identity
    from scripts.function_tracer_pcode.analysis.effects.location import (
        _impl_memory_expression_for_location as memory_expression_for_location,
    )

    if location is None or not location.base_ref.is_parameter():
        return None
    # 読み出しの lowering と同じく、位置の基底を parameter の identity（index）に結び付けてから番地の式にする
    location = _bind_location_to_parameter_identity(location, parameters)
    memory = memory_expression_for_location(location, parameters)
    if memory is None or memory.expr_type != ExpressionType.MEMORY or not memory.operands:
        return None
    return memory.operands[0]


def _sized(expr: Expression, size: int) -> Expression:
    expr.size = int(size)
    return expr


def _zero_extended(expr: Expression, size: int) -> Expression:
    if int(expr.size or 0) == int(size):
        return expr
    return _sized(Expression.unary_op("INT_ZEXT", expr), size)


def _store_byte(value: Expression, offset_in_store: Expression, store_size: int, big_endian: bool) -> Expression:
    """store の値の、store の先頭から `offset_in_store` byte 目（memory の順）の 1 byte。"""

    # 値の bit 列を、少なくとも 1 byte の 0 を上に足して広げる。`PIECE` は operand を bit 列として描く（浮動小数点の
    # 値も、その bit 列）。`INT_ZEXT` / `INT_RIGHT` を浮動小数点の値に直接当てると SMT の sort が合わない
    value_bytes = int(value.size or 0)
    width = max(_ADDRESS_BYTES, value_bytes, int(store_size)) + 1
    widened = _sized(Expression.binary_op("PIECE", Expression.constant(0, width - value_bytes), value), width)
    if big_endian:
        position = _sized(
            Expression.binary_op("INT_SUB", Expression.constant(int(store_size) - 1, _ADDRESS_BYTES), offset_in_store),
            _ADDRESS_BYTES,
        )
    else:
        position = offset_in_store
    shift = _sized(
        Expression.binary_op("INT_MULT", position, Expression.constant(8, _ADDRESS_BYTES)),
        _ADDRESS_BYTES,
    )
    shift = _zero_extended(shift, width)
    shifted = _sized(Expression.binary_op("INT_RIGHT", widened, shift), width)
    return _sized(Expression.binary_op("SUBPIECE", shifted, Expression.constant(0, 4)), 1)


def build_observation_surface(
    effects: Sequence[object],
    parameters: Optional[Sequence[Dict]],
    *,
    big_endian: Optional[bool],
) -> Optional[Expression]:
    """`effects`（観測する store）の面。作れない（番地・byte の順・値の幅が分からない）なら None。"""

    effects = list(effects or ())
    if not effects:
        return None
    if big_endian is None or parameters is None:
        return None
    index = observation_index_expression()
    branches: List[tuple] = []
    for effect in sorted(effects, key=lambda item: int(item.order_key), reverse=True):
        location = effect.location
        size = int(location.size or 0)
        value = getattr(effect, "value", None)
        if size <= 0 or value is None or int(value.size or 0) <= 0:
            return None
        address = _store_address_expression(location, parameters)
        if address is None:
            return None
        address = _zero_extended(address, _ADDRESS_BYTES)
        offset_in_store = _sized(Expression.binary_op("INT_SUB", index, address), _ADDRESS_BYTES)
        in_range = Expression.binary_op("INT_LESS", offset_in_store, Expression.constant(size, _ADDRESS_BYTES))
        condition = Condition.combine_and(list(effect.conditions or ()) + [Condition(in_range)])
        written = _sized(
            Expression.binary_op(
                "PIECE",
                Expression.constant(1, 1),
                _store_byte(value, offset_in_store, size, bool(big_endian)),
            ),
            2,
        )
        branches.append((condition, written))
    branches.append((None, _sized(Expression.binary_op("PIECE", Expression.constant(0, 1), Expression.constant(0, 1)), 2)))
    surface = Expression.phi(branches)
    surface.size = 2
    return surface
