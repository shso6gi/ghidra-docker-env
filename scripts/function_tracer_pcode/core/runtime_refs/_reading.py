"""runtime ref の読み手が、受理したまま持つ値（容器・行）を読む共通の読み方（Issue #242）。

`live_values` の reader（scalar の値の読み方）の上で、ref の層の読み手（検証・key の組み立て）が使う形を
1 か所に置く。どれも置き換える前の書き方（`tuple(x)` / `tuple(x or ())` / `for a, b in x`）と同じ要素・同じ
例外を返し、違うのは scalar の subclass を基底型の値で読むこと（subclass の `__iter__` / `__len__` /
`__bool__` / `__int__` などを呼ばない）だけ。組み込みの列（subclass は基底型の slot で）と scalar 以外の
iterable（generator・deque など）は、置き換える前と同じくその object の反復で読む（外の code）。
"""

from __future__ import annotations

from enum import Enum
from typing import Any, Tuple

from scripts.function_tracer_pcode.core.live_values import exact_scalar, exact_tree, scalar_bool, scalar_int, is_kind, type_name


def items(value: Any) -> Tuple[Any, ...]:
    """`tuple(value)` と同じ要素（scalar の subclass は基底型の値の文字の列。int / float は同じく `TypeError`）。"""

    if type(value) is tuple:
        return value
    if is_kind(value, tuple):
        return tuple(tuple.__iter__(value))
    if is_kind(value, list):
        return tuple(list.__iter__(value))
    if is_kind(value, str) and not is_kind(value, Enum):
        return tuple(str.__str__(value))
    if is_kind(value, (int, float)) and not is_kind(value, Enum):
        # 双子（基底型の値）の `tuple()` と同じ文: 型の名前は葉を写した値の型から、metaclass を通らない slot で
        raise TypeError(f"'{type_name(type(exact_scalar(value)))}' object is not iterable")
    return tuple(value)  # 組み込みの列・scalar でない iterable: その object の反復（外の code）


def optional_items(value: Any) -> Tuple[Any, ...]:
    """`tuple(value or ())`（真偽も基底型の値で読む）。"""

    return items(value) if scalar_bool(value) else ()


def rows(value: Any, width: int) -> Tuple[Tuple[Any, ...], ...]:
    """`for a, b, ... in value` と同じ行（行でない値・幅の違う行は unpack と同じ例外）を、葉を基底型の値で読む。"""

    width = scalar_int(width)
    out = []
    for row in items(value):
        cells = items(row)
        if len(cells) != width:
            raise ValueError(f"expected {width} values to unpack, got {len(cells)}")
        out.append(tuple(exact_tree(cell) for cell in cells))
    return tuple(out)


def pairs(value: Any) -> Tuple[Tuple[Any, Any], ...]:
    """`for a, b in value` と同じ 2 つ組（行でない値・幅の違う行は unpack と同じ例外）。組の中身は読まない
    （呼ぶ側が reader で読む: `rows` と違い、葉の値も容器の型も保つ）。"""

    out = []
    for row in items(value):
        cells = items(row)
        if len(cells) != 2:
            raise ValueError(f"expected 2 values to unpack, got {len(cells)}")
        out.append(cells)
    return tuple(out)


def optional_rows(value: Any, width: int) -> Tuple[Tuple[Any, ...], ...]:
    """`rows(value or (), width)`（真偽も基底型の値で読む）。"""

    return rows(value, width) if scalar_bool(value) else ()


__all__ = ["items", "optional_items", "optional_rows", "pairs", "rows"]
