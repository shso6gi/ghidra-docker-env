"""authority の値の canonical な表現の大きさ（作業量の単位）を、数えながら測る唯一の meter（Issue #110）。

`authority_digest(value)` は `canonical_value(value)`（再帰で全体を写す）と `json.dumps`（全体を書く）を
した後で hash する: 大きさを知るには全体を作るしかなかった。この meter は同じ規則の表現を **作らずに**
1 node ずつ辿り、辿る前に `sink.charge(n)` で数える。`sink` が上限を超えれば、残りを辿らずに止まる
（作ってから測らない）。

単位（canonical unit）は canonical JSON の byte 数に、並べ替えの手間（mapping の key の並べ替え・
集合の要素の digest と並べ替え）を足した決定的な量。同じ値なら同じ単位になる（呼び出しの順・cache に
依らない）。authority の event の契約（`authority/event_contract`）と封印の作業量
（`authority/seal_work`）が同じ meter を使う。
"""

from __future__ import annotations

import json
from collections.abc import Mapping as _AbcMapping
from dataclasses import fields, is_dataclass
from enum import Enum
from typing import Any, List

from scripts.function_tracer_pcode.authority.contracts import exact_primitive

#: 集合の要素 1 つを並べ替えるときの比較 1 回の単位（digest の 16 進 64 文字の比較）
SET_ORDER_UNITS = 64
#: mapping の key の比較 1 回の単位
KEY_ORDER_UNITS = 8

_ENCODE_STRING = json.encoder.encode_basestring
_LEAVE = object()


class UnitSink:
    """canonical unit を受け取る相手の protocol（`charge(n)` が上限を超えれば例外を上げる）。"""

    def charge(self, units: int) -> None:  # pragma: no cover - protocol
        raise NotImplementedError


def _log2_ceiling(count: int) -> int:
    return max(1, (count - 1).bit_length())


def _string_units(text: str, sink: UnitSink) -> int:
    # 長さを先に数えてから escape して書く（書く量は長さに比例する: 1 文字は 1 byte 以上）
    sink.charge(len(text) + 2)
    encoded = len(_ENCODE_STRING(text).encode("utf-8", "surrogatepass"))
    extra = encoded - len(text) - 2
    if extra > 0:
        sink.charge(extra)
    return encoded


def _scalar_units(value: Any, sink: UnitSink) -> int:
    if value is None or value is True:
        sink.charge(4)
        return 4
    if value is False:
        sink.charge(5)
        return 5
    kind = type(value)
    if kind is str:
        return _string_units(value, sink)
    if kind is int:
        # 桁数を作る前に数える（`int.__repr__` は桁数に比例する）
        sink.charge(max(1, value.bit_length() // 3 + 1))
        size = len(int.__repr__(value))
        return size
    if kind is float:
        size = len(json.dumps(value))
        sink.charge(size)
        return size
    raise TypeError(f"unsupported authority scalar: {kind.__name__}")


def measure_canonical_units(value: Any, sink: UnitSink) -> int:
    """`value` の canonical な表現の単位（`authority_digest` が書く canonical JSON と同じ規則）。

    辿る前に単位を `sink` へ数える（1 node・1 文字ずつ）。`canonical_value` が拒む値は同じく
    `TypeError`。再帰しない（深い入れ子でも Python の stack を使わない）。
    """

    total = 0
    # [子の iterator, この容器までの合計の単位, 集合か, 子の数]
    frames: List[List[Any]] = []
    pending: List[Any] = [value]
    while pending:
        item = pending.pop()
        if item is _LEAVE:
            frame = frames.pop()
            subtree = total - frame[1]
            if frame[2] and frame[3] > 1:
                # 集合は要素ごとの digest（要素の大きさ）と、その digest で並べ替える手間
                extra = subtree + frame[3] * _log2_ceiling(frame[3]) * SET_ORDER_UNITS
                sink.charge(extra)
                total += extra
            continue
        if item is None or type(item) in (str, int, float, bool):
            total += _scalar_units(item, sink)
            continue
        if isinstance(item, Enum):
            pending.append(item.value)
            continue
        to_authority_dict = getattr(item, "to_authority_dict", None)
        if to_authority_dict is not None:
            pending.append(to_authority_dict())
            continue
        if is_dataclass(item) and not isinstance(item, type):
            members = [(member.name, getattr(item, member.name)) for member in fields(item)]
            total += _open_pairs(members, frames, pending, total, sink, ordered=False)
            continue
        if isinstance(item, _AbcMapping):
            sink.charge(1 + len(item))
            members = [(str(key), child) for key, child in item.items()]
            total += _open_pairs(members, frames, pending, total, sink, ordered=True)
            continue
        if isinstance(item, (list, tuple, set, frozenset)):
            count = len(item)
            is_set = isinstance(item, (set, frozenset))
            local = 2 + max(0, count - 1)
            sink.charge(local)
            total += local
            frames.append([None, total - local, is_set, count])
            pending.append(_LEAVE)
            pending.extend(reversed(tuple(item)) if not is_set else tuple(item))
            continue
        if isinstance(item, (str, int, float)):
            total += _scalar_units(exact_primitive(item), sink)
            continue
        raise TypeError(f"unsupported authority value: {type(item).__name__}")
    return total


def _open_pairs(
    members: List[Any], frames: List[List[Any]], pending: List[Any], total: int,
    sink: UnitSink, *, ordered: bool,
) -> int:
    """(名前, 子) の組の列（canonical な形は `[["名前", 子], ...]`）を開く。返すのは組の外枠の単位。"""

    count = len(members)
    local = 2 + max(0, count - 1) + count * 3  # 外の [] と区切り、組ごとの [ , ]
    if ordered and count > 1:
        local += count * _log2_ceiling(count) * KEY_ORDER_UNITS
    sink.charge(local)
    frames.append([None, total, False, count])
    pending.append(_LEAVE)
    if ordered:
        members.sort(key=_member_name)
    for name, child in reversed(members):
        pending.append(child)
        pending.append(name)
    return local


def _member_name(member: Any) -> str:
    return member[0]


class LimitedUnits(UnitSink):
    """上限つきの単位の数え手（上限を超えたら `UnitLimitExceeded`）。"""

    __slots__ = ("limit", "consumed")

    def __init__(self, limit: int) -> None:
        if type(limit) is not int or limit < 0:
            raise ValueError("a canonical unit limit is a non-negative int")
        self.limit = limit
        self.consumed = 0

    def charge(self, units: int) -> None:
        self.consumed += units
        if self.consumed > self.limit:
            raise UnitLimitExceeded(self.limit)


class UnitLimitExceeded(Exception):
    """`LimitedUnits` の上限を超えた（測っていた値は上限より大きい）。"""

    def __init__(self, limit: int) -> None:
        super().__init__(f"canonical units exceed {limit}")
        self.limit = limit


def canonical_units_within(value: Any, limit: int) -> Any:
    """`value` の単位（上限 `limit` 以下なら int、超えれば `None`。上限 + 1 単位までしか辿らない）。"""

    sink = LimitedUnits(limit)
    try:
        return measure_canonical_units(value, sink)
    except UnitLimitExceeded:
        return None


__all__ = [
    "KEY_ORDER_UNITS",
    "LimitedUnits",
    "SET_ORDER_UNITS",
    "UnitLimitExceeded",
    "UnitSink",
    "canonical_units_within",
    "measure_canonical_units",
]
