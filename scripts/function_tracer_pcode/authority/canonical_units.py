"""authority の値の canonical な表現の大きさ（作業量の単位）を、数えながら測る唯一の meter（Issue #110）。

`authority_digest(value)` は `canonical_value(value)`（再帰で全体を写す）と `json.dumps`（全体を書く）を
した後で hash する: 大きさを知るには全体を作るしかなかった。この meter は同じ規則の表現を **作らずに**
1 node ずつ辿り、辿る前に `sink.charge(n)` で数える。`sink` が上限を超えれば、残りを辿らずに止まる
（作ってから測らない）。

単位（canonical unit）は canonical JSON の byte 数に、並べ替えの手間（mapping の key の並べ替え・
集合の要素の digest と並べ替え）を足した決定的な量。同じ値なら同じ単位になる（呼び出しの順・cache に
依らない）。authority の event の契約（`authority/event_contract`）と封印の作業量
（`authority/seal_work`）が同じ meter を使う。

authority の表現への射影（`to_authority_dict()`）を持つ値は、射影を **呼ぶ前に** その値を構造として
（公開 field を、射影を呼ばずに）数えてから射影を呼ぶ: 射影の仕事は数えた構造に比例する。射影を持てる
のは dataclass の値だけ（それ以外は `TypeError`: 任意の callable を呼ばない）。この値の単位は構造の単位と
射影の単位の和（canonical JSON の byte 以上。数えた単位と報告する単位が一致するので、上限はどれも
測りながら数えた量で強制できる）。
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
        # 桁数（と符号）を作る前に数える（`int.__repr__` は桁数に比例する）。書いた長さが数えた量を
        # 超えた分も足す（返す単位は必ず数えた単位以下）
        charged = value.bit_length() // 3 + 2
        sink.charge(charged)
        size = len(int.__repr__(value))
        if size > charged:
            sink.charge(size - charged)
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

    return _walk(value, sink, structural=False, projected={})


def _walk(value: Any, sink: UnitSink, *, structural: bool, projected: dict) -> int:
    """1 つの値を辿る。`structural` は射影を呼ばずに値の構造（公開 field）を数える走査。

    `projected` は構造を数え終えた射影を持つ値（id → 値。1 回の測定の中で同じ値の構造を 2 回数えない:
    射影が子の値をそのまま返しても、入れ子の深さの 2 乗にならない）。値を持ち続けるので、測定の途中で
    id が別の値に使い回されることはない。
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
            # 値への 1 hop も数える（hop だけが続く値でも作業量の上限で止まる）
            sink.charge(1)
            total += 1
            pending.append(item.value)
            continue
        to_authority_dict = getattr(item, "to_authority_dict", None)
        is_value_dataclass = is_dataclass(item) and not isinstance(item, type)
        if to_authority_dict is not None:
            if not is_value_dataclass:
                raise TypeError(
                    f"an authority projection must be a dataclass value: {type(item).__name__}"
                )
            # 射影への 1 hop も数える（自分自身を返す値でも上限で止まる）
            sink.charge(1)
            total += 1
            if structural:
                # 入れ子の射影の構造もここで数え済み（後で射影の結果から出会っても数え直さない）
                projected[id(item)] = item
                members = _public_members(item)
                total += _open_pairs(members, frames, pending, total, sink, ordered=False)
                continue
            if id(item) not in projected:
                # 射影を呼ぶ前に、射影が辿る構造を数える（射影は呼ばない）
                projected[id(item)] = item
                total += _walk(item, sink, structural=True, projected=projected)
            pending.append(to_authority_dict())
            continue
        if is_value_dataclass:
            members = (
                _public_members(item) if structural
                else [(member.name, getattr(item, member.name)) for member in fields(item)]
            )
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
        if structural:
            # 構造の走査の葉（射影が自分で表現を決める値）: 1 単位（その表現は射影の走査が数える）
            sink.charge(1)
            total += 1
            continue
        raise TypeError(f"unsupported authority value: {type(item).__name__}")
    return total


def _public_members(item: Any) -> List[Any]:
    """射影を持つ値の構造: 公開 field（`_` で始まる field は射影の外の封印の token など）。"""

    return [
        (member.name, getattr(item, member.name))
        for member in fields(item) if not member.name.startswith("_")
    ]


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


def plain_copy(value: Any, sink: UnitSink) -> Any:
    """`value`（live でもよい）を plain な値（`None`・bool・`str`・`int`・`float` と、それらの tuple）へ、
    数えながら写す。単位は canonical な表現と同じ規則で、写す **前に** `sink` へ数える。

    scalar の subclass（JPype の `JInt` など）は基底型の slot で基底型の値にする（値の code を呼ばない:
    `core.live_values.plain_scalar`）。容器は組み込みの tuple / list だけを辿る（中身の `__iter__` を上書き
    しない型だけ）。それ以外の値は `TypeError`（任意の object の表現を作らない）。再帰しない。
    """

    from scripts.function_tracer_pcode.core import live_values

    root: List[Any] = []
    # [親の list, 残りの子（逆順）]
    stack: List[List[Any]] = [[root, [value]]]
    while stack:
        frame = stack[-1]
        if not frame[1]:
            stack.pop()
            if stack:
                stack[-1][0].append(tuple(frame[0]))
            continue
        item = frame[1].pop()
        scalar = live_values.plain_scalar(item)
        if scalar is not live_values.NOT_PLAIN:
            _scalar_units(scalar, sink)
            frame[0].append(scalar)
            continue
        if live_values.builtin_sequence(item):
            count = live_values.size(item)
            sink.charge(2 + max(0, count - 1))
            children = []
            for child in live_values.elements_of(item):
                children.append(child)
            children.reverse()
            stack.append([[], children])
            continue
        raise TypeError("a limitation description is plain values and tuples only")
    return root[0]


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
    "plain_copy",
]
