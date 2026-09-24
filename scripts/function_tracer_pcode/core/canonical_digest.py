# -*- coding: utf-8 -*-
"""canonical な値の **有界な fingerprint**（Issue #22 PR-22-D）。

大きい証拠を authority 確定前に有界な表現へ置き換えるとき、その identity（照合用の
key）を、canonical な写しを作らずに、**作業量の上限の中で** 求める。

`canonical_fingerprint(value, work=...)` は `authority_digest(value)`（= canonical_value の
JSON の sha256。`authority/contracts`）と **同じ値** を streaming で求める。

* **契約**: 辿り終えたとき、値は `authority_digest(value)` と等しい。したがって canonical な
  形が等しい 2 つの値の fingerprint は必ず等しい。**逆は保証しない**: fingerprint が等しい
  ことは SHA-256 の衝突耐性のもとでの照合の手がかりで、値の等しさの証明ではない。判定・
  authority の入力に使わない。
* **有界**: 作業量は `work`（`charge(n)` を持つ予算。`JsonBudget` と同じ interface）へ、
  **並べる・hash する・子を積む前に** 足す。単位は canonical JSON の byte（容器・正規化の
  1 歩はそれぞれ 1 byte 以上）。超えたら `work.charge` の例外がそのまま上がる。
  - mapping / dataclass / 列は幅を数えてから子を積む（mapping は key で並べる）。set は
    要素ごとの canonical JSON を作業量の中で作ってから digest 順に並べる。文字列は chunk
    ごとに数えてから escape・hash する。整数は桁数を数えてから文字列にする。
* **producer を呼ばない**（Issue #22 PR-22-D、5 回目）: 走査の中で実行するのは組み込みの容器の
  振る舞いだけ。`to_authority_dict()`・`__getattr__`（`hasattr`）・上書きした `items()` /
  `__len__` / `__getitem__` / `__iter__`・dataclass の property は呼ばない（どれも work を
  受け取らずに入力に比例する仕事をし得る）。そういう値は `TypeError`（有界な canonical な形を
  持たない。呼ぶ側は型つき token の fingerprint へ退く）。例外は `register_fixed_canonical`
  で登録した固定の形の record（要約が O(1)。今は `BoundedEvidence` だけ）。
* **閉路** は `CanonicalValueCycle`（型つきの失敗）。辿っている容器の identity を持つので、
  stack は際限なく伸びない。
* **木として辿る**（共有部分も展開する）。共有 DAG は canonical JSON が大きくなるので作業量を
  超えて止まる（呼ぶ側は fingerprint の無い表現へ退く）。
* set の中の、mapping を値に持つ enum は `TypeError`（set の要素の並びが流す byte と別の形の
  digest で決まるため。呼ぶ側は型つき token の fingerprint へ退く）。深すぎる set の入れ子は
  `RecursionError`（set の要素は要素ごとに流して並べる）。
* mapping の key は scalar（`str` / `int` / `float` / `bool` / `None` / その値の enum）だけ。
  それ以外の key は `TypeError`（canonical_value は `str(key)` で受けるが、その写しの大きさを
  作る前に数えられない）。

この module は core の最下層で、project の他の module を import しない。
"""

from __future__ import annotations

import hashlib
import inspect
import json
import types
from collections import OrderedDict
from dataclasses import fields, is_dataclass
from enum import Enum
from typing import Any, Callable, Dict, List, Optional

from scripts.function_tracer_pcode.core.builtin_containers import (
    builtin_mapping,
    builtin_sequence,
    builtin_set,
    plain_field_value,
)


_PRIMITIVE_TYPES = frozenset({str, int, float, bool})
#: 文字列を hash へ流す単位（巨大な文字列を一度に escape・encode しない）
_STRING_CHUNK = 1 << 16
_ENCODE_BASESTRING = json.encoder.encode_basestring


class CanonicalValueCycle(ValueError):
    """canonical な値が自分自身を含む（有限の canonical な形を持たない）。"""


#: 固定の形の record（型 → その canonical な要約を返す関数。要約は O(1) の大きさ）
_FIXED_CANONICAL: Dict[type, Callable[[Any], Any]] = {}


def register_fixed_canonical(kind: type, summary: Callable[[Any], Any]) -> None:
    """`kind` の値を、`summary(value)`（固定の形の値）として辿る（`to_authority_dict` の代わり）。

    `summary` は入力に比例する仕事をしない関数だけ（固定個数の短い field を返す）。登録は
    `tests/unit/test_architecture_boundaries.py` が固定する。
    """

    _FIXED_CANONICAL[kind] = summary


_MAPPING_TYPES = (dict, OrderedDict, types.MappingProxyType)
_BUILTIN_ENUM_STR = frozenset({Enum.__str__, str.__str__, int.__repr__, int.__str__, object.__str__})


# 組み込みの `__len__` / `__getitem__` / `__iter__` のまま（namedtuple など）でなければ辿らない
_is_builtin_sequence = builtin_sequence
_is_builtin_set = builtin_set


_field_value = plain_field_value


def _exact_primitive(value: Any) -> Any:
    # `authority/contracts.exact_primitive` と同じ規則（基底型の subclass を基底型へ）
    if isinstance(value, bool):
        return bool(value)
    if isinstance(value, int):
        return int.__index__(value)
    if isinstance(value, str):
        return str.__str__(value)
    if isinstance(value, float):
        return float(float.__repr__(value))
    return value


def _scalar_key(key: Any, work: Any) -> str:
    """mapping の key の canonical な文字列（canonical_value と同じ `str(key)`）。

    scalar（`str` / `int` / `float` / `bool` / `None` / enum）でなければ `TypeError`。
    文字列の key は長さを数えてから写す。
    """

    if isinstance(key, str) and not isinstance(key, Enum):
        work.charge(len(key))
        return str.__str__(key)
    if isinstance(key, Enum):
        # enum の `__str__` は組み込みのものだけ（上書きした `__str__` は producer）
        if type(key).__str__ not in _BUILTIN_ENUM_STR:
            raise TypeError(f"mapping key {type(key).__name__} overrides __str__")
        return str(key)
    if key is None or isinstance(key, (bool, int, float)):
        return str(_exact_primitive(key)) if key is not None else "None"
    raise TypeError(f"mapping key {type(key).__name__} has no bounded canonical form")


def _json_key(key: Any, work: Any) -> str:
    """`json.dumps` が dict の key を文字列にする規則（enum の値の中の dict）。"""

    if isinstance(key, str):
        work.charge(len(key))
        return str.__str__(key)
    if key is True:
        return "true"
    if key is False:
        return "false"
    if key is None:
        return "null"
    if isinstance(key, int):
        return int.__repr__(int.__index__(key))
    if isinstance(key, float):
        return json.dumps(float(key))
    raise TypeError(f"keys must be str, int, float, bool or None, not {type(key).__name__}")


class _Sink:
    """canonical JSON の byte を hash（`keep` なら buffer にも）へ流す。流す前に数える。

    `in_set` は set の要素を流している sink（入れ子の sink も受け継ぐ）。
    """

    __slots__ = ("hasher", "buffer", "work", "in_set")

    def __init__(self, work: Any, *, keep: bool = False, in_set: bool = False) -> None:
        self.hasher = hashlib.sha256()
        self.buffer: Optional[List[bytes]] = [] if keep else None
        self.work = work
        self.in_set = in_set

    def emit(self, data: bytes) -> None:
        self.work.charge(len(data))
        self._put(data)

    def _put(self, data: bytes) -> None:
        self.hasher.update(data)
        if self.buffer is not None:
            self.buffer.append(data)

    def emit_string(self, value: str) -> None:
        self.emit(b'"')
        for start in range(0, len(value), _STRING_CHUNK):
            chunk = value[start:start + _STRING_CHUNK]
            # 切り出した chunk の長さを数えてから escape・encode する
            self.work.charge(len(chunk))
            self._put(_ENCODE_BASESTRING(chunk)[1:-1].encode("utf-8"))
        self.emit(b'"')

    def emit_leaf(self, value: Any) -> None:
        if value is None:
            self.emit(b"null")
        elif value is True:
            self.emit(b"true")
        elif value is False:
            self.emit(b"false")
        elif type(value) is str:
            self.emit_string(value)
        elif type(value) is int:
            # 桁数を作る前に数える（`int.__repr__` は桁数に比例する）
            self.work.charge(max(1, value.bit_length() // 3))
            self._put(int.__repr__(value).encode("ascii"))
        elif type(value) is float:
            self.emit(json.dumps(value).encode("ascii"))
        else:  # pragma: no cover - 呼ぶ側が基底型へ直してから渡す
            raise TypeError(f"unsupported authority leaf: {type(value).__name__}")


class _End:
    """容器を閉じる action（閉路の判定から外し、閉じ括弧を流す）。

    容器そのものを持つ: 固定の形の要約（`register_fixed_canonical`）が作った一時的な容器が、
    子を辿り終える前に解放されて `id` が別の容器に再利用されると、閉路でない値を閉路と誤る。
    """

    __slots__ = ("container", "closing")

    def __init__(self, container: Any, closing: bytes) -> None:
        self.container = container
        self.closing = closing


class _Raw:
    """canonical_value が正規化せずに返す値（容器の値を持つ enum）: `json.dumps` の形で流す。"""

    __slots__ = ("value",)

    def __init__(self, value: Any) -> None:
        self.value = value


def canonical_fingerprint(value: Any, *, work: Any) -> str:
    """`authority_digest(value)` と同じ digest を、`work` の中で streaming に求める。"""

    sink = _Sink(work)
    _emit(sink, value)
    return sink.hasher.hexdigest()


def _normalize(item: Any, work: Any) -> Any:
    """canonical_value と同じ正規化（容器以外）。1 歩ごとに数える。"""

    while True:
        if item is None or type(item) in _PRIMITIVE_TYPES:
            return item
        if isinstance(item, Enum):
            work.charge(1)
            # enum の値は組み込みの保存場所から読む（`value` を上書きした property は producer）
            raw = object.__getattribute__(item, "_value_")
            if raw is None or isinstance(raw, (bool, int, float, str)):
                return None if raw is None else _exact_primitive(raw)
            return _Raw(raw)
        summary = _FIXED_CANONICAL.get(type(item))
        if summary is not None:
            work.charge(1)
            item = summary(item)
            continue
        if isinstance(item, (str, int, float, bool)):
            return _exact_primitive(item)
        return item


def _emit(sink: _Sink, value: Any, active: Optional[set] = None) -> None:
    work = sink.work
    # 辿っている容器の identity（set の要素を流す入れ子の呼び出しも同じ集合を共有する）
    if active is None:
        active = set()
    # 後入れ先出しの action: 値 / byte 列 / 容器の終わり
    actions: list = [value]
    while actions:
        action = actions.pop()
        if type(action) is bytes:
            sink.emit(action)
            continue
        if type(action) is _End:
            active.discard(id(action.container))
            sink.emit(action.closing)
            continue
        if type(action) is _Key:
            sink.emit_string(action.text)
            continue
        raw_json = type(action) is _RawItem
        item = action.value if raw_json else _normalize(action, work)
        if type(item) is _Raw:
            item, raw_json = item.value, True
        if item is None or isinstance(item, (bool, int, float, str)):
            sink.emit_leaf(item if type(item) in _PRIMITIVE_TYPES or item is None else _exact_primitive(item))
            continue
        identity = id(item)
        if identity in active:
            raise CanonicalValueCycle("a canonical value contains itself")
        if raw_json:
            _push_raw_container(actions, item, work, in_set=sink.in_set)
            active.add(identity)
            continue
        if inspect.getattr_static(type(item), "to_authority_dict", None) is not None:
            # authority の値は `to_authority_dict()`（producer）の形で digest される: その形を作らずに
            # 同じ digest は求められない（field を辿ると別の digest を `canonical_sha256` と名乗る）
            raise TypeError(f"{type(item).__name__} has no bounded canonical form")
        if (is_dataclass(item) and not isinstance(item, type)) or (type(item) in _MAPPING_TYPES and builtin_mapping(item) is not None):
            pairs = _pairs(item, work)
            active.add(identity)
            sink.emit(b"[")
            actions.append(_End(item, b"]"))
            for index in range(len(pairs) - 1, -1, -1):
                key, child = pairs[index]
                # [key,value] の組（canonical_value の mapping / dataclass の形）
                actions.append(b"]")
                actions.append(child)
                actions.append(b",")
                actions.append(_Key(key))
                actions.append(b"[")
                if index:
                    actions.append(b",")
            continue
        if _is_builtin_sequence(item):
            work.charge(len(item) + 1)
            active.add(identity)
            sink.emit(b"[")
            actions.append(_End(item, b"]"))
            for index in range(len(item) - 1, -1, -1):
                actions.append(item[index])
                if index:
                    actions.append(b",")
            continue
        if _is_builtin_set(item):
            work.charge(len(item) + 1)
            active.add(identity)
            # canonical_value と同じ並び（要素の authority_digest 順）。要素の canonical JSON を
            # 作業量の中で作り、digest で並べてから流す（流す byte は数え済み）
            members = []
            for member in item:
                member_sink = _Sink(work, keep=True, in_set=True)
                _emit(member_sink, member, active)
                members.append((member_sink.hasher.hexdigest(), member_sink.buffer))
            active.discard(identity)
            members.sort(key=lambda pair: pair[0])
            sink.emit(b"[")
            for index, (_digest, chunks) in enumerate(members):
                if index:
                    sink.emit(b",")
                for data in chunks:
                    sink._put(data)
            sink.emit(b"]")
            continue
        # producer を持つ値（`to_authority_dict`・上書きした容器の振る舞い）と未知の型は辿らない
        raise TypeError(f"{type(item).__name__} has no bounded canonical form")


class _Key:
    __slots__ = ("text",)

    def __init__(self, text: str) -> None:
        self.text = text


class _RawItem:
    __slots__ = ("value",)

    def __init__(self, value: Any) -> None:
        self.value = value


def _pairs(item: Any, work: Any) -> list:
    """mapping / dataclass の (key, 子) を、幅を数えてから key で並べる。"""

    if is_dataclass(item):
        names = [field_info.name for field_info in fields(item)]
        work.charge(len(names) + 1)
        return [(name, _field_value(item, name)) for name in names]
    work.charge(len(item) + 1)
    pairs = [(_scalar_key(key, work), child) for key, child in item.items()]
    pairs.sort(key=lambda pair: pair[0])
    return pairs


def _push_raw_container(actions: list, item: Any, work: Any, *, in_set: bool) -> None:
    """enum の値（正規化されない値）を `json.dumps(sort_keys=True)` と同じ形で積む。"""

    if type(item) in _MAPPING_TYPES and builtin_mapping(item) is not None:
        if in_set:
            # set の要素の並びは要素の canonical な形を **もう一度** 正規化した値の digest
            # （mapping は [key, 値] の組になる）で、流す byte（`{...}`）とは別の形。有界な
            # canonical な形を約束しない（呼ぶ側は型つき token の fingerprint へ退く）
            raise TypeError("an enum mapping value inside a set has no bounded canonical form")
        work.charge(len(item) + 1)
        # `json.dumps(sort_keys=True)` と同じく元の key で並べてから文字列にする
        pairs = [(_json_key(key, work), child) for key, child in sorted(item.items())]
        actions.append(_End(item, b"}"))
        for index in range(len(pairs) - 1, -1, -1):
            key, child = pairs[index]
            actions.append(_RawItem(child))
            actions.append(b":")
            actions.append(_Key(key))
            if index:
                actions.append(b",")
        actions.append(b"{")
        return
    if _is_builtin_sequence(item):
        work.charge(len(item) + 1)
        actions.append(_End(item, b"]"))
        for index in range(len(item) - 1, -1, -1):
            actions.append(_RawItem(item[index]))
            if index:
                actions.append(b",")
        actions.append(b"[")
        return
    raise TypeError(f"unsupported enum value: {type(item).__name__}")


__all__ = ["CanonicalValueCycle", "canonical_fingerprint", "register_fixed_canonical"]
