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
* **producer を呼ばない**: 走査の中で実行するのは組み込みの容器の振る舞いだけ。
  `to_authority_dict()`・`__getattr__`（`hasattr`）・上書きした `items()` / `__len__` /
  `__getitem__` / `__iter__`・dataclass の property・metaclass の hook は呼ばない（どれも work を
  受け取らずに入力に比例する仕事をし得る。型の属性は `live_values.type_attribute` で読む: MRO の class の
  `__dict__` だけで、metaclass に置いた属性は見ない）。そういう
  値は `TypeError`（有界な canonical な形を持たない。呼ぶ側は型つき token の fingerprint へ退く）。
  例外は固定の形の record `BoundedEvidence`（要約が O(1)）だけ。
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

この module は core の最下層で、project の module は live な値の読み方の owner（`core.live_values`）
だけを import する（scalar・enum・容器・dataclass の field はすべてその規則で読む）。
"""

from __future__ import annotations

import hashlib
import json
import types
from collections import OrderedDict
from typing import Any, Callable, Dict, List, Optional, Tuple

from scripts.function_tracer_pcode.core.live_values import (
    metered_storage_reads,
    NOT_PLAIN,
    as_str,
    builtin_mapping,
    builtin_sequence,
    builtin_set,
    dataclass_field_names,
    elements_of,
    enum_value,
    field_value,
    is_enum,
    items_of,
    json_scalar,
    plain_scalar,
    size,
    type_attribute,
    type_name,
)


#: 文字列を escape・hash・書き出しへ流す単位（巨大な文字列を一度に escape・encode しない。
#: `core/json_encoding` の bounded な書き出しも同じ単位を使う）
STRING_CHUNK = 1 << 16
_ENCODE_BASESTRING = json.encoder.encode_basestring


class CanonicalValueCycle(ValueError):
    """canonical な値が自分自身を含む（有限の canonical な形を持たない）。"""


def _bounded_evidence_type() -> type:
    """固定の形の record（`BoundedEvidence`。canonical な形は O(1) の要約）の型。

    callable の登録表は持たない: 固定の形の record はこの 1 つだけで、要約は名前で呼ぶ
    （`BoundedEvidence.summary`）。json_encoding はこの module を import するので遅延で読む。
    """

    from scripts.function_tracer_pcode.core.json_encoding import BoundedEvidence

    return BoundedEvidence


def _exact_mapping_type(item: Any) -> bool:
    """型そのものが dict / OrderedDict / `MappingProxyType` か（identity で比べる。metaclass の `__eq__` を呼ばない）。"""

    kind = type(item)
    return kind is dict or kind is OrderedDict or kind is types.MappingProxyType


def _scalar_key(key: Any, work: Any) -> str:
    """mapping の key の canonical な文字列（canonical_value と同じ `str(key)`）。

    scalar（`str` / `int` / `float` / `bool` / `None` / enum）でなければ `TypeError`。
    文字列の key は長さを数えてから写す。enum は組み込みのままの `__str__` だけ
    （`live_values.as_str`。上書きした `__str__` は producer なので `TypeError`）。
    """

    base = plain_scalar(key)
    if base is NOT_PLAIN:
        if is_enum(key):
            return as_str(key)
        raise TypeError(f"mapping key {type_name(type(key))} has no bounded canonical form")
    if type(base) is str:
        work.charge(len(base))
        return base
    return str(base)


def _json_key(key: Any, work: Any) -> tuple:
    """`json.dumps(sort_keys=True)` が dict の key を並べる値と、文字列にした key（enum の値の中の dict）。"""

    base = json_scalar(key)
    kind = type(base)
    if kind is str:
        work.charge(len(base))
        return base, base
    if base is True:
        return base, "true"
    if base is False:
        return base, "false"
    if base is None:
        return base, "null"
    if kind is int:
        return base, int.__repr__(base)
    if kind is float:
        return base, json.dumps(base)
    raise TypeError(f"keys must be str, int, float, bool or None, not {type_name(type(key))}")


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
        for start in range(0, len(value), STRING_CHUNK):
            chunk = value[start:start + STRING_CHUNK]
            # 切り出した chunk の長さを数えてから escape・encode する（1 文字は 1 byte 以上）。
            # 流す byte が文字数より多い分（escape・多 byte の文字）は流す前に足す: 数える量は
            # 流した byte（単位は emit と同じ）
            self.work.charge(len(chunk))
            data = _ENCODE_BASESTRING(chunk)[1:-1].encode("utf-8")
            self.work.charge(len(data) - len(chunk))
            self._put(data)
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
            raise TypeError(f"unsupported authority leaf: {type_name(type(value))}")


#: action の種類（`_Actions` の `ops` の値）。値（live かもしれない）と walker 自身の印を同じ stack に混ぜない: 値を印と
#: 見分けるために値の型を調べない（値が印の型の instance でも・bytes でも、値として扱う）
_VALUE = 0      # 値（正規化して流す）
_BYTES = 1      # 流す byte 列
_END = 2        # 容器の終わり（payload は容器そのもの: 子を辿り終える前に解放されて `id` が再利用されないよう持つ）
_KEY = 3        # 文字列にした key
_RAW_ITEM = 4   # 正規化しない値（enum の容器の値の要素: `json.dumps` の形）


#: `_normalize` が値を積み直した印（値として流さない）
_PUSHED = object()


class _Actions:
    """後入れ先出しの action の stack（種類と payload を別の list に持つ: 種類は組み込みの int だけ）。"""

    __slots__ = ("ops", "payloads")

    def __init__(self) -> None:
        self.ops: List[int] = []
        self.payloads: List[Any] = []

    def push(self, op: int, payload: Any) -> None:
        self.ops.append(op)
        self.payloads.append(payload)


def canonical_fingerprint(value: Any, *, work: Any) -> str:
    """`authority_digest(value)` と同じ digest を、`work` の中で streaming に求める。"""

    sink = _Sink(work)
    # 値の storage の読みも固定の上限を超えた分はこの作業量へ（超えればこの作業量の超過）
    with metered_storage_reads(work):
        _emit(sink, value)
    return sink.hasher.hexdigest()


def _normalize(item: Any, work: Any, actions: _Actions) -> Any:
    """canonical_value と同じ正規化（容器以外）。1 歩ごとに数える。

    scalar（subclass を含む）は基底型の値（`live_values.plain_scalar`）、enum は `_value_`
    （`live_values.enum_value`。`value` を上書きした property は producer なので呼ばない）、
    容器の値を持つ enum はその値を正規化しない値として積み直して `_PUSHED`（`json.dumps` の形で流す）、それ以外は値そのもの。
    """

    while True:
        if item is None:
            return None
        kind = type(item)
        if kind is str or kind is int or kind is float or kind is bool:
            return plain_scalar(item)
        if is_enum(item):
            work.charge(1)
            raw = enum_value(item)
            scalar = plain_scalar(raw)
            if scalar is not NOT_PLAIN:
                return scalar
            actions.push(_RAW_ITEM, raw)
            return _PUSHED
        if kind is _bounded_evidence_type():
            from scripts.function_tracer_pcode.core.json_encoding import BoundedEvidence

            work.charge(1)
            item = BoundedEvidence.summary(item)
            continue
        scalar = plain_scalar(item)
        if scalar is not NOT_PLAIN:
            return scalar
        return item


def _emit(sink: _Sink, value: Any, active: Optional[set] = None) -> None:
    work = sink.work
    # 辿っている容器の identity（set の要素を流す入れ子の呼び出しも同じ集合を共有する）
    if active is None:
        active = set()
    # 後入れ先出しの action: 値 / byte 列 / 容器の終わり / key / 正規化しない値（種類は `ops`、中身は `payloads`）
    actions = _Actions()
    actions.push(_VALUE, value)
    ops = actions.ops
    payloads = actions.payloads
    while ops:
        op = ops.pop()
        action = payloads.pop()
        if op == _BYTES:
            if type(action) is not bytes:  # pragma: no cover - byte 列は walker が積む
                raise TypeError("a byte action holds bytes")
            sink.emit(action)
            continue
        if op == _END:
            active.discard(id(action))
            continue
        if op == _KEY:
            if type(action) is not str:  # pragma: no cover - key は文字列にしてから積む
                raise TypeError("a mapping key was not converted to text")
            sink.emit_string(action)
            continue
        # 速い経路: 組み込みの型そのものの scalar と列（正規化も producer の確認も要らない）
        if (type(action) is str or type(action) is int or type(action) is float or type(action) is bool):
            sink.emit_leaf(action)
            continue
        if action is None:
            sink.emit(b"null")
            continue
        if (type(action) is tuple or type(action) is list):
            identity = id(action)
            if identity in active:
                raise CanonicalValueCycle("a canonical value contains itself")
            count = size(action)
            work.charge(count + 1)
            active.add(identity)
            sink.emit(b"[")
            actions.push(_BYTES, b"]")
            actions.push(_END, action)
            for index in range(count - 1, -1, -1):
                actions.push(_VALUE, action[index])
                if index:
                    actions.push(_BYTES, b",")
            continue
        if op == _RAW_ITEM:
            item = action
            raw_json = True
        else:
            item = _normalize(action, work, actions)
            if item is _PUSHED:
                continue
            raw_json = False
        scalar = json_scalar(item) if raw_json else plain_scalar(item)
        if scalar is not NOT_PLAIN:
            sink.emit_leaf(scalar)
            continue
        identity = id(item)
        if identity in active:
            raise CanonicalValueCycle("a canonical value contains itself")
        if raw_json:
            _push_raw_container(actions, item, work, in_set=sink.in_set)
            active.add(identity)
            continue
        if type_attribute(type(item), "to_authority_dict") is not None:
            # authority の値は `to_authority_dict()`（producer）の形で digest される: その形を作らずに
            # 同じ digest は求められない（field を辿ると別の digest を `canonical_sha256` と名乗る）
            raise TypeError(f"{type_name(type(item))} has no bounded canonical form")
        if _pairs(actions, item, work):
            active.add(identity)
            sink.emit(b"[")
            continue
        if builtin_sequence(item):
            count = size(item)
            work.charge(count + 1)
            children = list(elements_of(item))
            active.add(identity)
            sink.emit(b"[")
            actions.push(_BYTES, b"]")
            actions.push(_END, item)
            for index in range(count - 1, -1, -1):
                actions.push(_VALUE, children[index])
                if index:
                    actions.push(_BYTES, b",")
            continue
        if builtin_set(item):
            work.charge(size(item) + 1)
            active.add(identity)
            # canonical_value と同じ並び（要素の authority_digest 順）。要素の canonical JSON を
            # 作業量の中で作り、digest で並べてから流す（流す byte は数え済み）。digest の等しい
            # 要素は canonical JSON も等しいので、(digest, byte 列) の組で並べても流す byte は同じ
            members = []
            for member in elements_of(item):
                member_sink = _Sink(work, keep=True, in_set=True)
                _emit(member_sink, member, active)
                members.append((member_sink.hasher.hexdigest(), member_sink.buffer))
            active.discard(identity)
            members.sort()
            sink.emit(b"[")
            for index, (_digest, chunks) in enumerate(members):
                if index:
                    sink.emit(b",")
                for data in chunks:
                    sink._put(data)
            sink.emit(b"]")
            continue
        # producer を持つ値（`to_authority_dict`・上書きした容器の振る舞い）と未知の型は辿らない
        raise TypeError(f"{type_name(type(item))} has no bounded canonical form")


def _pairs(actions: _Actions, item: Any, work: Any) -> bool:
    """mapping / dataclass の (key, 子) を、幅を数えてから key で並べて積む（容器の終わりを含む）。

    mapping / dataclass でなければ何も積まずに `False`。
    """

    names = dataclass_field_names(item)
    if names is not None:
        work.charge(len(names) + 1)
        texts = names
        children = [field_value(item, name) for name in names]
    else:
        mapping = builtin_mapping(item) if _exact_mapping_type(item) else None
        if mapping is None:
            return False
        work.charge(size(mapping) + 1)
        # (key の文字列, 元の位置) で並べる（key だけで並べる安定な整列と同じ順）
        keyed = []
        values = []
        for key, child in items_of(mapping):
            keyed.append((_scalar_key(key, work), len(values)))
            values.append(child)
        keyed.sort()
        texts = [text for text, _position in keyed]
        children = [values[position] for _text, position in keyed]
    actions.push(_BYTES, b"]")
    actions.push(_END, item)
    for index in range(len(texts) - 1, -1, -1):
        # [key,value] の組（canonical_value の mapping / dataclass の形）
        actions.push(_BYTES, b"]")
        actions.push(_VALUE, children[index])
        actions.push(_BYTES, b",")
        actions.push(_KEY, texts[index])
        actions.push(_BYTES, b"[")
        if index:
            actions.push(_BYTES, b",")
    return True


def _push_raw_container(actions: _Actions, item: Any, work: Any, *, in_set: bool) -> None:
    """enum の値（正規化されない値）を `json.dumps(sort_keys=True)` と同じ形で積む。"""

    mapping = builtin_mapping(item) if _exact_mapping_type(item) else None
    if mapping is not None:
        if in_set:
            # set の要素の並びは要素の canonical な形を **もう一度** 正規化した値の digest
            # （mapping は [key, 値] の組になる）で、流す byte（`{...}`）とは別の形。有界な
            # canonical な形を約束しない（呼ぶ側は型つき token の fingerprint へ退く）
            raise TypeError("an enum mapping value inside a set has no bounded canonical form")
        work.charge(size(mapping) + 1)
        # `json.dumps(sort_keys=True)` と同じく key の（基底型の）値で並べてから文字列にする
        keyed = []
        texts = []
        values = []
        for key, child in items_of(mapping):
            order, text = _json_key(key, work)
            keyed.append((order, len(values)))
            texts.append(text)
            values.append(child)
        order = sorted(keyed)
        actions.push(_BYTES, b"}")
        actions.push(_END, item)
        for index in range(len(order) - 1, -1, -1):
            position = order[index][1]
            actions.push(_RAW_ITEM, values[position])
            actions.push(_BYTES, b":")
            actions.push(_KEY, texts[position])
            if index:
                actions.push(_BYTES, b",")
        actions.push(_BYTES, b"{")
        return
    if builtin_sequence(item):
        count = size(item)
        work.charge(count + 1)
        children = list(elements_of(item))
        actions.push(_BYTES, b"]")
        actions.push(_END, item)
        for index in range(count - 1, -1, -1):
            actions.push(_RAW_ITEM, children[index])
            if index:
                actions.push(_BYTES, b",")
        actions.push(_BYTES, b"[")
        return
    raise TypeError(f"unsupported enum value: {type_name(type(item))}")


__all__ = ["CanonicalValueCycle", "canonical_fingerprint"]
