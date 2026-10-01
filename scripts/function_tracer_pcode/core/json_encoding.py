# -*- coding: utf-8 -*-
"""JSON の書き方・数え方・live object からの変換（Issue #22 PR-22-D）: **1 つの policy object**。

契約（PR-22-D の中心）:

> live object から prepared representation までの全経路で、予算を知らない producer が、
> 入力の大きさに比例して大きくなる完成 container / 文字列を先に作れない。

そのための仕組みは 1 つ — **producer は表現を作らず、walker が 1 要素ずつ引き出す**:

* record は `json_items()`（`(key, source)` の組を 1 つずつ yield する generator）を持つ。
  record の `to_dict()` は `JsonEncodingPolicy.materialize(record)`（LEGACY mode）で、
  schema は `json_items()` 1 つだけ。
* source の文法（これ以外は `JsonValueRejected`）:

  - scalar（`None` / `bool` / `int` / `float` / `str`。固定個数の既存値から作った scalar でよい）
  - 既に在る値への参照（container も。LEGACY では写さずに置き、どちらの mode でも数える）
  - record（`json_items()` を持つ object）、sized leaf（`__json_tree__` を持つ object =
    `Expression`: DAG のまま大きさを求めて予算と比べてから木を作る）
  - `each(items, fn)` / `nested(value)` / `as_list(items)` / `as_dict(mapping)` /
    `mapping_of(mapping, fn)` / `inline(*pairs)`: collection を 1 要素ずつ引き出す遅延構成子
  - `evidence(value, identity=)` / `text(value, max_chars)`: 出力（CANONICAL）では有界な表現、
    `to_dict()`（LEGACY）では元の値
  - `scan(values, reducer)`: 集計（件数・group by）。walker が要素を 1 つずつ引き出して
    作業量へ数えながら reducer に畳ませ、結果を辿る（producer が入力全体を先に辿らない）

* walker は 1 つで、mode が 2 つ:

  - **CANONICAL**（出力の準備）: 新しく作った canonical な JSON 値（`dict[str]` / `list` /
    scalar）だけを作る。`evidence` / `text` は有界な表現にする。
  - **LEGACY**（`to_dict()` と解析 1 件分の snapshot）: 旧 `to_dict()` と同じ構造を作る
    （既存の値への参照はそのまま置き、写さないが数える）。

  どちらも書き出し器と同じ規則で byte を数え、予算（`JsonBudget`）を超えた時点で止まる。
  止まるまでに作るのは「残り予算 + 超えたことに気付いた 1 要素」まで。

JSON の書き方（区切り・framing・escape・key の型変換）はすべて `JsonEncodingPolicy` の
method で、他の module は JSON の規則を計算しない。単位は UTF-8 byte。
"""

from __future__ import annotations

import contextvars
import hashlib
import functools
import json
import operator
import re
import types
from collections.abc import Mapping
from dataclasses import dataclass
from enum import Enum
from json.encoder import encode_basestring, encode_basestring_ascii
from typing import Any, Callable, Iterable, Iterator, List, NamedTuple, Optional, Tuple

from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.canonical_digest import STRING_CHUNK
from scripts.function_tracer_pcode.core.live_values import (
    NOT_PLAIN,
    builtin_enum as _builtin_enum,
    builtin_iterator,
    builtin_mapping,
    builtin_sequence,
    builtin_set,
    dataclass_field_names,
    items_of,
    json_scalar,
    field_value as plain_field_value,
    plain_scalar,
    str_value,
    type_attribute,
    type_module,
    type_name,
)
from scripts.function_tracer_pcode.core.errors import AnalysisFailureError
from scripts.function_tracer_pcode.core.render_output import utf8_length


class JsonOutputLimitExceeded(AnalysisFailureError):
    """bounded encoder が上限に達した（書き出しを止め、完成文字列を作らない）。"""

    def __init__(self, *, max_bytes: int, requested_bytes: int) -> None:
        super().__init__(
            f"JSON output exceeded {max_bytes} bytes (needed at least {requested_bytes})"
        )
        self.max_bytes = live_values.as_int(max_bytes)
        self.requested_bytes = live_values.as_int(requested_bytes)


class JsonBudgetExhausted(AnalysisFailureError):
    """walker が byte の上限に達した（そこで辿るのをやめた）。

    `consumed_bytes` は上限 + 1（上限の無い予算では止めた時点までに数えた量）で、値全体の
    大きさではない（残りは数えていない）。どこまで辿ってから止めたかに依らない値なので、
    限界の evidence（cause の identity）に入れてよい。
    """

    def __init__(self, *, consumed_bytes: int, max_bytes: Optional[int]) -> None:
        super().__init__(f"JSON projection exceeded {max_bytes} bytes")
        self.consumed_bytes = live_values.as_int(consumed_bytes)
        self.max_bytes = max_bytes


class JsonValueRejected(AnalysisFailureError):
    """source の文法に無い値（任意の object・閉路・key の衝突・上限を破った集計）。

    **producer のバグ** で、意味の限界ではない。`TypeError` 派生にしない（回復用の
    handler に吸われると、canonical でない値が prepared payload に入り得る）。
    """

    def __init__(self, message: str, *, path: str) -> None:
        super().__init__(f"{message} at {path}")
        self.path = path


class JsonValueCycle(JsonValueRejected):
    """値が自分自身を含む（walker が辿っている容器・record に戻った）。"""


class _OpaqueLeaf(JsonValueRejected):
    """型つき token の列に、型名しか持たない葉が現れた（値の fingerprint にならない）。"""


# ---------------------------------------------------------------------------
# source の遅延構成子（producer が collection を渡す唯一の方法）
# ---------------------------------------------------------------------------


#: 登録した source converter（module の top-level の関数だけ。import のときに 1 度だけ登録する）
_CONVERTERS: set = set()



def source_converter(fn: Callable[[Any], Any]) -> Callable[[Any], Any]:
    """`fn` を **source converter** として登録する（walker が要素ごとに呼んでよい関数）。

    module の top-level の関数（`types.FunctionType`）だけを、decorator として登録する（lambda・
    実行時に作った関数・callable な object は登録しない）。source converter は値 1 つから source
    （遅延構成子）か scalar を作るだけで、入力に比例する仕事（内包表記・複製・並べ替え・
    `to_dict()`・digest）をしない（`tests/unit/test_architecture_boundaries.py` の J11 / J19 が
    本体と呼び先を検査する）。walker が呼ぶ callback は、これと `Reducer` だけ。
    """

    if (
        not live_values.package_function(fn)
        or fn.__name__ == "<lambda>" or "<locals>" in fn.__qualname__
    ):
        raise TypeError("a source converter is a module-level function registered once at import")
    _CONVERTERS.add(fn)
    return fn


def _is_converter(fn: Any) -> bool:
    # 登録済みの関数そのものか（`fn` の属性を読まない。callable な object の `__getattr__` を呼ばない）
    return fn is None or fn is _RAW or fn is _NESTED or (type(fn) is types.FunctionType and fn in _CONVERTERS)


def _require_converter(fn: Any, where: str) -> None:
    if not _is_converter(fn):
        raise TypeError(f"{where} takes a registered source_converter, not {type_name(type(fn))}")


def exception_text(exc: BaseException, max_chars: int = 80) -> str:
    """例外の型名と、引数の先頭（`str(exc)` / `repr` を呼ばない。切り出してから連結する）。

    引数は組み込みの `args`（上書きした `args` を読まない）の先頭 4 つだけで、`str` は
    `max_chars` 字まで、scalar は桁数の上限の中で、それ以外は型名。bounded path の失敗の文は
    これだけで作る（`KeyError(<重い key>)` の `repr` を作らない）。
    """

    parts: List[str] = []
    args = BaseException.args.__get__(exc)
    for arg in args[:4]:
        kind = type(arg)
        if kind is str:
            parts.append(arg[:max_chars])
        elif arg is None:
            parts.append("None")
        elif kind is bool:
            parts.append("True" if arg else "False")
        elif kind is float:
            parts.append(float.__repr__(arg))
        elif kind is int:
            parts.append(int.__repr__(arg) if arg.bit_length() <= 64 else "<int>")
        else:
            parts.append(f"<{type_name(kind)}>")
    name = type_name(type(exc))
    return (f"{name}: {', '.join(parts)}" if parts else name)[:max_chars + len(name) + 2]


class _Source:
    __slots__ = ()


class _Each(_Source):
    __slots__ = ("items", "fn")

    def __init__(self, items: Iterable[Any], fn: Any) -> None:
        self.items = items
        self.fn = fn


class _Nested(_Source):
    __slots__ = ("value",)

    def __init__(self, value: Any) -> None:
        self.value = value


class _MappingOf(_Source):
    __slots__ = ("mapping", "fn", "stringify_keys")

    def __init__(self, mapping: Any, fn: Any, stringify_keys: bool = False) -> None:
        self.mapping = mapping
        self.fn = fn
        self.stringify_keys = stringify_keys


class _Inline(_Source):
    __slots__ = ("pairs",)

    def __init__(self, pairs: Tuple[Tuple[Any, Any], ...]) -> None:
        self.pairs = pairs


class _Raw(_Source):
    __slots__ = ("value",)

    def __init__(self, value: Any) -> None:
        self.value = value


class Reread(NamedTuple):
    """証拠の値を読み直す手順（任意の callable ではない）: `converter(getattr(record, attribute))`。

    `converter` は登録した source converter（`source_converter`。O(1) で source を作るだけ）か
    `None`。1 回しか辿れない列を要約の fingerprint のために作り直すときに使う。
    """

    record: Any
    attribute: str
    converter: Any = None


class _Evidence(_Source):
    __slots__ = ("value", "identity", "reread", "one_shot", "inline_bytes")

    def __init__(
        self,
        value: Any,
        identity: Optional[str],
        reread: Optional[Reread] = None,
        inline_bytes: Optional[int] = None,
        one_shot: bool = False,
    ) -> None:
        if identity is not None and type(identity) is not str:
            raise TypeError("an evidence identity is a precomputed str (no callable)")
        if reread is not None and (type(reread) is not Reread or not _is_converter(reread.converter)):
            raise TypeError("an evidence reread is a Reread with a registered converter")
        self.value = value
        self.identity = identity
        #: 同じ値の source を作り直す手順（遅延列は 1 回しか辿れないので、要約の fingerprint 用）
        self.reread = reread
        #: 作り直せない 1 回しか辿れない列（試しで辿った後は fingerprint を求めない）
        self.one_shot = one_shot
        #: そのまま置いてよい大きさ（既定は `EVIDENCE_INLINE_BYTES`）
        self.inline_bytes = EVIDENCE_INLINE_BYTES if inline_bytes is None else live_values.as_int(inline_bytes)


class _Text(_Source):
    __slots__ = ("value", "max_chars")

    def __init__(self, value: Any, max_chars: int) -> None:
        self.value = value
        self.max_chars = live_values.as_int(max_chars)


class _Scan(_Source):
    __slots__ = ("values", "reducer")

    def __init__(self, values: Any, reducer: Any) -> None:
        self.values = values
        self.reducer = reducer


class _Flatten(_Source):
    """`values` の要素ごとに、その属性 `attribute`（組み込みの振る舞いの列）の要素を順に並べた列。"""

    __slots__ = ("values", "attribute")

    def __init__(self, values: Any, attribute: str) -> None:
        self.values = values
        self.attribute = attribute


#: 要素をそのまま置く（LEGACY: 旧 `list(x)` / `dict(x)` の要素。CANONICAL では通常どおり）
_RAW = object()
#: 要素を `nested` の規則で写す
_NESTED = object()


def each(items: Iterable[Any], fn: Optional[Callable[[Any], Any]] = None) -> _Source:
    """要素を 1 つずつ引き出す配列（`[fn(x).to_dict() for x in items]` の遅延版）。

    要素（`fn` の返り値）は source として辿る（record は dict になる）。`fn` は登録した source
    converter（`source_converter`。要素 1 つ分の source を返すだけ）。
    """

    _require_converter(fn, "each")
    return _Each(items, fn)


def nested(value: Any) -> _Source:
    """入れ子の値を、tuple を配列にしながら 1 要素ずつ写す（旧 `_jsonable_nested_tuple`）。"""

    return _Nested(value)


def as_list(items: Iterable[Any]) -> _Source:
    """既存の iterable を配列として 1 要素ずつ写す（旧 `list(x)`。要素はそのまま）。"""

    return _Each(items, _RAW)


def as_dict(mapping: Any) -> _Source:
    """既存の mapping を 1 組ずつ写す（旧 `dict(x)`。値はそのまま）。"""

    return _MappingOf(mapping, _RAW)


def mapping_of(
    mapping: Any,
    fn: Optional[Callable[[Any], Any]] = None,
    *,
    stringify_keys: bool = False,
) -> _Source:
    """既存の mapping の値を 1 つずつ source として辿る（旧 `{str(k): fn(v) ...}`）。

    `stringify_keys` は key を walker が文字列にする（scalar と、scalar だけから成る tuple だけ。
    それ以外の key は JSON にならない値。任意の key 変換の callable は受けない）。
    """

    _require_converter(fn, "mapping_of")
    return _MappingOf(mapping, fn, stringify_keys)


class _PairsView:
    """(key, 値) の組を 1 つずつ返す iterable を mapping の形で見せる（1 回だけ辿る）。"""

    __slots__ = ("_pairs",)

    def __init__(self, pairs: Iterable[Tuple[Any, Any]]) -> None:
        self._pairs = pairs

    def items(self) -> Iterator[Tuple[Any, Any]]:
        return _walk_iter(self._pairs)


def pairs_of(
    pairs: Iterable[Tuple[Any, Any]],
    fn: Optional[Callable[[Any], Any]] = None,
) -> _Source:
    """(key, 値) の組の遅延列を object として 1 組ずつ写す（旧 `{k: fn(v) for k, v in ...}`）。

    `pairs` は generator でよい（walker が 1 組ずつ引き出す。1 回だけ辿る）。
    """

    _require_converter(fn, "pairs_of")
    return _MappingOf(_PairsView(pairs), fn)


#: package の code が作った generator か（判定は `live_values` だけが持つ。本体は J1 / J19 が検査する）
package_generator = live_values.package_generator


def _one_shot_items(items: Any) -> bool:
    """1 回しか辿れない列か（組み込みの容器の iterator・package の generator）。"""

    return package_generator(items) or (builtin_iterator(items) and type(items) is not range)


def _walkable_items(items: Any) -> bool:
    """`each` の列を辿ってよいか: 組み込みの振る舞いの容器・その iterator / view・package の generator。"""

    return (
        builtin_sequence(items) or builtin_set(items) or builtin_iterator(items)
        or package_generator(items) or builtin_mapping(items) is not None
    )


def _walk_iter(items: Any) -> Iterator[Any]:
    """walker が辿ってよい列の iterator（それ以外は `TypeError`。上書きした `__iter__` を呼ばない）。"""

    if not _walkable_items(items):
        raise TypeError(f"{type_name(type(items))} is not a builtin iterable")
    return iter(items)


def _is_one_shot(source: Any) -> bool:
    """1 回しか辿れない列か（iterator、iterator を包む `each` / `pairs_of`）。辿った後は読み直せない。"""

    if _one_shot_items(source):
        return True
    kind = type(source)
    if kind is _Each or kind is _Flatten:
        return _one_shot_items(source.values if kind is _Flatten else source.items)
    if kind is _MappingOf:
        mapping = source.mapping
        return type(mapping) is _PairsView and _one_shot_items(mapping._pairs)
    return False


def inline(*pairs: Tuple[Any, Any]) -> _Source:
    """固定個数の (key, source) から成る object（`each` の要素 1 つ分の表示など）。"""

    return _Inline(tuple(pairs))




def _record_protocol(kind: type, name: str) -> Any:
    """型の MRO が持つ protocol の method（`json_items` / `__json_tree__`）。package の code の関数だけ。

    信頼は関数の code の file（書き換えられない）で決める。型の `__module__` は書き換えられるので使わない。
    """

    if not live_values.package_type(kind):
        # （hash・比較を上書きした metaclass の型もここで外れる: 下の cache の key にしない）
        return None
    key = (kind, name)
    known = _RECORD_PROTOCOLS.get(key, _NO_PROTOCOL)
    if known is _NO_PROTOCOL:
        method = type_attribute(kind, name)
        known = _RECORD_PROTOCOLS[key] = method if live_values.package_function(method) else None
    return known


#: 型と名前ごとの `_record_protocol` の結果（package の型だけ）
_RECORD_PROTOCOLS: dict = {}
_NO_PROTOCOL = object()


def protocol_method(value: Any, name: str) -> Any:
    """package の型が定義した protocol の関数（無ければ `TypeError`）。"""

    method = _record_protocol(type(value), name)
    if method is None:
        raise TypeError(f"{type_name(type(value))} has no package {name}")
    return method


def is_json_record(value: Any) -> bool:
    """walker が辿れる object（package の型の `json_items()` を持つ record か、sized leaf）か。"""

    kind = type(value)
    return _record_protocol(kind, "json_items") is not None or _record_protocol(kind, "__json_tree__") is not None


def raw(value: Any) -> _Source:
    """旧 `to_dict` が値をそのまま置いていた場所（LEGACY では変換しない。数えはする）。"""

    return _Raw(value)


def evidence(
    value: Any,
    identity: Optional[str] = None,
    *,
    reread: Optional[Reread] = None,
    inline_bytes: Optional[int] = None,
) -> _Source:
    """重くなり得る証拠（key / evidence）。出力では有界な表現、`to_dict()` では元の値。

    `identity` は大きいときに使う identity（呼ぶ側が O(1) で作った文字列。callable は受けない）。
    省くと値の fingerprint を作業量の中で求める。`value` が遅延列（1 回しか辿れない）を含むなら
    `reread`（読み直す手順）を渡す。
    """

    return _Evidence(value, identity, reread, inline_bytes)


def text(value: Any, max_chars: int) -> _Source:
    """自由文。出力では `max_chars` 文字まで（超えた分は明示の marker）、`to_dict()` では元の値。"""

    return _Text(value, max_chars)


class Reducer:
    """`scan` の reducer の protocol（walker が呼ぶ集計の callback はこれだけ）。

    * `add(element, *, work)` — 要素 1 つを畳む。要素の中で入力に比例する仕事（列を辿る・
      文字列を hash する・行を作る）をするなら、**する前に** `work.charge` へ数える。
    * `result(*, work)` — 集計の source を返す（大きさは畳んだ要素の数以下）。
    walker は要素を 1 つ引き出すたびに 1 を数え、`work` に walk の作業量（`effort`）を渡す。
    任意の callable（key 関数・cost 関数）は受けない。
    """

    __slots__ = ()

    def add(self, element: Any, *, work: "JsonBudget") -> None:  # pragma: no cover - protocol
        raise NotImplementedError

    def result(self, *, work: "JsonBudget") -> Any:  # pragma: no cover - protocol
        raise NotImplementedError


def scan(values: Any, reducer: Reducer) -> _Source:
    """集計（件数・group by）: walker が `values` を 1 要素ずつ引き出して `reducer` へ渡す。

    `reducer` は `Reducer`（`add` / `result` が walk の作業量を受け取る）。作業量を使い切れば
    **その walk の予算の超過** にする（集計は途中で止めると値が変わるので marker / 限界 /
    契約違反は field の規則どおり）。集計の producer は入力全体を先に辿らない。
    """

    kind = type(reducer)
    if not (
        issubclass(kind, Reducer)
        and live_values.package_type(kind)
        and live_values.package_function(type_attribute(kind, "add"))
        and live_values.package_function(type_attribute(kind, "result"))
    ):
        raise TypeError(f"scan takes a package Reducer, not {type_name(kind)}")
    return _Scan(values, reducer)


def flatten(values: Any, attribute: Optional[str] = None) -> _Source:
    """`values` の要素の属性 `attribute`（組み込みの振る舞いの列）を順に並べた遅延列。

    `attribute` が `None` なら要素そのものが列（`itertools.chain(*values)` の代わり）。walker が
    外の要素も内の要素も 1 つずつ引き出して数える（属性を読むのは `live_values.attribute`。任意の
    callable は受けない）。要素を yield しないで探す・読み飛ばす仕事を producer に書かせない。
    """

    if attribute is not None and type(attribute) is not str:
        raise TypeError("flatten reads an attribute by name, not a callable")
    return _Flatten(values, attribute)


class Tally(Reducer):
    """`scan` の reducer: 要素の属性 `attribute` の値ごとの件数（最初に現れた順）。

    key は属性を読むだけ（任意の key 関数は受けない）。key は scalar だけ（それ以外は JSON に
    ならない値）。
    """

    __slots__ = ("attribute", "counts")

    def __init__(self, attribute: str) -> None:
        if type(attribute) is not str:
            raise TypeError("Tally counts by an attribute name, not a callable")
        self.attribute = attribute
        self.counts: Dict[Any, int] = {}

    def add(self, element: Any, *, work: "JsonBudget") -> None:
        key = hashable_key(live_values.attribute(element, self.attribute), work)
        if not (key is None or (type(key) is str or type(key) is int or type(key) is float or type(key) is bool)):
            raise TypeError(f"Tally key {type_name(type(key))} is not a scalar")
        self.counts[key] = self.counts.get(key, 0) + 1

    def result(self, *, work: "JsonBudget") -> Any:
        return pairs_of(iter(self.counts.items()))


#: `int` 1 つを書いたときの byte 数の上限（64 bit 符号付き）
INT_MAX_BYTES = 20


# ---------------------------------------------------------------------------
# 有界な証拠
# ---------------------------------------------------------------------------


#: 証拠をそのまま出してよい大きさ（JSON byte）。これを超える証拠は identity + 要約になる
#: （出力 schema の上限の根拠）。
EVIDENCE_INLINE_BYTES = 2048
#: 要約の identity / kind の最大文字数（schema 上の上限）
EVIDENCE_IDENTITY_MAX_CHARS = 96
EVIDENCE_KIND_MAX_CHARS = 64
#: 長い文字列の marker に入れる識別の窓（`work` を使い切ったときの有界な digest の範囲）
TEXT_MARKER_WINDOW_CHARS = 4096
#: `text()` が超えたときに足す marker の最大文字数（schema 上の上限。marker の書式から導く:
#: `…[+<最大 20 桁> chars sha256w:<64 桁>]`）
TEXT_MARKER_MAX_CHARS = len("…[+") + 20 + len(" chars sha256w:") + 64 + len("]")


#: 有界な証拠の文字列 field に許す文字（JSON で escape されない印字可能な ASCII）。
#: これで `EVIDENCE_SUMMARY_MAX_BYTES` が書き出しの byte 数の上限になる。
_PRINTABLE_WITHOUT_ESCAPE = re.compile(r'[ !#-\[\]-~]*')


@dataclass(frozen=True, eq=False)
class BoundedEvidence:
    """大きい証拠の代わりに置く有界な表現（fingerprint・種類・大きさの下限）。

    authority 確定前（または出力の準備の中）に `bounded_evidence` だけが作り、以後は元の値を
    参照しない。

    * `fingerprint` は **照合用の key**（collision-resistant な SHA-256）で、値の等しさの証明では
      ない。`fingerprint_kind`:
      - `canonical_sha256` — `authority_digest(元の値)` と同じ値（canonical な形の JSON の sha256）
      - `token_sha256` — canonical な値にならない証拠（live な object など）の型つき token 列の sha256
      - `authority_identity` — 呼ぶ側が渡した identity（例: `cause:<id>`。authority が封印した値）
    * 作業量の上限・閉路・未対応の値で fingerprint を求められなかったときは `fingerprint` が
      `None` で、`unfingerprinted` に理由を持つ（照合には使えない）。
    * `encoded_bytes_over` は元の値を書いたときの byte 数の **下限**（その byte 数を超える）。
      測らなかった（plain でない値）なら 0。
    * `==` は **要約どうし** の等しさ（同じ fingerprint・種類・下限）で、元の値の等しさを意味
      しない。元の値が等しいかを確かめる用途に使わない。fingerprint の無い要約は **自分自身と
      だけ** 等しい（別の値の要約を同じものとして重ねない）。
    """

    fingerprint: Optional[str]
    fingerprint_kind: Optional[str]
    kind: str
    encoded_bytes_over: int = 0
    unfingerprinted: Optional[str] = None

    def _fields(self) -> Tuple[Any, ...]:
        return (self.fingerprint, self.fingerprint_kind, self.kind, self.encoded_bytes_over)

    def __eq__(self, other: Any) -> bool:
        if type(other) is not BoundedEvidence:
            return NotImplemented
        if self.fingerprint is None or other.fingerprint is None:
            return self is other
        return self._fields() == other._fields()

    def __hash__(self) -> int:
        if self.fingerprint is None:
            return object.__hash__(self)
        return tuple.__hash__(self._fields())

    def __post_init__(self) -> None:
        for name, limit in (
            ("fingerprint", EVIDENCE_IDENTITY_MAX_CHARS),
            ("fingerprint_kind", EVIDENCE_KIND_MAX_CHARS),
            ("kind", EVIDENCE_KIND_MAX_CHARS),
            ("unfingerprinted", EVIDENCE_KIND_MAX_CHARS),
        ):
            value = getattr(self, name)
            if value is None and name != "kind":
                continue
            if (
                type(value) is not str or len(value) > limit
                or not _PRINTABLE_WITHOUT_ESCAPE.fullmatch(value)
            ):
                raise ValueError(
                    f"bounded evidence {name} must be short printable ASCII without escapes"
                )
        if (self.fingerprint is None) != (self.fingerprint_kind is None):
            raise ValueError("a bounded evidence fingerprint needs its kind")
        if (self.fingerprint is None) == (self.unfingerprinted is None):
            raise ValueError("bounded evidence has either a fingerprint or the reason it has none")

    def summary(self) -> dict:
        payload = {
            "bounded_evidence": "v2",
            "fingerprint": self.fingerprint,
            "fingerprint_kind": self.fingerprint_kind,
            "kind": self.kind,
            "encoded_bytes_over": live_values.as_int(self.encoded_bytes_over),
        }
        if self.unfingerprinted is not None:
            payload["unfingerprinted"] = self.unfingerprinted
        return payload

    def to_authority_dict(self) -> dict:
        return self.summary()




#: `BoundedEvidence.summary()` を書いたときの byte 数の上限（schema 上の上限）
EVIDENCE_SUMMARY_MAX_BYTES = (
    2 + 6 * 4  # 括弧と区切り（6 member、区切りは最大 2 byte と見積もる）
    + len('"bounded_evidence": "v2"')
    + len('"fingerprint": ') + 2 + EVIDENCE_IDENTITY_MAX_CHARS
    + len('"fingerprint_kind": ') + 2 + EVIDENCE_KIND_MAX_CHARS
    + len('"kind": ') + 2 + EVIDENCE_KIND_MAX_CHARS
    + len('"encoded_bytes_over": ') + 20
    + len('"unfingerprinted": ') + 2 + EVIDENCE_KIND_MAX_CHARS
)


def text_value_max_bytes(policy: "JsonEncodingPolicy", max_chars: int) -> int:
    """`text(value, max_chars)` が書く値の byte の上限（**唯一の定義**）。

    文字列は `max_chars` 文字以内ならそのまま、超えれば先頭 + marker で `max(max_chars,
    TEXT_MARKER_MAX_CHARS)` 文字以内（`_text_marker`）。文字列でない値は、その上限以下なら
    そのまま、超えれば有界な証拠の要約（`EVIDENCE_SUMMARY_MAX_BYTES` 以下）。
    """

    return max(
        4, policy.max_string_bytes(max(live_values.as_int(max_chars), TEXT_MARKER_MAX_CHARS)), EVIDENCE_SUMMARY_MAX_BYTES,
    )


#: fingerprint を求められなかった理由（`BoundedEvidence.unfingerprinted`）
UNFINGERPRINTED_WORK_EXHAUSTED = "work_exhausted"
UNFINGERPRINTED_CYCLE = "cycle"
UNFINGERPRINTED_UNSUPPORTED = "unsupported"
#: 値を持たない live な object（key も record の表現も field も無い）を含む: 型名しか分からないので
#: 値の fingerprint を作らない（別の値を同じ fingerprint にしない）
UNFINGERPRINTED_OPAQUE = "opaque"


def _source_value(value: Any) -> Any:
    """source の包み（`each` / `nested` / `raw`）なら中の値（fingerprint は値で求める）。"""

    kind = type(value)
    if kind is _Each and value.fn in (None, _RAW):
        return value.items
    if kind is _Nested or kind is _Raw:
        return value.value
    if kind is _MappingOf and value.fn in (None, _RAW) and type(value.mapping) is not _PairsView:
        return value.mapping
    if issubclass(kind, _Source):
        raise TypeError("a lazy source is summarized by its token digest")
    return value


def _value_kind(value: Any) -> str:
    kind = type(value)
    if kind is _Each:
        value = value.items
    elif kind is _Flatten:
        value = value.values
    elif kind is _MappingOf:
        value = value.mapping
        if type(value) is _PairsView:
            return "mapping"
    elif kind is _Nested or kind is _Raw:
        value = value.value
    name = type_name(type(value))
    # 組み込みの振る舞いの容器だけ長さを読む（上書きした `__len__` を呼ばない）
    if builtin_sequence(value) or builtin_mapping(value) is not None:
        return f"{name}[{live_values.size(value)}]"[:EVIDENCE_KIND_MAX_CHARS]
    return name[:EVIDENCE_KIND_MAX_CHARS]


# ---------------------------------------------------------------------------
# 行の schema（大きさの上限を型で持つ record の書き方）
# ---------------------------------------------------------------------------


#: 列の種類。`TEXT` は文字数の上限つき文字列（出力では超えた分を marker にする）、
#: `EVIDENCE` は有界な証拠（`evidence()`）、`INT` / `BOOL` は scalar。
TEXT = "text"
EVIDENCE = "evidence"
INT = "int"
BOOL = "bool"
_COLUMN_KINDS = frozenset({TEXT, EVIDENCE, INT, BOOL})


@dataclass(frozen=True)
class Column:
    """行（record の JSON object）の 1 列。**出力での大きさの上限** を型で持つ。

    * `key` — JSON の key。`attr` を省くと同名の属性を読む。
    * `kind` / `max_chars` — 出力（CANONICAL）での上限。`TEXT` は `max_chars` 文字
      （+ marker）、`EVIDENCE` は `EVIDENCE_INLINE_BYTES`（大きければ有界な要約）。
    * `legacy` — `to_dict()`（LEGACY）での写し方（旧 `to_dict` の `list(x)` など）。
      出力でも同じ構造を辿り、そのうえで上限を掛ける。
    * `omit_none` — 値が `None` なら member を出さない（旧 `to_dict` の条件付き key）。

    行の上限は `row_max_bytes`（出力 schema の headroom の根拠）。
    """

    key: str
    kind: str
    max_chars: int = 0
    attr: Optional[str] = None
    legacy: Optional[Callable[[Any], Any]] = None
    omit_none: bool = False
    #: `EVIDENCE` の列でそのまま置いてよい大きさ（既定は `EVIDENCE_INLINE_BYTES`）
    inline_bytes: Optional[int] = None

    def __post_init__(self) -> None:
        if self.kind not in _COLUMN_KINDS:
            raise ValueError(f"unknown column kind {self.kind!r}")
        if self.kind == TEXT and self.max_chars <= 0:
            raise ValueError(f"{self.key}: a text column needs max_chars")
        _require_converter(self.legacy, f"Column({self.key}).legacy")

    def source(self, value: Any, identity: Optional[str] = None, record: Any = None) -> Any:
        if self.kind == TEXT:
            return text(value, self.max_chars)
        if self.kind == EVIDENCE:
            return evidence(
                self._legacy_source(value), identity,
                reread=None if record is None else Reread(record, self.attr or self.key, self.legacy),
                inline_bytes=self.inline_bytes,
            )
        return value

    def _legacy_source(self, value: Any) -> Any:
        if value is not None and type(value) is not BoundedEvidence and self.legacy is not None:
            return self.legacy(value)
        return value

    def max_value_bytes(self, policy: "JsonEncodingPolicy") -> int:
        if self.kind == TEXT:
            return text_value_max_bytes(policy, self.max_chars)
        if self.kind == EVIDENCE:
            inline = EVIDENCE_INLINE_BYTES if self.inline_bytes is None else self.inline_bytes
            return max(4, inline, EVIDENCE_SUMMARY_MAX_BYTES)
        if self.kind == INT:
            return INT_MAX_BYTES
        return 5


def column_identity(identity: Optional[str], column: str) -> Optional[str]:
    """record の identity（例: `cause:<id>`）の、列 1 つ分の identity（`<identity>#<列>`）。"""

    return None if identity is None else f"{identity}#{column}"


def row_items(row: Tuple[Column, ...], record: Any, *, identity: Any = None):
    """`row` の列を `record` から読んで `(key, source)` を 1 つずつ返す（`json_items` の本体）。"""

    for column in row:
        name = column.attr or column.key
        # 行の record は package の型（列の値は instance の値か record の property）
        value = live_values.attribute(record, name)
        if column.omit_none and value is None:
            continue
        # identity は列ごと（同じ record の別の列の値に同じ fingerprint を付けない）
        yield column.key, column.source(value, column_identity(identity, column.key), record)


def row_max_bytes(row: Tuple[Column, ...], policy: Optional["JsonEncodingPolicy"] = None) -> int:
    """`row` の行を出力（CANONICAL）で書いたときの byte 数の上限。"""

    policy = RESULT_JSON_POLICY if policy is None else policy
    sizes = [policy.member_bytes(column.key, column.max_value_bytes(policy)) for column in row]
    return policy.container_frame_bytes(len(sizes)) + sum(sizes)


def row_min_bytes(row: Tuple[Column, ...], policy: Optional["JsonEncodingPolicy"] = None) -> int:
    """`row` の行を書いたときの byte 数の **下限**（省ける列は省き、値は最小の 1 byte）。"""

    policy = RESULT_JSON_POLICY if policy is None else policy
    sizes = [policy.member_bytes(column.key, 1) for column in row if not column.omit_none]
    return policy.container_frame_bytes(len(sizes)) + sum(sizes)


def max_rows_within(max_bytes: int, row_min: int, policy: Optional["JsonEncodingPolicy"] = None) -> int:
    """配列の byte 数が `max_bytes` 以下であり得る行数の上限（行の下限 `row_min` から）。

    これより多い行の配列は、行がどれだけ小さくても `max_bytes` を超える。上限を超える列を
    1 行ずつ辿らずに（件数だけで）判定するための値。
    """

    policy = RESULT_JSON_POLICY if policy is None else policy
    sep = utf8_length(policy.item_separator)
    if max_bytes < 2:
        return 0
    return max(0, (live_values.as_int(max_bytes) - 2 + sep) // (live_values.as_int(row_min) + sep))


# ---------------------------------------------------------------------------
# 予算（walker が数えた byte を渡す相手）
# ---------------------------------------------------------------------------


#: いま走っている walk の作業量（`_Walk.run` の間だけ）。その間に作った `JsonBudget` は子になる
_ACTIVE_WORK: "contextvars.ContextVar[Optional[JsonBudget]]" = contextvars.ContextVar(
    "json_encoding_active_work", default=None,
)


def active_walk_work() -> Optional["JsonBudget"]:
    """今 walk の中なら、その walk の作業量（walk の外なら `None`）。"""

    return _ACTIVE_WORK.get()


class JsonBudget:
    """walker が数えた byte を受け取る相手（上限を超えたら `exceeded()`）。

    snapshot 側の aggregate（`core/budget_policy.SerializationWork`）は継承せずに
    同じ interface（`charge` / `remaining` / `tree` / `exceeded`）を持ち、超過を
    pair terminal な限界に変え、木の distinct node も数える。
    """

    def __init__(self, max_bytes: Optional[int], *, detached: bool = False) -> None:
        # 上限は必ず渡す（既定値なし）。`None` は上限なしで、作ってよい場所は登録してある
        # （`tests/unit/test_architecture_boundaries.py` の J7）
        if not detached and _ACTIVE_WORK.get() is not None:
            # walk の中（converter・reducer・`json_items`）で新しい予算を作らない: その仕事は
            # walk の作業量へ `count_into(value, work)` で数える（owner は 1 つ）。数え済みの値を
            # 写し直す・大きさだけを返して呼ぶ側が 1 回数える登録した場所だけが `detached=True`
            raise TypeError("a work scope cannot start inside a walk; count into the walk's work instead")
        self.max_bytes = None if max_bytes is None else live_values.as_int(max_bytes)
        self.consumed = 0
        self.detached = detached
        #: 数えた量をそのまま数える呼ぶ側の作業量（`count_into` などの effort だけが持つ）
        self.parent: Optional["JsonBudget"] = None

    def remaining(self) -> Optional[int]:
        own = None if self.max_bytes is None else self.max_bytes - self.consumed
        parent = self.parent
        if parent is None:
            return own
        inherited = parent.remaining()
        if own is None:
            return inherited
        return own if inherited is None else min(own, inherited)

    def charge(self, size: int) -> None:
        if type(size) is not int:
            size = live_values.as_int(size)
        self.consumed += size
        if self.max_bytes is not None and self.consumed > self.max_bytes:
            self.exceeded()
        if self.parent is not None:
            self.parent.charge(size)

    def exceeded(self) -> None:
        # 超えた事実は上限 + 1 以上として伝える（作業量（effort）が先に尽きて止めたときも、
        # 呼ぶ側が「測った大きさ」を上限の内側と読み違えない。`JsonBudgetExhausted` の契約）
        # 値は上限 + 1（どこまで辿ってから止めたか・cache の当たり方に依らない）
        consumed = self.consumed if self.max_bytes is None else self.max_bytes + 1
        raise JsonBudgetExhausted(consumed_bytes=consumed, max_bytes=self.max_bytes)

    def tree(self, leaf: Any, *, build: bool, substitutable: bool = False) -> Tuple[Any, int]:
        """sized leaf の大きさを **作る前に** 求めて足し、`build` なら木を作る。

        `substitutable` は `SerializationWork.tree` と同じ interface（この予算は置き換えを持たない）。
        """

        remaining = self.remaining()
        # sized leaf の protocol は package の型の関数を直接呼ぶ（instance の属性を引かない）
        # 見積もりの作業量は今の walk の作業量（walk の外ならこの予算）へ数える（byte と分ける）
        active = _ACTIVE_WORK.get()
        size = protocol_method(leaf, "__json_tree_bytes__")(
            leaf, RESULT_JSON_POLICY, remaining, self if active is None else active,
        )
        if size is None:
            # DAG のまま見積もれない形（閉路。未凍結の式の中だけ）: node を 1 つ作るたびに
            # 数えながら作る（作ってから数えない）
            before = self.consumed
            built = protocol_method(leaf, "__json_tree_metered__")(leaf, RESULT_JSON_POLICY, self)
            return (built if build else None), self.consumed - before
        self.charge(size)
        return (protocol_method(leaf, "__json_tree__")(leaf) if build else None), size


# ---------------------------------------------------------------------------
# prepared value
# ---------------------------------------------------------------------------


_PREPARED_TOKEN = object()


class PreparedJson:
    """CANONICAL walker だけが作る canonical な JSON 値と、それを書いたときの byte 数。"""

    __slots__ = ("_value", "encoded_bytes", "policy")

    def __init__(self, value: Any, encoded_bytes: int, policy: "JsonEncodingPolicy", *, _token: Any) -> None:
        if _token is not _PREPARED_TOKEN:
            raise TypeError("PreparedJson is created only by JsonEncodingPolicy.prepare")
        self._value = value
        self.encoded_bytes = live_values.as_int(encoded_bytes)
        self.policy = policy

    def value(self) -> Any:
        """canonical な値の複製（container だけ作り直す。scalar は immutable）。"""

        return _copy_canonical(self._value)

    def __repr__(self) -> str:  # pragma: no cover - debug 表示
        return f"PreparedJson({self.encoded_bytes} bytes)"


def is_prepared_json(value: Any) -> bool:
    return type(value) is PreparedJson


def _copy_canonical(value: Any) -> Any:
    # canonical な値は walker が作った dict / list / scalar だけ（型そのもので判定する）
    if type(value) is not dict and type(value) is not list:
        return value
    root: List[Any] = [None]
    stack: List[Tuple[Any, Any, Any]] = [(value, root, 0)]
    while stack:
        source, parent, key = stack.pop()
        if type(source) is dict:
            out: Any = {}
            parent[key] = out
            for child_key, child in source.items():
                if type(child) is dict or type(child) is list:
                    out[child_key] = None
                    stack.append((child, out, child_key))
                else:
                    out[child_key] = child
        elif type(source) is list:
            out = [None] * len(source)
            parent[key] = out
            for index, child in enumerate(source):
                if type(child) is dict or type(child) is list:
                    stack.append((child, out, index))
                else:
                    out[index] = child
        else:
            parent[key] = source
    return root[0]


# ---------------------------------------------------------------------------
# policy
# ---------------------------------------------------------------------------


#: surrogate の code point（Python の文字列では単独の文字。surrogateescape で読んだ file 名など）。
#: `ensure_ascii=False` の書き出しでも `\uXXXX` に escape する（UTF-8 で書けないため。
#: JSON の読み手は同じ code point に戻す）。数え方も同じ規則（1 文字 6 byte）。
_SURROGATE = re.compile("[\ud800-\udfff]")
#: 長い文字列を数える・書くときの 1 回分の文字数（上限に届いたら残りを数えない単位。owner は
#: `core/canonical_digest.STRING_CHUNK`: fingerprint の streaming と同じ単位）
_STRING_CHUNK = STRING_CHUNK

CANONICAL = "canonical"
LEGACY = "legacy"


#: 整列の key（組の先頭。lambda を使わない）
_FIRST = operator.itemgetter(0)


def _escaped_surrogate(match: Any) -> str:
    """surrogate 1 文字の `\\uXXXX`（`re.sub` の置換）。"""

    return "\\u%04x" % ord(match.group(0))


def _float_text(value: float) -> str:
    """`json` が float を書くときの文字列（`allow_nan=True` の既定どおり）。"""

    if value != value:
        return "NaN"
    if value == float("inf"):
        return "Infinity"
    if value == -float("inf"):
        return "-Infinity"
    return float.__repr__(value)


#: log10(2) の下からの有理数近似（1233 / 4096 = 0.301025390625 < log10(2) = 0.30102999566...）
_LOG10_2_BELOW = (1233, 12)


def integer_digits_lower_bound(value: int) -> int:
    """`abs(value)` の 10 進の桁数の下界（符号は含まない）。文字列にせずに `bit_length` だけで決める。

    根拠: `value != 0` で bit 長が `b` なら `2 ** (b - 1) <= abs(value)` なので、桁数
    `floor(log10(abs(value))) + 1 >= floor((b - 1) * log10(2)) + 1 >= floor((b - 1) * 1233 / 4096) + 1`
    （`1233 / 4096 < log10(2)`）。`0` は 1 桁。
    """

    bits = int.bit_length(value)
    if bits == 0:
        return 1
    numerator, shift = _LOG10_2_BELOW
    return (((bits - 1) * numerator) >> shift) + 1


@dataclass(frozen=True)
class JsonEncodingPolicy:
    """JSON の書き方。数え方・変換・書き出しは必ずこの object を通す。"""

    ensure_ascii: bool = False
    sort_keys: bool = True
    item_separator: str = ", "
    key_separator: str = ": "

    def __post_init__(self) -> None:
        # 引数を束ねた `json.dumps`（値ごとに 1 度だけ作る。field ではないので比較・hash に入らない）
        object.__setattr__(self, "_bound_dumps", functools.partial(
            json.dumps, ensure_ascii=self.ensure_ascii, sort_keys=self.sort_keys,
            separators=(self.item_separator, self.key_separator),
        ))

    @property
    def separators(self) -> Tuple[str, str]:
        return (self.item_separator, self.key_separator)

    # -- framing -------------------------------------------------------------

    def container_frame_bytes(self, count: int) -> int:
        """`count` 個の要素を持つ object / array の括弧と要素間の区切りの byte 数。"""

        return 2 + utf8_length(self.item_separator) * max(0, live_values.as_int(count) - 1)

    def member_bytes(self, key: Any, value_bytes: int) -> int:
        """object の member 1 つ（key・key と値の区切り・値）の byte 数。"""

        return self.key_bytes(key) + utf8_length(self.key_separator) + live_values.as_int(value_bytes)

    def object_bytes(self, member_bytes: Iterable[int]) -> int:
        sizes = [live_values.as_int(size) for size in member_bytes]
        return self.container_frame_bytes(len(sizes)) + sum(sizes)

    def max_member_bytes(self, max_key_chars: int, value_bytes: int) -> int:
        """key が `max_key_chars` 文字以下の member 1 つの byte 数の上限。"""

        return self.max_string_bytes(max_key_chars) + utf8_length(self.key_separator) + live_values.as_int(value_bytes)

    def added_member_bytes(self, key: Any, value_bytes: int) -> int:
        """1 つ以上の member を持つ object に member を 1 つ足したときに増える byte 数。"""

        return utf8_length(self.item_separator) + self.member_bytes(key, value_bytes)

    def max_string_bytes(self, max_chars: int) -> int:
        """`max_chars` 文字以下の文字列を書いたときの byte 数の上限（最悪の escape = 6 byte/文字）。"""

        # 最悪の escape: `ensure_ascii` では非 BMP の 1 文字が `\uXXXX\uXXXX`（12 byte）、
        # それ以外では制御文字の `\u00XX`（6 byte）
        return 2 + (12 if self.ensure_ascii else 6) * live_values.as_int(max_chars)

    # -- 書き出し ------------------------------------------------------------

    def _encoder(self) -> json.JSONEncoder:
        return json.JSONEncoder(
            ensure_ascii=self.ensure_ascii,
            sort_keys=self.sort_keys,
            separators=self.separators,
        )

    def dumps(self, value: Any, *, default: Optional[Callable[[Any], Any]] = None) -> str:
        """上限なしで書く（大きさが既に分かっている小さい値だけに使う）。"""

        if default is None:
            # 引数を束ねた `json.dumps`（policy ごとに 1 度だけ作る。大量に呼ぶ fingerprint の経路）
            text_value = self._bound_dumps(value)
        else:
            text_value = json.dumps(
                value,
                ensure_ascii=self.ensure_ascii,
                sort_keys=self.sort_keys,
                separators=self.separators,
                default=default,
            )
        # `ensure_ascii` の出力は ASCII（surrogate は escape 済み）
        return text_value if self.ensure_ascii else self._escape_surrogates(text_value)

    def _escape_surrogates(self, text_value: str) -> str:
        """書いた JSON の中の surrogate を `\\uXXXX` にする（文字列の中にしか現れない）。"""

        if self.ensure_ascii or text_value.isascii():
            return text_value
        return _SURROGATE.sub(_escaped_surrogate, text_value)

    def encode_bounded(self, value: Any, *, max_bytes: Optional[int]) -> str:
        """上限付きで書く。上限を超えた時点で止め、途中までの断片も捨てる。"""

        parts: List[str] = []
        written = 0
        for chunk in self._encoder().iterencode(value):
            chunk = self._escape_surrogates(chunk)
            written += utf8_length(chunk)
            if max_bytes is not None and written > max_bytes:
                parts.clear()
                raise JsonOutputLimitExceeded(max_bytes=max_bytes, requested_bytes=written)
            parts.append(chunk)
        return "".join(parts)

    # -- 文字列と key ----------------------------------------------------------

    def _string_chunk_bytes(self, text_value: str) -> int:
        """引用符を除いた、文字列の一部を書いたときの byte 数（`json` の escape 関数で数える）。"""

        if self.ensure_ascii:
            return len(encode_basestring_ascii(text_value)) - 2
        quoted = encode_basestring(text_value)
        if quoted.isascii():
            return len(quoted) - 2
        # surrogate は `\uXXXX`（6 byte）で書く。surrogatepass の 3 byte との差を足す
        return len(quoted.encode("utf-8", "surrogatepass")) - 2 + 3 * len(_SURROGATE.findall(quoted))

    def string_bytes(self, text_value: str, *, max_bytes: Optional[int] = None) -> int:
        """文字列 1 つを JSON 文字列として書いたときの byte 数（引用符を含む）。

        `max_bytes` を超えた時点で `max_bytes + 1` を返して残りを数えない（chunk ごと）。
        """

        if max_bytes is not None and len(text_value) + 2 > max_bytes:
            return max_bytes + 1
        if max_bytes is None or len(text_value) <= _STRING_CHUNK:
            total = self._string_chunk_bytes(text_value) + 2
            if max_bytes is not None and total > max_bytes:
                return max_bytes + 1
            return total
        total = 2
        for start in range(0, len(text_value), _STRING_CHUNK):
            total += self._string_chunk_bytes(text_value[start:start + _STRING_CHUNK])
            if total > max_bytes:
                return max_bytes + 1
        return total

    def canonical_key(self, key: Any) -> str:
        """dict の key を JSON が書く文字列へ（`json` と同じ型変換）。"""

        if type(key) is str:
            return key
        if key is True:
            return "true"
        if key is False:
            return "false"
        if key is None:
            return "null"
        # subclass は JSON の scalar の規則（`live_values.json_scalar`）で基底型の値にする
        base = json_scalar(key)
        base_kind = type(base)
        if base_kind is str:
            return base
        if base_kind is int:
            return int.__repr__(base)
        if base_kind is float:
            return _float_text(base)
        raise TypeError(
            f"keys must be str, int, float, bool or None, not {type_name(type(key))}"
        )

    def key_bytes(self, key: Any) -> int:
        return self.string_bytes(self.canonical_key(key))

    # -- live → 表現 -----------------------------------------------------------

    def prepare(self, source: Any, *, max_bytes: Optional[int] = None) -> PreparedJson:
        """source を **上限まで** 引き出して canonical な JSON 値へ変える（出力の唯一の境界）。

        walk の外で使う（walk の中の入れ子の仕事は `count_into`）。
        """

        budget = JsonBudget(max_bytes)
        value = _Walk(self, CANONICAL, budget, build=True).run(source)
        return PreparedJson(value, budget.consumed, self, _token=_PREPARED_TOKEN)

    def prepare_into(self, source: Any, work: Any) -> Any:
        """source の canonical な JSON 値を、作りながら byte と作業量を `work` へ数える。

        写しは数えた走査そのものが作る（数えてから別の走査で写し直さない: 写しの中身と数えた量が
        食い違わない）。walk の中でも使える（予算を新しく作らない）。
        """

        return _Walk(self, CANONICAL, work, build=True, effort_to_budget=True).run(source)

    def measure(
        self, source: Any, *, max_bytes: Optional[int] = None, mode: str = CANONICAL,
        size_only: bool = False, effort: Optional[JsonBudget] = None,
    ) -> int:
        """`prepare`（mode=LEGACY なら `materialize`）と同じ走査で byte 数だけを数える。

        walk の外で使う。`size_only=True` は walk の中の登録した見積もり（大きさだけを返し、呼ぶ
        側がその大きさを **1 回だけ** 数える。上限は呼ぶ側の作業量の残り）でだけ使う（J16）。
        `effort` を渡すと、走査の作業量はその作業量（呼ぶ側の owner）へ数え、返すのは byte だけ
        （byte を出現の数だけ足す見積もりが、作業量を出現ごとに数え直さないため）。
        """

        if effort is not None:
            budget = JsonBudget(max_bytes, detached=True)
            _Walk(self, mode, budget, build=False, effort=effort).run(source)
            return budget.consumed
        budget = JsonBudget(max_bytes, detached=size_only)
        # 見積もり（`size_only`）は走査の作業量も返す大きさに含める: 呼ぶ側がそれを 1 回数える
        # （見積もりの effort を別の owner に残さない）
        _Walk(self, mode, budget, build=False, effort_to_budget=size_only).run(source)
        return budget.consumed

    def materialize(self, source: Any, *, budget: Optional[JsonBudget] = None, counted: bool = False) -> Any:
        """LEGACY 表現を作る（record の `to_dict()`・snapshot）。`budget` を渡すとそこへ数える。

        `counted=True` は大きさを数え終えた値を写すとき（数え直さない。walk の中でも作れる）。
        """

        if budget is None:
            return _Walk(self, LEGACY, JsonBudget(None, detached=counted), build=True).run(source)
        return _Walk(self, LEGACY, budget, build=True, effort_to_budget=True).run(source)

    def bounded_native_copy(self, value: Any, *, max_bytes: int) -> Optional[Tuple[Any, int]]:
        """JSON の値になる組み込みの型 **そのもの** だけの値の写しと、それを書いた byte 数。

        受けるのは葉 `None` / `bool` / `int` / 有限の `float` / `str` と、容器 `dict`（key は
        `str`）/ `list` / `tuple`（写しでも型を保つ）だけ。それ以外・閉路・`max_bytes` 超えなら `None`。

        **数え方は `dumps` が書く byte と同じ**（文字列は `string_bytes` の escape と UTF-8、key と
        値の区切り、要素の区切り、括弧）。数えるのは写す前で、合計が `max_bytes` を超えた時点で
        止まる: 写しの量も、辿る量（どの値も 1 byte 以上）も `max_bytes` で抑えられる。容器は
        先頭から 1 要素ずつ引き出し、上限の前に全体を写さない。整数は桁数の下界（`bit_length`）で
        残りを超えると分かれば文字列にしない。
        """

        item_sep = utf8_length(self.item_separator)
        key_sep = utf8_length(self.key_separator)
        total = 0
        root: List[Any] = [None]
        # [iterator, out, kind, id, first, parent, slot]
        stack: List[List[Any]] = [[iter((value,)), root, "root", None, True, None, None]]
        active: set = set()
        while stack:
            entry = stack[-1]
            try:
                item = next(entry[0])
            except StopIteration:
                stack.pop()
                if entry[3] is not None:
                    active.discard(entry[3])
                if entry[2] == "tuple":
                    entry[5][entry[6]] = tuple(entry[1])
                continue
            if entry[2] == "root":
                slot: Any = 0
            elif entry[4]:
                entry[4] = False
            else:
                total += item_sep
            if entry[2] == "dict":
                key, item = item
                if type(key) is not str:
                    return None
                total += self.string_bytes(key, max_bytes=max(0, max_bytes - total)) + key_sep
                slot = key
            elif entry[2] != "root":
                slot = len(entry[1])
                entry[1].append(None)
            if total > max_bytes:
                return None
            kind = type(item)
            if item is None:
                total += 4
            elif kind is bool:
                total += 4 if item else 5
            elif kind is int:
                # 文字列にする前に、桁数の **下界** だけで残りを超えると分かる整数を拒む（文字列化の
                # 仕事を残りの byte で抑える）。下界なので、収まる整数を拒まない
                if integer_digits_lower_bound(item) + (1 if item < 0 else 0) > max_bytes - total:
                    return None
                try:
                    total += len(int.__repr__(item))
                except ValueError:
                    return None
            elif kind is float:
                if item != item or item in (float("inf"), float("-inf")):
                    return None
                total += len(_float_text(item))
            elif kind is str:
                total += self.string_bytes(item, max_bytes=max(0, max_bytes - total))
            elif kind is dict or kind is list or kind is tuple:
                identity = id(item)
                if identity in active:
                    return None
                total += 2
                if total > max_bytes:
                    return None
                active.add(identity)
                out: Any = {} if kind is dict else []
                stack.append([
                    iter(item.items()) if kind is dict else iter(item),
                    out, "dict" if kind is dict else ("tuple" if kind is tuple else "list"),
                    identity, True, entry[1], slot,
                ])
                entry[1][slot] = out
                continue
            else:
                return None
            if total > max_bytes:
                return None
            entry[1][slot] = item
        return root[0], total

    def plain_bytes(
        self, value: Any, *, max_bytes: Optional[int] = None, size_only: bool = False,
        work: Optional[JsonBudget] = None,
    ) -> Optional[int]:
        """容器（tuple / list / dict）と基底型 **だけ** から成る値の byte 数（それ以外は `None`）。

        `size_only=True` は walk の中の登録した見積もり（呼ぶ側が返った大きさを 1 回だけ数える）。

        `max_bytes` を超えたら `JsonBudgetExhausted`。live な object（record・式・Ghidra の
        値など）を含む値は `None`（呼ぶ側は有界な証拠へ置き換える）。`work` を渡すと、`None` に
        なるまでに辿った分をその作業量へ数える（返った大きさは呼ぶ側が 1 回だけ数える）。
        """

        budget = JsonBudget(max_bytes, detached=size_only)
        done, _ = _Walk(self, LEGACY, budget, build=False, effort=work).plain(value, False)
        return budget.consumed if done else None

    def count_into(self, source: Any, budget: JsonBudget, *, mode: str = LEGACY) -> None:
        """source の byte 数を `budget` へ足す（作らない）。走査の作業量も `budget` へ数える。"""

        _Walk(self, mode, budget, build=False, effort_to_budget=True).run(source)

    def token_fingerprint(self, value: Any, *, work: "JsonBudget") -> str:
        """証拠の型つき token 列（dict は key 順）の sha256。辿る作業量を `work` へ数える。

        canonical な値にならない証拠（live な object を含む値）の fingerprint。作業量を超えたら
        `work` の例外（`JsonBudgetExhausted`）がそのまま上がる。
        """

        digest = hashlib.sha256()
        _Walk(self, LEGACY, work, build=False, token_sink=digest.update, effort_to_budget=True).run(value)
        return digest.hexdigest()


def evidence_kind(value: Any) -> str:
    """有界な証拠の `kind`（元の値の型と、容器なら要素数）。"""

    return _value_kind(value)


def bounded_evidence(
    value: Any,
    *,
    work: "JsonBudget",
    identity: Any = None,
    inline_bytes: Optional[int] = None,
    policy: Optional[JsonEncodingPolicy] = None,
) -> Any:
    """**証拠を有界にする唯一の入口**: 小さく plain なら値そのもの、それ以外は `BoundedEvidence`。

    辿る作業（大きさの確認・fingerprint）はすべて `work` へ数える。`work` を使い切っていたら、
    値を辿らずに fingerprint の無い `BoundedEvidence` にする（辿る量は `work` の上限で止まる）。

    * そのまま残すのは、容器と基底型だけから成り `inline_bytes`（既定 `EVIDENCE_INLINE_BYTES`）
      以下の値（live な object を持たない）。
    * `identity`（呼ぶ側が O(1) で作った文字列。callable は受けない）があれば、それを
      `authority_identity` の fingerprint にする（値は辿らない）。
    * それ以外は canonical な fingerprint（`core/canonical_digest.canonical_fingerprint`）、
      canonical な値にならなければ型つき token の fingerprint（`token_fingerprint`）。
    """

    if value is None or type(value) is BoundedEvidence:
        return value
    policy = RESULT_JSON_POLICY if policy is None else policy
    limit = EVIDENCE_INLINE_BYTES if inline_bytes is None else live_values.as_int(inline_bytes)
    over = 0  # 書いた byte 数の下限（plain でなく測れなければ 0）
    if not _exhausted(work):
        remaining = work.remaining()
        # 試しの予算（detached。使った分は下で `work` へ 1 回だけ数え戻す）
        attempt = JsonBudget(limit if remaining is None else min(limit, remaining), detached=True)
        try:
            # plain でないと分かるまでに辿った分は `work` へ直接数える（effort）
            done, _ = _Walk(policy, LEGACY, attempt, build=False, effort=work).plain(
                _source_value_or_self(value), False,
            )
        except JsonBudgetExhausted:
            done = False
            if attempt.consumed > attempt.max_bytes:
                over = attempt.max_bytes
        except PRODUCER_FAILURES:
            done = False
        _charge_quietly(work, attempt.consumed)
        if done and attempt.consumed <= limit:
            return value
    return _evidence_summary(value, work=work, identity=identity, policy=policy, over=over)


def _evidence_summary(
    value: Any, *, work: "JsonBudget", identity: Any, policy: JsonEncodingPolicy, over: int,
) -> BoundedEvidence:
    from scripts.function_tracer_pcode.core.canonical_digest import (
        CanonicalValueCycle,
        canonical_fingerprint,
    )

    kind = _value_kind(value)
    if identity is not None and type(identity) is not str:
        raise TypeError("an evidence identity is a precomputed str (no callable)")
    if identity is not None:
        return BoundedEvidence(
            fingerprint=_printable_identity(identity),
            fingerprint_kind="authority_identity",
            kind=kind,
            encoded_bytes_over=over,
        )
    if _exhausted(work):
        return _unfingerprinted(kind, UNFINGERPRINTED_WORK_EXHAUSTED, over)
    try:
        return BoundedEvidence(
            fingerprint=canonical_fingerprint(_source_value(value), work=work),
            fingerprint_kind="canonical_sha256",
            kind=kind,
            encoded_bytes_over=over,
        )
    except JsonBudgetExhausted:
        return _unfingerprinted(kind, UNFINGERPRINTED_WORK_EXHAUSTED, over)
    except CanonicalValueCycle:
        return _unfingerprinted(kind, UNFINGERPRINTED_CYCLE, over)
    except PRODUCER_FAILURES:
        # canonical な形を持たない（live な object・set の中の enum の mapping 値・深すぎる
        # set の入れ子）: 型つき token の fingerprint へ
        pass
    if _exhausted(work):
        return _unfingerprinted(kind, UNFINGERPRINTED_WORK_EXHAUSTED, over)
    try:
        return BoundedEvidence(
            fingerprint=policy.token_fingerprint(value, work=work),
            fingerprint_kind="token_sha256",
            kind=kind,
            encoded_bytes_over=over,
        )
    except JsonBudgetExhausted:
        return _unfingerprinted(kind, UNFINGERPRINTED_WORK_EXHAUSTED, over)
    except JsonValueCycle:
        return _unfingerprinted(kind, UNFINGERPRINTED_CYCLE, over)
    except _OpaqueLeaf:
        return _unfingerprinted(kind, UNFINGERPRINTED_OPAQUE, over)
    except (JsonValueRejected,) + PRODUCER_FAILURES:
        return _unfingerprinted(kind, UNFINGERPRINTED_UNSUPPORTED, over)


def _stringified_key(key: Any, work: "JsonBudget") -> str:
    """`mapping_of(stringify_keys=True)` の key の文字列（旧 `str(k)`）。

    組み込みの `str` / `repr` だけを使う: scalar と、scalar（と同じ形の tuple）だけから成る
    tuple。それ以外（`__str__` / `__repr__` を持つ object）は JSON にならない値（producer を
    呼ばない）。
    """

    kind = type(key)
    if kind is str:
        return key
    base = plain_scalar(key)
    if base is not NOT_PLAIN or _builtin_enum(key):
        # scalar（subclass は基底型の値）と組み込みのままの enum（`IntEnum` を含む）: 旧 `str(k)`
        return live_values.as_str(key)
    if kind is tuple:
        view = _plain_key_view(key, work)
        if view is not _NOT_PLAIN:
            # 基底型の値へ書き直した tuple の組み込みの `repr`（= `str`）
            return tuple.__repr__(view)
    raise TypeError(f"mapping key {type_name(kind)} is not stringified without its own __str__")


def stringify_plain_key(key: Any, work: "JsonBudget") -> str:
    """mapping の key の `str(key)`（scalar と scalar の tuple だけ。作る前に長さを `work` へ数える）。

    それ以外（`__str__` / `__repr__` を持つ object）は `TypeError`（producer を呼ばない）。
    """

    if type(key) is str:
        work.charge(1 + len(key))
        return key
    return _stringified_key(key, work)


def bounded_repr(value: Any, max_chars: int = 256) -> str:
    """組み込みの `repr` を上限の中でだけ使う（上書きした `__repr__` を呼ばない）。

    `None` / bool / 数値は組み込みの `repr`（桁数が大きい整数は桁数だけ）、文字列は先頭
    `max_chars` 文字の `repr`、それ以外は型名。
    """

    if value is None:
        return "None"
    if value is True or value is False:
        return "True" if value else "False"
    kind = type(value)
    # `repr` の規則（enum は型名）: 基底型の値は `live_values.plain_scalar` だけで読む
    base = plain_scalar(value)
    base_kind = type(base)
    if base_kind is int:
        bits = int.bit_length(base)
        return int.__repr__(base) if bits <= 1024 else f"<int {bits} bits>"
    if base_kind is float:
        return float.__repr__(base)
    if base_kind is str:
        return str.__repr__(base[:max_chars] if len(base) > max_chars else base)
    return f"<{type_name(kind)}>"


def hashable_key(value: Any, work: "JsonBudget") -> Any:
    """集計の key として hash・比較してよい値（hash する前に長さを `work` へ数える）。

    文字列・scalar・組み込みのままの enum・`BoundedEvidence`（固定長）・scalar の tuple は
    その値のまま（同じ値は同じ key）。それ以外（上書きした `__hash__` / `__eq__` を持ち得る
    object）は、その object の identity の key（`hash` / `==` を呼ばない。別の object は
    同じ値でも別の単位として数える — 集計を合併しない側へ倒す）。
    """

    if type(value) is str:
        work.charge(1 + len(value))
        return value
    return value_token(value, work)


def value_token(value: Any, work: Optional["JsonBudget"] = None, *, _depth: int = 0) -> Any:
    """live な値の、値で比べてよい決定的な印（`builtin_view` の写し・enum の名前・dataclass の field）。

    組み込みの値に書き直せる値はその写し、enum は (型名, 名前)、dataclass は (型名, field の印)。
    どれでもない値（field を持たない live な object）だけが `object_identity_token`（process の
    中でだけ意味を持つ）。`__str__` / `__repr__` / `__hash__` / property を呼ばない。
    """

    if work is None:
        # 作業量を渡されなければ固定の上限（`builtin_view` と同じ）の中でだけ辿る。超えれば
        # identity の印（値で比べない側へ倒す）
        units = _ViewUnits()
        try:
            return value_token(value, units, _depth=_depth)
        except _NotPlain:
            return object_identity_token(value)
    ok, view = builtin_view(value, work)
    if ok:
        return view
    kind = type(value)
    if issubclass(kind, Enum):
        work.charge(1)
        return ("<enum>", type_name(kind), live_values.enum_name(value))
    names = dataclass_field_names(value)
    if names is not None and _depth < _VALUE_TOKEN_MAX_DEPTH and type_attribute(kind, "to_authority_dict") is None:
        try:
            work.charge(1 + len(names))
            return ("<dataclass>", type_name(kind), tuple(
                (name, value_token(plain_field_value(value, name), work, _depth=_depth + 1)) for name in names
            ))
        except TypeError:
            pass
    return object_identity_token(value)


#: `value_token` が dataclass を辿る深さ（閉路・深い入れ子は identity の印）
_VALUE_TOKEN_MAX_DEPTH = 32


def object_identity_token(value: Any) -> Tuple[str, str, int]:
    """値で比べられない live な object の identity の印（型名と `id`。`hash` / `==` / `repr` を呼ばない）。

    別の object は同じ値でも別の印（集計を合併しない側へ倒す。旧実装の既定の `hash` / `repr` と
    同じく object ごとに区別する）。印は process の中でだけ意味を持つ（出力の値の等しさに使わない）。
    """

    return ("<object>", type_name(type(value)), id(value))


#: `plain_scalar` が scalar でない値に返す印（`live_values.NOT_PLAIN` と同じ object）
_NOT_PLAIN = NOT_PLAIN
#: 作業量を受け取らない `builtin_view` が書き直す量（要素と文字の数）の上限。超えれば書き直さない
#: （呼ぶ側は型名の印・identity の印へ倒す）。作業量を渡す呼び出しは作業量で止まる
BUILTIN_VIEW_MAX_UNITS = 1 << 16


class _ViewUnits:
    """作業量を受け取らない `builtin_view` の固定の上限（`JsonBudget` と同じ `charge` の protocol）。"""

    __slots__ = ("left",)

    def __init__(self) -> None:
        self.left = BUILTIN_VIEW_MAX_UNITS

    def charge(self, size: int) -> None:
        self.left -= size
        if self.left < 0:
            raise _NotPlain


#: 値の storage の読みを数える作業量の型（`live_values.metered_storage_reads` が受け取る）: 作業量
#: （`JsonBudget` と subclass の `SerializationWork`）と、作業量を受け取らない `builtin_view` の固定の単位
live_values.register_storage_meter(JsonBudget)
live_values.register_storage_meter(_ViewUnits)


def builtin_view(value: Any, work: Optional["JsonBudget"] = None) -> Tuple[bool, Any]:
    """組み込みの値だけで書き直した写し（`(True, 写し)`）。書き直せなければ `(False, None)`。

    scalar は基底型の値、組み込みのままの enum と `BoundedEvidence` はそのまま、tuple / list /
    dict / set / frozenset（型そのもの）は要素を書き直した同じ型。それ以外（live な object・
    組み込みでない容器・閉路）は書き直さない。写しの `str` / `repr` / `hash` / `==` は組み込みの
    実装だけで作られる。辿る前に文字列の長さ・容器の幅を `work`（無ければ固定の上限
    `BUILTIN_VIEW_MAX_UNITS`）へ数える。
    """

    units: Any = _ViewUnits() if work is None else work
    try:
        # 値の storage の読みも同じ単位で数える（作業量が無ければ固定の上限 `_ViewUnits`: 超えれば書き直さない）
        with live_values.metered_storage_reads(units):
            return True, _builtin_view_of(value, units, set())
    except (_NotPlain, RecursionError, TypeError):
        return False, None


def _builtin_view_of(item: Any, units: Any, active: set) -> Any:
    """`builtin_view` の 1 段（組み込みの scalar・enum・証拠と、組み込みの型そのままの容器だけ）。"""

    base = plain_scalar(item)
    if base is not NOT_PLAIN:
        units.charge(1 + len(base) if type(base) is str else 1)
        return base
    kind = type(item)
    if kind is BoundedEvidence or _builtin_enum(item):
        units.charge(1)
        return item
    if kind is tuple or kind is list or kind is set or kind is frozenset or kind is dict:
        if id(item) in active:
            raise _NotPlain
        units.charge(1 + len(item))
        active.add(id(item))
        try:
            if kind is dict:
                return {
                    _builtin_view_of(key, units, active): _builtin_view_of(child, units, active)
                    for key, child in items_of(item)
                }
            return kind(_builtin_view_of(child, units, active) for child in item)
        finally:
            active.discard(id(item))
    raise _NotPlain


def renders_with_builtins(value: Any) -> bool:
    """`value` を組み込みの値だけで書き直せるか（`builtin_view`。scalar の subclass も基底型として）。"""

    return builtin_view(value)[0]


def _builtin_text(view: Any) -> str:
    """`builtin_view` の写しの `str`（型の分かった組み込みの実装だけで作る）。"""

    if type(view) is str:
        return view
    if plain_scalar(view) is not NOT_PLAIN or _builtin_enum(view):
        return live_values.as_str(view)
    # tuple / list / dict / set / frozenset / `BoundedEvidence`: その型の組み込みの `__repr__`（= `str`）
    return type(view).__repr__(view)


def builtin_str(value: Any) -> str:
    """組み込みの `str` だけで作る文字列（`builtin_view` の写しの `str`。書き直せない値は型名の印）。

    上書きした `__str__` / `__repr__`（producer）を呼ばない。組み込みの値と、基底型と同じに書く
    scalar の subclass（JPype の `JInt` など）では `str(value)` と同じ文字列。
    """

    if type(value) is str:
        return value
    ok, view = builtin_view(value)
    if ok:
        return _builtin_text(view)
    return f"<{type_name(type(value))}>"


def _builtin_hashed_key(key: Any) -> bool:
    """新しい dict へ置いてよい key か（`__hash__` / `__eq__` が組み込みの実装: 組み込みの scalar と
    組み込みのままの enum）。"""

    kind = type(key)
    return (
        key is None or kind is str or kind is int or kind is bool or kind is float
        or _builtin_enum(key) or live_values.builtin_hashed_scalar(key)
    )


def _plain_key_view(part: Any, work: "JsonBudget") -> Any:
    """scalar と tuple だけから成る `part` の、基底型の値で書き直した写し（それ以外は `NOT_PLAIN`）。

    確かめる走査と写す走査は 1 回（要素を数えながら。`str()` の手間も同じ量で、上限は `work`
    だけ: 固定の上限で別に止めない）。
    """

    root: List[Any] = [None]
    stack: List[Tuple[Any, Any, int]] = [(part, root, 0)]
    # 子を写し終えてから tuple にする list（親が先に積まれる: 逆順に閉じる）
    closing: List[Tuple[List[Any], Any, int]] = []
    while stack:
        item, parent, index = stack.pop()
        kind = type(item)
        if kind is tuple:
            work.charge(1 + len(item))
            out: List[Any] = [None] * len(item)
            closing.append((out, parent, index))
            for position in range(len(item) - 1, -1, -1):
                stack.append((item[position], out, position))
        elif kind is str:
            work.charge(1 + len(item))
            parent[index] = item
        else:
            base = plain_scalar(item)
            if base is _NOT_PLAIN:
                return _NOT_PLAIN
            work.charge(1)
            parent[index] = base
    for out, parent, index in reversed(closing):
        parent[index] = tuple(out)
    return root[0]


def identity_key_of(value: Any, *, names: Tuple[str, ...] = ("stable_key", "to_key")) -> Tuple[bool, Any]:
    """producer の identity key（`names` の順: 既定は `stable_key()`、無ければ `to_key()`）。

    **bounded path がこれを呼ぶ唯一の場所**。method は型から引く（instance の `__getattr__` を
    呼ばない）。key を作る仕事は identity の owner の契約（#194）で、作業量を受け取らない —
    本 PR の依存として 1 箇所に閉じる。返った key は呼ぶ側が作業量の中で辿る。`names` は
    その値の identity の規則（例: 切り捨て事実は `stable_key` だけ）に合わせる。`(True, key)`
    か、key を持たなければ `(False, None)`。
    """

    kind = type(value)
    for name in names:
        # 型の `__dict__` の関数だけ（metaclass の hook・instance の `__getattr__` を呼ばない）
        method = type_attribute(kind, name)
        if live_values.package_function(method) and live_values.package_type(kind):
            return True, method(value)
    return False, None


def _reread(reread: Reread) -> Any:
    """証拠の値を読み直す（属性を読み、登録した converter で source にする。どちらも O(1)）。"""

    value = live_values.attribute(reread.record, reread.attribute)
    if value is None or type(value) is BoundedEvidence or reread.converter is None:
        return value
    return reread.converter(value)


def _unfingerprinted(kind: str, reason: str, over: int) -> BoundedEvidence:
    return BoundedEvidence(
        fingerprint=None, fingerprint_kind=None, kind=kind, encoded_bytes_over=over, unfingerprinted=reason,
    )


def _printable_identity(identity: str) -> str:
    """identity をそのまま書ける短い文字列に（長い・escape の要る identity は全体の digest。切り詰めない:
    切り詰めると先頭が同じ別の identity が同じ fingerprint になる）。"""

    text_value = str_value(identity)
    if text_value is NOT_PLAIN:
        raise TypeError(f"{type_name(type(identity))} is not an identity string")
    if len(text_value) > EVIDENCE_IDENTITY_MAX_CHARS or not _PRINTABLE_WITHOUT_ESCAPE.fullmatch(text_value):
        text_value = "sha256:" + hashlib.sha256(text_value.encode("utf-8", "surrogatepass")).hexdigest()
    return text_value


def _exhausted(work: "JsonBudget") -> bool:
    remaining = work.remaining()
    return remaining is not None and remaining <= 0


def _charge_quietly(work: "JsonBudget", size: int) -> None:
    """辿った分を `work` へ数える（使い切りは次の `_exhausted` で分かる。ここでは上げない）。"""

    try:
        work.charge(size)
    except JsonBudgetExhausted:
        pass


def _source_value_or_self(value: Any) -> Any:
    try:
        return _source_value(value)
    except TypeError:
        return value


def bounded_text(value: Any, max_chars: int, *, work: "JsonBudget") -> Any:
    """`value` が `max_chars` 文字を超える文字列なら、先頭 + 明示の marker に置き換える。

    marker は必ず識別の digest を持つ（marker の文字列を集計の key にする consumer がいる）:
    * 文字列の長さを `work` へ数えられれば、全体の SHA-256（`sha256:`）。
    * 数えられなければ、長さと先頭・末尾 `TEXT_MARKER_WINDOW_CHARS` 文字の SHA-256
      （`sha256w:`。範囲が有界な digest で、長さと先頭・末尾が同じ別の文字列とは区別しない）。
    """

    text_value = str_value(value)
    if text_value is not NOT_PLAIN and len(text_value) > max_chars:
        value = text_value
        digest = None
        if not _exhausted(work):
            try:
                work.charge(len(value))
            except JsonBudgetExhausted:
                pass
            else:
                digest = "sha256:" + _string_sha256(value)
        if digest is None:
            _charge_quietly(work, 2 * TEXT_MARKER_WINDOW_CHARS)
            digest = "sha256w:" + _window_sha256(value)
        return _text_marker(value, max_chars, digest)
    return value


def _string_sha256(value: str) -> str:
    hasher = hashlib.sha256()
    for start in range(0, len(value), _STRING_CHUNK):
        # 巨大な文字列を一度に encode しない（chunk ごとに hash へ流す）
        hasher.update(value[start:start + _STRING_CHUNK].encode("utf-8", "surrogatepass"))
    return hasher.hexdigest()


def _window_sha256(value: str) -> str:
    """長さと先頭・末尾の窓だけの SHA-256（範囲は `2 * TEXT_MARKER_WINDOW_CHARS` 文字で有界）。"""

    hasher = hashlib.sha256(int.__repr__(len(value)).encode("ascii") + b"\x1f")
    hasher.update(value[:TEXT_MARKER_WINDOW_CHARS].encode("utf-8", "surrogatepass") + b"\x1f")
    hasher.update(value[-TEXT_MARKER_WINDOW_CHARS:].encode("utf-8", "surrogatepass"))
    return hasher.hexdigest()


def _text_marker(value: str, max_chars: int, digest: Optional[str]) -> str:
    """`max_chars` 文字 **以内** に収まる「先頭 + 明示の marker」（同じ上限で冪等）。"""

    note = f" {digest}" if digest is not None else ""
    keep = max(0, max_chars - TEXT_MARKER_MAX_CHARS)
    tail = f"…[+{len(value) - keep} chars{note}]"
    keep = max(0, max_chars - len(tail))
    tail = f"…[+{len(value) - keep} chars{note}]"
    return (value[:keep] + tail)[:max(max_chars, len(tail))]


class _Frame:
    __slots__ = (
        "kind", "iterator", "out", "parent", "key", "count", "source_id", "source", "build",
        "keys", "fn", "current", "preserve_keys",
    )


#: 短い文字列の JSON byte 数の cache（policy ごと。key の語彙は繰り返し現れる）
_STRING_BYTES_CACHES: dict = {}
_STRING_BYTES_CACHE_MAX = 1 << 16
_SHORT_STRING = 128


#: tuple だけから成る部分木の byte 数（policy ごと、id → (値, byte 数)）。pair の終わりに
#: 空にする（`clear_size_caches`、`core/budget_policy.budget_policy_scope` が呼ぶ）
_PURE_TUPLE_SIZES: dict = {}
_PURE_TUPLE_CACHE_MAX = 1 << 18


def cached_string_bytes(policy: "JsonEncodingPolicy", text_value: str, *, max_bytes: Optional[int]) -> int:
    """短い文字列の JSON byte 数（policy ごとの cache を使う）。

    長い文字列は cache せず、`max_bytes` を超えた時点で数えるのをやめる（`string_bytes` の
    打ち切り。上限を知らずに文字列全体を escape しない）。
    """

    if len(text_value) > _SHORT_STRING:
        return policy.string_bytes(text_value, max_bytes=max_bytes)
    cache = _STRING_BYTES_CACHES.get(policy)
    if cache is None or len(cache) > _STRING_BYTES_CACHE_MAX:
        cache = _STRING_BYTES_CACHES[policy] = {}
    size = cache.get(text_value)
    if size is None:
        size = cache[text_value] = policy.string_bytes(text_value)
    return size


def clear_size_caches() -> None:
    """walker の大きさの cache を空にする（pair の終わり。値への参照を手放す）。"""

    _PURE_TUPLE_SIZES.clear()


def _base_scalar(item: Any) -> Any:
    """基底型の subclass（Java primitive など）を基底型の値へ直す（CANONICAL の写し）。"""

    kind = type(item)
    if kind is str or kind is int or kind is float or kind is bool or item is None:
        return item
    base = plain_scalar(item)
    return item if base is NOT_PLAIN else base


def _copy_pure_tuple(value: tuple, convert: bool = False) -> list:
    """tuple だけから成る値の写し（tuple → list）。大きさは数え済み（cache）なので数えない。

    `convert` なら基底型の subclass を基底型へ直す（CANONICAL で subclass を含む tuple）。
    """

    root: List[Any] = []
    stack = [(iter((value,)), root)]
    while stack:
        iterator, out = stack[-1]
        for item in iterator:
            if type(item) is tuple:
                child: List[Any] = []
                out.append(child)
                stack.append((iter(item), child))
                break
            out.append(_base_scalar(item) if convert else item)
        else:
            stack.pop()
    return root[0]


def copy_legacy_containers(value: Any) -> Any:
    """LEGACY 表現の容器（dict / list）だけを作り直した写し（葉はそのまま置く）。

    数え済みの表現を別の位置へもう一度置くときに使う（呼ぶ側が書き換えても元が
    変わらないように）。再帰しない。
    """

    kind = type(value)
    if kind is not dict and kind is not list:
        return value
    root: List[Any] = []
    stack: List[Tuple[Iterator[Any], Any, bool]] = [(iter(((None, value),)), root, False)]
    while stack:
        iterator, out, is_dict = stack[-1]
        for key, item in iterator:
            kind = type(item)
            if kind is dict or kind is list:
                child: Any = {} if kind is dict else []
                if is_dict:
                    out[key] = child
                else:
                    out.append(child)
                stack.append(
                    (iter(item.items()) if kind is dict else iter(zip(_NONE_KEYS, item)),
                     child, kind is dict)
                )
                break
            if is_dict:
                out[key] = item
            else:
                out.append(item)
        else:
            stack.pop()
    return root[0]


class _NoneKeys:
    """`zip` で list の要素に key `None` を付けるための無限列。"""

    def __iter__(self):
        return self

    def __next__(self):
        return None


_NONE_KEYS = _NoneKeys()


#: producer（`json_items`・集計の reducer・`each` の変換・`to_authority_dict` とその helper）が
#: 値の不備で上げる例外。walker と有界な証拠はこれを「JSON にならない値」
#: （`JsonValueRejected` / fingerprint の無い要約）に変える（`RecursionError` は `RuntimeError`、
#: `UnicodeError` は `ValueError` の派生）
PRODUCER_FAILURES = (TypeError, ValueError, AttributeError, LookupError, RuntimeError, ArithmeticError)


class _NotPlain(Exception):
    """純粋なデータ（容器と基底型だけ）の高速経路が扱えない値に出会った。"""


class _Walk:
    """source を 1 要素ずつ引き出して数え（CANONICAL / LEGACY）、`build` なら作る。

    再帰しない（frame の stack）。予算は `JsonBudget` が持ち、超えたらそこで止まる。
    `token_sink` を渡すと、値の型つき token 列を流す（`token_fingerprint`）。

    出力の byte（`budget`）とは別に、証拠を有界にする作業（大きさの確認・fingerprint・長い
    文字列の hash）を `effort` へ数える。`effort` の上限は走査を始めたときの `budget` の残り
    （`budget` が無制限なら無制限）で、使い切ったら証拠は fingerprint の無い要約になる
    （出力の byte の勘定は変わらない）。

    予算の owner（exact-once の規則。`test_issue22d_capabilities.py` の property test が固定する）:
    * 仕事の 1 単位は、ちょうど 1 つの owner へちょうど 1 回数える。書く byte は **出力の byte**
      として、byte を持たない仕事（高速経路が辿り直した分・reducer へ渡した要素・`flatten` の空の
      外の要素・証拠の試し）は **作業量** として数える（同じ単位を両方へは数えない）。
    * top-level の walk（`prepare` / `measure`）: 出力の byte の owner は walk の `budget`（呼ぶ側の
      `max_bytes`）、作業量の owner は walk の `effort`（上限は始めたときの `budget` の残り）。
    * 呼ぶ側の作業量で辿る walk（`count_into` / `materialize(budget=)` / `token_fingerprint`）: byte も
      作業量も呼ぶ側の作業量 1 つへ数える（`effort.parent`。呼ぶ側は返った量を数え直さない）。
    * walk の中（converter・reducer・`json_items`）では新しい予算を作れない（`JsonBudget` が
      `TypeError`）。入れ子の仕事は `count_into(value, work)` で walk の作業量へ 1 回だけ数える
      （呼ぶ側は数え直さない）。
    * 例外は登録した detached な場所だけ: 数え済みの値の写し（canonical な複製・数え済みの木）と、
      大きさだけを返して呼ぶ側がその大きさを 1 回数える見積もり（sized leaf の `__json_tree_bytes__`）、
      walker と `bounded_evidence` の中の試しの予算（使った分を 1 回だけ数え戻す）。
    * 自動で親へ数える経路は無い（`JsonBudget.parent` は `effort_to_budget` の effort だけ）。
    """

    def __init__(
        self,
        policy: JsonEncodingPolicy,
        mode: str,
        budget: JsonBudget,
        *,
        build: bool,
        token_sink: Optional[Callable[[bytes], None]] = None,
        effort: Optional[JsonBudget] = None,
        effort_to_budget: bool = False,
    ) -> None:
        self.policy = policy
        self.mode = mode
        self.budget = budget
        if effort is None:
            # walk の作業量（この walk の owner。walk が作るので detached）
            effort = JsonBudget(budget.remaining(), detached=True)
            if effort_to_budget:
                # 呼ぶ側の作業量（`count_into` / `materialize(budget=)` / `token_fingerprint`）で
                # 辿る: 走査の作業量もその作業量へ数える（呼ぶたびに新しい上限を持たない）
                effort.parent = budget
        self.effort = effort
        self.build = build
        self.token_sink = token_sink
        #: 1 回しか辿れない列（iterator）を辿ったか（辿った後の値は同じ値として辿り直せない）
        self.entered_iterator = False
        #: sized leaf を予算の置き換え（`SerializationWork.leaf_substitution`）に任せてよいか。walk の外から
        #: 始めた LEGACY の構築だけ（`run` が決める）: 置き換えた葉は、walk を始めた呼ぶ側だけが受け取る。
        #: walk の中の producer（`json_items` とその helper）が始めた walk の値は、producer の code が読むので
        #: 置き換えない
        self.substitutable = False
        self.item_separator = utf8_length(policy.item_separator)
        self.key_separator = utf8_length(policy.key_separator)
        self.stack: List[_Frame] = []
        self.active: set = set()
        cache = _STRING_BYTES_CACHES.get(policy)
        if cache is None or len(cache) > _STRING_BYTES_CACHE_MAX:
            cache = _STRING_BYTES_CACHES[policy] = {}
        self.string_cache = cache
        sizes = _PURE_TUPLE_SIZES.get(policy)
        if sizes is None:
            sizes = _PURE_TUPLE_SIZES[policy] = {}
        self.tuple_sizes = sizes

    # -- 位置（拒むときだけ組み立てる） -------------------------------------------

    def path(self) -> str:
        parts = ["$"]
        for frame in self.stack:
            current = frame.current
            parts.append(f"[{current}]" if type(current) is int else f".{current}")
        return "".join(parts)

    def reject(self, message: str) -> None:
        raise JsonValueRejected(message, path=self.path())

    def token(self, text_value: str) -> None:
        if self.token_sink is not None:
            self.token_sink(text_value.encode("utf-8", "surrogatepass") + b"\x1f")

    # -- 葉 ------------------------------------------------------------------

    def scalar(self, item: Any) -> Tuple[bool, Any]:
        """scalar なら数えて (True, 置く値)。LEGACY は元の値（サブクラスも）をそのまま置く。"""

        if item is None or item is True or item is False:
            self.budget.charge(5 if item is False else 4)
            if self.token_sink is not None:
                self.token("n" if item is None else ("b1" if item else "b0"))
            return True, item
        kind_of = type(item)
        if kind_of is str or kind_of is int or kind_of is float:
            base = item
        else:
            # subclass（JPype の `JInt`・mixin の enum）は基底型の値（読み方は `live_values` の
            # JSON の規則だけ。上書きした `__len__` / `__add__` / `__index__` を呼ばない）
            base = json_scalar(item)
            if base is NOT_PLAIN:
                return False, None
        base_kind = type(base)
        if base_kind is str:
            self.budget.charge(
                self.string_bytes(base) if kind_of is str
                else self.policy.string_bytes(base, max_bytes=self.budget.remaining())
            )
            if self.token_sink is not None:
                self.token("s" + base)
            if kind_of is not str and self.mode == CANONICAL:
                item = base
            return True, item
        if base_kind is int:
            value = base
            try:
                digits = len(int.__repr__(value))
            except ValueError:
                # 桁数が Python の文字列化の上限を超える整数は JSON に書けない
                self.reject("integer has too many digits to write as JSON")
            self.budget.charge(digits)
            if self.token_sink is not None:
                self.token("i" + int.__repr__(value))
            return True, (value if self.mode == CANONICAL else item)
        if base_kind is float:
            value = base
            self.budget.charge(len(_float_text(value)))
            if self.token_sink is not None:
                self.token(
                    ("i" + int.__repr__(live_values.as_int(value))) if value.is_integer() else ("f" + _float_text(value))
                )
            return True, (value if self.mode == CANONICAL else item)
        return False, None

    def string_bytes(self, text_value: str) -> int:
        if len(text_value) <= _SHORT_STRING:
            size = self.string_cache.get(text_value)
            if size is None:
                size = self.string_cache[text_value] = self.policy.string_bytes(text_value)
            return size
        return self.policy.string_bytes(text_value, max_bytes=self.budget.remaining())

    # -- 純粋なデータの高速経路 --------------------------------------------------

    def plain(self, value: Any, build: bool) -> Tuple[bool, Any]:
        """容器（tuple / list / dict）と基底型だけから成る値を、frame を積まずに数えて写す。

        数え方・予算で止まる位置は一般の経路と同じ（1 要素ごとに残り予算と比べ、超えたら
        その時点で `charge` して止まる）。基底型の subclass は基底型として数える（一般の
        経路と同じ）。record・sized leaf・source などに出会ったら (False, None) を返し、
        呼び出し側が一般の経路で辿り直す（それまでの byte は予算ではなく作業量 `effort` へ
        数える）。LEGACY は tuple → 配列・dict の key をそのまま、
        CANONICAL は dict の key を JSON の文字列にする。

        tuple だけから成る（不変な）部分木の byte 数は pair の間 cache する
        （`_PURE_TUPLE_SIZES`、値への参照を持つので id は再利用されない）。同じ key を
        何度も書く snapshot は、2 回目から数え直さずに（写すだけで）済む。
        """

        if self.token_sink is not None:
            return False, None
        policy = self.policy
        canonical = self.mode == CANONICAL
        sep = self.item_separator
        key_sep = self.key_separator
        string_bytes = self.string_bytes
        sizes = self.tuple_sizes
        remaining = self.budget.remaining()
        total = 0
        root: List[Any] = []
        active: set = set()
        # [iterator, out, is_dict, id, total_at_open, pure_tuple, obj, has_scalar_subclass]
        stack: List[List[Any]] = [[iter((value,)), root, False, None, 0, False, None, False]]
        try:
            while stack:
                entry = stack[-1]
                try:
                    item = next(entry[0])
                except StopIteration:
                    stack.pop()
                    if entry[3] is not None:
                        active.discard(entry[3])
                    if entry[5]:
                        if len(sizes) > _PURE_TUPLE_CACHE_MAX:
                            sizes.clear()
                        sizes[id(entry[6])] = (entry[6], total - entry[4], entry[7])
                    elif stack:
                        stack[-1][5] = False
                    if entry[7] and stack:
                        stack[-1][7] = True
                    continue
                if entry[2]:
                    key, item = item
                    if type(key) is str:
                        text_key = key
                    elif canonical and not (
                        issubclass(type(key), str) and live_values.builtin_hashed_scalar(key)
                    ):
                        # str でない key（`1` と `"1"`）・比較を上書きした str の subclass の key
                        # （`K("a")` と `"a"`）は JSON の文字列にすると別の key と衝突し得る。衝突を
                        # 拒むのは一般の経路（ここで写すと片方が黙って消える）。hash・比較が `str` の
                        # 実装のままの subclass は同じ文字列の key と同じ key（衝突しない）
                        raise _NotPlain
                    elif canonical:
                        text_key = policy.canonical_key(key)
                    elif _builtin_hashed_key(key):
                        # LEGACY は key をそのまま新しい dict へ置く: hash・比較が組み込みの実装の
                        # key だけ（基底型の subclass は一般の経路と同じ `canonical_key` で数える）
                        text_key = policy.canonical_key(key)
                    elif issubclass(type(key), (str, int, float)) and not _builtin_enum(key):
                        # hash を上書きした scalar の subclass（JPype の `JInt` など）: 値と同じく
                        # 基底型の値の key として置く（key の `__hash__` / `__eq__` を呼ばない）
                        text_key = policy.canonical_key(key)
                        key = json_scalar(key)
                    else:
                        raise _NotPlain
                    total += string_bytes(text_key) + key_sep
                    out_key = text_key if canonical else key
                else:
                    out_key = None
                kind = type(item)
                if kind is str:
                    total += string_bytes(item)
                elif item is None:
                    total += 4
                elif kind is bool:
                    total += 4 if item else 5
                elif kind is int:
                    try:
                        total += len(int.__repr__(item))
                    except ValueError:
                        raise _NotPlain
                elif kind is float:
                    total += len(_float_text(item))
                elif kind is tuple:
                    known = sizes.get(id(item))
                    if known is not None and known[0] is item:
                        total += known[1]
                        if known[2]:
                            entry[7] = True
                        if remaining is not None and total > remaining:
                            break
                        if build:
                            copied = _copy_pure_tuple(item, canonical and known[2])
                            if entry[2]:
                                entry[1][out_key] = copied
                            else:
                                entry[1].append(copied)
                        continue
                    count = len(item)
                    total += 2 + (sep * (count - 1) if count else 0)
                    if remaining is not None and total > remaining:
                        break
                    out = [] if build else None
                    if build:
                        if entry[2]:
                            entry[1][out_key] = out
                        else:
                            entry[1].append(out)
                    stack.append([iter(item), out, False, None, total - (2 + (sep * (count - 1) if count else 0)), True, item, False])
                    continue
                elif kind is list or kind is dict:
                    count = len(item)
                    total += 2 + (sep * (count - 1) if count else 0)
                    if remaining is not None and total > remaining:
                        break
                    identity = id(item)
                    if identity in active:
                        raise _NotPlain
                    active.add(identity)
                    entry[5] = False
                    out = ({} if kind is dict else []) if build else None
                    if build:
                        if entry[2]:
                            entry[1][out_key] = out
                        else:
                            entry[1].append(out)
                    stack.append([
                        iter(item.items()) if kind is dict else iter(item),
                        out, kind is dict, identity, 0, False, None, False,
                    ])
                    continue
                elif issubclass(kind, (str, int, float)):
                    # 基底型の subclass（PyGhidra の Java primitive `JInt` / `JLong`、IntEnum
                    # など）。一般の経路（`scalar`）と同じく基底型の値で数え、LEGACY はその
                    # まま置き、CANONICAL は基底型へ直す。これを一般の経路へ落とすと、実
                    # バイナリの値のほとんどが高速経路を外れる。subclass を含む tuple も
                    # cache するが、CANONICAL の写しでは基底型へ直す（cache の印）。
                    entry[7] = True
                    base = json_scalar(item)
                    base_kind = type(base)
                    if base_kind is str:
                        total += string_bytes(base)
                    elif base_kind is int:
                        try:
                            total += len(int.__repr__(base))
                        except ValueError:
                            raise _NotPlain
                    else:
                        total += len(_float_text(base))
                    if canonical:
                        item = base
                else:
                    raise _NotPlain
                if build:
                    if entry[2]:
                        entry[1][out_key] = item
                    else:
                        entry[1].append(item)
                if remaining is not None and total > remaining:
                    break
        except _NotPlain:
            # 一般の経路で辿り直す。ここまで数えた分は作業量（`effort`）へ足す（入れ子の各段で
            # 高速経路が辿り直す分も数える: 深い値の底に live な object があっても、辿り直しの
            # 合計は作業量で止まる）
            try:
                self.effort.charge(total)
            except JsonBudgetExhausted:
                self.budget.exceeded()
            return False, None
        self.budget.charge(total)
        return True, (root[0] if build else None)

    # -- 容器 ------------------------------------------------------------------

    def push(self, kind: str, iterator: Iterator[Any], parent: Any, key: Any, source: Any,
             *, build: bool, fn: Any = None, preserve_keys: bool = False) -> None:
        if _is_one_shot(source):
            self.entered_iterator = True
        # 閉路の判定は **参照している値**（record / 容器）の identity で行う。遅延構成子の
        # 包み（`each` など）はその場で作る一時 object なので、中身の値で数える。frame が
        # 値を保持するので、辿っている間に id が再利用されることは無い。
        source_kind = type(source)
        if issubclass(source_kind, _Source):
            if source_kind is _Each:
                source = source.items
            elif source_kind is _MappingOf:
                source = source.mapping
            else:
                source = None
        source_id = None if source is None else id(source)
        if source_id is not None:
            if source_id in self.active:
                raise JsonValueCycle("circular reference", path=self.path())
            self.active.add(source_id)
        self.budget.charge(2)
        if self.token_sink is not None:
            self.token("{" if kind == "dict" else "[")
            if kind == "dict":
                # digest は dict の並びに依らない（key の文字列で整列）。並べる前に、引き出す
                # 1 組ごとに数える（幅が予算を超えれば並べずに止まる）
                pairs = []
                for pair in iterator:
                    self.budget.charge(1)
                    pairs.append(pair)
                # 数え終えてから key の文字列を作り、それだけで整列する（同じ文字列の key は元の順。
                # 安定な sort）
                canonical_key = self.policy.canonical_key
                keyed = [(canonical_key(pair[0]), pair) for pair in pairs]
                keyed.sort(key=_FIRST)
                iterator = (pair for _key, pair in keyed)
        frame = _Frame()
        frame.kind = kind
        frame.iterator = iterator
        frame.out = ({} if kind == "dict" else []) if build else None
        frame.parent = parent
        frame.key = key
        frame.count = 0
        frame.source_id = source_id
        frame.source = source
        frame.build = build
        frame.keys = set()
        frame.fn = fn
        frame.current = None
        frame.preserve_keys = preserve_keys
        self.stack.append(frame)

    def place(self, parent: Any, key: Any, value: Any, build: bool) -> None:
        if build and parent is not None:
            parent[key] = value

    def count_only(self, item: Any, *, raw_leaves: bool) -> None:
        """`item` を数えるだけ（作らない・置かない）。"""

        depth = len(self.stack)
        if raw_leaves:
            self.enter_raw(item, None, None, False)
        else:
            self.enter(item, None, None, False)
        self.drain_to(depth)

    def enter(self, item: Any, parent: Any, key: Any, build: bool) -> None:
        """source 1 つを数え、`build` なら置く（容器なら frame を積む）。"""

        is_scalar, value = self.scalar(item)
        if is_scalar:
            self.place(parent, key, value, build)
            return
        kind = type(item)
        if issubclass(kind, _Source):
            self.enter_source(item, parent, key, build)
            return
        if builtin_iterator(item) or package_generator(item):
            # 組み込みの容器の iterator・package の generator は遅延配列: 1 要素ずつ引き出す
            # （pure layer の record は source の構成子を import できないので、これで列を渡す）
            self.push("list", item, parent, key, item, build=build)
            return
        json_items = _record_protocol(kind, "json_items")
        if json_items is not None:
            # package の型の `json_items`（record の protocol。型の関数を直接呼ぶ）
            self.push("dict", _walk_iter(json_items(item)), parent, key, item, build=build)
            return
        if _record_protocol(kind, "__json_tree__") is not None:
            built, size = self.budget.tree(item, build=build, substitutable=self.substitutable)
            if self.token_sink is not None:
                self.token("t" + protocol_method(item, "__json_identity__")(item))
            if build:
                if self.mode == CANONICAL:
                    # 大きさは作る前に数え済み。canonical な複製は予算の外（同じ大きさ）
                    self.place(parent, key, _canonical_copy_uncounted(self.policy, built), True)
                else:
                    self.place(parent, key, built, True)
            return
        if type(item) is BoundedEvidence:
            if self.mode == CANONICAL:
                self.enter(item.summary(), parent, key, build)
            else:
                self.count_only(item.summary(), raw_leaves=False)
                self.place(parent, key, item, build)
            return
        mapping = builtin_mapping(item)
        if mapping is not None or builtin_sequence(item):
            if self.mode == LEGACY:
                # 既に在る値への参照: 写さずに数え、元の object をそのまま置く
                done, _ = self.plain(item, False)
                if not done:
                    # 高速経路が辿った分は作業量へ数え済み: 一般の経路で 1 回だけ辿り直す
                    # （`enter_raw` を通すと高速経路をもう 1 度試して同じ前半を 2 回数える）
                    self.count_raw_container(item, mapping)
                self.place(parent, key, item, build)
                return
            done, value = self.plain(item, build)
            if done:
                self.place(parent, key, value, build)
                return
            if mapping is not None:
                self.push("dict", items_of(mapping), parent, key, item, build=build)
            else:
                self.push("list", iter(item), parent, key, item, build=build)
            return
        if self.mode == LEGACY:
            self.enter_raw(item, parent, key, build)
            return
        self.reject(f"{type_name(kind)} is not a JSON source")

    def enter_raw(self, item: Any, parent: Any, key: Any, build: bool) -> None:
        """LEGACY で元の値をそのまま置く場所（旧 `list(x)` の要素・`nested` の葉・参照）。

        値は変換しないが、後段（snapshot の codec）が表す大きさで数える: container は中身、
        record は `json_items()`、sized leaf は木の大きさ、それ以外は型名など。
        """

        if self.mode != LEGACY:
            self.enter(item, parent, key, build)
            return
        is_scalar, value = self.scalar(item)
        if is_scalar:
            self.place(parent, key, value, build)
            return
        mapping = builtin_mapping(item)
        if mapping is not None or builtin_sequence(item):
            done, _ = self.plain(item, False)
            if not done:
                self.count_raw_container(item, mapping)
        else:
            self.count_raw_leaf(item)
        self.place(parent, key, item, build)

    def legacy_key(self, key: Any) -> Any:
        """LEGACY で新しい dict へ置く key（元の key を置くと key の `__hash__` / `__eq__` を呼び得る）。

        hash・比較が組み込みの実装の key はそのまま。それ以外の scalar の subclass（JPype の `JInt`
        など）は値と同じく基底型の値、そういう scalar を含む tuple は基底型の値の tuple（作業量の中で
        1 回だけ作る）。それ以外の key は JSON にならない値。
        """

        if _builtin_hashed_key(key) or live_values.hash_safe_key(key):
            return key
        if issubclass(type(key), (str, int, float)) and not _builtin_enum(key):
            return json_scalar(key)
        if type(key) is tuple:
            view = _plain_key_view(key, self.effort)
            if view is not _NOT_PLAIN:
                return view
        self.reject(f"mapping key {type_name(type(key))} is not hashed by a builtin")

    def count_raw_container(self, item: Any, mapping: Any) -> None:
        """高速経路で辿れなかった容器を、一般の経路で 1 回だけ数える（要素は元の値のまま）。"""

        if mapping is not None:
            self.push("dict", items_of(mapping), None, None, item, build=False,
                      fn=_RAW, preserve_keys=True)
        else:
            self.push("list", iter(item), None, None, item, build=False, fn=_RAW)
        self.drain_to(len(self.stack) - 1)

    def count_raw_leaf(self, item: Any) -> None:
        """LEGACY でそのまま置く JSON 型でない葉を、**後段の codec が写す形で** 数える。

        snapshot の codec（`SnapshotFingerprintCodec._freeze`）は、この葉を `stable_key()` /
        `to_key()`・record の表現・dataclass の field の順で写す。同じ順で、その写しの
        大きさを数える（型名だけ数えて、中身を数えずに写させない）。
        """

        kind = type(item)
        if issubclass(kind, Enum):
            self.opaque(item)
            return
        has_key, identity_key = identity_key_of(item)
        if has_key:
            self.opaque(item)
            self.count_only(identity_key, raw_leaves=True)
            return
        if is_json_record(item) or kind is BoundedEvidence:
            self.count_only(item, raw_leaves=False)
            return
        names = dataclass_field_names(item)
        if names is not None:
            self.opaque(item)
            for name in names:
                self.budget.charge(self.policy.string_bytes(name) + 4)
                self.count_only(plain_field_value(item, name), raw_leaves=True)
            return
        if self.token_sink is not None:
            # 型名しか分からない葉: 型つき token の fingerprint は値を区別しない（fingerprint を作らない）
            raise _OpaqueLeaf(f"{type_name(kind)} has no value to fingerprint", path=self.path())
        self.opaque(item)

    def opaque(self, item: Any) -> None:
        """JSON 型でない葉（旧 `to_dict` がそのまま置いた値）: 型名や enum の値で数える。"""

        kind = type(item)
        name = type_name(kind)
        is_enum = issubclass(kind, Enum)
        if is_enum:
            raw_value = live_values.enum_value(item)
            label = raw_value if type(raw_value) is str else name
        else:
            label = name
        self.budget.charge(self.policy.string_bytes(label))
        if self.token_sink is not None:
            self.token("o" + name + ":" + (label if is_enum else ""))

    def enter_source(self, item: _Source, parent: Any, key: Any, build: bool) -> None:
        kind = type(item)
        if kind is _Each:
            if not _walkable_items(item.items):
                # 組み込みの振る舞いでない iterable（上書きした `__iter__`）は辿らない
                self.reject(f"{type_name(type(item.items))} is not a builtin iterable")
            self.push("list", iter(item.items), parent, key, item, build=build, fn=item.fn)
        elif kind is _Flatten:
            self.push("list", self._flat_elements(item), parent, key, item, build=build)
        elif kind is _MappingOf:
            mapping = item.mapping
            if type(mapping) is not _PairsView and builtin_mapping(mapping) is None:
                self.reject(f"{type_name(type(mapping))} is not a builtin mapping")
            pairs: Iterator[Any] = mapping.items() if type(mapping) is _PairsView else items_of(mapping)
            if item.stringify_keys:
                effort = self.effort
                pairs = ((_stringified_key(child_key, effort), child) for child_key, child in pairs)
            self.push(
                "dict", pairs, parent, key, item, build=build,
                fn=item.fn, preserve_keys=(self.mode == LEGACY),
            )
        elif kind is _Inline:
            self.push("dict", iter(item.pairs), parent, key, item, build=build)
        elif kind is _Nested:
            self.enter_nested(item.value, parent, key, build)
        elif kind is _Raw:
            self.enter_raw(item.value, parent, key, build)
        elif kind is _Evidence:
            self.enter_evidence(item, parent, key, build)
        elif kind is _Text:
            value = item.value
            if self.mode == CANONICAL and value is not None and not issubclass(type(value), str):
                # 文字列でない値（case の組など）も、列の上限まで: 収まらなければ有界な証拠
                self.enter_evidence(
                    _Evidence(
                        value, None,
                        inline_bytes=text_value_max_bytes(self.policy, item.max_chars),
                        one_shot=_is_one_shot(value),
                    ),
                    parent, key, build,
                )
                return
            if self.mode == CANONICAL and issubclass(type(value), str):
                # str の subclass（str の enum を含む）は JSON の規則の基底型の文字列で長さを見る
                base = json_scalar(value)
                if len(base) > item.max_chars:
                    value = bounded_text(base, item.max_chars, work=self.effort)
            self.enter(value, parent, key, build)
        elif kind is _Scan:
            reducer = item.reducer
            # reducer の method は型の関数（`scan` が確かめた package の関数）を直接呼ぶ（instance の
            # 属性に置いた callable を呼ばない）
            add = type_attribute(type(reducer), "add")
            values = item.values
            if _is_one_shot(values):
                self.entered_iterator = True
            try:
                effort = self.effort
                elements = (
                    () if values is None
                    else self._flat_elements(values) if type(values) is _Flatten
                    else _walk_iter(values)
                )
                for element in elements:
                    # 引き出した要素を畳み込む前に数える（上限を超えれば残りを引き出さない）。
                    # 要素の中の仕事は reducer が同じ作業量へ数える
                    effort.charge(1)
                    add(reducer, element, work=effort)
            except PRODUCER_FAILURES as exc:
                self.reject(f"producer failed ({exception_text(exc)})")
            except JsonBudgetExhausted:
                # 集計を途中で止めた値は別の値: この walk の予算の超過として扱う
                self.budget.exceeded()
                raise
            try:
                produced = type_attribute(type(reducer), "result")(reducer, work=self.effort)
            except JsonBudgetExhausted:
                self.budget.exceeded()
                raise
            except PRODUCER_FAILURES as exc:
                self.reject(f"producer failed ({exception_text(exc)})")
            self.enter(produced, parent, key, build)
        else:  # pragma: no cover - 文法の追加漏れ
            self.reject(f"unknown source {type_name(kind)}")

    def _flat_elements(self, item: "_Flatten") -> Iterator[Any]:
        """`flatten` の要素（内の要素を順に返す）。

        内の要素は、受け取る側（配列の書き出し・`scan` の畳み込み）が 1 つずつ作業量へ数える。
        外の要素がその分を持たない（内が `None` か空）ときだけ、ここで 1 を数える。数える量は
        「外の要素 1 つにつき 1 以上」で、内の要素を 2 重には数えない（出力 byte と一致させる）。
        """

        effort = self.effort
        for outer in _walk_iter(item.values):
            inner = outer if item.attribute is None else live_values.attribute(outer, item.attribute)
            produced = False
            if inner is not None:
                for element in _walk_iter(inner):
                    produced = True
                    yield element
            if not produced:
                effort.charge(1)

    def enter_nested(self, value: Any, parent: Any, key: Any, build: bool) -> None:
        """旧 `_jsonable_nested_tuple`: dict は dict、tuple / list は配列、それ以外はそのまま。"""

        mapping = builtin_mapping(value) if issubclass(type(value), dict) else None
        sequence = builtin_sequence(value)
        if mapping is not None or sequence:
            done, built = self.plain(value, build)
            if done:
                self.place(parent, key, built, build)
                return
        if mapping is not None:
            self.push("dict", items_of(mapping), parent, key, value, build=build, fn=_NESTED,
                      preserve_keys=(self.mode == LEGACY))
        elif sequence:
            self.push("list", iter(value), parent, key, value, build=build, fn=_NESTED)
        else:
            # 組み込みの振る舞いでない容器は元の値として（`enter_raw` の規則で）数える
            self.enter_raw(value, parent, key, build)

    def enter_evidence(self, item: _Evidence, parent: Any, key: Any, build: bool) -> None:
        value = item.value
        if self.mode == LEGACY or value is None or type(value) is BoundedEvidence:
            self.enter(value, parent, key, build)
            return
        limit = EVIDENCE_INLINE_BYTES if item.inline_bytes is None else live_values.as_int(item.inline_bytes)
        over = 0  # 書いた byte 数の下限（測れなければ 0）
        if not _exhausted(self.effort):
            remaining = self.effort.remaining()
            # 試しの予算（walker の中の detached な予算。使った分は下で作業量へ 1 回だけ数え戻す）
            attempt = JsonBudget(limit if remaining is None else min(limit, remaining), detached=True)
            attempt_walk = _Walk(self.policy, CANONICAL, attempt, build=True, effort=self.effort)
            try:
                # 上限（`inline_bytes`）まで 1 回だけ作る。収まればその値を置く（作業は effort へ）
                inline_value = attempt_walk.run(value)
            except JsonBudgetExhausted:
                _charge_quietly(self.effort, attempt.consumed)
                if attempt.consumed > attempt.max_bytes:
                    over = attempt.max_bytes
            except JsonValueRejected:
                # 小さくても JSON にならない値（live な object）: 大きい値と同じく有界な要約へ
                # （`bounded_evidence` と同じ規則。大きさで受け入れが変わらない）
                _charge_quietly(self.effort, attempt.consumed)
            else:
                _charge_quietly(self.effort, attempt.consumed)
                if attempt.consumed <= limit:
                    self.enter(inline_value, parent, key, build)
                    return
                over = limit
            if item.one_shot or (attempt_walk.entered_iterator and item.reread is None):
                # 試しで 1 回しか辿れない列を辿った: 同じ値として辿り直せない（別の値の
                # fingerprint を同じ値のものとして置かない）
                self.enter(
                    _unfingerprinted(_value_kind(value), UNFINGERPRINTED_UNSUPPORTED, over),
                    parent, key, build,
                )
                return
        try:
            fresh = value if item.reread is None else _reread(item.reread)
        except PRODUCER_FAILURES:
            summary = _unfingerprinted(_value_kind(value), UNFINGERPRINTED_UNSUPPORTED, over)
        else:
            summary = _evidence_summary(
                fresh, work=self.effort, identity=item.identity, policy=self.policy, over=over,
            )
        self.enter(summary, parent, key, build)

    # -- 本体 ------------------------------------------------------------------

    def run(self, source: Any) -> Any:
        holder: List[Any] = [None]
        self.substitutable = (
            _ACTIVE_WORK.get() is None and self.mode == LEGACY and self.build and self.token_sink is None
        )
        # walk の間に呼ぶ producer が作る予算は、この walk の作業量の子（`JsonBudget.parent`）
        active = _ACTIVE_WORK.set(self.effort)
        try:
            # 値の storage の読み（key の検査・instance の状態）も固定の上限を超えた分はこの walk の作業量へ
            # 数える（組み込みのままの容器は要素ごとに数えて辿るので、検査の要る容器も同じ意味にする）
            with live_values.metered_storage_reads(self.effort):
                self.enter(source, holder, 0, self.build)
                self.drain_to(0)
        finally:
            _ACTIVE_WORK.reset(active)
        return holder[0]

    def drain_to(self, depth: int) -> None:
        stack = self.stack
        while len(stack) > depth:
            frame = stack[-1]
            try:
                child = next(frame.iterator)
            except PRODUCER_FAILURES as exc:
                # producer（`json_items` とその helper）の失敗は、その値が JSON にならないこと
                # （field の規則どおり: 診断は marker、準備する意味の値は内部エラー）
                self.reject(f"producer failed ({exception_text(exc)})")
            except JsonBudgetExhausted:
                # producer が引き出しの中で作業量（reducer・`count_into`）を使い切った: この walk の予算の超過
                self.budget.exceeded()
                raise
            except StopIteration:
                stack.pop()
                if frame.source_id is not None:
                    self.active.discard(frame.source_id)
                if self.token_sink is not None:
                    self.token("}" if frame.kind == "dict" else "]")
                if frame.build and frame.parent is not None:
                    frame.parent[frame.key] = frame.out
                continue
            separator = self.item_separator if frame.count else 0
            frame.count += 1
            if frame.kind == "dict":
                child_key, target = child
                if type(child_key) is str:
                    text_key = child_key
                else:
                    try:
                        text_key = self.policy.canonical_key(child_key)
                    except TypeError as exc:
                        self.reject(exception_text(exc))
                if text_key in frame.keys:
                    self.reject(f"key {text_key!r} collides after JSON key conversion")
                frame.keys.add(text_key)
                frame.current = text_key
                self.budget.charge(separator + self.string_bytes(text_key) + self.key_separator)
                if self.token_sink is not None:
                    self.token("k" + text_key)
                out_key = self.legacy_key(child_key) if frame.preserve_keys else text_key
            else:
                if separator:
                    self.budget.charge(separator)
                target = child
                frame.current = frame.count - 1
                if frame.build:
                    frame.out.append(None)
                out_key = frame.count - 1
            parent = frame.out if frame.build else None
            fn = frame.fn
            if fn is None:
                self.enter(target, parent, out_key, frame.build)
            elif fn is _RAW:
                self.enter_raw(target, parent, out_key, frame.build)
            elif fn is _NESTED:
                self.enter_nested(target, parent, out_key, frame.build)
            else:
                try:
                    converted = fn(target)
                except PRODUCER_FAILURES as exc:
                    self.reject(f"producer failed ({exception_text(exc)})")
                self.enter(converted, parent, out_key, frame.build)


def _canonical_copy_uncounted(policy: JsonEncodingPolicy, value: Any) -> Any:
    # `tree()` が作る前に数え済みの木の canonical な複製（数え直さない）
    return _Walk(policy, CANONICAL, JsonBudget(None, detached=True), build=True).run(value)


_ALL_RESERVATIONS = object()


class JsonObjectBudget:
    """1 つの JSON object へ member を順に足していく勘定（framing は policy が決める）。"""

    def __init__(self, policy: JsonEncodingPolicy, max_bytes: Optional[int]) -> None:
        self.policy = policy
        self.max_bytes = max_bytes
        self._count = 0
        self._members = 0
        #: 後で足す member のために空けておく byte（key → member の byte。`remaining_for` が
        #: その key 以外の予約を差し引く）
        self._reserved: Dict[Any, int] = {}

    @live_values.readable_property
    def total_bytes(self) -> int:
        return self.policy.container_frame_bytes(self._count) + self._members

    @property
    def member_count(self) -> int:
        return self._count

    def added_bytes(self, key: Any, value_bytes: int) -> int:
        return (
            self.policy.container_frame_bytes(self._count + 1)
            - self.policy.container_frame_bytes(self._count)
            + self.policy.member_bytes(key, value_bytes)
        )

    def remaining_for(self, key: Any) -> Optional[int]:
        if self.max_bytes is None:
            return None
        others = [size for reserved, size in self._reserved.items() if reserved != key]
        count = self._count + len(others)
        total = self.policy.container_frame_bytes(count) + self._members + sum(others)
        added = (
            self.policy.container_frame_bytes(count + 1) - self.policy.container_frame_bytes(count)
            + self.policy.member_bytes(key, 0)
        )
        return self.max_bytes - total - added

    def room(self) -> Optional[int]:
        """足した member と予約をすべて差し引いた残り（負なら予約が上限を超えている）。"""

        if self.max_bytes is None:
            return None
        count = self._count + len(self._reserved)
        return self.max_bytes - (
            self.policy.container_frame_bytes(count) + self._members + sum(self._reserved.values())
        )

    def reserve(self, key: Any, value_bytes: int) -> None:
        """後で `key` に `value_bytes` の値を足すための byte を空けておく（他の member の残りから引く）。

        key ごとに 1 つ（複数の key を同時に予約できる）。
        """

        self._reserved[key] = self.policy.member_bytes(key, value_bytes)

    def release_reservation(self, key: Any = _ALL_RESERVATIONS) -> None:
        """`key` の予約を外す（省略すればすべて）。"""

        if key is _ALL_RESERVATIONS:
            self._reserved.clear()
        else:
            self._reserved.pop(key, None)

    def add(self, key: Any, value_bytes: int) -> None:
        self._members += self.policy.member_bytes(key, value_bytes)
        self._count += 1


#: 結果 JSON（CLI が書く `EQUIVALENCE_RESULT_JSON`）の書き方。**唯一の定義**。
RESULT_JSON_POLICY = JsonEncodingPolicy()
#: 永続化する canonical result envelope の書き方: 結果 JSON と同じ文字列の規則（UTF-8 のまま、
#: surrogate だけ escape）で、区切りだけ詰める（書いた payload の byte は結果 JSON 以下）
PERSISTED_ENVELOPE_JSON_POLICY = JsonEncodingPolicy(item_separator=",", key_separator=":")


def scalar_record_dict(record: Any) -> dict:
    """**scalar だけ** を yield する固定の形の record の LEGACY 表現（walker を通さない）。

    `json_items()` が固定個数の scalar（`None` / `bool` / `int` / `float` / `str`）しか
    返さない record（`StorageInfo` など）だけが使う。大きさは field の数と scalar の
    長さで決まり、入力に比例して育たない。scalar 以外が来たら `TypeError`（schema の
    誤り。`tests/unit/test_architecture_boundaries.py` が該当 class を固定する）。

    scalar の subclass（PyGhidra の Java primitive `JInt` / `JLong` など）は旧
    `to_dict()` と同じくそのまま置く（LEGACY）。出力では walker が基底型へ直す。
    """

    out = {}
    for key, value in record.json_items():
        if value is not None and not issubclass(type(value), _SCALAR_TYPES):
            raise TypeError(
                f"{type_name(type(record))}.{key} is not a scalar; use materialize()"
            )
        out[key] = value
    return out


_SCALAR_TYPES = (bool, int, float, str)


#: 解析 1 件分の直列化の外で呼ばれた record の `to_dict()` を数える観測点。
RECORD_SERIALIZATION_SITE = "core.json_encoding.materialize"


def materialize(source: Any) -> Any:
    """record の `to_dict()`（LEGACY 表現）。pair の予算の中では必ず直列化の作業量へ数える。

    解析 1 件分の直列化（`SerializationWork`）の最中ならその作業量へ合流し、そうでなく
    pair の予算 scope の中なら、この 1 件だけの作業量を開く（木を含む record が予算を
    知らずに作られる経路を残さない）。予算 scope の外（部品単体の呼び出し）は数えない。
    """

    from scripts.function_tracer_pcode.core.budget_policy import (
        active_serialization_work,
        budget_scope_is_active,
        serialization_scope,
    )

    work = active_serialization_work()
    if work is not None:
        return RESULT_JSON_POLICY.materialize(source, budget=work)
    if not budget_scope_is_active():
        return RESULT_JSON_POLICY.materialize(source)
    with serialization_scope(
        site=RECORD_SERIALIZATION_SITE, target_parts=("record", type_name(type(source))),
    ) as work:
        return RESULT_JSON_POLICY.materialize(source, budget=work)



# 組み込みの source の構成子は source converter（O(1) で source を作るだけ）
for _constructor in (each, nested, as_list, as_dict, mapping_of, pairs_of, inline, raw, text, evidence, flatten):
    source_converter(_constructor)
del _constructor

__all__ = [
    "BOOL",
    "BoundedEvidence",
    "Column",
    "EVIDENCE",
    "INT",
    "TEXT",
    "CANONICAL",
    "EVIDENCE_INLINE_BYTES",
    "EVIDENCE_SUMMARY_MAX_BYTES",
    "JsonBudget",
    "JsonBudgetExhausted",
    "JsonEncodingPolicy",
    "JsonObjectBudget",
    "JsonOutputLimitExceeded",
    "JsonValueCycle",
    "PERSISTED_ENVELOPE_JSON_POLICY",
    "PRODUCER_FAILURES",
    "JsonValueRejected",
    "LEGACY",
    "PreparedJson",
    "RESULT_JSON_POLICY",
    "identity_key_of",
    "bounded_repr",
    "builtin_str",
    "exception_text",
    "hashable_key",
    "object_identity_token",
    "value_token",
    "builtin_view",
    "NOT_PLAIN",
    "plain_scalar",
    "renders_with_builtins",
    "stringify_plain_key",
    "Reread",
    "Reducer",
    "source_converter",
    "TEXT_MARKER_MAX_CHARS",
    "text_value_max_bytes",
    "UNFINGERPRINTED_CYCLE",
    "UNFINGERPRINTED_OPAQUE",
    "column_identity",
    "UNFINGERPRINTED_UNSUPPORTED",
    "UNFINGERPRINTED_WORK_EXHAUSTED",
    "as_dict",
    "as_list",
    "Tally",
    "bounded_evidence",
    "bounded_text",
    "cached_string_bytes",
    "clear_size_caches",
    "each",
    "evidence",
    "evidence_kind",
    "inline",
    "is_json_record",
    "is_prepared_json",
    "mapping_of",
    "materialize",
    "nested",
    "pairs_of",
    "raw",
    "row_items",
    "row_max_bytes",
    "row_min_bytes",
    "flatten",
    "package_generator",
    "protocol_method",
    "scan",
    "max_rows_within",
    "scalar_record_dict",
    "text",
]
