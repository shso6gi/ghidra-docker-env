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
  - `bounded_summary(fn, max_bytes)`: 出力の大きさが schema から上限を持つ集計（登録 reason
    ごとの件数など）。walker が残り予算 ≥ 上限を確かめてから作らせ、作った値が上限内かを
    確かめる（上限を破れば `JsonValueRejected`）

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

import hashlib
import json
import re
from collections.abc import Iterator as _AbcIterator, Mapping
from dataclasses import dataclass, fields as dataclass_fields, is_dataclass
from enum import Enum
from json.encoder import encode_basestring, encode_basestring_ascii
from typing import Any, Callable, Iterable, Iterator, List, Optional, Tuple

from scripts.function_tracer_pcode.core.errors import AnalysisFailureError
from scripts.function_tracer_pcode.core.render_output import utf8_length


class JsonOutputLimitExceeded(AnalysisFailureError):
    """bounded encoder が上限に達した（書き出しを止め、完成文字列を作らない）。"""

    def __init__(self, *, max_bytes: int, requested_bytes: int) -> None:
        super().__init__(
            f"JSON output exceeded {max_bytes} bytes (needed at least {requested_bytes})"
        )
        self.max_bytes = int(max_bytes)
        self.requested_bytes = int(requested_bytes)


class JsonBudgetExhausted(AnalysisFailureError):
    """walker が byte の上限に達した（そこで辿るのをやめた）。

    `consumed_bytes` は止めた時点までに数えた byte 数（上限 + 1 以上）で、値全体の
    大きさではない（残りは数えていない）。
    """

    def __init__(self, *, consumed_bytes: int, max_bytes: Optional[int]) -> None:
        super().__init__(f"JSON projection exceeded {max_bytes} bytes")
        self.consumed_bytes = int(consumed_bytes)
        self.max_bytes = max_bytes


class JsonValueRejected(AnalysisFailureError):
    """source の文法に無い値（任意の object・閉路・key の衝突・上限を破った集計）。

    **producer のバグ** で、意味の限界ではない。`TypeError` 派生にしない（回復用の
    handler に吸われると、canonical でない値が prepared payload に入り得る）。
    """

    def __init__(self, message: str, *, path: str) -> None:
        super().__init__(f"{message} at {path}")
        self.path = path


# ---------------------------------------------------------------------------
# source の遅延構成子（producer が collection を渡す唯一の方法）
# ---------------------------------------------------------------------------


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
    __slots__ = ("mapping", "fn", "key_fn")

    def __init__(self, mapping: Any, fn: Any, key_fn: Optional[Callable[[Any], Any]] = None) -> None:
        self.mapping = mapping
        self.fn = fn
        self.key_fn = key_fn


class _Inline(_Source):
    __slots__ = ("pairs",)

    def __init__(self, pairs: Tuple[Tuple[Any, Any], ...]) -> None:
        self.pairs = pairs


class _Raw(_Source):
    __slots__ = ("value",)

    def __init__(self, value: Any) -> None:
        self.value = value


class _Evidence(_Source):
    __slots__ = ("value", "identity", "refresh", "inline_bytes")

    def __init__(
        self,
        value: Any,
        identity: Any,
        refresh: Optional[Callable[[], Any]] = None,
        inline_bytes: Optional[int] = None,
    ) -> None:
        self.value = value
        self.identity = identity
        #: 同じ値の source を作り直す（遅延列は 1 回しか辿れないので、要約の digest 用）
        self.refresh = refresh
        #: そのまま置いてよい大きさ（既定は `EVIDENCE_INLINE_BYTES`）
        self.inline_bytes = EVIDENCE_INLINE_BYTES if inline_bytes is None else int(inline_bytes)


class _Text(_Source):
    __slots__ = ("value", "max_chars")

    def __init__(self, value: Any, max_chars: int) -> None:
        self.value = value
        self.max_chars = int(max_chars)


class _BoundedSummary(_Source):
    __slots__ = ("fn", "max_bytes")

    def __init__(self, fn: Callable[[], Any], max_bytes: int) -> None:
        self.fn = fn
        self.max_bytes = int(max_bytes)


#: 要素をそのまま置く（LEGACY: 旧 `list(x)` / `dict(x)` の要素。CANONICAL では通常どおり）
_RAW = object()
#: 要素を `nested` の規則で写す
_NESTED = object()


def each(items: Iterable[Any], fn: Optional[Callable[[Any], Any]] = None) -> _Source:
    """要素を 1 つずつ引き出す配列（`[fn(x).to_dict() for x in items]` の遅延版）。

    要素（`fn` の返り値）は source として辿る（record は dict になる）。`fn` は要素 1 つ分の
    source を返す（表現を作らない）。
    """

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
    key: Optional[Callable[[Any], Any]] = None,
) -> _Source:
    """既存の mapping の値を 1 つずつ source として辿る（旧 `{key(k): fn(v) ...}`）。"""

    return _MappingOf(mapping, fn, key)


class _PairsView:
    """(key, 値) の組を 1 つずつ返す iterable を mapping の形で見せる（1 回だけ辿る）。"""

    __slots__ = ("_pairs",)

    def __init__(self, pairs: Iterable[Tuple[Any, Any]]) -> None:
        self._pairs = pairs

    def items(self) -> Iterator[Tuple[Any, Any]]:
        return iter(self._pairs)


def pairs_of(
    pairs: Iterable[Tuple[Any, Any]],
    fn: Optional[Callable[[Any], Any]] = None,
) -> _Source:
    """(key, 値) の組の遅延列を object として 1 組ずつ写す（旧 `{k: fn(v) for k, v in ...}`）。

    `pairs` は generator でよい（walker が 1 組ずつ引き出す。1 回だけ辿る）。
    """

    return _MappingOf(_PairsView(pairs), fn)


def inline(*pairs: Tuple[Any, Any]) -> _Source:
    """固定個数の (key, source) から成る object（`each` の要素 1 つ分の表示など）。"""

    return _Inline(tuple(pairs))


def is_json_record(value: Any) -> bool:
    """walker が辿れる object（`json_items()` を持つ record か、sized leaf）か。"""

    kind = type(value)
    return getattr(kind, "json_items", None) is not None or getattr(kind, "__json_tree__", None) is not None


def raw(value: Any) -> _Source:
    """旧 `to_dict` が値をそのまま置いていた場所（LEGACY では変換しない。数えはする）。"""

    return _Raw(value)


def evidence(
    value: Any,
    identity: Any = None,
    *,
    refresh: Optional[Callable[[], Any]] = None,
    inline_bytes: Optional[int] = None,
) -> _Source:
    """重くなり得る証拠（key / evidence）。出力では有界な表現、`to_dict()` では元の値。

    `identity` は大きいときに使う identity（文字列、または値を受け取る callable）。
    省くと値の型つき token 列の digest を streaming で求める。`value` が遅延列（1 回
    しか辿れない）を含むなら `refresh` に同じ source を作り直す callable を渡す。
    """

    return _Evidence(value, identity, refresh, inline_bytes)


def text(value: Any, max_chars: int) -> _Source:
    """自由文。出力では `max_chars` 文字まで（超えた分は明示の marker）、`to_dict()` では元の値。"""

    return _Text(value, max_chars)


def bounded_summary(fn: Callable[[], Any], max_bytes: int) -> _Source:
    """出力の大きさが schema で抑えられた集計（作る前に残り予算 ≥ 上限を確かめる）。"""

    return _BoundedSummary(fn, max_bytes)


#: `int` 1 つを書いたときの byte 数の上限（64 bit 符号付き）
INT_MAX_BYTES = 20


def counts_max_bytes(keys: Iterable[Any], policy: Optional["JsonEncodingPolicy"] = None) -> int:
    """key が有限の登録 `keys` に限られる件数 object（`{key: int}`）の byte 数の上限。

    `bounded_summary` に渡す上限を、登録（opcode 表・reason registry など）から求める。
    """

    policy = RESULT_JSON_POLICY if policy is None else policy
    sizes = [policy.member_bytes(key, INT_MAX_BYTES) for key in keys]
    return policy.container_frame_bytes(len(sizes)) + sum(sizes)


# ---------------------------------------------------------------------------
# 有界な証拠
# ---------------------------------------------------------------------------


#: 証拠をそのまま出してよい大きさ（JSON byte）。これを超える証拠は identity + 要約になる
#: （出力 schema の上限の根拠）。
EVIDENCE_INLINE_BYTES = 2048
#: 要約の identity / kind の最大文字数（schema 上の上限）
EVIDENCE_IDENTITY_MAX_CHARS = 96
EVIDENCE_KIND_MAX_CHARS = 64
#: `text()` が超えたときに足す marker の最大文字数（schema 上の上限）
TEXT_MARKER_MAX_CHARS = 64


#: 有界な証拠の文字列 field に許す文字（JSON で escape されない印字可能な ASCII）。
#: これで `EVIDENCE_SUMMARY_MAX_BYTES` が書き出しの byte 数の上限になる。
_PRINTABLE_WITHOUT_ESCAPE = re.compile(r'[ !#-\[\]-~]*')


@dataclass(frozen=True)
class BoundedEvidence:
    """大きい証拠の代わりに置く有界な表現（identity・種類・大きさの下限）。

    authority 確定前に作り、以後は元の値を参照しない。等しさは identity で決まる。
    `match_digests` は生成側が付ける照合用の digest（例: legacy reason と cause の照合）。
    """

    identity: str
    identity_kind: str
    kind: str
    encoded_bytes_over: int = EVIDENCE_INLINE_BYTES
    match_digests: Tuple[Tuple[str, str], ...] = ()
    #: 元の値の distinct な node の数（DAG-aware に数えられたときだけ）
    distinct_nodes: Optional[int] = None

    def __post_init__(self) -> None:
        for name, limit in (
            ("identity", EVIDENCE_IDENTITY_MAX_CHARS),
            ("identity_kind", EVIDENCE_KIND_MAX_CHARS),
            ("kind", EVIDENCE_KIND_MAX_CHARS),
        ):
            value = getattr(self, name)
            if (
                type(value) is not str or len(value) > limit
                or not _PRINTABLE_WITHOUT_ESCAPE.fullmatch(value)
            ):
                raise ValueError(
                    f"bounded evidence {name} must be short printable ASCII without escapes"
                )

    def match_digest(self, name: str) -> Optional[str]:
        for key, value in self.match_digests:
            if key == name:
                return value
        return None

    def summary(self) -> dict:
        payload = {
            "bounded_evidence": "v1",
            "identity": self.identity,
            "identity_kind": self.identity_kind,
            "kind": self.kind,
            "encoded_bytes_over": int(self.encoded_bytes_over),
        }
        if self.distinct_nodes is not None:
            payload["distinct_nodes"] = int(self.distinct_nodes)
        return payload

    def to_authority_dict(self) -> dict:
        return self.summary()

    def __eq__(self, other: Any) -> bool:
        return (
            type(other) is BoundedEvidence
            and other.identity_kind == self.identity_kind
            and other.identity == self.identity
        )

    def __hash__(self) -> int:
        return hash((self.identity_kind, self.identity))


#: `BoundedEvidence.summary()` を書いたときの byte 数の上限（schema 上の上限）
EVIDENCE_SUMMARY_MAX_BYTES = (
    2 + 6 * 4  # 括弧と区切り（6 member、区切りは最大 2 byte と見積もる）
    + len('"bounded_evidence": "v1"')
    + len('"identity": ') + 2 + EVIDENCE_IDENTITY_MAX_CHARS
    + len('"identity_kind": ') + 2 + EVIDENCE_KIND_MAX_CHARS
    + len('"kind": ') + 2 + EVIDENCE_KIND_MAX_CHARS
    + len('"encoded_bytes_over": ') + 20
    + len('"distinct_nodes": ') + 20
)


def _source_value(value: Any) -> Any:
    """source の包み（`each` / `nested` / `raw`）なら中の値（Merkle digest は値で求める）。"""

    if isinstance(value, _Each) and value.fn in (None, _RAW):
        return value.items
    if isinstance(value, (_Nested, _Raw)):
        return value.value
    if isinstance(value, _MappingOf) and value.fn in (None, _RAW) and not isinstance(value.mapping, _PairsView):
        return value.mapping
    if isinstance(value, _Source):
        raise TypeError("a lazy source is summarized by its token digest")
    return value


def _value_kind(value: Any) -> str:
    if isinstance(value, _Each):
        value = value.items
    elif isinstance(value, _MappingOf):
        value = value.mapping
        if isinstance(value, _PairsView):
            return "mapping"
    elif isinstance(value, (_Nested, _Raw)):
        value = value.value
    name = type(value).__qualname__
    if isinstance(value, (list, tuple, Mapping)):
        try:
            return f"{name}[{len(value)}]"[:EVIDENCE_KIND_MAX_CHARS]
        except TypeError:
            pass
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

    def source(self, value: Any, identity: Any = None, reread: Optional[Callable[[], Any]] = None) -> Any:
        if self.kind == TEXT:
            return text(value, self.max_chars)
        if self.kind == EVIDENCE:
            return evidence(
                self._legacy_source(value), identity,
                refresh=None if reread is None else (lambda: self._legacy_source(reread())),
                inline_bytes=self.inline_bytes,
            )
        return value

    def _legacy_source(self, value: Any) -> Any:
        if value is not None and type(value) is not BoundedEvidence and self.legacy is not None:
            return self.legacy(value)
        return value

    def max_value_bytes(self, policy: "JsonEncodingPolicy") -> int:
        if self.kind == TEXT:
            return max(4, policy.max_string_bytes(self.max_chars + TEXT_MARKER_MAX_CHARS))
        if self.kind == EVIDENCE:
            inline = EVIDENCE_INLINE_BYTES if self.inline_bytes is None else self.inline_bytes
            return max(4, inline, EVIDENCE_SUMMARY_MAX_BYTES)
        if self.kind == INT:
            return INT_MAX_BYTES
        return 5


def row_items(row: Tuple[Column, ...], record: Any, *, identity: Any = None):
    """`row` の列を `record` から読んで `(key, source)` を 1 つずつ返す（`json_items` の本体）。"""

    for column in row:
        name = column.attr or column.key
        value = getattr(record, name)
        if column.omit_none and value is None:
            continue
        yield column.key, column.source(
            value, identity, reread=lambda name=name: getattr(record, name),
        )


def row_max_bytes(row: Tuple[Column, ...], policy: Optional["JsonEncodingPolicy"] = None) -> int:
    """`row` の行を出力（CANONICAL）で書いたときの byte 数の上限。"""

    policy = RESULT_JSON_POLICY if policy is None else policy
    sizes = [policy.member_bytes(column.key, column.max_value_bytes(policy)) for column in row]
    return policy.container_frame_bytes(len(sizes)) + sum(sizes)


# ---------------------------------------------------------------------------
# 予算（walker が数えた byte を渡す相手）
# ---------------------------------------------------------------------------


class JsonBudget:
    """walker が数えた byte を受け取る相手（上限を超えたら `exceeded()`）。

    snapshot 側の aggregate（`core/budget_policy.SerializationWork`）は継承せずに
    同じ interface（`charge` / `remaining` / `tree` / `exceeded`）を持ち、超過を
    pair terminal な限界に変え、木の distinct node も数える。
    """

    def __init__(self, max_bytes: Optional[int] = None) -> None:
        self.max_bytes = max_bytes
        self.consumed = 0

    def remaining(self) -> Optional[int]:
        return None if self.max_bytes is None else self.max_bytes - self.consumed

    def charge(self, size: int) -> None:
        self.consumed += int(size)
        if self.max_bytes is not None and self.consumed > self.max_bytes:
            self.exceeded()

    def exceeded(self) -> None:
        raise JsonBudgetExhausted(consumed_bytes=self.consumed, max_bytes=self.max_bytes)

    def tree(self, leaf: Any, *, build: bool) -> Tuple[Any, int]:
        """sized leaf の大きさを **作る前に** 求めて足し、`build` なら木を作る。"""

        remaining = self.remaining()
        size = leaf.__json_tree_bytes__(RESULT_JSON_POLICY, remaining)
        if size is None:
            # DAG のまま見積もれない形（閉路。未凍結の式の中だけ）: node を 1 つ作るたびに
            # 数えながら作る（作ってから数えない）
            before = self.consumed
            built = leaf.__json_tree_metered__(RESULT_JSON_POLICY, self.charge)
            return (built if build else None), self.consumed - before
        self.charge(size)
        return (leaf.__json_tree__() if build else None), size


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
        self.encoded_bytes = int(encoded_bytes)
        self.policy = policy

    def value(self) -> Any:
        """canonical な値の複製（container だけ作り直す。scalar は immutable）。"""

        return _copy_canonical(self._value)

    def __repr__(self) -> str:  # pragma: no cover - debug 表示
        return f"PreparedJson({self.encoded_bytes} bytes)"


def is_prepared_json(value: Any) -> bool:
    return type(value) is PreparedJson


def _copy_canonical(value: Any) -> Any:
    if not isinstance(value, (dict, list)):
        return value
    root: List[Any] = [None]
    stack: List[Tuple[Any, Any, Any]] = [(value, root, 0)]
    while stack:
        source, parent, key = stack.pop()
        if isinstance(source, dict):
            out: Any = {}
            parent[key] = out
            for child_key, child in source.items():
                if isinstance(child, (dict, list)):
                    out[child_key] = None
                    stack.append((child, out, child_key))
                else:
                    out[child_key] = child
        elif isinstance(source, list):
            out = [None] * len(source)
            parent[key] = out
            for index, child in enumerate(source):
                if isinstance(child, (dict, list)):
                    stack.append((child, out, index))
                else:
                    out[index] = child
        else:
            parent[key] = source
    return root[0]


# ---------------------------------------------------------------------------
# policy
# ---------------------------------------------------------------------------


#: `ensure_ascii=False` で escape される文字（`json.encoder.ESCAPE` と同じ集合）。
_ESCAPE_UNICODE = re.compile(r'[\x00-\x1f\\"]')
#: `ensure_ascii=True` で escape される文字（`json.encoder.ESCAPE_ASCII` と同じ集合）。
_ESCAPE_ASCII = re.compile(r'([\\"]|[^\ -~])')
#: 2 文字の escape（`\"` `\\` `\b` `\f` `\n` `\r` `\t`）になる文字。
_SHORT_ESCAPES = frozenset('\\"\b\f\n\r\t')
#: 長い文字列を数えるときの 1 回分の文字数（上限に届いたら残りを数えない単位）。
_STRING_CHUNK = 1 << 16

CANONICAL = "canonical"
LEGACY = "legacy"


def _float_text(value: float) -> str:
    """`json` が float を書くときの文字列（`allow_nan=True` の既定どおり）。"""

    if value != value:
        return "NaN"
    if value == float("inf"):
        return "Infinity"
    if value == -float("inf"):
        return "-Infinity"
    return float.__repr__(value)


@dataclass(frozen=True)
class JsonEncodingPolicy:
    """JSON の書き方。数え方・変換・書き出しは必ずこの object を通す。"""

    ensure_ascii: bool = False
    sort_keys: bool = True
    item_separator: str = ", "
    key_separator: str = ": "

    @property
    def separators(self) -> Tuple[str, str]:
        return (self.item_separator, self.key_separator)

    # -- framing -------------------------------------------------------------

    def container_frame_bytes(self, count: int) -> int:
        """`count` 個の要素を持つ object / array の括弧と要素間の区切りの byte 数。"""

        return 2 + utf8_length(self.item_separator) * max(0, int(count) - 1)

    def member_bytes(self, key: Any, value_bytes: int) -> int:
        """object の member 1 つ（key・key と値の区切り・値）の byte 数。"""

        return self.key_bytes(key) + utf8_length(self.key_separator) + int(value_bytes)

    def object_bytes(self, member_bytes: Iterable[int]) -> int:
        sizes = [int(size) for size in member_bytes]
        return self.container_frame_bytes(len(sizes)) + sum(sizes)

    def max_member_bytes(self, max_key_chars: int, value_bytes: int) -> int:
        """key が `max_key_chars` 文字以下の member 1 つの byte 数の上限。"""

        return self.max_string_bytes(max_key_chars) + utf8_length(self.key_separator) + int(value_bytes)

    def added_member_bytes(self, key: Any, value_bytes: int) -> int:
        """1 つ以上の member を持つ object に member を 1 つ足したときに増える byte 数。"""

        return utf8_length(self.item_separator) + self.member_bytes(key, value_bytes)

    def max_string_bytes(self, max_chars: int) -> int:
        """`max_chars` 文字以下の文字列を書いたときの byte 数の上限（最悪の escape = 6 byte/文字）。"""

        # 最悪の escape: `ensure_ascii` では非 BMP の 1 文字が `\uXXXX\uXXXX`（12 byte）、
        # それ以外では制御文字の `\u00XX`（6 byte）
        return 2 + (12 if self.ensure_ascii else 6) * int(max_chars)

    # -- 書き出し ------------------------------------------------------------

    def _encoder(self) -> json.JSONEncoder:
        return json.JSONEncoder(
            ensure_ascii=self.ensure_ascii,
            sort_keys=self.sort_keys,
            separators=self.separators,
        )

    def dumps(self, value: Any, *, default: Optional[Callable[[Any], Any]] = None) -> str:
        """上限なしで書く（大きさが既に分かっている小さい値だけに使う）。"""

        return json.dumps(
            value,
            ensure_ascii=self.ensure_ascii,
            sort_keys=self.sort_keys,
            separators=self.separators,
            default=default,
        )

    def encode_bounded(self, value: Any, *, max_bytes: Optional[int]) -> str:
        """上限付きで書く。上限を超えた時点で止め、途中までの断片も捨てる。"""

        parts: List[str] = []
        written = 0
        for chunk in self._encoder().iterencode(value):
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
        return len(quoted.encode("utf-8", "surrogatepass")) - 2

    def _string_chunk_bytes_by_rule(self, text_value: str) -> int:
        """`_string_chunk_bytes` と同じ値を escape の規則から数える（test の照合用）。"""

        if self.ensure_ascii:
            total = len(text_value)
            for match in _ESCAPE_ASCII.finditer(text_value):
                char = match.group(0)
                if char in _SHORT_ESCAPES:
                    total += 1
                elif ord(char) > 0xFFFF:
                    total += 11  # surrogate pair: \uXXXX\uXXXX
                else:
                    total += 5  # \uXXXX
            return total
        total = (
            len(text_value) if text_value.isascii()
            else len(text_value.encode("utf-8", "surrogatepass"))
        )
        for match in _ESCAPE_UNICODE.finditer(text_value):
            total += 1 if match.group(0) in _SHORT_ESCAPES else 5
        return total

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

        if isinstance(key, str):
            return key if type(key) is str else str.__str__(key)
        if key is True:
            return "true"
        if key is False:
            return "false"
        if key is None:
            return "null"
        if isinstance(key, int):
            return int.__repr__(key)
        if isinstance(key, float):
            return _float_text(key)
        raise TypeError(
            f"keys must be str, int, float, bool or None, not {type(key).__name__}"
        )

    def key_bytes(self, key: Any) -> int:
        return self.string_bytes(self.canonical_key(key))

    # -- live → 表現 -----------------------------------------------------------

    def prepare(self, source: Any, *, max_bytes: Optional[int] = None) -> PreparedJson:
        """source を **上限まで** 引き出して canonical な JSON 値へ変える（出力の唯一の境界）。"""

        budget = JsonBudget(max_bytes)
        value = _Walk(self, CANONICAL, budget, build=True).run(source)
        return PreparedJson(value, budget.consumed, self, _token=_PREPARED_TOKEN)

    def measure(
        self, source: Any, *, max_bytes: Optional[int] = None, mode: str = CANONICAL,
    ) -> int:
        """`prepare`（mode=LEGACY なら `materialize`）と同じ走査で byte 数だけを数える。"""

        budget = JsonBudget(max_bytes)
        _Walk(self, mode, budget, build=False).run(source)
        return budget.consumed

    def materialize(self, source: Any, *, budget: Optional[JsonBudget] = None) -> Any:
        """LEGACY 表現を作る（record の `to_dict()`・snapshot）。`budget` を渡すとそこへ数える。"""

        return _Walk(self, LEGACY, budget or JsonBudget(None), build=True).run(source)

    def plain_bytes(self, value: Any, *, max_bytes: Optional[int] = None) -> Optional[int]:
        """容器（tuple / list / dict）と基底型 **だけ** から成る値の byte 数（それ以外は `None`）。

        `max_bytes` を超えたら `JsonBudgetExhausted`。live な object（record・式・Ghidra の
        値など）を含む値は `None`（呼ぶ側は有界な証拠へ置き換える）。
        """

        budget = JsonBudget(max_bytes)
        done, _ = _Walk(self, LEGACY, budget, build=False).plain(value, False)
        return budget.consumed if done else None

    def count_into(self, source: Any, budget: JsonBudget, *, mode: str = LEGACY) -> None:
        """source の byte 数を `budget` へ足す（作らない）。"""

        _Walk(self, mode, budget, build=False).run(source)

    def bounded_evidence(self, value: Any, identity: Any = None) -> Any:
        """証拠を有界にする: 小さければ値そのもの、大きければ `BoundedEvidence`。"""

        if type(value) is BoundedEvidence or value is None:
            return value
        try:
            self.measure(value, max_bytes=EVIDENCE_INLINE_BYTES, mode=LEGACY)
            return value
        except JsonBudgetExhausted:
            pass
        return _summarize_evidence(self, value, identity)

    def summarize_evidence(self, value: Any, identity: Any = None) -> BoundedEvidence:
        """大きさに依らず、証拠を有界な要約にする（identity + 種類）。"""

        return _summarize_evidence(self, value, identity)

    def evidence_digest(self, value: Any) -> str:
        """証拠の型つき token 列（dict は key 順に整列）の sha256（1 回辿る。作らない）。"""

        digest = hashlib.sha256()
        _Walk(self, LEGACY, JsonBudget(None), build=False, token_sink=digest.update).run(value)
        return digest.hexdigest()


def evidence_kind(value: Any) -> str:
    """有界な証拠の `kind`（元の値の型と、容器なら要素数）。"""

    return _value_kind(value)


def _summarize_evidence(policy: JsonEncodingPolicy, value: Any, identity: Any) -> BoundedEvidence:
    if callable(identity):
        identity = identity(value)
    if identity is None:
        from scripts.function_tracer_pcode.core.canonical_digest import canonical_merkle_digest

        try:
            # canonical な形の値は DAG-aware な Merkle digest（共有部分を 1 回だけ辿る）
            merkle, distinct = canonical_merkle_digest(_source_value(value))
        except (TypeError, UnicodeError):
            return BoundedEvidence(
                identity=policy.evidence_digest(value),
                identity_kind="sha256",
                kind=_value_kind(value),
            )
        return BoundedEvidence(
            identity=merkle,
            identity_kind="canonical_merkle_sha256",
            kind=_value_kind(value),
            distinct_nodes=distinct,
        )
    return BoundedEvidence(
        identity=str(identity)[:EVIDENCE_IDENTITY_MAX_CHARS],
        identity_kind="authority",
        kind=_value_kind(value),
    )


def bounded_text(value: Any, max_chars: int) -> Any:
    """`value` が `max_chars` 文字を超える文字列なら、先頭 + 明示の marker に置き換える。"""

    if isinstance(value, str) and len(value) > max_chars:
        return _text_marker(value, max_chars)
    return value


def _text_marker(value: str, max_chars: int) -> str:
    """`max_chars` 文字 **以内** に収まる「先頭 + 明示の marker」（同じ上限で冪等）。"""

    hasher = hashlib.sha256()
    for start in range(0, len(value), _STRING_CHUNK):
        # 巨大な文字列を一度に encode しない（chunk ごとに hash へ流す）
        hasher.update(value[start:start + _STRING_CHUNK].encode("utf-8", "surrogatepass"))
    digest = hasher.hexdigest()[:16]
    keep = max(0, max_chars - TEXT_MARKER_MAX_CHARS)
    tail = f"…[+{len(value) - keep} chars sha256:{digest}]"
    keep = max(0, max_chars - len(tail))
    tail = f"…[+{len(value) - keep} chars sha256:{digest}]"
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


def cached_string_bytes(policy: "JsonEncodingPolicy", text_value: str) -> int:
    """短い文字列の JSON byte 数（policy ごとの cache を使う。長い文字列は数えるだけ）。"""

    if len(text_value) > _SHORT_STRING:
        return policy.string_bytes(text_value)
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


def _copy_pure_tuple(value: tuple) -> list:
    """tuple だけから成る値の写し（tuple → list）。大きさは数え済み（cache）なので数えない。"""

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
            out.append(item)
        else:
            stack.pop()
    return root[0]


class _NotPlain(Exception):
    """純粋なデータ（容器と基底型だけ）の高速経路が扱えない値に出会った。"""


class _Walk:
    """source を 1 要素ずつ引き出して数え（CANONICAL / LEGACY）、`build` なら作る。

    再帰しない（frame の stack）。予算は `JsonBudget` が持ち、超えたらそこで止まる。
    `token_sink` を渡すと、値の型つき token 列を流す（`evidence_digest`）。
    """

    def __init__(
        self,
        policy: JsonEncodingPolicy,
        mode: str,
        budget: JsonBudget,
        *,
        build: bool,
        token_sink: Optional[Callable[[bytes], None]] = None,
    ) -> None:
        self.policy = policy
        self.mode = mode
        self.budget = budget
        self.build = build
        self.token_sink = token_sink
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
            parts.append(f"[{current}]" if isinstance(current, int) else f".{current}")
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
        if kind_of is str or isinstance(item, str):
            self.budget.charge(
                self.string_bytes(item) if kind_of is str
                else self.policy.string_bytes(item, max_bytes=self.budget.remaining())
            )
            if self.token_sink is not None:
                self.token("s" + item)
            if kind_of is not str and self.mode == CANONICAL:
                item = str.__str__(item)
            return True, item
        if kind_of is int or isinstance(item, int):
            value = int(item)
            self.budget.charge(len(int.__repr__(value)))
            if self.token_sink is not None:
                self.token("i" + int.__repr__(value))
            return True, (value if self.mode == CANONICAL else item)
        if isinstance(item, float):
            value = float(item)
            self.budget.charge(len(_float_text(value)))
            if self.token_sink is not None:
                self.token(
                    ("i" + int.__repr__(int(value))) if value.is_integer() else ("f" + _float_text(value))
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
        呼び出し側が一般の経路で辿り直す（それまでの勘定は `charge` していない）。LEGACY は tuple → 配列・dict の key をそのまま、
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
        # [iterator, out, is_dict, id, total_at_open, pure_tuple, obj]
        stack: List[List[Any]] = [[iter((value,)), root, False, None, 0, False, None]]
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
                        sizes[id(entry[6])] = (entry[6], total - entry[4])
                    elif stack:
                        stack[-1][5] = False
                    continue
                if entry[2]:
                    key, item = item
                    if type(key) is str:
                        text_key = key
                    elif key is None or isinstance(key, (str, int, float)):
                        # 基底型の subclass の key も一般の経路と同じ `canonical_key`
                        text_key = policy.canonical_key(key)
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
                    total += len(int.__repr__(item))
                elif kind is float:
                    total += len(_float_text(item))
                elif kind is tuple:
                    known = sizes.get(id(item))
                    if known is not None and known[0] is item:
                        total += known[1]
                        if remaining is not None and total > remaining:
                            break
                        if build:
                            copied = _copy_pure_tuple(item)
                            if entry[2]:
                                entry[1][out_key] = copied
                            else:
                                entry[1].append(copied)
                        continue
                    count = len(item)
                    total += 2 + (sep * (count - 1) if count else 0)
                    out = [] if build else None
                    if build:
                        if entry[2]:
                            entry[1][out_key] = out
                        else:
                            entry[1].append(out)
                    stack.append([iter(item), out, False, None, total - (2 + (sep * (count - 1) if count else 0)), True, item])
                    continue
                elif kind is list or kind is dict:
                    count = len(item)
                    total += 2 + (sep * (count - 1) if count else 0)
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
                        out, kind is dict, identity, 0, False, None,
                    ])
                    continue
                elif isinstance(item, (str, int, float)):
                    # 基底型の subclass（PyGhidra の Java primitive `JInt` / `JLong`、IntEnum
                    # など）。一般の経路（`scalar`）と同じく基底型の値で数え、LEGACY はその
                    # まま置き、CANONICAL は基底型へ直す。これを一般の経路へ落とすと、実
                    # バイナリの値のほとんどが高速経路を外れる。tuple の cache は基底型だけの
                    # 木に限る（cache の写しは値をそのまま置くので）。
                    entry[5] = False
                    if isinstance(item, str):
                        base = str.__str__(item)
                        total += string_bytes(base)
                    elif isinstance(item, int):
                        base = int(item)
                        total += len(int.__repr__(base))
                    else:
                        base = float(item)
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
            return False, None
        self.budget.charge(total)
        return True, (root[0] if build else None)

    # -- 容器 ------------------------------------------------------------------

    def push(self, kind: str, iterator: Iterator[Any], parent: Any, key: Any, source: Any,
             *, build: bool, fn: Any = None, preserve_keys: bool = False) -> None:
        # 閉路の判定は **参照している値**（record / 容器）の identity で行う。遅延構成子の
        # 包み（`each` など）はその場で作る一時 object なので、中身の値で数える。frame が
        # 値を保持するので、辿っている間に id が再利用されることは無い。
        if isinstance(source, _Source):
            if type(source) is _Each:
                source = source.items
            elif type(source) is _MappingOf:
                source = source.mapping
            else:
                source = None
        source_id = None if source is None else id(source)
        if source_id is not None:
            if source_id in self.active:
                self.reject("circular reference")
            self.active.add(source_id)
        self.budget.charge(2)
        if self.token_sink is not None:
            self.token("{" if kind == "dict" else "[")
            if kind == "dict":
                # digest は dict の並びに依らない（key の文字列で整列）
                iterator = iter(sorted(iterator, key=lambda pair: self.policy.canonical_key(pair[0])))
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
        if isinstance(item, _Source):
            self.enter_source(item, parent, key, build)
            return
        if isinstance(item, _AbcIterator):
            # iterator（generator を含む）は遅延配列: 1 要素ずつ引き出す（pure layer の
            # record は source の構成子を import できないので、これで列を渡す）
            self.push("list", item, parent, key, item, build=build)
            return
        if getattr(type(item), "json_items", None) is not None:
            self.push("dict", iter(item.json_items()), parent, key, item, build=build)
            return
        if getattr(type(item), "__json_tree__", None) is not None:
            built, size = self.budget.tree(item, build=build)
            if self.token_sink is not None:
                self.token("t" + item.__json_identity__())
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
        if isinstance(item, (Mapping, list, tuple)):
            if self.mode == LEGACY:
                # 既に在る値への参照: 写さずに数え、元の object をそのまま置く
                done, _ = self.plain(item, False)
                if not done:
                    self.count_only(item, raw_leaves=True)
                self.place(parent, key, item, build)
                return
            done, value = self.plain(item, build)
            if done:
                self.place(parent, key, value, build)
                return
            if isinstance(item, Mapping):
                self.push("dict", iter(item.items()), parent, key, item, build=build)
            else:
                self.push("list", iter(item), parent, key, item, build=build)
            return
        if self.mode == LEGACY:
            self.enter_raw(item, parent, key, build)
            return
        self.reject(f"{type(item).__qualname__} is not a JSON source")

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
        if isinstance(item, (Mapping, list, tuple)):
            done, _ = self.plain(item, False)
            if not done:
                if isinstance(item, Mapping):
                    self.push("dict", iter(item.items()), None, None, item, build=False,
                              fn=_RAW, preserve_keys=True)
                else:
                    self.push("list", iter(item), None, None, item, build=False, fn=_RAW)
                self.drain_to(len(self.stack) - 1)
        else:
            self.count_raw_leaf(item)
        self.place(parent, key, item, build)

    def count_raw_leaf(self, item: Any) -> None:
        """LEGACY でそのまま置く JSON 型でない葉を、**後段の codec が写す形で** 数える。

        snapshot の codec（`SnapshotFingerprintCodec._freeze`）は、この葉を `stable_key()` /
        `to_key()`・record の表現・dataclass の field の順で写す。同じ順で、その写しの
        大きさを数える（型名だけ数えて、中身を数えずに写させない）。
        """

        kind = type(item)
        if isinstance(item, Enum):
            self.opaque(item)
            return
        key_fn = getattr(item, "stable_key", None)
        if not callable(key_fn):
            key_fn = getattr(item, "to_key", None)
        if callable(key_fn):
            self.opaque(item)
            self.count_only(key_fn(), raw_leaves=True)
            return
        if (
            getattr(kind, "json_items", None) is not None
            or getattr(kind, "__json_tree__", None) is not None
            or kind is BoundedEvidence
        ):
            self.count_only(item, raw_leaves=False)
            return
        if is_dataclass(item) and not isinstance(item, type):
            self.opaque(item)
            for field_info in dataclass_fields(item):
                self.budget.charge(self.policy.string_bytes(field_info.name) + 4)
                self.count_only(getattr(item, field_info.name), raw_leaves=True)
            return
        self.opaque(item)

    def opaque(self, item: Any) -> None:
        """JSON 型でない葉（旧 `to_dict` がそのまま置いた値）: 型名や enum の値で数える。"""

        if isinstance(item, Enum):
            raw_value = item.value
            label = raw_value if isinstance(raw_value, str) else type(item).__qualname__
        else:
            label = type(item).__qualname__
        self.budget.charge(self.policy.string_bytes(label))
        if self.token_sink is not None:
            self.token("o" + type(item).__qualname__ + ":" + (label if isinstance(item, Enum) else ""))

    def enter_source(self, item: _Source, parent: Any, key: Any, build: bool) -> None:
        kind = type(item)
        if kind is _Each:
            self.push("list", iter(item.items), parent, key, item, build=build, fn=item.fn)
        elif kind is _MappingOf:
            pairs: Iterator[Any] = iter(item.mapping.items())
            if item.key_fn is not None:
                key_fn = item.key_fn
                pairs = ((key_fn(child_key), child) for child_key, child in pairs)
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
            if self.mode == CANONICAL and value is not None and not isinstance(value, str):
                # 文字列でない値（case の組など）も、列の上限まで: 収まらなければ有界な証拠
                self.enter_evidence(
                    _Evidence(
                        value, None,
                        inline_bytes=self.policy.max_string_bytes(item.max_chars + TEXT_MARKER_MAX_CHARS),
                    ),
                    parent, key, build,
                )
                return
            if self.mode == CANONICAL and isinstance(value, str) and len(value) > item.max_chars:
                value = _text_marker(value, item.max_chars)
            self.enter(value, parent, key, build)
        elif kind is _BoundedSummary:
            remaining = self.budget.remaining()
            if remaining is not None and remaining < item.max_bytes:
                # 上限ぶんの余地が無い: 作る前に止まる
                self.budget.charge(item.max_bytes)
            try:
                # 宣言した上限まで 1 回だけ作る（超えたら producer の契約違反）
                value = _Walk(
                    self.policy, self.mode, JsonBudget(item.max_bytes), build=True,
                ).run(item.fn())
            except JsonBudgetExhausted:
                self.reject(f"bounded summary exceeded its declared {item.max_bytes} bytes")
            self.enter(value, parent, key, build)
        else:  # pragma: no cover - 文法の追加漏れ
            self.reject(f"unknown source {kind.__qualname__}")

    def enter_nested(self, value: Any, parent: Any, key: Any, build: bool) -> None:
        """旧 `_jsonable_nested_tuple`: dict は dict、tuple / list は配列、それ以外はそのまま。"""

        if isinstance(value, (dict, tuple, list)):
            done, built = self.plain(value, build)
            if done:
                self.place(parent, key, built, build)
                return
        if isinstance(value, dict):
            self.push("dict", iter(value.items()), parent, key, value, build=build, fn=_NESTED,
                      preserve_keys=(self.mode == LEGACY))
        elif isinstance(value, (tuple, list)):
            self.push("list", iter(value), parent, key, value, build=build, fn=_NESTED)
        else:
            self.enter_raw(value, parent, key, build)

    def enter_evidence(self, item: _Evidence, parent: Any, key: Any, build: bool) -> None:
        value = item.value
        if self.mode == LEGACY or value is None or type(value) is BoundedEvidence:
            self.enter(value, parent, key, build)
            return
        try:
            # 上限（`inline_bytes`）まで 1 回だけ作る。収まればその値を置く
            inline_value = _Walk(
                self.policy, CANONICAL, JsonBudget(item.inline_bytes), build=True,
            ).run(value)
        except JsonBudgetExhausted:
            fresh = item.refresh() if item.refresh is not None else value
            self.enter(_summarize_evidence(self.policy, fresh, item.identity), parent, key, build)
            return
        self.enter(inline_value, parent, key, build)

    # -- 本体 ------------------------------------------------------------------

    def run(self, source: Any) -> Any:
        holder: List[Any] = [None]
        self.enter(source, holder, 0, self.build)
        self.drain_to(0)
        return holder[0]

    def drain_to(self, depth: int) -> None:
        stack = self.stack
        while len(stack) > depth:
            frame = stack[-1]
            try:
                child = next(frame.iterator)
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
                        self.reject(str(exc))
                if text_key in frame.keys:
                    self.reject(f"key {text_key!r} collides after JSON key conversion")
                frame.keys.add(text_key)
                frame.current = text_key
                self.budget.charge(separator + self.string_bytes(text_key) + self.key_separator)
                if self.token_sink is not None:
                    self.token("k" + text_key)
                out_key = child_key if frame.preserve_keys else text_key
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
                self.enter(fn(target), parent, out_key, frame.build)


def _canonical_copy_uncounted(policy: JsonEncodingPolicy, value: Any) -> Any:
    return _Walk(policy, CANONICAL, JsonBudget(None), build=True).run(value)


class JsonObjectBudget:
    """1 つの JSON object へ member を順に足していく勘定（framing は policy が決める）。"""

    def __init__(self, policy: JsonEncodingPolicy, max_bytes: Optional[int]) -> None:
        self.policy = policy
        self.max_bytes = max_bytes
        self._count = 0
        self._members = 0

    @property
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
        return self.max_bytes - self.total_bytes - self.added_bytes(key, 0)

    def add(self, key: Any, value_bytes: int) -> None:
        self._members += self.policy.member_bytes(key, value_bytes)
        self._count += 1


#: 結果 JSON（CLI が書く `EQUIVALENCE_RESULT_JSON`）の書き方。**唯一の定義**。
RESULT_JSON_POLICY = JsonEncodingPolicy()


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
        if value is not None and not isinstance(value, _SCALAR_TYPES):
            raise TypeError(
                f"{type(record).__qualname__}.{key} is not a scalar; use materialize()"
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
        site=RECORD_SERIALIZATION_SITE, target_parts=("record", type(source).__qualname__),
    ) as work:
        return RESULT_JSON_POLICY.materialize(source, budget=work)


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
    "JsonValueRejected",
    "LEGACY",
    "PreparedJson",
    "RESULT_JSON_POLICY",
    "TEXT_MARKER_MAX_CHARS",
    "as_dict",
    "as_list",
    "bounded_summary",
    "bounded_text",
    "cached_string_bytes",
    "clear_size_caches",
    "counts_max_bytes",
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
    "scalar_record_dict",
    "text",
]
