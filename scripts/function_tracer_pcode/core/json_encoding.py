# -*- coding: utf-8 -*-
"""JSON の書き方・数え方・live object からの変換（Issue #22 PR-22-D）: **1 つの policy object**。

結果 JSON の大きさを「書く前に数える側」と「実際に書く側」が別々の規則で数えると、
見積りが実際の byte を下回ったときに予算が効かなくなる。だから次をすべて
`JsonEncodingPolicy` の method にし、他の module は JSON の規則（区切りの長さ・
key の型変換・escape）を自分で書かない:

* 書き方の設定（`ensure_ascii` / `sort_keys` / 区切り 2 種）
* framing の勘定（`{}` / `[]`、先頭と 2 つ目以降の区切り、key と値の区切り）
  — `JsonObjectBudget` が 1 つの object へ member を足していく勘定を持つ
* escape の規則（`"` `\\` 制御文字、`ensure_ascii` なら非 ASCII と surrogate pair）
* key の型変換（`true` / `false` / `null` / 数値の文字列化。`json` と同じ規則）
* live な値から **canonical な JSON 値** への変換（`prepare`）と、その上限
* 書き出し（`encode` / `encode_bounded`）

**live → prepared の唯一の変換境界は `prepare`**。入力は「JSON source」:

* scalar（`None` / `bool` / `int` / `float` / `str`、そのサブクラスは基底型へ）
* 既に在る container（`list` / `tuple` / `Mapping`）— 参照を渡すだけ
* `json_view()` を持つ object — 自分の表現を **浅く** 返す（下の規則）
* `JsonLazy(producer)` — 辿り着いたときに初めて呼ばれる値（record 1 件分の
  `to_dict` を遅らせるのに使う）
* `JsonLazyArray(iterable)` — 1 要素ずつ取り出される配列（generator でよい）
* `JsonLazyObject(pairs)` — (key, 値) を 1 組ずつ取り出す object

それ以外（集合・任意の object）は `JsonValueRejected`。`prepare` は source を
**1 要素ずつ** 辿りながら数え、上限を超えた時点で `JsonBudgetExhausted` を上げて
それ以上辿らない（写した量は残り予算 + 超えたことに気付いた 1 要素まで）。出力は
新しく作った `dict`（key は `str`）/ `list` と immutable な scalar だけの canonical な
JSON 値で、元の object を参照しない。書き出しはこの値を `default` hook 無しで書く
だけなので、authority 確定後に初めて型エラーが見つかる経路は無い。

`json_view()` の規則（`tests/unit/test_architecture_boundaries.py` が AST で固定）:
自分の直下の field を並べた mapping を返し、collection は既存の参照か
`JsonLazyArray` / generator で渡す。`to_dict()` の呼び出し・複製・内包表記・
`list(...)` などで表現を先に作らない（作るのは `prepare` だけ）。record 1 件分の
表現を `to_dict` に任せるときは `JsonLazy(record.to_dict)` と **呼ばずに** 渡す。

数えるだけの入口は 2 つ: `measure`（`prepare` と同じ走査。数え済みの部分を避けて
辿れる）と `measure_elements`（既に在る値を要素 1 つずつ C 実装の encoder で書いて
数える。snapshot の aggregate が使う）。どちらも書き出し器と同じ byte 数を返し、
上限を超えた時点で止まる。

単位は UTF-8 byte（`core/render_output.utf8_length` と同じ数え方）。
"""

from __future__ import annotations

import json
import re
from collections.abc import Mapping
from json.encoder import encode_basestring, encode_basestring_ascii
from dataclasses import dataclass
from typing import Any, Callable, Iterable, Iterator, List, Optional, Tuple

from scripts.function_tracer_pcode.core.errors import AnalysisFailureError
from scripts.function_tracer_pcode.core.render_output import utf8_length


class JsonOutputLimitExceeded(AnalysisFailureError):
    """bounded encoder が上限に達した（書き出しを止め、完成文字列を作らない）。

    `ValueError` 派生にしない（回復用の handler に吸われると上限が効かなくなる）。
    """

    def __init__(self, *, max_bytes: int, requested_bytes: int) -> None:
        super().__init__(
            f"JSON output exceeded {max_bytes} bytes (needed at least {requested_bytes})"
        )
        self.max_bytes = int(max_bytes)
        self.requested_bytes = int(requested_bytes)


class JsonBudgetExhausted(AnalysisFailureError):
    """`prepare` / `measure` が上限に達した（そこで辿るのをやめた）。

    `consumed_bytes` は止めた時点までに数えた byte 数（上限 + 1 以上）で、値全体の
    大きさではない（残りは数えていない）。
    """

    def __init__(self, *, consumed_bytes: int, max_bytes: Optional[int]) -> None:
        super().__init__(f"JSON projection exceeded {max_bytes} bytes")
        self.consumed_bytes = int(consumed_bytes)
        self.max_bytes = max_bytes


class JsonValueRejected(AnalysisFailureError):
    """JSON source の文法に無い値（集合・任意の object・閉路・key の衝突）。

    **producer のバグ** で、意味の限界ではない。出力の準備（authority 確定前）では
    内部エラーとして記録される。`TypeError` 派生にしない（回復用の handler に
    吸われると、canonical でない値が prepared payload に入り得る）。
    """

    def __init__(self, message: str, *, path: str) -> None:
        super().__init__(f"{message} at {path}")
        self.path = path


# ---------------------------------------------------------------------------
# JSON source の遅延構成子
# ---------------------------------------------------------------------------


class JsonLazy:
    """辿り着いたときに初めて作る値（record 1 件分の `to_dict` など）。

    `producer` は引数なしの callable。返り値もまた JSON source として辿る。
    """

    __slots__ = ("producer",)

    def __init__(self, producer: Callable[[], Any]) -> None:
        if not callable(producer):
            raise TypeError("JsonLazy needs a callable")
        self.producer = producer


class JsonLazyArray:
    """1 要素ずつ取り出される配列（generator でよい。1 回だけ辿る）。"""

    __slots__ = ("items",)

    def __init__(self, items: Iterable[Any]) -> None:
        self.items = items


class JsonLazyObject:
    """(key, 値) の組を 1 つずつ取り出す object（generator でよい。1 回だけ辿る）。

    既存の mapping を別の形に並べ直すとき（値の形を変える・一部だけ出す）に、
    並べ直した dict を先に作らないために使う。
    """

    __slots__ = ("pairs",)

    def __init__(self, pairs: Iterable[Tuple[Any, Any]]) -> None:
        self.pairs = pairs


def lazy_record(value: Any) -> Any:
    """record 1 件分の表現を、辿り着いたときに初めて `value.to_dict` で作らせる。

    偽の値（`None` など）は `None` として出す（従来の `x.to_dict() if x else None`）。
    """

    return JsonLazy(value.to_dict) if value else None


def lazy_records(values: Iterable[Any]) -> JsonLazyArray:
    """record の列を、1 件ずつ `to_dict` させる配列にする（列は複製しない）。"""

    return JsonLazyArray(JsonLazy(value.to_dict) for value in values)


# ---------------------------------------------------------------------------
# prepared value
# ---------------------------------------------------------------------------


_PREPARED_TOKEN = object()


class PreparedJson:
    """`prepare` だけが作る canonical な JSON 値と、それを書いたときの byte 数。

    値は新しく作った `dict`（key は `str`）/ `list` と immutable な scalar だけで、
    live な object を参照しない。外へ渡すのは複製（`value()`）だけなので、受け取った
    側が壊しても準備済みの値は変わらない。
    """

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


def _float_text(value: float) -> str:
    """`json` が float を書くときの文字列（`allow_nan=True` の既定どおり）。"""

    if value != value:
        return "NaN"
    if value == float("inf"):
        return "Infinity"
    if value == -float("inf"):
        return "-Infinity"
    return float.__repr__(value)


_PLAIN_CONTAINERS = (dict, list, tuple)


def _resolve(item: Any) -> Any:
    """遅延構成子と `json_view()` を、JSON の値の形になるまで解く。"""

    while True:
        if type(item) is JsonLazy:
            item = item.producer()
            continue
        view = getattr(type(item), "json_view", None)
        if view is not None and not isinstance(item, (str, int, float, list, tuple, Mapping)):
            item = item.json_view()
            continue
        return item


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
        """member の byte 数（`member_bytes()` の値）の列から object 全体の byte 数。"""

        sizes = [int(size) for size in member_bytes]
        return self.container_frame_bytes(len(sizes)) + sum(sizes)

    # -- 書き出し ------------------------------------------------------------

    def _encoder(self) -> json.JSONEncoder:
        return json.JSONEncoder(
            ensure_ascii=self.ensure_ascii,
            sort_keys=self.sort_keys,
            separators=self.separators,
        )

    def dumps(self, value: Any, *, default: Optional[Callable[[Any], Any]] = None) -> str:
        """上限なしで書く（大きさが既に分かっている小さい値だけに使う）。

        `default` は JSON 型でない値の代用表現（`json.dumps` と同じ意味）。
        """

        return json.dumps(
            value,
            ensure_ascii=self.ensure_ascii,
            sort_keys=self.sort_keys,
            separators=self.separators,
            default=default,
        )

    def encode_bounded(self, value: Any, *, max_bytes: Optional[int]) -> str:
        """上限付きで書く。上限を超えた時点で止め、途中までの断片も捨てる。

        `json.JSONEncoder.iterencode` の断片を数えながら貯めるので、出力は
        `dumps()` と同じ文字列になる（同じ encoder・同じ設定・`default` 無し）。
        """

        parts: List[str] = []
        written = 0
        for chunk in self._encoder().iterencode(value):
            written += utf8_length(chunk)
            if max_bytes is not None and written > max_bytes:
                parts.clear()
                raise JsonOutputLimitExceeded(
                    max_bytes=max_bytes, requested_bytes=written,
                )
            parts.append(chunk)
        return "".join(parts)

    # -- 文字列と key ----------------------------------------------------------

    def _string_chunk_bytes(self, text: str) -> int:
        """引用符を除いた、文字列の一部を書いたときの byte 数。

        `json` の escape 関数（C 実装）で書いた長さから引用符 2 つを引く。escape の
        規則は `json` そのものなので、書き出し器と食い違わない。
        """

        if self.ensure_ascii:
            return len(encode_basestring_ascii(text)) - 2
        quoted = encode_basestring(text)
        if quoted.isascii():
            return len(quoted) - 2
        return len(quoted.encode("utf-8", "surrogatepass")) - 2

    def _string_chunk_bytes_by_rule(self, text: str) -> int:
        """`_string_chunk_bytes` と同じ値を escape の規則から数える（test の照合用）。"""

        if self.ensure_ascii:
            total = len(text)
            for match in _ESCAPE_ASCII.finditer(text):
                char = match.group(0)
                if char in _SHORT_ESCAPES:
                    total += 1
                elif ord(char) > 0xFFFF:
                    total += 11  # surrogate pair: \uXXXX\uXXXX
                else:
                    total += 5  # \uXXXX
            return total
        total = len(text) if text.isascii() else len(text.encode("utf-8", "surrogatepass"))
        for match in _ESCAPE_UNICODE.finditer(text):
            total += 1 if match.group(0) in _SHORT_ESCAPES else 5
        return total

    def string_bytes(self, text: str, *, max_bytes: Optional[int] = None) -> int:
        """文字列 1 つを JSON 文字列として書いたときの byte 数（引用符を含む）。

        `max_bytes` を渡すと、超えた時点で `max_bytes + 1` を返して残りを数えない
        （長い文字列を一度に encode しない: `_STRING_CHUNK` 文字ずつ数える）。
        1 文字は少なくとも 1 byte なので、文字数だけで超えると分かればそこで止まる。
        """

        if max_bytes is not None and len(text) + 2 > max_bytes:
            return max_bytes + 1
        if max_bytes is None or len(text) <= _STRING_CHUNK:
            total = self._string_chunk_bytes(text) + 2
            if max_bytes is not None and total > max_bytes:
                return max_bytes + 1
            return total
        total = 2
        for start in range(0, len(text), _STRING_CHUNK):
            total += self._string_chunk_bytes(text[start:start + _STRING_CHUNK])
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
        """dict の key を書いたときの byte 数。"""

        return self.string_bytes(self.canonical_key(key))

    # -- live → canonical ----------------------------------------------------

    def prepare(self, source: Any, *, max_bytes: Optional[int] = None) -> PreparedJson:
        """JSON source を **上限まで** 辿って canonical な JSON 値へ変える（唯一の境界）。

        上限を超えた時点で `JsonBudgetExhausted`、文法に無い値は `JsonValueRejected`。
        """

        value, size = self._walk(source, max_bytes, build=True, exclude_ids=None)
        return PreparedJson(value, size, self, _token=_PREPARED_TOKEN)

    def measure(
        self,
        source: Any,
        *,
        max_bytes: Optional[int] = None,
        exclude_ids: Optional[Any] = None,
        opaque_bytes: Optional[Callable[[Any], int]] = None,
    ) -> int:
        """`prepare` と同じ走査で byte 数だけを数える（写さない）。

        超えたら `JsonBudgetExhausted`。`exclude_ids` に id がある container は数えず
        中へも入らない（別の勘定で既に数えた部分: 木表現の予算を参照）。
        `opaque_bytes` を渡すと、JSON source でない葉を拒まずにその大きさで数える
        （snapshot のように、後段の codec が別途 canonical にする表現を数えるとき）。
        """

        return self._walk(
            source, max_bytes, build=False, exclude_ids=exclude_ids, opaque_bytes=opaque_bytes,
        )[1]

    def measure_elements(
        self,
        value: Any,
        *,
        max_bytes: Optional[int] = None,
        opaque_text: Optional[Callable[[Any], str]] = None,
        whole: bool = False,
    ) -> int:
        """既に在る値の byte 数を **1 要素ずつ** 書き出し器で数える（写さない）。

        `whole=True` は値全体を 1 回で書いて数える（既に作ってある record 1 件分用）。

        `measure` と同じ byte 数（書き出し器そのものの長さ）を、C 実装の encoder で
        要素 1 つずつ求める。container は要素ごとに数えて上限を超えた時点で
        `JsonBudgetExhausted`（残りの要素は数えない）。文字列は chunk ごとに数える。
        JSON source でない葉は `opaque_text` の文字列として数える。1 要素の文字列は
        作るので、`exclude_ids` のように中の一部を数えない必要があるときは `measure`。
        """

        total = 0

        def charge(size: int) -> None:
            nonlocal total
            total += size
            if max_bytes is not None and total > max_bytes:
                raise JsonBudgetExhausted(consumed_bytes=total, max_bytes=max_bytes)

        def remaining() -> Optional[int]:
            return None if max_bytes is None else max_bytes - total

        def one(element: Any) -> int:
            if isinstance(element, str):
                return self.string_bytes(element, max_bytes=remaining())
            try:
                return utf8_length(self.dumps(element, default=opaque_text))
            except (TypeError, ValueError, RecursionError):
                # 混在した key 型・閉路など: 同じ規則の走査で数える
                return self.measure(element, max_bytes=remaining(), opaque_bytes=(
                    None if opaque_text is None
                    else (lambda leaf: self.string_bytes(opaque_text(leaf)))
                ))

        if whole:
            charge(one(value))
        elif isinstance(value, Mapping):
            charge(self.container_frame_bytes(len(value)))
            for key, element in value.items():
                charge(self.key_bytes(key) + utf8_length(self.key_separator))
                charge(one(element))
        elif isinstance(value, (list, tuple)):
            charge(self.container_frame_bytes(len(value)))
            for element in value:
                charge(one(element))
        else:
            charge(one(value))
        return total

    def materialize(self, source: Any) -> Any:
        """上限なしで canonical な値を作る（`to_dict()` を `json_view()` で定義する側用）。"""

        return self._walk(source, None, build=True, exclude_ids=None)[0]

    def _walk(self, value, max_bytes, *, build, exclude_ids, opaque_bytes=None):
        item_separator = utf8_length(self.item_separator)
        key_separator = utf8_length(self.key_separator)
        total = 0

        def charge(size: int) -> None:
            nonlocal total
            total += size
            if max_bytes is not None and total > max_bytes:
                raise JsonBudgetExhausted(consumed_bytes=total, max_bytes=max_bytes)

        def remaining() -> Optional[int]:
            return None if max_bytes is None else max_bytes - total

        holder: List[Any] = [None]
        active = set()
        # frame: [kind, iterator, out, parent, parent_key, count, source_id, current_key, keys]
        stack: List[List[Any]] = []

        def path() -> str:
            """今辿っている位置（拒むときだけ組み立てる。深い入れ子で 2 乗にしない）。"""

            parts = ["$"]
            for frame in stack:
                current = frame[7]
                parts.append(f"[{current}]" if isinstance(current, int) else f".{current}")
            return "".join(parts)

        def enter(item, parent, key) -> None:
            kind_of = type(item)
            if kind_of is str:
                charge(self.string_bytes(item, max_bytes=remaining()))
                if build:
                    parent[key] = item
                return
            if kind_of is int:
                charge(len(int.__repr__(item)))
                if build:
                    parent[key] = item
                return
            if kind_of not in _PLAIN_CONTAINERS and item is not None and item is not True and item is not False:
                item = _resolve(item)
            if item is None or item is True or item is False:
                charge(4 if item is not False else 5)
                result = item
            elif isinstance(item, str):
                charge(self.string_bytes(item, max_bytes=remaining()))
                result = item if type(item) is str else str.__str__(item)
            elif isinstance(item, int):
                result = int(item)
                charge(len(int.__repr__(result)))
            elif isinstance(item, float):
                result = float(item)
                charge(len(_float_text(result)))
            elif isinstance(item, (list, tuple, Mapping, JsonLazyArray, JsonLazyObject)):
                source_id = id(item)
                if exclude_ids is not None and source_id in exclude_ids:
                    return
                if source_id in active:
                    raise JsonValueRejected("circular reference", path=path())
                active.add(source_id)
                charge(2)
                if isinstance(item, Mapping):
                    kind = "dict"
                    iterator: Iterator[Any] = iter(item.items())
                    out: Any = {} if build else None
                elif type(item) is JsonLazyObject:
                    kind = "dict"
                    iterator = iter(item.pairs)
                    out = {} if build else None
                elif type(item) is JsonLazyArray:
                    kind = "list"
                    iterator = iter(item.items)
                    out = [] if build else None
                else:
                    kind = "list"
                    iterator = iter(item)
                    out = [] if build else None
                stack.append([kind, iterator, out, parent, key, 0, source_id, None, set()])
                return
            elif opaque_bytes is not None and not build:
                charge(int(opaque_bytes(item)))
                return
            else:
                raise JsonValueRejected(
                    f"{type(item).__qualname__} is not a JSON source", path=path(),
                )
            if build:
                parent[key] = result

        enter(value, holder, 0)
        while stack:
            frame = stack[-1]
            kind, iterator, out, parent, key, count, source_id, _current, keys = frame
            try:
                child = next(iterator)
            except StopIteration:
                stack.pop()
                active.discard(source_id)
                if build:
                    parent[key] = out
                continue
            if count:
                charge(item_separator)
            frame[5] = count + 1
            if kind == "dict":
                child_key, child_value = child
                try:
                    text_key = self.canonical_key(child_key)
                except TypeError as exc:
                    raise JsonValueRejected(str(exc), path=path()) from None
                if text_key in keys:
                    raise JsonValueRejected(
                        f"key {text_key!r} collides after JSON key conversion", path=path(),
                    )
                keys.add(text_key)
                frame[7] = text_key
                charge(self.string_bytes(text_key) + key_separator)
                enter(child_value, out, text_key)
            else:
                if build:
                    out.append(None)
                frame[7] = count
                enter(child, out, count)
        return holder[0], total


class JsonObjectBudget:
    """1 つの JSON object へ member を順に足していく勘定（framing は policy が決める）。

    出力の準備（authority 確定前）と最終 envelope（authority 確定後）が、同じ
    object の byte 数を同じ規則で数えるための唯一の道。区切りの長さや先頭 member の
    扱いを呼ぶ側が計算しない。
    """

    def __init__(self, policy: JsonEncodingPolicy, max_bytes: Optional[int]) -> None:
        self.policy = policy
        self.max_bytes = max_bytes
        self._count = 0
        self._members = 0

    @property
    def total_bytes(self) -> int:
        """今の member だけで閉じた object の byte 数。"""

        return self.policy.container_frame_bytes(self._count) + self._members

    @property
    def member_count(self) -> int:
        return self._count

    def added_bytes(self, key: Any, value_bytes: int) -> int:
        """member を 1 つ足したときに object が増える byte 数（区切りを含む）。"""

        return (
            self.policy.container_frame_bytes(self._count + 1)
            - self.policy.container_frame_bytes(self._count)
            + self.policy.member_bytes(key, value_bytes)
        )

    def remaining_for(self, key: Any) -> Optional[int]:
        """次に `key` の member を足すとき、値に使ってよい byte 数（負なら入らない）。"""

        if self.max_bytes is None:
            return None
        return self.max_bytes - self.total_bytes - self.added_bytes(key, 0)

    def add(self, key: Any, value_bytes: int) -> None:
        self._members += self.policy.member_bytes(key, value_bytes)
        self._count += 1


#: 結果 JSON（CLI が書く `EQUIVALENCE_RESULT_JSON`）の書き方。**唯一の定義**。
#: 見積り・準備・bounded encoder・CLI の出力はすべてこれを使う。
RESULT_JSON_POLICY = JsonEncodingPolicy()


__all__ = [
    "JsonBudgetExhausted",
    "JsonEncodingPolicy",
    "JsonLazy",
    "JsonLazyArray",
    "JsonLazyObject",
    "JsonObjectBudget",
    "JsonOutputLimitExceeded",
    "JsonValueRejected",
    "PreparedJson",
    "RESULT_JSON_POLICY",
    "is_prepared_json",
    "lazy_record",
    "lazy_records",
]
