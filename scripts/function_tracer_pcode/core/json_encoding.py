# -*- coding: utf-8 -*-
"""JSON の書き方と大きさの数え方（Issue #22 PR-22-D）: **1 つの policy object**。

結果 JSON の大きさを「書く前に見積もる側」（出力の準備・式の木表現の予算）と
「実際に書く側」（CLI の bounded encoder）が別々の規則で数えると、見積りが実際の
byte を下回ったときに予算が効かなくなる。だから

* `JsonEncodingPolicy` が `ensure_ascii` / `sort_keys` / separators を 1 箇所で持ち、
* 見積り（`value_bytes` / `string_bytes`）も書き出し（`dumps` / `encode_bounded`）も
  同じ object の method にし、
* escape の規則（`"` `\\` 制御文字、`ensure_ascii` なら非 ASCII と surrogate pair）も
  その policy から導く。

見積りは **実際の encoder と同じ byte 数** を返す（上界として等号で成り立つ）。
巨大な値を一度 `json.dumps` してから長さを測ることはしない — 見積りは値を
走査するだけで文字列を作らず、`limit` を超えたら `limit + 1` で飽和してそれ以上
走査しない。

単位は UTF-8 byte（`core/render_output.utf8_length` と同じ数え方）。
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from typing import Any, Callable, List, Optional, Tuple

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


#: `ensure_ascii=False` で escape される文字（`json.encoder.ESCAPE` と同じ集合）。
_ESCAPE_UNICODE = re.compile(r'[\x00-\x1f\\"]')
#: `ensure_ascii=True` で escape される文字（`json.encoder.ESCAPE_ASCII` と同じ集合）。
_ESCAPE_ASCII = re.compile(r'([\\"]|[^\ -~])')
#: 2 文字の escape（`\"` `\\` `\b` `\f` `\n` `\r` `\t`）になる文字。
_SHORT_ESCAPES = frozenset('\\"\b\f\n\r\t')


def _float_text(value: float) -> str:
    """`json` が float を書くときの文字列（`allow_nan=True` の既定どおり）。"""

    if value != value:
        return "NaN"
    if value == float("inf"):
        return "Infinity"
    if value == -float("inf"):
        return "-Infinity"
    return float.__repr__(value)


_ENTER = object()
_EXIT = object()


@dataclass(frozen=True)
class JsonEncodingPolicy:
    """JSON の書き方。見積りと書き出しは必ずこの object を通す。"""

    ensure_ascii: bool = False
    sort_keys: bool = True
    item_separator: str = ", "
    key_separator: str = ": "

    @property
    def separators(self) -> Tuple[str, str]:
        return (self.item_separator, self.key_separator)

    def _encoder(self) -> json.JSONEncoder:
        return json.JSONEncoder(
            ensure_ascii=self.ensure_ascii,
            sort_keys=self.sort_keys,
            separators=self.separators,
        )

    # -- 書き出し ------------------------------------------------------------

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
        `dumps()` と同じ文字列になる（同じ encoder・同じ設定）。
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

    # -- 見積りと上限付きの写し -----------------------------------------------

    def _string_chunk_bytes(self, text: str) -> int:
        """引用符を除いた、文字列の一部を書いたときの byte 数。"""

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

    def _key_bytes(self, key: Any) -> int:
        """dict の key を書いたときの byte 数（`json` と同じ型変換）。"""

        if isinstance(key, str):
            return self.string_bytes(key)
        if key is True:
            return 6  # "true"
        if key is False:
            return 7  # "false"
        if key is None:
            return 6  # "null"
        if isinstance(key, int):
            return len(int.__repr__(key)) + 2
        if isinstance(key, float):
            return self.string_bytes(_float_text(key))
        raise TypeError(
            f"keys must be str, int, float, bool or None, not {type(key).__name__}"
        )

    def value_bytes(
        self,
        value: Any,
        *,
        max_bytes: Optional[int] = None,
        opaque_bytes: Optional[Callable[[Any], int]] = None,
    ) -> int:
        """`value` を書いたときの byte 数（`max_bytes` を超えたら `max_bytes + 1`）。

        値は写さない（`project_bounded` と同じ走査で数えるだけ）。
        """

        try:
            return self._walk(value, max_bytes, opaque_bytes, build=False)[1]
        except JsonBudgetExhausted:
            return max_bytes + 1

    def project_bounded(
        self,
        value: Any,
        *,
        max_bytes: Optional[int] = None,
        opaque_bytes: Optional[Callable[[Any], int]] = None,
    ) -> Tuple[Any, int]:
        """`value` を **上限まで** 写す。写した値と、それを書いたときの byte 数を返す。

        live な値（結果が持つ dict / list / 文字列）を、出力へ置く凍結した写しに
        変える唯一の道。写しながら数えるので、`max_bytes` を超えた時点で
        `JsonBudgetExhausted` を上げてそれ以上写さない — 写す量は残りの予算
        （+ 超えたことに気付いた 1 要素）までに収まる。container の型（list /
        tuple / dict）は保つ（`copy.deepcopy` と同じ形）。文字列と scalar は
        immutable なので参照のまま置く。JSON にならない値は `opaque_bytes` で数え、
        参照のまま置く（JSON にできるかの判定は最終 encoder が行う）。
        """

        return self._walk(value, max_bytes, opaque_bytes, build=True)

    def _walk(self, value, max_bytes, opaque_bytes, *, build):
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
        # frame: [kind, iterator, out, parent, parent_key, count, source_id]
        stack: List[List[Any]] = []

        def place(parent, key, item) -> None:
            if not build:
                return
            parent[key] = item

        def enter(item, parent, key) -> None:
            if item is None:
                charge(4)
            elif item is True:
                charge(4)
            elif item is False:
                charge(5)
            elif isinstance(item, str):
                limit = remaining()
                charge(self.string_bytes(item, max_bytes=limit))
            elif isinstance(item, int):
                charge(len(int.__repr__(item)))
            elif isinstance(item, float):
                charge(len(_float_text(item)))
            elif isinstance(item, (list, tuple, dict)):
                source_id = id(item)
                if source_id in active:
                    raise ValueError("Circular reference detected")
                active.add(source_id)
                charge(2)
                if isinstance(item, dict):
                    out = {} if build else None
                    iterator = iter(item.items())
                    kind = "dict"
                else:
                    out = [] if build else None
                    iterator = iter(item)
                    kind = "tuple" if isinstance(item, tuple) else "list"
                stack.append([kind, iterator, out, parent, key, 0, source_id, item])
                return
            elif opaque_bytes is not None:
                charge(int(opaque_bytes(item)))
            else:
                raise TypeError(
                    f"Object of type {type(item).__name__} is not JSON serializable"
                )
            place(parent, key, item)

        enter(value, holder, 0)
        while stack:
            frame = stack[-1]
            kind, iterator, out, parent, key, count, source_id, source = frame
            try:
                child = next(iterator)
            except StopIteration:
                stack.pop()
                active.discard(source_id)
                if build:
                    if kind == "tuple":
                        if type(source) is tuple:
                            out = tuple(out)
                        elif hasattr(source, "_fields"):  # NamedTuple
                            out = type(source)(*out)
                        else:
                            out = type(source)(out)
                    elif kind == "list" and type(source) is not list:
                        out = type(source)(out)
                    elif kind == "dict" and type(source) is not dict:
                        out = type(source)(out)
                place(parent, key, out)
                continue
            if count:
                charge(item_separator)
            frame[5] = count + 1
            if kind == "dict":
                child_key, child_value = child
                charge(self._key_bytes(child_key) + key_separator)
                enter(child_value, out if build else None, child_key)
            else:
                if build:
                    out.append(None)
                enter(child, out if build else None, count)
        return holder[0], total


class JsonBudgetExhausted(AnalysisFailureError):
    """`project_bounded` が上限に達した（写すのをそこで止めた）。

    `consumed_bytes` は止めた時点までに数えた byte 数（上限 + 1 以上）で、値全体の
    大きさではない（残りは数えていない）。
    """

    def __init__(self, *, consumed_bytes: int, max_bytes: Optional[int]) -> None:
        super().__init__(f"JSON projection exceeded {max_bytes} bytes")
        self.consumed_bytes = int(consumed_bytes)
        self.max_bytes = max_bytes


#: 長い文字列を数えるときの 1 回分の文字数（上限に届いたら残りを数えない単位）。
_STRING_CHUNK = 1 << 16


#: 結果 JSON（CLI が書く `EQUIVALENCE_RESULT_JSON`）の書き方。**唯一の定義**。
#: 見積り・bounded encoder・CLI の出力はすべてこれを使う。
RESULT_JSON_POLICY = JsonEncodingPolicy()


__all__ = [
    "JsonBudgetExhausted",
    "JsonEncodingPolicy",
    "JsonOutputLimitExceeded",
    "RESULT_JSON_POLICY",
]
