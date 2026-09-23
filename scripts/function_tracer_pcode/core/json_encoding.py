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

    # -- 見積り --------------------------------------------------------------

    def string_bytes(self, text: str) -> int:
        """文字列 1 つを JSON 文字列として書いたときの byte 数（引用符を含む）。"""

        if self.ensure_ascii:
            total = len(text) + 2
            for match in _ESCAPE_ASCII.finditer(text):
                char = match.group(0)
                if char in _SHORT_ESCAPES:
                    total += 1
                elif ord(char) > 0xFFFF:
                    total += 11  # surrogate pair: \\uXXXX\\uXXXX
                else:
                    total += 5  # \\uXXXX
            return total
        total = (len(text) if text.isascii() else len(text.encode("utf-8", "surrogatepass"))) + 2
        for match in _ESCAPE_UNICODE.finditer(text):
            total += 1 if match.group(0) in _SHORT_ESCAPES else 5
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

        走査は反復で、文字列は作らない。上限を超えた時点で残りを見ない。循環参照は
        `json` と同じく `ValueError`。JSON にできない型は既定で `TypeError`（`json`
        と同じ契約）。`opaque_bytes` を渡すと、その型の値をその byte 数で数える
        （JSON へは書かない表現 — 式の木表現など — の大きさを測るとき用）。
        """

        item_separator = utf8_length(self.item_separator)
        key_separator = utf8_length(self.key_separator)
        total = 0
        active = set()
        stack: List[Tuple[Any, Any]] = [(_ENTER, value)]
        while stack:
            marker, item = stack.pop()
            if marker is _EXIT:
                active.discard(id(item))
                continue
            if item is None:
                size = 4
            elif item is True:
                size = 4
            elif item is False:
                size = 5
            elif isinstance(item, str):
                size = self.string_bytes(item)
            elif isinstance(item, int):
                size = len(int.__repr__(item))
            elif isinstance(item, float):
                size = len(_float_text(item))
            elif isinstance(item, (list, tuple, dict)):
                marker_id = id(item)
                if marker_id in active:
                    raise ValueError("Circular reference detected")
                active.add(marker_id)
                stack.append((_EXIT, item))
                count = len(item)
                size = 2 + max(0, count - 1) * item_separator
                if isinstance(item, dict):
                    size += count * key_separator
                    for key, child in item.items():
                        size += self._key_bytes(key)
                        stack.append((_ENTER, child))
                else:
                    for child in item:
                        stack.append((_ENTER, child))
            elif opaque_bytes is not None:
                size = int(opaque_bytes(item))
            else:
                raise TypeError(
                    f"Object of type {type(item).__name__} is not JSON serializable"
                )
            total += size
            if max_bytes is not None and total > max_bytes:
                return max_bytes + 1
        return total


#: 結果 JSON（CLI が書く `EQUIVALENCE_RESULT_JSON`）の書き方。**唯一の定義**。
#: 見積り・bounded encoder・CLI の出力はすべてこれを使う。
RESULT_JSON_POLICY = JsonEncodingPolicy()


__all__ = [
    "JsonEncodingPolicy",
    "JsonOutputLimitExceeded",
    "RESULT_JSON_POLICY",
]
