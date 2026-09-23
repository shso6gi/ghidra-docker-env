# -*- coding: utf-8 -*-
"""`canonical_value`（`authority/contracts`）の形の DAG-aware な digest（Issue #22 PR-22-D）。

大きい証拠を authority 確定前に有界な表現へ置き換えるとき、その identity と照合用の
digest を、canonical な写しを作らずに求める。canonical_value と同じ正規化（enum は値、
`to_authority_dict` を持つ値はその dict、dataclass は field の組、mapping は key の
文字列で整列した組、list / tuple は tuple、set は整列した tuple）の形を辿る。

* 同じ容器 object は 1 回だけ辿る（**DAG-aware**。共有部分のある key でも distinct な
  node の数に比例する）。
* 2 つの値の digest が等しい ⇔ canonical_value が Python の `==` で等しい（数値は
  `==` と同じく 1 / 1.0 / True を同一視する）。例外は 2 つ: NaN は自分自身と等しい、
  enum の値が list / dict のときは tuple と同じ形として扱う（canonical_value はその
  値を正規化せずに返すので、`==` では list と tuple が等しくない）。

この module は core の最下層で、project の他の module を import しない。
"""

from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping as _AbcMapping
from dataclasses import fields, is_dataclass
from enum import Enum
from typing import Any, Dict, List, Tuple


_PRIMITIVE_TYPES = frozenset({str, int, float, bool})


class RawLeaf:
    """canonical_value がそのまま返す非基底型の値（enum の値など、小さい定数）。"""

    __slots__ = ("value",)

    def __init__(self, value: Any) -> None:
        self.value = value


def canonical_children(item: Any):
    """canonical_value で tuple になる値の子（mapping / dataclass の 1 組は 2 要素の tuple）。"""

    if is_dataclass(item):
        return [(field_info.name, getattr(item, field_info.name)) for field_info in fields(item)]
    if isinstance(item, _AbcMapping):
        return [
            (str(key), child)
            for key, child in sorted(item.items(), key=lambda pair: str(pair[0]))
        ]
    return list(item)


def _children(item: Any) -> List[Any]:
    if isinstance(item, (set, frozenset)):
        return list(item)
    return canonical_children(item)


def _leaf_token(value: Any) -> bytes:
    """葉の token（Python の `==` と同じ同一視: bool / int / 整数値の float は同じ token）。"""

    if value is None:
        return b"z"
    if isinstance(value, bool):
        return b"n" + str(int(value)).encode()
    if isinstance(value, int):
        return b"n" + str(int.__index__(value)).encode()
    if isinstance(value, float):
        if value == value and value not in (float("inf"), float("-inf")) and value.is_integer():
            return b"n" + str(int(value)).encode()
        return b"f" + float.__repr__(float(value)).encode()
    if isinstance(value, str):
        return b"s" + str.__str__(value).encode("utf-8", "surrogatepass")
    if type(value) is RawLeaf:
        return b"r" + json.dumps(
            value.value, sort_keys=True, separators=(",", ":"), ensure_ascii=False, default=repr,
        ).encode("utf-8", "surrogatepass")
    raise TypeError(f"unsupported authority value: {type(value).__name__}")


def canonical_merkle_digest(value: Any) -> Tuple[str, int]:
    """`canonical_value(value)` の形の DAG-aware な digest と、distinct な node の数。

    再帰しない（明示の stack）。同じ容器 object（tuple / list / mapping / dataclass /
    set）は 1 回だけ辿り、その digest を再利用する（共有部分がある key でも distinct な
    node の数に比例する）。
    """

    memo: Dict[int, bytes] = {}
    keep: list = []
    nodes = 0

    def _normalize(item: Any) -> Any:
        # canonical_value と同じ正規化（容器以外）
        while True:
            if item is None or type(item) in _PRIMITIVE_TYPES:
                return item
            if isinstance(item, Enum):
                # canonical_value は enum の値をそのまま返す。容器の値も同じ形として辿る
                item = item.value
                continue
            if hasattr(item, "to_authority_dict"):
                item = item.to_authority_dict()
                continue
            return item

    def _is_container(item: Any) -> bool:
        return is_dataclass(item) or isinstance(item, (_AbcMapping, list, tuple, set, frozenset))

    root = _normalize(value)
    if not _is_container(root):
        return hashlib.sha256(b"L" + _leaf_token(root)).hexdigest(), 1
    # frame: [object, children, child digests, is_set]
    stack: list = [[root, _children(root), [], isinstance(root, (set, frozenset))]]
    keep.append(root)
    result = b""
    while stack:
        frame = stack[-1]
        obj, children, digests, is_set = frame
        if len(digests) < len(children):
            child = _normalize(children[len(digests)])
            if _is_container(child):
                known = memo.get(id(child))
                if known is not None:
                    digests.append(known)
                    continue
                keep.append(child)
                stack.append([child, _children(child), [], isinstance(child, (set, frozenset))])
                continue
            nodes += 1
            digests.append(hashlib.sha256(b"L" + _leaf_token(child)).digest())
            continue
        stack.pop()
        nodes += 1
        ordered = sorted(digests) if is_set else digests
        digest = hashlib.sha256(
            b"T" + str(len(ordered)).encode() + b":" + b"".join(ordered)
        ).digest()
        memo[id(obj)] = digest
        if stack:
            stack[-1][2].append(digest)
        else:
            result = digest
    return result.hex(), nodes




__all__ = ["RawLeaf", "canonical_children", "canonical_merkle_digest"]
