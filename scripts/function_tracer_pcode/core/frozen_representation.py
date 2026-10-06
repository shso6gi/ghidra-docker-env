# -*- coding: utf-8 -*-
"""検証済みの値が抱える runtime ref の LEGACY 表現の不変な写し（Issue #219 C-RS2）。

runtime ref の表現を作る code（record の `json_items`、そこから dispatch される method …）は
field の外の可変な状態を読み得るので、「その code が純粋か」を証明することはできない。そこで
表現を **直列化の owner 自身に 1 回だけ作らせ**、その結果を組み込みの値だけから成る不変な木として
持つ。以後の直列化は、この木から毎回新しい容器を作って描く（ref の code は 2 度と走らない）。
写すのは検証の transaction の外、closed の問い合わせのとき（`core/semantic_freeze.seal_runtime_ref`）。

木に入れてよいのは JSON の値になる組み込みの型 **そのもの** だけ:

* 葉: `None` / `bool` / `int` / `float`（有限）/ `str`
* 容器: `dict`（key は `str`）/ `list` / `tuple`（区別して保つので、描き直すと元と同じ型になる）

それ以外（`bytes`・record・enum・scalar の subclass・任意の object）を 1 つでも含む表現、閉路を
含む表現、`CAPTURE_MAX_BYTES` を超える表現は写さない（`freeze_legacy_tree` が `None`）。

**大きさの数え方と写し方は JSON の owner が持つ**（`JsonEncodingPolicy.bounded_native_copy`）。数える
byte は result JSON の writer（`RESULT_JSON_POLICY.dumps`）が書く byte と同じ（UTF-8・escape・
整数の桁・key と区切り）で、写す前に数え、上限を超えた時点で止まる。写しの量と辿る量の両方が上限で
抑えられる（上限の前に容器全体を写さない）。walker の葉としてそのまま置かれた容器（`raw()`）は、
walker が数えた後で中身が変わり得るので、walker の勘定ではなく、写す時点の中身を数える。

描き直した表現は、完成した表現として扱う（`thaw` の結果を生の ref と同じ変換へ通さない）。
見積もりは完成した表現の byte を数える（`Expression` の `_CompletedRefChild`）。
"""

from __future__ import annotations

from typing import Any, List, NamedTuple, Optional, Tuple

#: 写してよい表現の大きさの上限（JSON の byte）。runtime ref の表現は field の値の分しかなく
#: 通常は数百 byte。これを超える表現は写さない（その node は closed にならないだけ）
CAPTURE_MAX_BYTES = 1 << 16


class _Marker:
    """`_runtime_ref_payload` に置く状態の印（写しの代わり）。"""

    __slots__ = ("name",)

    def __init__(self, name: str) -> None:
        self.name = name

    def __repr__(self) -> str:
        return self.name

    def __reduce__(self):
        return (_marker, (self.name,))


def _marker(name: str) -> "_Marker":
    return SEAL_PENDING if name == "SEAL_PENDING" else UNSEALABLE


#: 写せる ref で、まだ写していない（closed の問い合わせで写す。それまでは生の ref を描く）
SEAL_PENDING = _Marker("SEAL_PENDING")
#: 写そうとして写せなかった（以後は生の ref から描く。closed にならない）
UNSEALABLE = _Marker("UNSEALABLE")


class FrozenDict(NamedTuple):
    """写した `dict`（key の順を保つ）。"""

    keys: Tuple[str, ...]
    values: Tuple[Any, ...]


class FrozenList(NamedTuple):
    """写した `list`。"""

    items: Tuple[Any, ...]


class FrozenTuple(NamedTuple):
    """写した `tuple`（描き直すと `tuple` に戻る）。"""

    items: Tuple[Any, ...]


class FrozenLegacyTree(NamedTuple):
    """組み込みの値だけから成る LEGACY 表現の不変な写し。"""

    root: Any

    def thaw(self) -> Any:
        """写した時点の表現と同じ値を、毎回新しい容器で作る（呼ぶ側が書き換えても写しは動かない）。"""

        return _thaw(self.root)


def freeze_legacy_tree(value: Any) -> Optional[FrozenLegacyTree]:
    """`value`（owner が作った LEGACY 表現）の不変な写し。写せない値を含むか上限を超えれば `None`。"""

    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY

    copied = RESULT_JSON_POLICY.bounded_native_copy(value, max_bytes=CAPTURE_MAX_BYTES)
    if copied is None:
        return None
    return FrozenLegacyTree(_freeze_native(copied[0]))


def _is_leaf(value: Any) -> bool:
    kind = type(value)
    if kind is float:
        # JSON の writer は非有限の値を JSON として書かない（写せる表現は JSON の値になるものだけ）
        return value == value and value not in (float("inf"), float("-inf"))
    return value is None or kind is bool or kind is int or kind is str


def _freeze_native(value: Any) -> Any:
    """owner が上限の中で写した組み込みの値（JSON の値になる型だけ・閉路なし）を不変な node にする。"""

    results: List[Any] = []
    stack: List[Tuple[Any, bool]] = [(value, False)]
    while stack:
        item, leaving = stack.pop()
        kind = type(item)
        if leaving:
            count = len(item)
            children = tuple(results[len(results) - count:]) if count else ()
            if count:
                del results[len(results) - count:]
            if kind is dict:
                results.append(FrozenDict(tuple(item), children))
            elif kind is list:
                results.append(FrozenList(children))
            else:
                results.append(FrozenTuple(children))
            continue
        if kind is dict or kind is list or kind is tuple:
            stack.append((item, True))
            children_in_order = tuple(item.values()) if kind is dict else tuple(item)
            stack.extend((child, False) for child in reversed(children_in_order))
            continue
        if not _is_leaf(item):
            raise TypeError("the bounded copy holds only JSON-native built-in values")
        results.append(item)
    return results[0]


def _thaw(frozen: Any) -> Any:
    # `_freeze` と同じ形の明示 stack（辿る値と「出る」印を別の stack に持つ）。出る時に子の値から
    # 容器を組む。写しは `_freeze` が作ったこの module の型と組み込みの葉だけなので、型を確かめて
    # から field を読む（確かめられない値は `TypeError`: 写しの外から来た値）
    results: List[Any] = []
    stack: List[Any] = [frozen]
    exits: List[bool] = [False]
    while stack:
        node = stack.pop()
        exiting = exits.pop()
        if type(node) is FrozenDict:
            keys = node.keys
            values = node.values
            if type(keys) is not tuple:
                raise TypeError("a frozen dict holds a tuple of keys")
            if type(values) is not tuple:
                raise TypeError("a frozen dict holds a tuple of values")
            if exiting is True:
                children = _pop_children(results, len(values))
                built: dict = {}
                for index in range(len(keys)):
                    key = keys[index]
                    if type(key) is not str:
                        raise TypeError("a frozen dict holds str keys")
                    built[key] = children[index]
                results.append(built)
            else:
                _push_children(stack, exits, node, values)
            continue
        if type(node) is FrozenList:
            items = node.items
            if type(items) is not tuple:
                raise TypeError("a frozen list holds a tuple of items")
            if exiting is True:
                results.append(_pop_children(results, len(items)))
            else:
                _push_children(stack, exits, node, items)
            continue
        if type(node) is FrozenTuple:
            items = node.items
            if type(items) is not tuple:
                raise TypeError("a frozen tuple holds a tuple of items")
            if exiting is True:
                results.append(tuple(_pop_children(results, len(items))))
            else:
                _push_children(stack, exits, node, items)
            continue
        if not _is_leaf(node):
            raise TypeError("a frozen legacy tree holds only built-in leaves")
        results.append(node)
    return results[0]


def _push_children(stack: List[Any], exits: List[bool], node: Any, children: Tuple[Any, ...]) -> None:
    """`node` を「出る」印つきで積み、その上に子を（先頭が先に出るよう逆順に）積む。"""

    stack.append(node)
    exits.append(True)
    for index in range(len(children) - 1, -1, -1):
        stack.append(children[index])
        exits.append(False)


def _pop_children(results: List[Any], count: int) -> List[Any]:
    """`results` の末尾 `count` 個（子の値。push した順）を取り出す。"""

    children: List[Any] = []
    for _ in range(count):
        children.append(results.pop())
    children.reverse()
    return children
