# -*- coding: utf-8 -*-
"""凍結時に作った LEGACY 表現の不変な写し（Issue #219 C-RS2）。

検証済みの意味値が抱える生 object（runtime ref）の表現は、表現を作る code（record の
`json_items`、そこから dispatch される method、snapshot codec が読む `stable_key` …）が
field の外の可変な状態を読み得るので、「その code が純粋か」を後から証明することはできない。
そこで凍結の時点で **直列化の owner 自身に 1 回だけ表現を作らせ**、その結果を組み込みの値だけから
成る不変な木として持つ（`SemanticSnapshot` が生 object を 1 回だけ読んで値にするのと同じ原理）。
以後の直列化は、この木から毎回新しい容器を作って描く（生 object の code は 2 度と走らない）。

木に入れてよいのは組み込みの型 **そのもの** だけ:

* 葉: `None` / `bool` / `int` / `float` / `str` / `bytes`
* 容器: `dict`（key は `str`）/ `list` / `tuple`（区別して保つので、描き直すと元と同じ型になる）

それ以外（record・enum・scalar の subclass・任意の object）を 1 つでも含む表現は写さない
（`freeze_legacy_tree` が `None`）。そういう葉は、描いた後で snapshot codec や JSON の writer が
その型の規則（任意の code）で読むので、写しても不変と言えない。

写しの大きさは、写すときに直列化の owner が上限（`CAPTURE_MAX_BYTES`）の中で作った表現の大きさで
抑えられる（上限を超える表現は写さない）。描き直す `thaw` はその写しだけを辿る。
"""

from __future__ import annotations

from typing import Any, List, NamedTuple, Optional, Tuple

#: 写してよい表現の大きさの上限（JSON の byte）。runtime ref の表現は field の値の分しかなく
#: 通常は数百 byte。これを超える表現は写さない（その node は closed にならないだけ）
CAPTURE_MAX_BYTES = 1 << 16


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
    """`value`（owner が作った LEGACY 表現）の不変な写し。写せない値を含めば `None`。"""

    ok, frozen = _freeze(value)
    return FrozenLegacyTree(frozen) if ok else None


def _is_leaf(value: Any) -> bool:
    kind = type(value)
    return value is None or kind is bool or kind is int or kind is float or kind is str or kind is bytes


def _freeze(value: Any) -> Tuple[bool, Any]:
    # 明示 stack（深い表現でも再帰上限に当たらない）。出る時に子の写しから親を組む
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
        if _is_leaf(item):
            results.append(item)
            continue
        if kind is dict:
            for key in item:
                if type(key) is not str:
                    return False, None
            stack.append((item, True))
            stack.extend((child, False) for child in reversed(tuple(item.values())))
            continue
        if kind is list or kind is tuple:
            stack.append((item, True))
            stack.extend((child, False) for child in reversed(item))
            continue
        return False, None
    return True, results[0]


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
