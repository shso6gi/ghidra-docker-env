"""組み込みの振る舞いのままの容器の判定（Issue #22 PR-22-D）。

bounded path（walker・canonical digest・出力の marker）は、容器の中身を辿る前にこれで確かめる:
上書きした `items` / `__iter__` / `__len__` / `__getitem__` は producer（入力に比例する仕事を
作業量の外でし得る任意の code）なので呼ばない。判定そのものは型の属性と `gc.get_referents`
（proxy が包む値）だけを読み、user code を呼ばない。
"""

from __future__ import annotations

import gc
import inspect
import types
from collections import OrderedDict
from typing import Any, Mapping, Optional

#: 組み込みの振る舞い（`items` / `__iter__` / `__len__`）のまま辿ってよい mapping の型
_BUILTIN_DICTS = (dict, OrderedDict)


def builtin_mapping(item: Any) -> Optional[Mapping]:
    """`item` が組み込みの振る舞いの mapping ならそれを、そうでなければ `None`。

    dict / OrderedDict とその subclass（`items` / `__iter__` / `__len__` を上書きしないもの）と、
    それらを包む `MappingProxyType`（proxy は包んだ値の method へ転送するので、包んだ値の型を
    `gc.get_referents` で確かめる）。
    """

    kind = type(item)
    if kind is types.MappingProxyType:
        referents = gc.get_referents(item)
        if len(referents) != 1 or builtin_mapping(referents[0]) is None:
            return None
        return item
    for base in _BUILTIN_DICTS:
        if isinstance(item, base):
            if kind.items is base.items and kind.__iter__ is base.__iter__ and kind.__len__ is base.__len__:
                return item
            return None
    return None


def builtin_sequence(item: Any) -> bool:
    """`item` が組み込みの振る舞い（`__iter__` / `__len__` / `__getitem__`）の list / tuple か（namedtuple を含む）。"""

    kind = type(item)
    for base in (tuple, list):
        if isinstance(item, base):
            return (
                kind.__iter__ is base.__iter__
                and kind.__len__ is base.__len__
                and kind.__getitem__ is base.__getitem__
            )
    return False


def builtin_set(item: Any) -> bool:
    """`item` が組み込みの振る舞い（`__iter__` / `__len__`）の set / frozenset か。"""

    kind = type(item)
    for base in (frozenset, set):
        if isinstance(item, base):
            return kind.__iter__ is base.__iter__ and kind.__len__ is base.__len__
    return False


def plain_field_value(item: Any, name: str) -> Any:
    """dataclass の field の値（instance の `__dict__` か slot。property などの descriptor は呼ばない）。

    field 名を property が上書きしていれば `TypeError`（読み方が producer なので辿らない）。
    """

    state = getattr(type(item), "__dictoffset__", 0) and object.__getattribute__(item, "__dict__")
    if state and name in state:
        return state[name]
    descriptor = inspect.getattr_static(type(item), name, None)
    if isinstance(descriptor, types.MemberDescriptorType):
        return descriptor.__get__(item, type(item))
    raise TypeError(f"field {name!r} of {type(item).__name__} is not a plain attribute")


__all__ = ["builtin_mapping", "builtin_sequence", "builtin_set", "plain_field_value"]
