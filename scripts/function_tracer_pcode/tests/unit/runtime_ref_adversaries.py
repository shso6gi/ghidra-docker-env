# -*- coding: utf-8 -*-
"""Issue #242 の構築の契約の test が共有する、値を偽る scalar の subclass と比べるための view。

偽る型は基底型の値（内部の値）を持ちながら、subclass の code（変換・真偽・比較・hash・format・算術・文字列の
method）をすべて嘘で返し、呼ばれた回数を `HOOK_CALLS` に数える。構築の契約を満たす経路は、その code を
1 度も呼ばずに基底型の値だけで結果を作るので、結果は内部の値の双子から作ったものと同じになる。
"""

from __future__ import annotations

import collections
import dataclasses
import enum
from typing import Any, Dict

HOOK_CALLS: "collections.Counter[str]" = collections.Counter()

_LYING_INT = {
    "__int__": lambda self: 999,
    "__index__": lambda self: 999,
    "__float__": lambda self: 999.0,
    "__bool__": lambda self: not int.__bool__(self),
    "__repr__": lambda self: "LIE",
    "__str__": lambda self: "LIE",
    "__format__": lambda self, spec: "LIE",
    "__eq__": lambda self, other: False,
    "__ne__": lambda self, other: True,
    "__hash__": lambda self: 7,
    "__lt__": lambda self, other: True,
    "__le__": lambda self, other: True,
    "__gt__": lambda self, other: True,
    "__ge__": lambda self, other: True,
    "__neg__": lambda self: 999,
    "__pos__": lambda self: 999,
    "__abs__": lambda self: 999,
    "__invert__": lambda self: 999,
    "__add__": lambda self, other: 999,
    "__radd__": lambda self, other: 999,
    "__sub__": lambda self, other: 999,
    "__rsub__": lambda self, other: 999,
    "__mul__": lambda self, other: 999,
    "__rmul__": lambda self, other: 999,
    "__floordiv__": lambda self, other: 999,
    "__rfloordiv__": lambda self, other: 999,
    "__mod__": lambda self, other: 999,
    "__rmod__": lambda self, other: 999,
    "__and__": lambda self, other: 999,
    "__or__": lambda self, other: 999,
    "__xor__": lambda self, other: 999,
    "__lshift__": lambda self, other: 999,
    "__rshift__": lambda self, other: 999,
    "bit_length": lambda self: 999,
}
_LYING_STR = {
    "__str__": lambda self: "LIE",
    "__repr__": lambda self: "'LIE'",
    "__format__": lambda self, spec: "LIE",
    "__eq__": lambda self, other: False,
    "__ne__": lambda self, other: True,
    "__hash__": lambda self: 7,
    "__lt__": lambda self, other: True,
    "__gt__": lambda self, other: True,
    "__len__": lambda self: 3,
    "__bool__": lambda self: not str.__len__(self),
    "__iter__": lambda self: iter("LIE"),
    "__getitem__": lambda self, key: "L",
    "__contains__": lambda self, item: True,
    "__add__": lambda self, other: "LIE",
    "__mod__": lambda self, other: "LIE",
    "strip": lambda self, *args: "LIE",
    "lower": lambda self, *args: "LIE",
    "startswith": lambda self, *args: True,
    "endswith": lambda self, *args: True,
    "split": lambda self, *args: ["LIE"],
    "encode": lambda self, *args: b"LIE",
    "format": lambda self, *args, **kwargs: "LIE",
}
_LYING_FLOAT = {
    "__int__": lambda self: 999,
    "__float__": lambda self: 999.0,
    "__bool__": lambda self: not float.__bool__(self),
    "__repr__": lambda self: "LIE",
    "__str__": lambda self: "LIE",
    "__format__": lambda self, spec: "LIE",
    "__eq__": lambda self, other: False,
    "__ne__": lambda self, other: True,
    "__hash__": lambda self: 7,
    "__lt__": lambda self, other: True,
    "__gt__": lambda self, other: True,
    "__add__": lambda self, other: 999.0,
    "__mul__": lambda self, other: 999.0,
}


def _lying(base: type, name: str, table: Dict[str, Any]) -> type:
    namespace = {}
    for method, implementation in table.items():
        def hook(self, *args, _method=method, _implementation=implementation, **kwargs):
            HOOK_CALLS[f"{name}.{_method}"] += 1
            return _implementation(self, *args, **kwargs)

        namespace[method] = hook
    return type(name, (base,), namespace)


#: 値を偽る int / str / float の subclass（`Liar(1)` は JBoolean のような「真偽が int の値」の代わりにもなる）
Liar = _lying(int, "Liar", _LYING_INT)
LiarStr = _lying(str, "LiarStr", _LYING_STR)
LiarFloat = _lying(float, "LiarFloat", _LYING_FLOAT)


def lie(value: Any) -> Any:
    """exact な int / str / float を値を偽る subclass へ（bool・None・それ以外はそのまま）。"""

    kind = type(value)
    if kind is int:
        return Liar(value)
    if kind is str:
        return LiarStr(value)
    if kind is float:
        return LiarFloat(value)
    return value


def view(value: Any, _depth: int = 0) -> Any:
    """比べるための値: 型の札つきの基底型の値（`True` と `1`、`None` と `""` を区別する）。

    subclass の code を呼ばない（基底型の slot で読む）。容器は型を保って辿り、dataclass は field を辿る。
    """

    kind = type(value)
    if value is None:
        return ("none",)
    if kind is bool:
        return ("bool", value)
    if isinstance(value, enum.Enum):
        return ("enum", type(value).__qualname__, value.name)
    if issubclass(kind, int):
        return ("int", int.__index__(value))
    if issubclass(kind, str):
        return ("str", str.__str__(value))
    if issubclass(kind, float):
        return ("float", float.__repr__(float.__float__(value)))
    if kind is tuple or kind is list:
        return (kind.__name__, tuple(view(item, _depth + 1) for item in value))
    if _depth < 12 and dataclasses.is_dataclass(value) and not isinstance(value, type):
        return (
            kind.__qualname__,
            tuple((item.name, view(getattr(value, item.name), _depth + 1)) for item in dataclasses.fields(value) if item.compare),
        )
    return ("object", kind.__qualname__)
