# -*- coding: utf-8 -*-
"""Issue #242 の構築の契約の test が共有する、値を偽る scalar の subclass・代わりの型と、比べるための view。

偽る型は基底型の値（内部の値）を持ちながら、基底型の **すべての** method（変換・真偽・比較・hash・format・算術・
文字列の method・`__len__` / `__iter__` など）を上書きして呼ばれた回数を `HOOK_CALLS` に数える（値を変える method
は嘘を返し、それ以外は基底型の実装を返す）。代わりの型（`Duck`）は本物の ref の値を持つが ref の class ではない
object。構築の契約を満たす経路は偽る型の code を 1 度も呼ばずに基底型の値だけで結果を作るので、結果は双子
（基底型の値・正直な代わりの型）から作ったものと、`view` で同じになる。`view` は scalar を型の札つきで、容器
（tuple / list / dict / set / frozenset / named tuple / bytes）を中まで、dataclass を比べない field と field で
ない instance の状態（構築が作る cache など）まで読む。`view` の scalar の札は基底型の名前で、subclass の
leaf と基底型の leaf を見分けない（値で比べる）。owner が写す位置の型は `test_issue242_construction_contract.py`
が型そのもので確かめ、注釈が Any の位置・代わりの型が返す値は写さない規則（受け取った側が reader で読む）。
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


#: 偽る型が上書きしない名前（構築・pickle・属性の仕組み。値の読みではない）
_NOT_HOOKED = frozenset({
    "__new__", "__init__", "__getattribute__", "__setattr__", "__delattr__", "__class__", "__init_subclass__",
    "__subclasshook__", "__reduce__", "__reduce_ex__", "__getnewargs__", "__getstate__", "__sizeof__", "__dir__",
    "__doc__", "__class_getitem__", "maketrans", "from_bytes", "fromhex", "fromkeys",
})


def _lying(base: type, name: str, table: Dict[str, Any]) -> type:
    """基底型のすべての method を数える subclass（`table` の method は値を偽り、それ以外は基底型の実装を返す）。"""

    namespace = {}
    methods = {
        attribute for attribute in dir(base)
        if attribute not in _NOT_HOOKED and callable(getattr(base, attribute, None)) and not isinstance(getattr(base, attribute), type)
    }
    for method in sorted(methods | set(table)):
        implementation = table.get(method)
        if implementation is None:
            implementation = (lambda _base_method: lambda self, *args, **kwargs: _base_method(self, *args, **kwargs))(getattr(base, method))

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
    if issubclass(kind, bytes):
        return ("bytes", bytes(value))
    if _depth > 12:
        return ("deep", kind.__qualname__)
    if kind is Duck:  # 代わりの型（偽る / 正直な双子）は包んだ本物の値で比べる
        return ("duck", view(object.__getattribute__(value, "_ref"), _depth + 1))
    if kind is tuple or kind is list:
        return (kind.__name__, tuple(view(item, _depth + 1) for item in value))
    if isinstance(value, tuple):  # named tuple など
        return (kind.__qualname__, tuple(view(item, _depth + 1) for item in tuple.__iter__(value)))
    if kind is dict:
        return ("dict", tuple(sorted(((view(k, _depth + 1), view(v, _depth + 1)) for k, v in dict.items(value)), key=repr)))
    if kind is set or kind is frozenset:
        return (kind.__name__, tuple(sorted((view(item, _depth + 1) for item in kind.__iter__(value)), key=repr)))
    if dataclasses.is_dataclass(value) and not isinstance(value, type):
        # field（比べない field を含む）と、field でない instance の状態（構築が作る cache など）
        fields = tuple((item.name, view(getattr(value, item.name), _depth + 1)) for item in dataclasses.fields(value))
        names = {item.name for item in dataclasses.fields(value)}
        extra = tuple(
            (key, view(item, _depth + 1)) for key, item in sorted(getattr(value, "__dict__", {}).items()) if key not in names
        )
        return (kind.__qualname__, fields, extra)
    if kind.__module__.startswith("scripts.function_tracer_pcode.") and not callable(value):
        state = dict(getattr(value, "__dict__", {}))
        for slot in getattr(kind, "__slots__", ()):
            if hasattr(value, slot):
                state[slot] = getattr(value, slot)
        return ("object", kind.__qualname__, tuple((key, view(item, _depth + 1)) for key, item in sorted(state.items())))
    return ("object", kind.__qualname__)


def _is_record(value: Any) -> bool:
    from scripts.function_tracer_pcode.core.runtime_ref_record import is_runtime_ref_record

    return dataclasses.is_dataclass(value) and not isinstance(value, type) and is_runtime_ref_record(type(value))


class Duck:
    """ref の代わりの型（duck typing）: 本物の ref の値を持つが ref の class ではない object。

    属性は本物の ref の値、method は本物の ref の method の戻り値を返す。`lying=True` なら、その scalar の葉を
    値を偽る subclass にし、入れ子の ref も偽る `Duck` にする（`lying=False` は同じ形の正直な双子）。偽る値は
    基底型の slot で作るので、この class 自身は偽る型の code を呼ばない。ref の構築は代わりの型を受理し得る
    （dataclass の field の型は実行時に確かめない）ので、受理した後で読む code の読み方を確かめるのに使う。
    """

    def __init__(self, ref: Any, lying: bool, objects: bool = False):
        object.__setattr__(self, "_ref", ref)
        object.__setattr__(self, "_lying", lying)
        object.__setattr__(self, "_objects", objects)

    def __getattr__(self, name: str) -> Any:
        ref = object.__getattribute__(self, "_ref")
        lying = object.__getattribute__(self, "_lying")
        objects = object.__getattribute__(self, "_objects")
        value = getattr(ref, name)
        if callable(value) and not isinstance(value, type) and not _is_record(value) and not _is_package_object(value):
            def method(*args: Any, **kwargs: Any) -> Any:
                return disguise(value(*args, **kwargs), lying, objects=objects)

            return method
        return disguise(value, lying, objects=objects)


def _is_package_object(value: Any) -> bool:
    kind = type(value)
    return (
        not isinstance(value, (type, enum.Enum)) and not callable(value)
        and kind.__module__.startswith("scripts.function_tracer_pcode.")
    )


def disguise(value: Any, lying: bool, _depth: int = 0, *, objects: bool = False) -> Any:
    """値の中の ref を `Duck` に（`lying` なら scalar の葉も偽る型に）する。容器は型を保って辿る。

    `objects` なら ref 以外の package の object（式・storage など）も `Duck` にする（属性を読む code の読み方を
    確かめる）。enum の member・型・callable はそのまま。
    """

    kind = type(value)
    if _depth > 12:
        return value
    if lying and kind in (int, str, float):
        return lie(value)
    if kind is tuple or kind is list:
        return kind(disguise(item, lying, _depth + 1, objects=objects) for item in value)
    if isinstance(value, tuple) and hasattr(kind, "_fields"):  # named tuple（`PhiBranch` など）は field ごとに
        return kind(*(disguise(item, lying, _depth + 1, objects=objects) for item in value))
    if kind is dict:
        return {disguise(k, lying, _depth + 1, objects=objects): disguise(v, lying, _depth + 1, objects=objects) for k, v in value.items()}
    if _is_record(value) or (objects and _is_package_object(value)):
        return Duck(value, lying, objects=objects)
    return value


def lie_deep(value: Any, _depth: int = 0) -> Any:
    """容器（tuple / list / dict）を辿って exact な scalar の葉をすべて偽る型にする（ref・式はそのまま）。"""

    kind = type(value)
    if kind in (int, str, float):
        return lie(value)
    if _depth > 12:
        return value
    if kind is tuple or kind is list:
        return kind(lie_deep(item, _depth + 1) for item in value)
    if kind is dict:
        return {lie_deep(k, _depth + 1): lie_deep(v, _depth + 1) for k, v in value.items()}
    return value
