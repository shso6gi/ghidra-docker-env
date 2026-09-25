"""bounded path が live な値を読む **唯一の** 規則（Issue #22 PR-22-D）。

bounded path（walker・canonical digest・snapshot の codec・有界な証拠・key・出力の準備）は、
解析が持ってきた値（JPype の `JInt`・Ghidra の object・test の object・上書きした容器）を
この module の関数だけで読む。ここに無い読み方（`int(x)` / `float(x)` / `str(x)` /
`repr(x)` / `hash(x)` / `len(x)` / `iter(x)` / `isinstance(x, T)` / `getattr(x, name)` /
`dataclasses.fields(x)`）は live な値の user code（`__int__` / `__float__` / `__str__` /
`__repr__` / `__hash__` / `__len__` / `__iter__` / `__class__` / `__getattr__` / property /
metaclass の `__getattribute__`）を呼び得る。`tests/unit/test_architecture_boundaries.py` の
J19 が bounded path の関数からそれらの直接の呼び出しを拒む。

規則:

* 型は `type(x)` だけで決める（`isinstance` は上書きした `__class__` を読む）。型の属性は
  `inspect.getattr_static` で読む（metaclass の `__getattr__` / `__getattribute__` を呼ばない）。
* scalar の subclass（`bool` / `int` / `float` / `str`）は基底型の slot で基底型の値にする
  （`int.__index__` / `float.__float__` / `str.__str__`）。enum は scalar として扱わない。
* 容器は組み込みの振る舞い（`items` / `__iter__` / `__len__` / `__getitem__` を上書きしない
  dict / OrderedDict / list / tuple / set / frozenset、組み込みの dict を包む `MappingProxyType`、
  組み込みの容器の iterator）だけを辿る。
* instance の属性は instance の `__dict__` / slot から読む。property は package の型のもの
  （record の API）だけを呼ぶ。
"""

from __future__ import annotations

import gc
import inspect
import os
import sys
import types
from collections import OrderedDict
from enum import Enum
from typing import Any, Iterator, Optional, Tuple

#: 基底型でない値に `plain_scalar` / `*_value` が返す印
NOT_PLAIN = object()
#: package の directory（この file の 1 つ上）。package の code（関数・generator・property）の判定に使う
PACKAGE_DIR = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")) + os.sep
#: package の中でも package の code として信頼しない directory（test / fixture: 記録した Ghidra の
#: 値の代わりの object は live な値と同じに扱う）。test の harness だけが `trust_code_directory` で足す
_UNTRUSTED_DIRS = (os.path.join(PACKAGE_DIR, "tests") + os.sep,)
_TRUSTED_EXTRA_DIRS: list = []
_PACKAGE_FILES: dict = {}


def trust_code_directory(path: str) -> None:
    """test の harness が自分の code（test の module の record・converter・reducer）を信頼する。

    production は呼ばない（信頼は package の code だけ）。足すだけで取り消さない。
    """

    directory = os.path.normpath(os.path.abspath(path)) + os.sep
    if directory not in _TRUSTED_EXTRA_DIRS:
        _TRUSTED_EXTRA_DIRS.append(directory)
        _PACKAGE_FILES.clear()


def package_file(path: Any) -> bool:
    """file の path が package の code か（正規化して 1 度だけ調べる。test / fixture は除く）。"""

    if type(path) is not str:
        return False
    known = _PACKAGE_FILES.get(path)
    if known is None:
        normalized = os.path.normpath(os.path.abspath(path))
        known = any(normalized.startswith(directory) for directory in _TRUSTED_EXTRA_DIRS) or (
            normalized.startswith(PACKAGE_DIR)
            and not any(normalized.startswith(directory) for directory in _UNTRUSTED_DIRS)
        )
        _PACKAGE_FILES[path] = known
    return known


def package_code(code: Any) -> bool:
    """code object が package の file のものか（code の file 名は型の `__module__` と違い書き換えられない）。"""

    return type(code) is types.CodeType and package_file(code.co_filename)


def package_function(value: Any) -> bool:
    """package の code の関数か（型の MRO から引いた protocol の method・converter を呼んでよいかの判定）。"""

    return type(value) is types.FunctionType and package_code(value.__code__)


_BUILTIN_DICTS = (dict, OrderedDict)
_TYPE_QUALNAME = type.__dict__["__qualname__"]
_TYPE_MODULE = type.__dict__["__module__"]
_TYPE_MRO = type.__dict__["__mro__"]
#: 組み込みの容器の iterator（中身を辿るのは C の実装。generator のような code を持たない）
_BUILTIN_ITERATOR_TYPES = frozenset(
    type(iter(sample)) for sample in (
        (), [], {}, set(), frozenset(), "", b"", range(0), {}.keys(), {}.values(), {}.items(),
        reversed(()), reversed([]),
    )
)
_BUILTIN_VIEW_TYPES = frozenset(type(view) for view in ({}.keys(), {}.values(), {}.items()))


# ---------------------------------------------------------------------------
# 型
# ---------------------------------------------------------------------------


_TYPE_DICT = type.__dict__["__dict__"]
#: 型の flag（`Py_TPFLAGS_HEAPTYPE`: class 文で作った型。無ければ C で定義した組み込みの型）
_TYPE_FLAGS = type.__dict__["__flags__"]
_HEAP_TYPE = 1 << 9


def type_attribute(kind: type, name: str) -> Any:
    """型 `kind` の属性（MRO の各 class の `__dict__` から。metaclass の hook を呼ばない）。無ければ `None`。

    `inspect.getattr_static(kind, name)` の instance 向けの部分と同じ（metaclass の属性は含めない）。
    組み込みの slot（`__mro__` / `__dict__`）だけを読む。
    """

    for klass in _TYPE_MRO.__get__(kind):
        namespace = _TYPE_DICT.__get__(klass)
        if name in namespace:
            return namespace[name]
    return None


def _type_lookup(kind: type, name: str, missing: Any) -> Any:
    """`type_attribute` と同じ（無ければ `missing`。値が `None` の属性と区別する）。"""

    for klass in _TYPE_MRO.__get__(kind):
        namespace = _TYPE_DICT.__get__(klass)
        if name in namespace:
            return namespace[name]
    return missing


_TYPE_NAME = type.__dict__["__name__"]


def type_name(kind: type) -> str:
    """型の `__qualname__`（metaclass の property を通らない組み込みの slot で読む）。"""

    return _TYPE_QUALNAME.__get__(kind)


def type_module(kind: type) -> str:
    return _TYPE_MODULE.__get__(kind)


def is_kind(value: Any, base: type) -> bool:
    """`value` の型が `base` の subclass か（`isinstance` の代わり。`__class__` を読まない）。"""

    return issubclass(type(value), base)


def is_enum(value: Any) -> bool:
    return issubclass(type(value), Enum)


# ---------------------------------------------------------------------------
# scalar
# ---------------------------------------------------------------------------


def plain_scalar(value: Any) -> Any:
    """scalar なら基底型の値（subclass は基底型の slot で写す）、それ以外は `NOT_PLAIN`。"""

    if value is None or value is True or value is False:
        return value
    kind = type(value)
    if kind is str or kind is int or kind is float:
        return value
    if issubclass(kind, Enum):
        return NOT_PLAIN
    if issubclass(kind, bool):
        return bool.__bool__(value)
    if issubclass(kind, int):
        return int.__index__(value)
    if issubclass(kind, float):
        return float.__float__(value)
    if issubclass(kind, str):
        return str.__str__(value)
    return NOT_PLAIN


def json_scalar(value: Any) -> Any:
    """JSON の scalar としての基底型の値（`None` / bool / str・int・float とその subclass）。それ以外は `NOT_PLAIN`。

    JSON の規則（`json.dumps` と同じ）: mixin の enum（`IntEnum` / `str` の enum）も基底型の値で
    書く。`plain_scalar`（`str()` / `int()` の規則）は enum を除く。どちらも基底型の slot で読む。
    """

    if value is None or value is True or value is False:
        return value
    kind = type(value)
    if kind is str or kind is int or kind is float:
        return value
    if issubclass(kind, str):
        return str.__str__(value)
    if issubclass(kind, int):
        return int.__index__(value)
    if issubclass(kind, float):
        return float.__float__(value)
    return NOT_PLAIN


def str_value(value: Any) -> Any:
    """文字列（subclass を含む。enum を除く）なら基底型の `str`、それ以外は `NOT_PLAIN`。"""

    kind = type(value)
    if kind is str:
        return value
    if issubclass(kind, str) and not issubclass(kind, Enum):
        return str.__str__(value)
    return NOT_PLAIN


def int_value(value: Any) -> Any:
    """整数（bool を除く。subclass を含む。enum を除く）なら基底型の `int`、それ以外は `NOT_PLAIN`。"""

    kind = type(value)
    if kind is int:
        return value
    if issubclass(kind, int) and not issubclass(kind, (bool, Enum)):
        return int.__index__(value)
    return NOT_PLAIN


def float_value(value: Any) -> Any:
    kind = type(value)
    if kind is float:
        return value
    if issubclass(kind, float) and not issubclass(kind, Enum):
        return float.__float__(value)
    return NOT_PLAIN


def as_int(value: Any) -> int:
    """`int(value)` と同じ値（bool / int / float / str とその subclass）を基底型の slot で求める。

    それ以外（`__int__` / `__index__` を持つ object・enum）は `TypeError`（user code を呼ばない）。
    """

    kind = type(value)
    if kind is int:
        return value
    if value is True or value is False:
        return 1 if value else 0
    if issubclass(kind, Enum):
        raise TypeError(f"{type_name(kind)} is not converted to int without its own code")
    if issubclass(kind, int):
        return int.__index__(value)
    if issubclass(kind, float):
        return int(float.__float__(value))
    if issubclass(kind, str):
        return int(str.__str__(value))
    raise TypeError(f"{type_name(kind)} is not converted to int without its own code")


def as_float(value: Any) -> float:
    kind = type(value)
    if kind is float:
        return value
    if value is True or value is False:
        return 1.0 if value else 0.0
    if issubclass(kind, Enum):
        raise TypeError(f"{type_name(kind)} is not converted to float without its own code")
    if issubclass(kind, float):
        return float.__float__(value)
    if issubclass(kind, int):
        return float(int.__index__(value))
    if issubclass(kind, str):
        return float(str.__str__(value))
    raise TypeError(f"{type_name(kind)} is not converted to float without its own code")


def as_bool(value: Any) -> bool:
    """`bool(value)` と同じ値（scalar・組み込みの振る舞いの容器）。それ以外は `TypeError`。"""

    if value is None or value is True or value is False:
        return bool(value)
    base = plain_scalar(value)
    if base is not NOT_PLAIN:
        return bool(base)
    if builtin_container(value):
        return size(value) > 0
    kind = type(value)
    # `__bool__` / `__len__` を MRO のどこにも持たない型の値は常に真（`bool(x)` と同じ。その値の
    # code は無い: record・generator・関数など）
    if (
        type_attribute(kind, "__bool__") is None
        and type_attribute(kind, "__len__") is None
    ):
        return True
    if issubclass(kind, Enum) and builtin_enum(value):
        return True
    raise TypeError(f"{type_name(kind)} is not converted to bool without its own code")


def as_str(value: Any) -> str:
    """`str(value)` と同じ文字列（scalar・組み込みのままの enum）。それ以外は `TypeError`。"""

    base = plain_scalar(value)
    if base is not NOT_PLAIN:
        return base if type(base) is str else str(base)
    if builtin_enum(value):
        return _enum_text(value, "__str__")
    raise TypeError(f"{type_name(type(value))} is not converted to str without its own code")


def as_repr(value: Any) -> str:
    """`repr(value)` と同じ文字列（scalar・組み込みのままの enum）。それ以外は `TypeError`。"""

    base = plain_scalar(value)
    if base is not NOT_PLAIN:
        return type(base).__repr__(base)
    if builtin_enum(value):
        return _enum_text(value, "__repr__")
    raise TypeError(f"{type_name(type(value))} is not converted to repr without its own code")


def _enum_text(value: Any, slot: str) -> str:
    """組み込みのままの enum の `str()` / `repr()`（`Enum.__str__` / `Enum.__repr__` を、`__class__` を読まずに再現する）。"""

    kind = type(value)
    method = type_attribute(kind, slot)
    if slot == "__str__" and method is object.__str__:
        # `object.__str__` は `repr()` と同じ
        slot, method = "__repr__", type_attribute(kind, "__repr__")
    class_name = _TYPE_NAME.__get__(kind)
    if method is Enum.__str__:
        return f"{class_name}.{enum_name(value)}"
    if method is Enum.__repr__:
        member = plain_scalar(instance_state(value, "_value_", None))
        return f"<{class_name}.{enum_name(value)}: {type(member).__repr__(member)}>"
    if method is str.__str__:
        return str.__str__(value)
    if method is int.__repr__ or method is int.__str__:
        return int.__repr__(value)
    raise TypeError(f"{type_name(kind)} has its own {slot}")


_BUILTIN_ENUM_STR = frozenset({Enum.__str__, str.__str__, int.__repr__, int.__str__, object.__str__})
_BUILTIN_ENUM_REPR = frozenset({Enum.__repr__, object.__repr__})
_BUILTIN_HASH = frozenset({Enum.__hash__, str.__hash__, int.__hash__, object.__hash__})


def builtin_enum(value: Any) -> bool:
    """組み込みのままの enum の member か（`__str__` / `__repr__` / `__hash__` を上書きせず、値が scalar）。"""

    kind = type(value)
    if not issubclass(kind, Enum):
        return False
    from enum import EnumMeta

    # `Enum.__str__` / `__repr__` / `__hash__` は Python の code で、member の属性と `__class__` を
    # 読み、値の `repr` を呼ぶ: それらも組み込みのまま（metaclass・属性の読み方・値の型）のときだけ
    member = instance_state(value, "_value_", None)
    return (
        type(kind) is EnumMeta
        and type_attribute(kind, "__str__") in _BUILTIN_ENUM_STR
        and type_attribute(kind, "__repr__") in _BUILTIN_ENUM_REPR
        and type_attribute(kind, "__hash__") in _BUILTIN_HASH
        and type_attribute(kind, "__eq__") in _BUILTIN_EQ
        and type_attribute(kind, "__format__") in _BUILTIN_ENUM_FORMAT
        and type_attribute(kind, "__getattribute__") in _BUILTIN_GETATTRIBUTE
        and type_attribute(kind, "__class__") is _OBJECT_CLASS
        and (member is None or type(member) is str or type(member) is int or type(member) is float or type(member) is bool)
    )


_BUILTIN_EQ = frozenset({object.__eq__, str.__eq__, int.__eq__, float.__eq__})
_BUILTIN_ENUM_FORMAT = frozenset({Enum.__format__, object.__format__, str.__format__, int.__format__, float.__format__})
_OBJECT_CLASS = object.__dict__["__class__"]
_BUILTIN_GETATTRIBUTE = frozenset({
    object.__getattribute__, str.__getattribute__, int.__getattribute__, float.__getattribute__,
})


def enum_value(value: Any) -> Any:
    """enum の member の値（instance の `_value_`。`value` の property を呼ばない）。"""

    return instance_state(value, "_value_")


def enum_name(value: Any) -> Any:
    return instance_state(value, "_name_")


# ---------------------------------------------------------------------------
# instance の属性
# ---------------------------------------------------------------------------


_MISSING = object()
#: `attribute` が instance の値の無いことを知る印（`instance_state` の既定値）
_ABSENT = object()


def instance_state(value: Any, name: str, default: Any = _MISSING) -> Any:
    """instance の `__dict__` か slot に在る値（descriptor・`__getattr__` を呼ばない）。"""

    kind = type(value)
    offset_holder = type_attribute(kind, "__dict__")
    # instance の `__dict__` の組み込みの getset（型の MRO のどこかが持つもの。metatype の
    # `__dict__`（型 object 用）を instance に当てない）
    # `__dict__` は組み込みの getset か（`types.SimpleNamespace` などの C の型は）member descriptor
    holder_kind = type(offset_holder)
    if (
        (holder_kind is types.GetSetDescriptorType or holder_kind is types.MemberDescriptorType)
        and offset_holder.__objclass__ in _TYPE_MRO.__get__(kind)
    ):
        state = offset_holder.__get__(value, kind)
        if type(state) is dict and name in state:
            return state[name]
    descriptor = type_attribute(kind, name)
    if type(descriptor) is types.MemberDescriptorType:
        try:
            return descriptor.__get__(value, kind)
        except AttributeError:
            pass
    if default is not _MISSING:
        return default
    raise TypeError(f"{name!r} of {type_name(kind)} is not plain instance state")


def attribute(value: Any, name: str, default: Any = None) -> Any:
    """record の属性（instance の値。無ければ package の型の property。それ以外は `default`）。

    live な object の `__getattr__` / 上書きした `__getattribute__` / package の外の property は
    呼ばない（`default`）。class の属性（method・定数）は返さない。
    """

    state = instance_state(value, name, _ABSENT)
    if state is not _ABSENT:
        return state
    kind = type(value)
    descriptor = _type_lookup(kind, name, _ABSENT)
    if descriptor is _ABSENT:
        return default
    descriptor_kind = type(descriptor)
    if descriptor_kind is property:
        getter = descriptor.fget
        # package の code が定義した property（record の API）だけを呼ぶ
        if type(getter) is types.FunctionType and package_code(getter.__code__):
            return getter(value)
        return default
    # class の定数（descriptor でない値: `__get__` を持たない型の値）はそのまま
    if _type_lookup(descriptor_kind, "__get__", _ABSENT) is _ABSENT:
        return descriptor
    return default


def set_state(value: Any, name: str, new: Any) -> None:
    """package の record の instance の値を書く（`setattr` の代わり。`__setattr__` / property の setter を呼ばない）。

    書ける場所は instance の `__dict__` か slot だけ。package の型が定義した `__setattr__`（record の
    不変条件の検査）は型の関数を直接呼ぶ。それ以外の `__setattr__` を持つ型・名前が property など
    data descriptor の値は `TypeError`（その値の code を呼ばない）。
    """

    kind = type(value)
    setter = type_attribute(kind, "__setattr__")
    if setter is not object.__setattr__:
        if type(setter) is types.FunctionType and package_code(setter.__code__):
            setter(value, name, new)
            return
        if type(setter) is types.WrapperDescriptorType and not (_TYPE_FLAGS.__get__(setter.__objclass__) & _HEAP_TYPE):
            # C で定義した組み込みの型の `__setattr__`（`types.SimpleNamespace` など。上書きできない）
            setter(value, name, new)
            return
        raise TypeError(f"{type_name(kind)} has its own __setattr__")
    descriptor = _type_lookup(kind, name, _ABSENT)
    if type(descriptor) is types.MemberDescriptorType:
        descriptor.__set__(value, new)
        return
    if descriptor is not _ABSENT and _type_lookup(type(descriptor), "__set__", _ABSENT) is not _ABSENT:
        raise TypeError(f"{name!r} of {type_name(kind)} is not plain instance state")
    holder = type_attribute(kind, "__dict__")
    holder_kind = type(holder)
    if (
        (holder_kind is types.GetSetDescriptorType or holder_kind is types.MemberDescriptorType)
        and holder.__objclass__ in _TYPE_MRO.__get__(kind)
    ):
        state = holder.__get__(value, kind)
        if type(state) is dict:
            state[name] = new
            return
    raise TypeError(f"{type_name(kind)} has no instance state for {name!r}")


def has_attribute(value: Any, name: str) -> bool:
    """`attribute` が値を返すか（`hasattr` の代わり。`__getattr__` を呼ばない）。"""

    return attribute(value, name, _ABSENT) is not _ABSENT


# ---------------------------------------------------------------------------
# dataclass
# ---------------------------------------------------------------------------


def dataclass_field_names(value: Any) -> Optional[Tuple[str, ...]]:
    """dataclass の instance なら field の名前（`dataclasses.fields` と同じ順と規則）、それ以外は `None`。"""

    kind = type(value)
    if issubclass(kind, type):
        return None
    table = type_attribute(kind, "__dataclass_fields__")
    if type(table) is not dict:
        return None
    import dataclasses

    # `dataclasses.fields` と同じ判定。表の中身も組み込みの型そのものだけ（`Field` の slot を
    # 型の descriptor で読む。偽の表の object の属性・`__getattr__` を呼ばない）
    field_type_slot = _type_lookup(dataclasses.Field, "_field_type", None)
    names = []
    for name, field_info in dict.items(table):
        if type(name) is not str or type(field_info) is not dataclasses.Field:
            return None
        if field_type_slot.__get__(field_info, dataclasses.Field) is dataclasses._FIELD:  # type: ignore[attr-defined]
            names.append(name)
    return tuple(names)


def field_value(value: Any, name: str) -> Any:
    """dataclass の field の値（instance の値だけ。field 名を property が上書きしていれば `TypeError`）。"""

    return instance_state(value, name)


# ---------------------------------------------------------------------------
# 容器
# ---------------------------------------------------------------------------


def builtin_mapping(item: Any) -> Any:
    """組み込みの振る舞いの mapping ならそれを、そうでなければ `None`。

    dict / OrderedDict とその subclass（`items` / `__iter__` / `__len__` を上書きしないもの）と、
    それらを包む `MappingProxyType`（包んだ値の型を `gc.get_referents` で確かめる）。
    """

    kind = type(item)
    if kind is dict or kind is OrderedDict:
        return item
    if kind is types.MappingProxyType:
        referents = gc.get_referents(item)
        if len(referents) != 1 or builtin_mapping(referents[0]) is None:
            return None
        return item
    return item if _builtin_behaviour(kind, _BUILTIN_DICTS, ("items", "__iter__", "__len__")) else None


def builtin_sequence(item: Any) -> bool:
    """組み込みの振る舞い（`__iter__` / `__len__` / `__getitem__`）の list / tuple か（namedtuple を含む）。"""

    kind = type(item)
    if kind is tuple or kind is list:
        return True
    return _builtin_behaviour(kind, (tuple, list), ("__iter__", "__len__", "__getitem__"))


def builtin_set(item: Any) -> bool:
    kind = type(item)
    if kind is frozenset or kind is set:
        return True
    return _builtin_behaviour(kind, (frozenset, set), ("__iter__", "__len__"))


_BUILTIN_BEHAVIOUR: dict = {}


def _builtin_behaviour(kind: type, bases: Tuple[type, ...], names: Tuple[str, ...]) -> bool:
    """`kind` が `bases` のどれかの subclass で、`names` の method を上書きしていないか（型ごとに 1 度だけ）。"""

    if not _plain_metatype(kind):
        # metaclass が `__eq__` / `__hash__` を持つ型は cache の key にもしない（その code を呼ばない）
        return False
    key = (kind, bases)
    known = _BUILTIN_BEHAVIOUR.get(key)
    if known is None:
        known = False
        for base in bases:
            if issubclass(kind, base):
                known = all(type_attribute(kind, name) is type_attribute(base, name) for name in names)
                break
        _BUILTIN_BEHAVIOUR[key] = known
    return known


def builtin_iterator(item: Any) -> bool:
    """組み込みの容器の iterator / dict の view か（中身を辿るのは組み込みの実装だけ）。"""

    kind = type(item)
    if kind is range:
        return True
    return _plain_metatype(kind) and (kind in _BUILTIN_ITERATOR_TYPES or kind in _BUILTIN_VIEW_TYPES)


def _plain_metatype(kind: type) -> bool:
    """型の hash・比較が組み込みの実装か（metaclass が `__eq__` / `__hash__` を上書きしない）。"""

    metatype = type(kind)
    if metatype is type:
        return True
    return (
        _type_lookup(metatype, "__eq__", None) is object.__eq__
        and _type_lookup(metatype, "__hash__", None) is object.__hash__
    )


def builtin_container(item: Any) -> bool:
    return builtin_sequence(item) or builtin_set(item) or builtin_mapping(item) is not None


def size(item: Any) -> int:
    """組み込みの振る舞いの容器・文字列・bytes の長さ（基底型の `__len__`）。それ以外は `TypeError`。"""

    kind = type(item)
    if kind is str or kind is list or kind is tuple or kind is dict or kind is bytes:
        return len(item)
    text = str_value(item)
    if text is not NOT_PLAIN:
        return len(text)
    if builtin_container(item) or kind is types.MappingProxyType and builtin_mapping(item) is not None:
        return len(item)
    raise TypeError(f"{type_name(kind)} has no builtin length")


def _mapping_base(mapping: Any) -> type:
    """組み込みの振る舞いの mapping の基底型（その型の method を名指しで呼ぶ。`__getattribute__` を通らない）。"""

    if builtin_mapping(mapping) is None:
        raise TypeError(f"{type_name(type(mapping))} is not a builtin mapping")
    kind = type(_unwrapped(mapping))
    return OrderedDict if issubclass(kind, OrderedDict) else dict


def _unwrapped(mapping: Any) -> Any:
    """`MappingProxyType` なら包んだ mapping（proxy の method は包んだ値の method を名前で呼ぶので使わない）。"""

    if type(mapping) is types.MappingProxyType:
        return gc.get_referents(mapping)[0]
    return mapping


def items_of(mapping: Any) -> Iterator[Tuple[Any, Any]]:
    """組み込みの振る舞いの mapping の (key, 値)。それ以外は `TypeError`。"""

    if type(mapping) is dict:
        return iter(dict.items(mapping))
    return iter(_mapping_base(mapping).items(_unwrapped(mapping)))


def values_of(mapping: Any) -> Iterator[Any]:
    """組み込みの振る舞いの mapping の値。それ以外は `TypeError`。"""

    if type(mapping) is dict:
        return iter(dict.values(mapping))
    return iter(_mapping_base(mapping).values(_unwrapped(mapping)))


def merged_mappings(*mappings: Any) -> dict:
    """組み込みの振る舞いの mapping（key は組み込みの `str` だけ）を順に重ねた新しい dict。

    key を hash・比較するのは組み込みの `str` の実装だけ（上書きした `__hash__` / `__eq__` を
    呼ばない）。key が `str` でない mapping は `TypeError`。
    """

    merged: dict = {}
    for mapping in mappings:
        for key, value in items_of(mapping):
            if type(key) is not str:
                raise TypeError(f"mapping key {type_name(type(key))} is not a builtin str")
            merged[key] = value
    return merged


def lookup(mapping: Any, key: Any, default: Any = None) -> Any:
    """組み込みの振る舞いの mapping の `key` の値（基底型の `get`）。`key` は plain な値に限る。

    `key` の `__hash__` / `__eq__` を呼ぶので、key は組み込みの scalar か、その tuple だけ。
    """

    if not _plain_key(key):
        raise TypeError(f"{type_name(type(key))} is not a plain mapping key")
    if type(mapping) is dict:
        return dict.get(mapping, key, default)
    return _mapping_base(mapping).get(_unwrapped(mapping), key, default)


def _plain_key(key: Any) -> bool:
    kind = type(key)
    if key is None or kind is str or kind is int or kind is bool or kind is float:
        return True
    if kind is tuple:
        return all(_plain_key(part) for part in key)
    return False


def package_generator(value: Any) -> bool:
    """package の code の generator か（中身を作るのは package の code だけ）。"""

    return type(value) is types.GeneratorType and package_code(value.gi_code)


def elements_of(values: Any) -> Iterator[Any]:
    """組み込みの振る舞いの列・集合・iterator・package の generator の要素。それ以外は `TypeError`。"""

    if builtin_sequence(values) or builtin_set(values) or builtin_iterator(values) or package_generator(values):
        return iter(values)
    if builtin_mapping(values) is not None:
        return iter(values)
    raise TypeError(f"{type_name(type(values))} is not a builtin iterable")


__all__ = [
    "NOT_PLAIN",
    "PACKAGE_DIR",
    "package_code",
    "package_file",
    "package_generator",
    "package_function",
    "trust_code_directory",
    "as_bool",
    "as_float",
    "as_int",
    "as_repr",
    "as_str",
    "builtin_enum",
    "attribute",
    "builtin_container",
    "builtin_iterator",
    "builtin_mapping",
    "builtin_sequence",
    "builtin_set",
    "dataclass_field_names",
    "elements_of",
    "enum_name",
    "enum_value",
    "field_value",
    "float_value",
    "has_attribute",
    "instance_state",
    "int_value",
    "is_enum",
    "is_kind",
    "json_scalar",
    "items_of",
    "lookup",
    "merged_mappings",
    "plain_scalar",
    "set_state",
    "size",
    "str_value",
    "type_attribute",
    "type_module",
    "type_name",
    "values_of",
]
