"""runtime ref の scalar の field を組み込みの型そのものにする owner（Issue #242）。

runtime ref（`core/runtime_refs` の frozen な dataclass と `core/call_target.CallTargetRef`）の scalar の
field に、外の runtime の scalar の subclass（JPype の `JInt` / `JLong` / `JBoolean` など）が残ると、検証済みの
値の直列化の不変性（#219 C-RS2）がその ref を写せず、それを持つ式が serialization-closed にならない。
作る site ごとの正規化は漏れる（`int(...)` も `x or default` も subclass を返し得る）ので、ref の構築の入口
（`@runtime_ref_record`）で、注釈が scalar / tuple の field を 1 つの規則で写す。

**規則**（値の写し方の owner は `live_values.exact_scalar`。ここは field の注釈ごとの適用だけを持つ）:

- exact な組み込みの値・`None`・Enum の member（`IntEnum` / str の enum を含む）は変えない。
- scalar の subclass（Enum でない）は基底型の slot で読んだ値にする（subclass の code を呼ばない）。
- 注釈が `bool` の field だけ、int の subclass を `bool` にする（JBoolean の真偽を保つ）。
- 注釈が tuple の field は、exact な `tuple` の容器だけを辿り、葉に同じ規則を当てる（注釈は葉の分類に使わない）。
- 注釈が scalar / tuple でない field（`Any`・record・式）と、写せない値（scalar でない object）は変えない。

**順序**: `@dataclass` の **下** に置く（素の class に先に当たる）。class の `__dict__` に `__post_init__` を置く
（既存のものは包む）ので、生成された `__init__` は field の代入の後にそれを呼ぶ。正規化は class 自身の検証
（既存の `__post_init__` の本体）より前に走り、検証は exact な値だけを見る。検証が field を書き直したとき
（list から tuple を作るなど）は、書き直した field だけをもう一度写す。自前の `__init__` を持つ class
（`init=False`）は、その `__init__` の後に写す。`dataclasses.replace` は `__init__` を通るので同じ規則になる。

field の分類は class ごとに最初の構築で 1 度だけ決め（前方参照の注釈を解決できるのはその時点）、この
module の dict に置く。class の namespace には書かない（`live_values.package_type` の判定を変えない）。
"""

from __future__ import annotations

import dataclasses
import typing
from typing import Any, Callable, Dict, Tuple

from scripts.function_tracer_pcode.core.live_values import NOT_PLAIN, exact_scalar, int_value

#: field の分類（注釈 → 規則の当て方）。`object` の field は写さないので分類の列に入れない。
_SCALAR_KINDS = {int: "scalar", float: "scalar", str: "scalar", bool: "bool"}

#: class → 写す field の (名前, 分類) の列。最初の構築で決める。
_FIELD_KINDS: Dict[type, Tuple[Tuple[str, str], ...]] = {}

#: この decorator が置いた `__post_init__` / `__init__` → 包んだ元の関数（無ければ `None`）。
#: 継承した包みを二重に包まないため、また ref の class がこの owner を通ることを確かめるために使う。
_WRAPPERS: Dict[Callable[..., Any], Any] = {}


def _kind_of(annotation: Any) -> str:
    origin = typing.get_origin(annotation)
    if origin is typing.Union:
        rest = [arg for arg in typing.get_args(annotation) if arg is not type(None)]
        return _kind_of(rest[0]) if len(rest) == 1 else "object"
    kind = _SCALAR_KINDS.get(annotation) if isinstance(annotation, type) else None
    if kind is not None:
        return kind
    if origin is tuple:
        return "tuple"
    return "object"


def _field_hints(cls: type) -> Dict[str, Any]:
    """dataclass の field の注釈を解決した値（field を宣言した class の module で解決する）。

    `typing.get_type_hints(cls)` は class の全注釈を解決し、python 3.10 では文字列の `InitVar[...]` を
    型でないとして拒む。field でない注釈（`InitVar` / `ClassVar`）は解決しない。
    """

    names = {item.name for item in dataclasses.fields(cls)}
    hints: Dict[str, Any] = {}
    for klass in reversed(cls.__mro__):
        own = {
            name: annotation
            for name, annotation in klass.__dict__.get("__annotations__", {}).items()
            if name in names
        }
        if own:
            holder = type(klass.__name__, (), {"__annotations__": own, "__module__": klass.__module__})
            hints.update(typing.get_type_hints(holder))
    return hints


def field_kinds(cls: type) -> Tuple[Tuple[str, str], ...]:
    """`cls` の写す field の (名前, 分類)。class ごとに 1 度だけ注釈を解決する。"""

    known = _FIELD_KINDS.get(cls)
    if known is None:
        hints = _field_hints(cls)
        known = tuple(
            (item.name, kind)
            for item in dataclasses.fields(cls)
            for kind in (_kind_of(hints[item.name]),)
            if kind != "object"
        )
        _FIELD_KINDS[cls] = known
    return known


def exact_field_value(value: Any, kind: str) -> Any:
    """分類 `kind` の field に置く値（規則は module の docstring）。変えない値は同じ object を返す。"""

    holder = type(value)
    if holder is tuple:
        return _exact_tree(value) if kind == "tuple" else value
    if kind == "tuple":
        return value
    if kind == "bool" and holder is not int and holder is not bool:
        number = int_value(value)
        if number is not NOT_PLAIN:
            return number != 0
    return exact_scalar(value)


def _exact_tree(value: Tuple[Any, ...]) -> Tuple[Any, ...]:
    """exact な tuple の葉を写した tuple（葉がどれも変わらなければ同じ tuple）。"""

    items = None
    for index, item in enumerate(value):
        holder = type(item)
        if holder is tuple:
            new = _exact_tree(item)
        elif item is None or holder is int or holder is str or holder is bool or holder is float:
            continue
        else:
            new = exact_scalar(item)
        if new is not item:
            if items is None:
                items = list(value)
            items[index] = new
    return value if items is None else tuple(items)


def _normalize(instance: Any, kinds: Tuple[Tuple[str, str], ...]) -> None:
    for name, kind in kinds:
        value = object.__getattribute__(instance, name)
        holder = type(value)
        if value is None or holder is int or holder is str or holder is bool or holder is float:
            continue
        new = exact_field_value(value, kind)
        if new is not value:
            object.__setattr__(instance, name, new)


def normalize_fields(instance: Any) -> None:
    """`instance` の scalar / tuple の field を規則で写す（frozen でも書く）。"""

    _normalize(instance, field_kinds(type(instance)))


def _run_and_renormalize(instance: Any, run: Callable[[], None]) -> None:
    """class 自身の `__post_init__`（検証）を走らせ、その中で書き直された field だけを写し直す。"""

    kinds = field_kinds(type(instance))
    before = [object.__getattribute__(instance, name) for name, _kind in kinds]
    run()
    changed = tuple(
        entry for entry, old in zip(kinds, before) if object.__getattribute__(instance, entry[0]) is not old
    )
    if changed:
        _normalize(instance, changed)


def _original_of(function: Any) -> Any:
    """継承した包みなら、その包みが包んだ元の関数（包みを二重にしない）。"""

    return _WRAPPERS.get(function, function) if function is not None else None


def runtime_ref_record(cls: type) -> type:
    """runtime ref の class に scalar の正規化を付ける（`@dataclass(...)` の **下** に置く）。"""

    if "__dataclass_fields__" in cls.__dict__:
        raise TypeError(f"@runtime_ref_record must be applied below @dataclass ({cls.__qualname__})")
    custom_init = cls.__dict__.get("__init__")
    if custom_init is not None:
        # `init=False` で自前の `__init__` を持つ class（`CanonicalLocation`）: その後で写す
        original_init = _original_of(custom_init)

        def __init__(self: Any, *args: Any, **kwargs: Any) -> None:
            original_init(self, *args, **kwargs)
            normalize_fields(self)

        __init__.__qualname__ = f"{cls.__qualname__}.__init__"
        _WRAPPERS[__init__] = original_init
        cls.__init__ = __init__  # type: ignore[misc]
        return cls
    # 自分の `__post_init__` が無ければ継承したもの（包みなら元の関数）を呼ぶ
    original = _original_of(cls.__dict__.get("__post_init__") or getattr(cls, "__post_init__", None))

    if original is None:
        def __post_init__(self: Any, *init_vars: Any) -> None:
            normalize_fields(self)
    else:
        def __post_init__(self: Any, *init_vars: Any) -> None:
            normalize_fields(self)
            _run_and_renormalize(self, lambda: original(self, *init_vars))

    __post_init__.__qualname__ = f"{cls.__qualname__}.__post_init__"
    _WRAPPERS[__post_init__] = original
    cls.__post_init__ = __post_init__  # type: ignore[attr-defined]
    return cls


def is_runtime_ref_record(cls: type) -> bool:
    """`cls` の構築がこの owner の正規化を通るか（`__post_init__` か自前の `__init__` が包み）。"""

    for name in ("__post_init__", "__init__"):
        function = cls.__dict__.get(name)
        if function is not None and function in _WRAPPERS:
            return True
    return False


__all__ = [
    "exact_field_value",
    "field_kinds",
    "is_runtime_ref_record",
    "normalize_fields",
    "runtime_ref_record",
]
