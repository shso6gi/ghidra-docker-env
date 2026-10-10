"""runtime ref の scalar の field を組み込みの型そのものにする owner（Issue #242）。

runtime ref（`core/runtime_refs` の frozen な dataclass と `core/call_target.CallTargetRef`）の scalar の
field に、外の runtime の scalar の subclass（JPype の `JInt` / `JLong` / `JBoolean` など）が残ると、検証済みの
値の直列化の不変性（#219 C-RS2）がその ref を写せず、それを持つ式が serialization-closed にならない。
作る site ごとの正規化は漏れる（`int(...)` も `x or default` も subclass を返し得る）ので、ref の構築の入口
（`@runtime_ref_record`）で、注釈が scalar / tuple の field を 1 つの規則で写す。

**責務の分け方**:

- scalar の値の読み方（基底型の slot で読む）は `live_values`（`exact_scalar` / `scalar_int` / `scalar_text` /
  `scalar_bool` / `scalar_int_or`、容器の `builtin_items`、比べる前の値の `exact_tree`）。容器・行を読む ref の層の形は
  `runtime_refs/_reading`（`items` / `optional_items` / `rows`）。
- その規則を field に当てる（どの field に、いつ）のと、入口の引数に当てる（signature の束縛と同じ対応で、
  本体が消費する前に）のはこの module（`runtime_ref_record` / `runtime_ref_entry`）。
- ref ごとの検証と意味（list から tuple を作る・範囲を確かめる・key を作るなど）は各 ref。容器の中・注釈が
  `Any` / record の値・他の object の属性・他の object の method の戻り値は、owner が写した値ではないので、
  消費する前に上の reader で読む（この module は list や任意の object を辿らない）。

**規則**:

- exact な組み込みの値・`None`・Enum の member（`IntEnum` / str の enum を含む）は変えない。
- scalar の subclass（Enum でない）は基底型の slot で読んだ値にする（subclass の code を呼ばない）。
- 注釈が `bool` の field だけ、int の subclass を `bool` にする（JBoolean の真偽を保つ）。
- 注釈が tuple の field は、exact な `tuple` の容器だけを辿り、葉に同じ規則を当てる（注釈は葉の分類に使わない）。
  共有された tuple は 1 回の正規化の中で 1 度だけ辿り、写した結果も共有する（葉が変わらない tuple は同じ object）。
- 注釈が scalar / tuple でない field（`Any`・record・式）と、写せない値（scalar でない object）は変えない。
- 型は identity で見る（型の `__eq__` / `__hash__`、metaclass の hook を呼ばない）。

**注釈の分類**: `X` / `Optional[X]` / `Union[X, None]` / `X | None` / `Annotated[X, ...]`（`X` は `int` / `float` /
`str` / `bool` / `tuple` / `Tuple[...]`）を分類する。それ以外（`Any`・record・`Dict`・複数の型の `Union`）は写さない。

**順序**: `@dataclass` の **下** に置く（素の class に先に当たる）。class の `__dict__` に `__post_init__` を置く
（既存のものは包む）ので、生成された `__init__` は field の代入の後にそれを呼ぶ。正規化は class 自身の検証
（既存の `__post_init__` の本体）より前に走り、検証が読む scalar / bool の field と exact な tuple の葉は写した
値になる（list のまま受理した値・注釈が `Any` / record の値は写さないので、検証は reader で読む）。検証が field を書き直したとき
（list から tuple を作るなど）は、書き直した field だけをもう一度写す。自前の `__init__` を持つ class
（`init=False`）は、その `__init__` の後に写す。`dataclasses.replace` は `__init__` を通るので同じ規則になる。

**field の値の置き場所**: instance の `__dict__`・`__slots__`（基底の class の slot を含む）・class の既定値
（`field(init=False, default=...)`）のどれでも、属性として読む（`object.__getattribute__`）。値が無い field
（自前の `__init__` が置かなかった field）は写さない。

field の分類は class ごとに最初の構築で 1 度だけ決め（前方参照の注釈を解決できるのはその時点）、この
module の dict に置く。class の namespace には書かない（`live_values.package_type` の判定を変えない）。
"""

from __future__ import annotations

import dataclasses
import functools
import inspect
import types
import typing
from typing import Any, Callable, Dict, List, Optional, Tuple

from scripts.function_tracer_pcode.core.live_values import NOT_PLAIN, exact_scalar, int_value

#: class → 写す field の (名前, 分類) の列。最初の構築で決める。
_FIELD_KINDS: Dict[type, Tuple[Tuple[str, str], ...]] = {}

#: この decorator が置いた `__post_init__` / `__init__` → 包んだ元の関数（無ければ `None`）。
#: ref の class がこの owner を通ることを確かめる読み口（`is_runtime_ref_record`）が使う。
_WRAPPERS: Dict[Callable[..., Any], Any] = {}

#: field に値が無い印（自前の `__init__` が置かなかった field）
_ABSENT = object()

#: `runtime_ref_entry` が作った包み → 包んだ入口の関数。
_ENTRY_WRAPPERS: Dict[Callable[..., Any], Callable[..., Any]] = {}

#: 入口の関数 → 引数の写し方（`_CallPlan`）。最初の呼び出しで決める。
_ENTRY_PLANS: Dict[Callable[..., Any], "_CallPlan"] = {}


def _kind_of(annotation: Any) -> str:
    """注釈の分類（`scalar` / `bool` / `tuple` / `object`）。型は identity で比べる。"""

    origin = typing.get_origin(annotation)
    if origin is typing.Annotated:
        return _kind_of(typing.get_args(annotation)[0])
    if origin is typing.Union or origin is types.UnionType:
        rest = [arg for arg in typing.get_args(annotation) if arg is not type(None)]
        return _kind_of(rest[0]) if len(rest) == 1 else "object"
    if annotation is bool:
        return "bool"
    if annotation is int or annotation is float or annotation is str:
        return "scalar"
    if annotation is tuple or origin is tuple:
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
            hints.update(typing.get_type_hints(holder, include_extras=True))
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


def _exact(value: Any) -> bool:
    """値が写さなくてよい値か（`None` と exact な組み込みの scalar。型は identity で見る）。"""

    holder = type(value)
    return value is None or holder is int or holder is str or holder is bool or holder is float


def exact_field_value(value: Any, kind: str) -> Any:
    """分類 `kind` の field に置く値（規則は module の docstring）。変えない値は同じ object を返す。"""

    holder = type(value)
    if holder is tuple:
        return _exact_tree(value) if kind == "tuple" else value
    if _exact(value):
        return value
    if kind == "tuple":
        # tuple の注釈に tuple でない値: list や object は辿らない。scalar の subclass は値の基底型へ
        return exact_scalar(value)
    if kind == "bool":
        number = int_value(value)
        if number is not NOT_PLAIN:
            return number != 0
    return exact_scalar(value)


def _exact_tree(root: Tuple[Any, ...]) -> Tuple[Any, ...]:
    """exact な tuple の葉を写した tuple（葉がどれも変わらなければ同じ tuple）。

    明示 stack の後順走査（入れ子が深くても再帰の上限に当たらない）。memo（元の tuple の `id` → 結果）は
    この 1 回の走査の中だけで持つ: 元の tuple は `root` から到達できるので走査の間は生きていて、`id` が
    別の object に再利用されることは無い。共有された tuple は 1 度だけ辿り、結果も共有する。
    """

    done: Dict[int, Tuple[Any, ...]] = {}
    stack: List[Tuple[Tuple[Any, ...], bool]] = [(root, False)]
    while stack:
        node, leaving = stack.pop()
        if leaving:
            items: Optional[List[Any]] = None
            index = 0
            for item in node:
                if type(item) is tuple:
                    new = done[id(item)]
                elif _exact(item):
                    index += 1
                    continue
                else:
                    new = exact_scalar(item)
                if new is not item:
                    if items is None:
                        items = list(node)
                    items[index] = new
                index += 1
            done[id(node)] = node if items is None else tuple(items)
            continue
        if id(node) in done:
            continue
        # 入った印（tuple は閉路を作れないので、同じ tuple に再び出会うのは別の経路からの共有だけ。
        # 共有先は親より先に後順の処理を終える）
        done[id(node)] = node
        stack.append((node, True))
        for item in node:
            if type(item) is tuple:
                stack.append((item, False))
    return done[id(root)]


def _normalize(instance: Any, kinds: Tuple[Tuple[str, str], ...]) -> List[Any]:
    """`kinds` の field を写し、写した後の値の列を返す（検証の後に、書き直された field を見分けるため）。

    field は属性として読む（`__dict__`・slot・class の既定値のどこに在っても同じ）。値が無い field は
    `_ABSENT`。構築ごとに通る hot path なので、`_exact` と同じ判定をここでは展開して書く。
    """

    values: List[Any] = []
    append = values.append
    read = object.__getattribute__
    for name, kind in kinds:
        try:
            value = read(instance, name)
        except AttributeError:
            append(_ABSENT)
            continue
        holder = type(value)
        if not (value is None or holder is int or holder is str or holder is bool or holder is float):
            new = exact_field_value(value, kind)
            if new is not value:
                object.__setattr__(instance, name, new)
                value = new
        append(value)
    return values


def _renormalize_rewritten(instance: Any, kinds: Tuple[Tuple[str, str], ...], before: List[Any]) -> None:
    """class 自身の `__post_init__`（検証）が書き直した field だけを、もう一度写す。"""

    read = object.__getattribute__
    rewritten = []
    for entry, old in zip(kinds, before):
        try:
            current = read(instance, entry[0])
        except AttributeError:
            current = _ABSENT
        if current is not old:
            rewritten.append(entry)
    if rewritten:
        _normalize(instance, tuple(rewritten))


def normalize_fields(instance: Any) -> None:
    """`instance` の scalar / tuple の field を規則で写す（frozen でも書く）。"""

    _normalize(instance, field_kinds(type(instance)))


@dataclasses.dataclass(frozen=True)
class _CallPlan:
    """入口の関数の引数の写し方（`inspect.signature` の束縛規則を、注釈の分類の表にしたもの）。

    呼び出しの `args` / `kwargs` は、関数がそのまま受けるもの（method なら `self` / `cls` を含む）。
    注釈の無い引数（`self` / `cls` を含む）と `Any` の引数は `object`（写さない）。
    """

    #: 位置で渡せる引数（位置専用・位置またはキーワード）の分類。i 番目の位置の値に当てる
    positional: Tuple[str, ...]
    #: `*args` の各要素の分類（`*args` が無ければ `None`: 余った位置の値は関数が拒む）
    var_positional: Optional[str]
    #: キーワードで渡せる引数（位置またはキーワード・キーワード専用）の名前 → 分類
    by_name: Dict[str, str]
    #: `**kwargs` の各値の分類（`**kwargs` が無ければ `None`: 知らない名前は関数が拒む）
    var_keyword: Optional[str]


def _entry_plan(function: Callable[..., Any]) -> _CallPlan:
    """入口の関数の引数の分類（注釈を最初の呼び出しで 1 度だけ解決する）。

    引数の種類（位置専用・位置またはキーワード・`*args`・キーワード専用・`**kwargs`）をすべて表に載せる。
    注釈を解決できない入口は、保証を黙って欠かさずに例外にする。
    """

    plan = _ENTRY_PLANS.get(function)
    if plan is None:
        hints = typing.get_type_hints(function, include_extras=True)
        positional: List[str] = []
        by_name: Dict[str, str] = {}
        var_positional: Optional[str] = None
        var_keyword: Optional[str] = None
        for parameter in inspect.signature(function).parameters.values():
            kind = _kind_of(hints[parameter.name]) if parameter.name in hints else "object"
            if parameter.kind is parameter.VAR_POSITIONAL:
                var_positional = kind
            elif parameter.kind is parameter.VAR_KEYWORD:
                var_keyword = kind
            else:
                if parameter.kind is not parameter.KEYWORD_ONLY:
                    positional.append(kind)
                if parameter.kind is not parameter.POSITIONAL_ONLY:
                    by_name[parameter.name] = kind
        plan = _CallPlan(tuple(positional), var_positional, by_name, var_keyword)
        _ENTRY_PLANS[function] = plan
    return plan


def _entry_value(value: Any, kind: Optional[str]) -> Any:
    holder = type(value)
    if kind is None or kind == "object" or value is None or holder is int or holder is str or holder is bool or holder is float:
        return value
    return exact_field_value(value, kind)


def entry_arguments(
    function: Callable[..., Any], args: Tuple[Any, ...], kwargs: Dict[str, Any],
) -> Tuple[Tuple[Any, ...], Dict[str, Any]]:
    """入口 `function` へ渡す引数を、注釈の分類で写した引数（field と同じ規則。`Any` の引数は変えない）。

    `args` / `kwargs` は `function` がそのまま受けるもの（method なら先頭は `self` / `cls`）。位置の値は
    signature の位置の順に、余りは `*args` の注釈で、キーワードの値は名前で、知らない名前は `**kwargs` の
    注釈で写す。関数が拒む呼び出し（引数の数・名前の誤り）は写した後も同じく関数が拒む。
    """

    plan = _ENTRY_PLANS.get(function)
    if plan is None:
        plan = _entry_plan(function)
    positional = plan.positional
    count = len(positional)
    rewritten: Optional[List[Any]] = None
    for index, value in enumerate(args):
        new = _entry_value(value, positional[index] if index < count else plan.var_positional)
        if new is not value:
            if rewritten is None:
                rewritten = list(args)
            rewritten[index] = new
    if rewritten is not None:
        args = tuple(rewritten)
    by_name = plan.by_name
    copied = False
    for name, value in kwargs.items():
        new = _entry_value(value, by_name[name] if name in by_name else plan.var_keyword)
        if new is not value:
            if not copied:
                kwargs = dict(kwargs)  # 呼び出し元の dict は書き換えない
                copied = True
            kwargs[name] = new
    return args, kwargs


def _entry_wrapper(function: Callable[..., Any], finish: Optional[Callable[[Any], None]] = None) -> Callable[..., Any]:
    """`function` の引数を本体の前に写す包み（`finish` は本体の後に先頭の引数（`self`）へ当てる）。

    包みは元の関数の名前・module・doc・注釈・`__wrapped__` を持つ（`inspect.signature` は元の signature を返す）。
    """

    if type(function) is not types.FunctionType:
        raise TypeError(
            f"runtime ref entries must wrap a plain function (place @runtime_ref_entry below "
            f"@classmethod / @staticmethod): {function!r}"
        )

    def entry(*args: Any, **kwargs: Any) -> Any:
        args, kwargs = entry_arguments(function, args, kwargs)
        result = function(*args, **kwargs)
        if finish is not None:
            finish(args[0])
        return result

    functools.update_wrapper(entry, function)
    _ENTRY_WRAPPERS[entry] = function
    return entry


def runtime_ref_entry(function: Callable[..., Any]) -> Callable[..., Any]:
    """ref を作る入口（factory・ref から ref を作る method・ref を作る公開の関数）の引数を、本体が値を
    消費する **前に** 注釈の型規則で写す（`classmethod` / `staticmethod` の **下** に置く）。

    本体が引数を `or` / 比較 / format / 文字列の method で読む前に subclass を基底型の値にするので、
    本体は subclass の code を呼ばない。注釈が `bool` の引数は bool の規則（JBoolean は `bool`）、`Any`・
    record・式の引数と注釈の無い引数は変えない（本体が値として読むなら `live_values` の reader で読む）。
    引数の対応は signature の束縛と同じ（位置・キーワード・`*args`・`**kwargs`）。
    """

    return _entry_wrapper(function)


def is_runtime_ref_entry(function: Any) -> bool:
    """`function`（`classmethod` / `staticmethod` なら中身）が `runtime_ref_entry` の包みか。"""

    inner = getattr(function, "__func__", function)
    return type(inner) is types.FunctionType and inner in _ENTRY_WRAPPERS


def runtime_ref_record(cls: type) -> type:
    """runtime ref の class に scalar の正規化を付ける（`@dataclass(...)` の **下** に置く）。"""

    if "__dataclass_fields__" in cls.__dict__:
        raise TypeError(f"@runtime_ref_record must be applied below @dataclass ({cls.__qualname__})")
    custom_init = cls.__dict__.get("__init__")
    if custom_init is not None:
        # `init=False` で自前の `__init__` を持つ class（`CanonicalLocation`）: 引数は入口として本体の前に写し、
        # 本体が置いた field をその後で写す
        # 自前の `__init__` は入口と同じ包み（引数の束縛は `self` を含む signature のまま）の後に field を写す
        __init__ = _entry_wrapper(custom_init, normalize_fields)
        _WRAPPERS[__init__] = custom_init
        cls.__init__ = __init__  # type: ignore[misc]
        return cls
    # 自分の `__post_init__` が無ければ継承したものを呼ぶ（継承したものが包みなら、その中でもう 1 度
    # 写すだけで、検証は 1 度）
    original = cls.__dict__.get("__post_init__") or getattr(cls, "__post_init__", None)

    if original is None:
        def __post_init__(self: Any, *init_vars: Any) -> None:
            normalize_fields(self)
    else:
        def __post_init__(self: Any, *init_vars: Any) -> None:
            kinds = field_kinds(type(self))
            before = _normalize(self, kinds)
            original(self, *init_vars)
            _renormalize_rewritten(self, kinds, before)

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
    "entry_arguments",
    "exact_field_value",
    "field_kinds",
    "is_runtime_ref_entry",
    "is_runtime_ref_record",
    "runtime_ref_entry",
    "normalize_fields",
    "runtime_ref_record",
]
