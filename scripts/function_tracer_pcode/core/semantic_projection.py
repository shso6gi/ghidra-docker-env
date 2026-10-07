# -*- coding: utf-8 -*-
"""生 runtime object → immutable な意味値（Issue #22 PR-22-B）。

**生 object を読んでよい 2 つの module のうちの 1 つ**。この module が汎用の
読み方（`semantic_key()` / storage / 宣言型 / global address）を決め、loop summary
ref の schema だけは `core/loop_lowering_semantics.py` が持つ（厳密 lowering の
可否という別の判断と一緒に置いてあり、この module はその結果を受け取る）。
どちらから外へ出るのも pure な value だけで、生 object への参照も、あとから生
object を読み直す遅延セルも渡さない。

なぜ 1 owner にするか: `runtime_ref.semantic_key()` を「identity として何に使うか」
という判断が、structural key・solver query・unknown 宣言・loop lowering の 4 箇所に
散っていた。同じ問いに 4 つの答えがあると、どれか 1 つを直したときに他が置いて
いかれる（実際 `except` の範囲も 3 通りに分かれていた）。新しい runtime ref 種別を
足すときに触るのもここだけになる。

読み取りの境界（凍結後に何を読んでよいか）:

* `SemanticSnapshot` の pure value — 常に可
* 生 object（`runtime_ref`、Ghidra の `data_type_obj`、`StorageInfo`）— **不可**。
  consumer が読むのは、この module が凍結時に作った値だけ

ref の構造を辿る必要がある判断は、この module が凍結時に済ませて値にする。
loop lowering はそれが一番大きいので、判断そのものは
`core/loop_lowering_semantics.py` が持ち、ここはそれを 1 回呼んで
`RuntimeRefProjection.loop_lowering` に入れる（`isinstance` による ref 種別の
振り分けも、厳密 lowering の可否も、向こうに 1 つだけある）。

失敗の扱い: identity が取れないことは「無い」であって例外ではない（従来の
包括捕捉と同じ結果）。ただし捕まえる型は列挙する — 包括捕捉を増やさないため。
"""

from __future__ import annotations

from dataclasses import dataclass
import gc
import struct
from types import MappingProxyType
from enum import Enum
from typing import Any, NamedTuple, Optional, Tuple

from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.loop_lowering_semantics import (
    ABSENT_LOWERING,
    LoopLoweringSemantics,
    project_loop_lowering,
)
from scripts.function_tracer_pcode.core.runtime_refs import (
    AddressValueRef,
    CanonicalLocation,
    PostStateReadRef,
    PostStateValueRef,
    loop_summary_method_b_key,
)


CanonicalAtoms = Tuple[Any, ...]

#: identity の評価で「値が得られなかった」と扱う失敗の範囲。
#: 旧実装の `except Exception` と同じ結果になるよう選んである（`RecursionError` は
#: 深い式で実際に起きるので外せない）。
IDENTITY_EVALUATION_ERRORS = (
    AttributeError,
    LookupError,
    TypeError,
    ValueError,
    ArithmeticError,
    RecursionError,
    NotImplementedError,
)


# ---------------------------------------------------------------------------
# canonical value
# ---------------------------------------------------------------------------


_SEQUENCE_TAGS = frozenset({"tuple", "list"})
_SET_TAGS = frozenset({"set", "frozenset"})


def read_container(value: Any) -> Optional[Tuple[str, Tuple[Any, ...]]]:
    """容器の中身を **基底型の実装で、型と対応を保って** 読む（値の読み方の唯一の入口、Issue #215）。

    返すのは ``(tag, 要素)``: tag は ``"tuple"`` / ``"list"`` / ``"set"`` / ``"frozenset"`` /
    ``"dict"``（dict の要素は ``(key, value)`` の組）。容器でなければ None。subclass の
    `__iter__` / `__getitem__` / `__len__` / `items` を呼ばない（基底型の storage を読む）。
    `MappingProxyType` は包んだ dict を基底型の実装で読む（dict でない mapping を包む proxy は読めない）。要素の順は storage の順で、並べ替えと同一視は呼び出し側が atom で行う。
    """

    kind = type(value)
    if issubclass(kind, tuple):
        return ("tuple", tuple(tuple.__iter__(value)))
    if issubclass(kind, list):
        return ("list", tuple(list.__iter__(value)))
    if issubclass(kind, frozenset):
        return ("frozenset", tuple(frozenset.__iter__(value)))
    if issubclass(kind, set):
        return ("set", tuple(set.__iter__(value)))
    if issubclass(kind, dict):
        return ("dict", tuple(dict.items(value)))
    if kind is MappingProxyType:
        # 包んだ mapping を取り出し、組み込みの dict のときだけ基底型の実装で読む（それ以外の mapping
        # の `items` は呼ばない: 読めない容器）
        wrapped = [item for item in gc.get_referents(value) if issubclass(type(item), dict)]
        if len(wrapped) != 1:
            return None
        return ("dict", tuple(dict.items(wrapped[0])))
    return None


def _ordered_by_atom(pairs: list) -> Optional[list]:
    """(atom, 付随する値) の組を atom の順に並べる。atom が重複するか順序が付かなければ None。

    別の要素が同じ atom になった（hash を上書きした subclass と基底型の値など）なら、atom では
    どの要素かを区別できない。呼び出し側はその容器を識別できない値として扱う。
    """

    atoms = [atom for atom, _item in pairs]
    try:
        if len(set(atoms)) != len(atoms):
            return None
        return sorted(pairs, key=lambda pair: pair[0])
    except TypeError:
        return None


def canonical_atom(value: Any) -> CanonicalAtoms:
    """任意の値を structural key 用の atom へ落とす（**値の区別を落とさない**、Issue #215）。

    scalar は基底型の slot の exact な値、容器は `read_container` で型の tag と対応を保つ
    （list と tuple、set と tuple、dict と組の列を同一視しない）。object を値で表すのは状態の
    全部を読めるときだけで、それ以外は `object_id`（構造 key では識別不能）。atom の中身は
    exact な組み込みの値だけ。
    """

    return _canonical_atom(value, set())


def _canonical_atom(value: Any, active: set) -> CanonicalAtoms:
    """`canonical_atom` の本体。`active` は辿っている容器・object の id（閉路は識別できない値）。"""

    def _atom(item: Any) -> CanonicalAtoms:
        return _canonical_atom(item, active)


    if value is None:
        return ("none", "")
    if value is True or value is False:
        return ("bool", int(value))
    # scalar の値は `live_values` の規則（基底型の slot）で読む: subclass（JPype の `JInt`・
    # mixin の enum）は基底型の値になり、atom の中身は常に exact な組み込みの値（Issue #215
    # C-K1 / C-K7）。subclass の `__eq__` / `__hash__` を atom に持ち込むと、別の値の atom が
    # 等しくなり得る（構造 key の owner は exact でない中身を識別不能として扱う）
    scalar = live_values.json_scalar(value)
    if scalar is not live_values.NOT_PLAIN:
        if scalar is True or scalar is False:
            return ("bool", int(scalar))
        if type(scalar) is int:
            return ("int", scalar)
        if type(scalar) is float:
            # 値の bit 列（-0.0 と 0.0、NaN の payload も区別する）。float は immutable なので
            # 値が identity。`object_id` に落とすと死後の `id()` 再利用で別の値と一致する（Issue #215）
            return ("float", struct.pack(">d", scalar).hex())
        return ("str", scalar)
    kind = type(value)
    if issubclass(kind, bytes):
        return ("bytes", bytes.hex(value))
    if kind is UnsupportedSemanticValue:
        # 値として固定できなかったものの印（型名しか残っていない）。tuple として畳むと、
        # 同じ型の別の object どうしが同じ atom になり識別できたように見える。印の tag を
        # 残し、構造 key の owner（`core/structural`）が識別不能として扱う（Issue #215）
        return (UNSUPPORTED_VALUE_TAG, value.type_module, value.type_qualname)
    value_id = id(value)
    if value_id in active:
        # 閉路（自分を含む容器・自分を返す stable_key）: 有限の atom で値を表せない
        return ("object_id", type(value).__module__, type(value).__qualname__, value_id)
    active.add(value_id)
    try:
        return _composite_atom(value, kind, _atom)
    finally:
        active.discard(value_id)


def _composite_atom(value: Any, kind: type, _atom) -> CanonicalAtoms:
    """容器と object の atom（`_canonical_atom` が閉路を見張りながら呼ぶ）。"""

    # 容器は `read_container`（基底型の実装で、型と対応を保って読む）で辿る
    container = read_container(value)
    if container is not None:
        tag, elements = container
        if tag in _SEQUENCE_TAGS:
            return (tag, tuple(_atom(item) for item in elements))
        if tag in _SET_TAGS:
            ordered = _ordered_by_atom([(_atom(item), None) for item in elements])
            if ordered is None:
                return ("object_id", type(value).__module__, type(value).__qualname__, id(value))
            return (tag, tuple(atom for atom, _item in ordered))
        ordered = _ordered_by_atom([(_atom(key), _atom(item)) for key, item in elements])
        if ordered is None:
            # 別の key（hash を上書きした subclass と基底型の値など）が同じ atom になった: どの値が
            # どの key のものかを atom では区別できない
            return ("object_id", type(value).__module__, type(value).__qualname__, id(value))
        return ("dict", tuple(ordered))
    # 値が自分の identity を明示する method（型の属性だけを見る。instance の `__getattr__` を呼ばない）
    stable_key = declared_method(kind, value, "stable_key")
    if stable_key is not None:
        try:
            return ("stable", _atom(stable_key()))
        except IDENTITY_EVALUATION_ERRORS:
            pass
    to_dict = declared_method(kind, value, "to_dict")
    if to_dict is not None:
        try:
            return ("object_dict", _atom(to_dict()))
        except IDENTITY_EVALUATION_ERRORS:
            pass
    # ここから先は、状態の全部を読めると確かめられる値だけを値で表す（Issue #215 C-K1）。読めない
    # 状態（slot・組み込みの基底型の中身・field でない属性）を落として残りで表すと、それだけが違う
    # 2 つの値が同じ atom になる。確かめられなければ `object_id`（構造 key では識別不能）
    qualname = type(value).__qualname__
    if type(qualname) is str and "<locals>" not in qualname:
        # 型の名前で型を識別できる（関数の中で作った class は同じ名前の別の型があり得る）
        names = live_values.dataclass_field_names(value)
        if names is not None and _frozen_dataclass(kind, value, names):
            try:
                return (
                    "dataclass",
                    type(value).__module__,
                    qualname,
                    tuple((name, _atom(live_values.field_value(value, name))) for name in names),
                )
            except TypeError:
                pass
        if issubclass(kind, Enum):
            # 値を持たない enum の member は singleton で、名前が member を識別する（mixin の enum は
            # 上の scalar の規則で基底型の値になる）
            name = live_values.str_value(live_values.enum_name(value))
            if type(name) is str:
                return ("enum", type(value).__module__, qualname, name)
    return ("object_id", type(value).__module__, type(value).__qualname__, id(value))


def declared_method(kind: type, value: Any, name: str) -> Any:
    """型が宣言した method を `value` に束縛したもの（無ければ None）。"""

    declared = live_values.type_attribute(kind, name)
    if declared is None:
        return None
    binder = live_values.type_attribute(type(declared), "__get__")
    bound = declared.__get__(value, kind) if binder is not None else declared
    return bound if callable(bound) else None


def _frozen_dataclass(kind: type, value: Any, names: Tuple[str, ...]) -> bool:
    """`value` の状態が dataclass の field で尽きるか（凍結した dataclass で、field でない状態が無い）。

    - 型自身が凍結した dataclass として宣言されている（継承しただけの subclass は属性を足せる）
    - instance の `__dict__` の key が field 名だけ（`object.__setattr__` で足した属性が無い）
    - MRO のどの `__slots__` も field か `__dict__` / `__weakref__` だけ（slot に隠れた状態が無い）
    """

    own = _TYPE_DICT.__get__(kind)
    params = own.get("__dataclass_params__")
    if params is None or live_values.instance_state(params, "frozen", False) is not True:
        return False
    allowed = set(names)
    holder = live_values.type_attribute(kind, "__dict__")
    if holder is not None and live_values.type_attribute(type(holder), "__get__") is not None:
        try:
            state = holder.__get__(value, kind)
        except (AttributeError, TypeError):
            return False
        if type(state) is not dict:
            return False
        if not all(type(key) is str and key in allowed for key in dict.__iter__(state)):
            return False
    for klass in _TYPE_MRO.__get__(kind):
        slots = _TYPE_DICT.__get__(klass).get("__slots__", ())
        slots = (slots,) if type(slots) is str else slots
        for slot in (tuple.__iter__(slots) if type(slots) is tuple else list.__iter__(slots) if type(slots) is list else ()):
            if not (type(slot) is str and (slot in allowed or slot in ("__dict__", "__weakref__"))):
                return False
    return True


#: 型の属性の辞書と MRO を読む組み込みの descriptor（metaclass の hook を呼ばない）
_TYPE_DICT = type.__dict__["__dict__"]
_TYPE_MRO = type.__dict__["__mro__"]


def canonical_value_key(value: Any) -> CanonicalAtoms:
    """`value` の意味内容による表現。**container 種別を落とさない**。

    freeze は list を tuple へ畳むが、畳んだ事実で `["a"]` と `("a",)` を同一視
    しては意味が変わる。`canonical_atom` と同じ tag 体系（`list` / `tuple` /
    `dict`）を使うので、旧実装で異なった値は新実装でも異なる。

    Python object そのものは `("opaque_value", module, qualname)` にする。
    **process 依存の `id()` は入れない**ので digest が run 間で決定的になる。
    「同じ object かどうか」の区別が要る比較側は `canonical_atom` を使う。
    """

    if value is None:
        return ("none", "")
    if value is True or value is False:
        return ("bool", int(value))
    # 読み方は `canonical_atom` と同じ（Issue #215: scalar は基底型の slot、容器は `read_container`。
    # subclass の `__iter__` / `__repr__` / `__eq__` を呼ばない）
    scalar = live_values.json_scalar(value)
    if scalar is not live_values.NOT_PLAIN:
        if scalar is True or scalar is False:
            return ("bool", int(scalar))
        if type(scalar) is int:
            return ("int", scalar)
        if type(scalar) is float:
            return ("float", float.__repr__(scalar))
        return ("str", scalar)
    kind = type(value)
    if issubclass(kind, bytes):
        return ("bytes", bytes.hex(value))
    container = read_container(value)
    if container is not None:
        tag, elements = container
        if tag in _SEQUENCE_TAGS:
            return (tag, tuple(canonical_value_key(item) for item in elements))
        if tag in _SET_TAGS:
            ordered = _ordered_by_atom([(canonical_value_key(item), None) for item in elements])
            if ordered is None:
                return ("opaque_value", kind.__module__, kind.__qualname__)
            return (tag, tuple(key for key, _item in ordered))
        ordered = _ordered_by_atom([(canonical_value_key(key), canonical_value_key(item)) for key, item in elements])
        if ordered is None:
            # 別の key が同じ表現になった: どの値がどの key のものかを区別できない（値として支えない）
            return ("opaque_value", kind.__module__, kind.__qualname__)
        return ("dict", tuple(ordered))
    raw = _stable_key_or_none(value)
    if raw is not None:
        return ("stable", canonical_value_key(raw))
    return ("opaque_value", type(value).__module__, type(value).__qualname__)


def value_key_is_opaque(key: CanonicalAtoms) -> bool:
    """`canonical_value_key` が object 表現へ落ちたか。"""

    return bool(key) and key[0] == "opaque_value"


#: snapshot がそのまま値として抱えてよい型。ここに無い型は「値」ではないので
#: canonical な表現へ落とすか、落とせないなら unsupported として印を付ける。
IMMUTABLE_SCALARS = (type(None), bool, int, float, str, bytes)


#: `canonical_atom` が `UnsupportedSemanticValue` を表す atom の tag
UNSUPPORTED_VALUE_TAG = "unsupported_value"


class UnsupportedSemanticValue(NamedTuple):
    """値として固定できなかったものの印。

    `stable_key()` が可変な object を返したとき、それを snapshot が抱えると
    「凍結後も中身が変わり得る値」を意味として持つことになる。かといって捨てると
    別の値と同一視してしまうので、**型名だけを残して「支えられない」と明示**し、
    identity の完全性（`identity_complete`）を落とす。
    """

    type_module: str
    type_qualname: str


def immutable_value(value: Any) -> Any:
    """`stable_key()` / `semantic_key()` の戻り値を不変な値へ畳む（snapshot・描画の identity 用）。

    container は tuple へ、Enum は値へ、`stable_key()` を持つ object はその key へ
    再帰的に落とす。どれでもない object は `UnsupportedSemanticValue` にする
    （生 object を snapshot に残さない）。

    読み方は `read_container` / `live_values` と同じ（基底型の実装。subclass の `__iter__` /
    `__repr__` を呼ばない）。set と dict は `canonical_atom` の順に並べ、別の要素が同じ atom に
    なる容器は `UnsupportedSemanticValue`（どの要素かを区別できない）。**この形は容器の型を
    畳むので、構造 key には使わない**（構造 key は生の値を `canonical_atom` で読む:
    `semantic_runtime_ref_key`）。
    """

    return _immutable_value(value, set())


def _immutable_value(value: Any, active: set) -> Any:
    """`immutable_value` の本体。`active` は辿っている容器・object の id（閉路は支えられない値）。"""

    def _value(item: Any) -> Any:
        return _immutable_value(item, active)

    if value is None or value is True or value is False:
        return value
    scalar = live_values.json_scalar(value)
    if scalar is not live_values.NOT_PLAIN and not issubclass(type(value), Enum):
        return scalar
    kind = type(value)
    if issubclass(kind, bytes):
        return bytes(bytes.__iter__(value)) if kind is not bytes else value
    value_id = id(value)
    if value_id in active:
        # 閉路は有限の値で表せない
        return UnsupportedSemanticValue(kind.__module__, kind.__qualname__)
    container = read_container(value)
    if container is not None:
        tag, elements = container
        active.add(value_id)
        try:
            return _container_value(kind, tag, elements, _value)
        finally:
            active.discard(value_id)
    if issubclass(kind, Enum):
        return _value(live_values.enum_value(value))
    active.add(value_id)
    try:
        raw = _declared_key_raw(value, "stable_key")
        nested = None if raw is None else _value(raw)
    finally:
        active.discard(value_id)
    if nested is not None:
        return nested
    return UnsupportedSemanticValue(
        type(value).__module__, type(value).__qualname__
    )


def _container_value(kind: type, tag: str, elements: tuple, _value) -> Any:
    """`read_container` で読んだ容器の不変な値（set / dict は atom の順。衝突は支えられない値）。"""

    if tag in _SEQUENCE_TAGS:
        return tuple(_value(item) for item in elements)
    if tag in _SET_TAGS:
        ordered = _ordered_by_atom([(canonical_atom(item), _value(item)) for item in elements])
    else:
        ordered = _ordered_by_atom([
            (canonical_atom(key), (_value(key), _value(item))) for key, item in elements
        ])
    if ordered is None:
        return UnsupportedSemanticValue(kind.__module__, kind.__qualname__)
    return tuple(item for _atom, item in ordered)


def contains_unsupported_value(value: Any) -> bool:
    """`immutable_value` が値として固定できなかったものを含むか。"""

    if isinstance(value, UnsupportedSemanticValue):
        return True
    if isinstance(value, tuple):
        return any(contains_unsupported_value(item) for item in value)
    return False


def _declared_key_raw(value: Any, name: str) -> Any:
    """型が宣言した `stable_key()` / `semantic_key()` の生の戻り値（無ければ・失敗すれば None）。"""

    method = declared_method(type(value), value, name)
    if method is None:
        return None
    try:
        return method()
    except IDENTITY_EVALUATION_ERRORS:
        return None


def _stable_key_or_none(value: Any) -> Any:
    key = _declared_key_raw(value, "stable_key")
    return None if key is None else immutable_value(key)


def _semantic_key_or_none(value: Any) -> Any:
    key = _declared_key_raw(value, "semantic_key")
    return None if key is None else immutable_value(key)


def semantic_runtime_ref_key(value: Any) -> Optional[CanonicalAtoms]:
    """structural key に載せてよい runtime ref の意味 key（無ければ `None`）。

    任意の object 属性は見ない。debug 用・付随的な runtime object が構造の
    等価性を動かしてよいのは、明示的な安定 key を出しているときだけ。

    **生の値を `canonical_atom` と同じ読み方で atom にする**（Issue #215）。`stable_key()` の
    戻り値も `immutable_value` で畳まずに読む: 畳むと容器の型・要素の対応が落ち、後段の分類では
    取り戻せない。安定 key を出さない object を含む容器は、従来どおり意味 key を持たない
    （None）。別の要素が同じ atom になる容器は識別できない値（`unsupported_value`）にする。
    """

    if value is None:
        return None
    scalar = live_values.json_scalar(value)
    if (scalar is not live_values.NOT_PLAIN and type(scalar) is not float) or issubclass(type(value), bytes):
        # bool / int / str / bytes（とその subclass）は `canonical_atom` と同じ規則（基底型の slot の
        # exact な値）。float は従来どおり安定 key を出さない値として扱う（意味 key に入れない）
        return canonical_atom(value)
    container = read_container(value)
    if container is not None:
        tag, elements = container
        if tag in _SEQUENCE_TAGS:
            items = []
            for item in elements:
                item_key = semantic_runtime_ref_key(item)
                if item_key is None:
                    return None
                items.append(item_key)
            return (tag, tuple(items))
        if tag == "dict":
            pairs = []
            for key, item in elements:
                key_key = semantic_runtime_ref_key(key)
                item_key = semantic_runtime_ref_key(item)
                if key_key is None or item_key is None:
                    return None
                pairs.append((key_key, item_key))
            ordered = _ordered_by_atom(pairs)
            if ordered is None:
                return (UNSUPPORTED_VALUE_TAG, type(value).__module__, type(value).__qualname__)
            return ("dict", tuple(ordered))
        # set は従来どおり安定 key を出さない値
        return None
    stable = _declared_key_raw(value, "stable_key")
    if stable is None:
        return None
    return ("stable_runtime_ref", canonical_atom(stable))


# ---------------------------------------------------------------------------
# projections
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class RuntimeRefProjection:
    """1 つの runtime ref から読み取った意味値（凍結時に 1 回だけ作る）。

    生 ref への参照は持たない。consumer がここに無い identity を必要としたら、
    field を 1 つ足すのが正しい（consumer 側で生 ref を読み直さない）。
    """

    #: structural key に載せる意味 key
    structural_key: Optional[CanonicalAtoms]
    #: `stable_key()`（不変化済み）
    stable_key: Any
    #: `semantic_key()`（不変化済み）
    semantic_key: Any
    #: `(origin_kind, origin_stable_key)`（unknown 宣言 identity 用）
    stable_origin: Optional[Tuple[Any, ...]]
    #: parameter を指す ref か（solver query identity 用）
    is_parameter_ref: bool
    #: `("parameter", …)` 形の stable key（provenance 用）
    parameter_stable_key: Optional[CanonicalAtoms]
    #: 定数アドレスを指す ref か（VARIABLE のアドレス描画に使う）
    is_address_value_ref: bool
    #: そのアドレスのオフセット
    address_offset: Optional[int]
    #: 名前付き global object のアドレス identity `(symbol, size, offset)`
    address_object_identity: Optional[Tuple[Any, ...]]
    #: loop lowering の SMT function identity
    lowering_identity: Optional[Tuple[Any, ...]]
    #: loop lowering に必要な意味（renderer が見るのはこれだけ）
    loop_lowering: LoopLoweringSemantics
    #: VARIABLE がそのまま unknown symbol として宣言される種別か
    declares_variable_symbol: bool
    #: ref の identity（stable / semantic / origin / address の key）に値として固定できない部分が
    #: あった（Issue #215）。そのときは stable / semantic / origin の field を全部 None にし（address は
    #: その key だけ外す）、identity の完全性と、
    #: ref を持たない式との区別はこの印で判断する
    identity_unfixable: bool = False


_ABSENT_RUNTIME = RuntimeRefProjection(
    structural_key=None,
    stable_key=None,
    semantic_key=None,
    stable_origin=None,
    is_parameter_ref=False,
    parameter_stable_key=None,
    is_address_value_ref=False,
    address_offset=None,
    address_object_identity=None,
    lowering_identity=None,
    loop_lowering=ABSENT_LOWERING,
    declares_variable_symbol=False,
)


@dataclass(frozen=True)
class StorageProjection:
    """storage からの意味値。`StorageInfo` は可変なのでここで値にして固定する。"""

    identity: Optional[CanonicalAtoms]
    #: identity key を出す storage があったか（「無い」と「出せない」は別の意味）
    supported: bool


_ABSENT_STORAGE = StorageProjection(identity=None, supported=False)


@dataclass(frozen=True)
class DeclaredTypeProjection:
    """宣言型からの意味値。生の `data_type_obj` は持たない。"""

    #: 宣言型が signed か（宣言型が無ければ `None`）
    signedness: Optional[bool]
    #: 宣言型が存在したか
    declared: bool


_ABSENT_DECLARED_TYPE = DeclaredTypeProjection(signedness=None, declared=False)


def absent_runtime_projection() -> RuntimeRefProjection:
    return _ABSENT_RUNTIME


def absent_storage_projection() -> StorageProjection:
    return _ABSENT_STORAGE


def absent_declared_type_projection() -> DeclaredTypeProjection:
    return _ABSENT_DECLARED_TYPE


class ExpressionProjection(NamedTuple):
    """1 つの式が持つ生 object をすべて読み終えた結果。

    **式のどの属性が生 object なのかを知っているのはこの module だけ**。
    表現（`SemanticSnapshot`）は「どんな意味値があるか」だけを知り、「それが
    どこから来たか」は知らない。生 object 由来の意味 field を足すときに触るのも
    ここ 1 箇所になる。
    """

    runtime: RuntimeRefProjection
    storage: StorageProjection
    declared_type: DeclaredTypeProjection
    has_runtime_ref: bool
    has_data_type_obj: bool


def project_expression(expr: Any, *, declared_type_kinds: Any = None) -> ExpressionProjection:
    """式が抱えている生 object を 1 回だけ読んで意味値にする。

    `declared_type_kinds` は宣言型を読む node 種別名の集合（幅合わせがその
    種別でしか宣言型を見ないので、他の種別で型 object を叩かない）。
    """

    runtime_ref = getattr(expr, "runtime_ref", None)
    data_type_obj = getattr(expr, "data_type_obj", None)
    kind = getattr(getattr(expr, "expr_type", None), "name", None)

    declared_type = _ABSENT_DECLARED_TYPE
    if data_type_obj is not None and (
        declared_type_kinds is None or kind in declared_type_kinds
    ):
        declared_type = project_declared_type(
            data_type_obj, getattr(expr, "data_type", None)
        )

    return ExpressionProjection(
        runtime=project_runtime_ref(expr, runtime_ref),
        storage=project_storage(getattr(expr, "storage_info", None)),
        declared_type=declared_type,
        has_runtime_ref=runtime_ref is not None,
        has_data_type_obj=data_type_obj is not None,
    )


def project_runtime_ref(expr: Any, runtime_ref: Any) -> RuntimeRefProjection:
    """生 ref を 1 回だけ読んで意味値にする。"""

    if runtime_ref is None:
        return _ABSENT_RUNTIME
    # identity の field は値として固定できる key だけを持つ（Issue #215 `identity_value`）。型名だけの
    # 印を含む key を持たせると、それを読む全 consumer（SMT の unknown 記号・条件 oracle の記号・
    # provenance key・loop lowering の関数名）で別の ref が同じ identity になる。外したことは
    # `identity_unfixable` に残す
    stable_raw = _stable_key_or_none(runtime_ref)
    semantic_raw = _semantic_key_or_none(runtime_ref)
    address_raw = _address_object_identity(runtime_ref)
    stable = identity_value(stable_raw)
    semantic = identity_value(semantic_raw)
    address_identity = identity_value(address_raw)
    origin = _stable_origin(runtime_ref)
    unfixable = (
        (stable_raw is not None and stable is None)
        or (semantic_raw is not None and semantic is None)
        or (address_raw is not None and address_identity is None)
        or _origin_unfixable(runtime_ref)
    )
    if unfixable:
        # 一部でも固定できないなら、残りの key（stable・semantic・origin）にも頼らない: consumer は
        # semantic → stable → origin の順に退避するので、固定できない成分を落とした粗い key で別の
        # ref と併合し得る
        stable = semantic = origin = None
    lowering_identity = _lowering_identity(expr, runtime_ref, stable, semantic)
    return RuntimeRefProjection(
        structural_key=semantic_runtime_ref_key(runtime_ref),
        stable_key=stable,
        semantic_key=semantic,
        stable_origin=origin,
        is_parameter_ref=_is_parameter_ref(runtime_ref, stable),
        parameter_stable_key=_parameter_stable_key(stable),
        is_address_value_ref=isinstance(runtime_ref, AddressValueRef),
        address_offset=_address_offset(runtime_ref),
        address_object_identity=address_identity,
        lowering_identity=lowering_identity,
        loop_lowering=project_loop_lowering(
            expr, runtime_ref, identity=lowering_identity
        ),
        declares_variable_symbol=isinstance(
            runtime_ref, (CanonicalLocation, PostStateReadRef, PostStateValueRef)
        ),
        identity_unfixable=unfixable,
    )


def _origin_unfixable(runtime_ref: Any) -> bool:
    """origin の stable key が値として固定できなかったか（`_stable_origin` が外した）。"""

    origin_ref = getattr(runtime_ref, "origin_ref", None)
    if getattr(runtime_ref, "origin_kind", None) is None or origin_ref is None:
        return False
    raw = _stable_key_or_none(origin_ref)
    return raw is not None and identity_value(raw) is None


def identity_value(value: Any) -> Any:
    """identity に使ってよい不変な値（`UnsupportedSemanticValue` を含むなら None: identity を持たない）。

    projection の `stable_key` / `semantic_key` は完全性の判定（`contains_unsupported_value`）の
    ために印を含んだまま持つ。**それを identity（SMT の記号・provenance key・関数名）に使う側は
    この関数を通す**: 印は型名しか残っていないので、別の値どうしが同じ identity になる。
    """

    if value is None or contains_unsupported_value(value):
        return None
    return value


def project_storage(storage_info: Any) -> StorageProjection:
    """storage identity を値にする。"""

    storage_key_fn = getattr(storage_info, "storage_identity_key", None)
    if not callable(storage_key_fn):
        return _ABSENT_STORAGE
    try:
        storage_key = storage_key_fn()
    except IDENTITY_EVALUATION_ERRORS:
        return StorageProjection(identity=None, supported=True)
    if storage_key is None:
        return StorageProjection(identity=None, supported=True)
    return StorageProjection(
        identity=canonical_value_key(immutable_value(storage_key)), supported=True
    )


def project_declared_type(
    data_type_obj: Any, declared_name: Optional[str]
) -> DeclaredTypeProjection:
    """宣言型の signedness を値にする。

    pointer は宣言名だけで判定できるので、その場合は型 object へ問い合わせない。
    `get_declared_type_signedness` も pointer には常に `False` を返すので意味は
    同じで、**解析が読まなかった型 object を新しく叩かない**という性質だけが
    増える（記録済みの観測列に無い問い合わせを凍結が作らない）。
    """

    if data_type_obj is None:
        return _ABSENT_DECLARED_TYPE
    if _declared_name_is_pointer(declared_name):
        return DeclaredTypeProjection(signedness=False, declared=True)
    from scripts.function_tracer_pcode.core.signature import get_declared_type_signedness

    try:
        signed = get_declared_type_signedness(
            data_type_obj, fallback_name=None, fallback_signed=False
        )
    except IDENTITY_EVALUATION_ERRORS:
        return DeclaredTypeProjection(signedness=False, declared=True)
    return DeclaredTypeProjection(signedness=bool(signed), declared=True)


def _declared_name_is_pointer(declared_name: Optional[str]) -> bool:
    if not declared_name:
        return False
    return declared_name.rstrip().endswith("*")


def _stable_origin(runtime_ref: Any) -> Optional[Tuple[Any, ...]]:
    origin_kind = getattr(runtime_ref, "origin_kind", None)
    origin_ref = getattr(runtime_ref, "origin_ref", None)
    if origin_kind is None or origin_ref is None:
        return None
    if declared_method(type(origin_ref), origin_ref, "stable_key") is None:
        return None
    origin_key = identity_value(_stable_key_or_none(origin_ref))
    if origin_key is None:
        return None
    # 形は unknown 宣言 identity がそのまま使う（変えると symbol 名が動く）。
    return (origin_kind, origin_key)


def _is_parameter_ref(runtime_ref: Any, stable_key: Any) -> bool:
    is_parameter = getattr(runtime_ref, "is_parameter", None)
    if callable(is_parameter):
        try:
            return bool(is_parameter())
        except IDENTITY_EVALUATION_ERRORS:
            return False
    return bool(
        isinstance(stable_key, tuple) and stable_key and stable_key[0] == "parameter"
    )


def _parameter_stable_key(stable_key: Any) -> Optional[CanonicalAtoms]:
    if isinstance(stable_key, tuple) and stable_key and stable_key[0] == "parameter":
        return stable_key
    return None


def _address_offset(runtime_ref: Any) -> Optional[int]:
    if not isinstance(runtime_ref, AddressValueRef):
        return None
    try:
        return int(runtime_ref.address_offset)
    except IDENTITY_EVALUATION_ERRORS:
        return None


def _address_object_identity(runtime_ref: Any) -> Optional[Tuple[Any, ...]]:
    if not isinstance(runtime_ref, AddressValueRef):
        return None
    try:
        identity = runtime_ref.global_object_identity()
    except IDENTITY_EVALUATION_ERRORS:
        return None
    return None if identity is None else immutable_value(identity)


def _lowering_identity(
    expr: Any, runtime_ref: Any, stable_key: Any, semantic_key: Any
) -> Optional[Tuple[Any, ...]]:
    """loop lowering が SMT function 名に使う identity。

    形は既存の出力をそのまま保つ（変えると SMT symbol 名が動く）。証明が要る
    loop summary と key を出せない ref だけが `id()` を含む process 依存の値に
    なる。**その値をここで凍結時に確定させる**ので、consumer が生 ref を読み
    直すことはなくなり、process 依存が残る場所もこの 1 関数だけになる。
    """

    loop_summary = getattr(runtime_ref, "loop_summary", None)
    if loop_summary is not None:
        requires_effect_proof = getattr(loop_summary, "requires_effect_proof", None)
        requires_path_proof = getattr(loop_summary, "requires_path_proof", None)
        effect_required = callable(requires_effect_proof) and requires_effect_proof()
        path_required = callable(requires_path_proof) and requires_path_proof()
        if effect_required or path_required:
            return (
                "opaque_loop_summary_identity",
                type(runtime_ref).__module__,
                type(runtime_ref).__qualname__,
                "effect_proof_required" if effect_required else "path_proof_required",
                id(runtime_ref),
                id(loop_summary),
                id(expr),
            )
        method_b_key = loop_summary_method_b_key(loop_summary)
        if method_b_key is not None:
            return (
                "loop_summary_method_b_runtime",
                type(runtime_ref).__module__,
                type(runtime_ref).__qualname__,
                ("ref_constant_bias", int(getattr(runtime_ref, "constant_bias", 0) or 0)),
                method_b_key,
            )
        if _stable_key_or_none(loop_summary) is None:
            return (
                "opaque_loop_summary_identity",
                type(runtime_ref).__module__,
                type(runtime_ref).__qualname__,
                "unkeyable",
                id(runtime_ref),
                id(loop_summary),
                id(expr),
            )
    if semantic_key is not None:
        return semantic_key
    if stable_key is not None and declared_method(type(runtime_ref), runtime_ref, "stable_key") is not None:
        return stable_key
    return (
        "opaque_runtime_ref",
        type(runtime_ref).__module__,
        type(runtime_ref).__qualname__,
        id(runtime_ref),
        id(expr),
    )
