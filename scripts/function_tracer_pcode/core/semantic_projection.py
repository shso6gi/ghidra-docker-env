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
from scripts.function_tracer_pcode.core.atom_validity import (  # noqa: F401  (tag は再 export)
    OBJECT_ID_TAG,
    UNSUPPORTED_VALUE_TAG,
    atom_validity,
    parameter_schema_complete,
    usable_as_symbol_identity,
)
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


#: `canonical_atom` が値として読む入れ子の深さの上限（容器と object の段の数）。これより深い値は
#: 値として固定できない（識別不能）。atom から作る表現（value key・runtime ref の key・identity の
#: 形）の再帰の深さも、これで抑えられる
MAX_VALUE_DEPTH = 64


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
    value_id = id(value)
    if value_id in active or len(active) >= MAX_VALUE_DEPTH:
        # 閉路（自分を含む容器・自分を返す stable_key）: 有限の atom で値を表せない。値として
        # 固定できない印にする（`object_id` と違い、読める object の「同じ object か」でもない）。
        # 入れ子が上限より深い値も同じ（明示の制限: 読み手の再帰の深さをここで抑える。`active` は
        # いま辿っている経路の容器・object なので、その数が入れ子の深さ）
        return _unfixable_atom(value)
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
                return _unfixable_atom(value)
            return (tag, tuple(atom for atom, _item in ordered))
        ordered = _ordered_by_atom([(_atom(key), _atom(item)) for key, item in elements])
        if ordered is None:
            # 別の key（hash を上書きした subclass と基底型の値など）が同じ atom になった: どの値が
            # どの key のものかを atom では区別できない
            return _unfixable_atom(value)
        return ("dict", tuple(ordered))
    # 値が自分の identity を明示する method（型の属性だけを見る。instance の `__getattr__` を呼ばない）
    stable_key = declared_method(kind, value, "stable_key")
    if stable_key is not None:
        try:
            return ("stable", _atom(stable_key()))
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
    # `to_dict()` は直列化の宣言（状態の一部を落とし得る）: 値は残すが identity にはしない
    # （`core/atom_validity` が識別しない）。状態の全部を読める凍結 dataclass・enum は上で値になる
    to_dict = declared_method(kind, value, "to_dict")
    if to_dict is not None:
        try:
            return ("object_dict", _atom(to_dict()))
        except IDENTITY_EVALUATION_ERRORS:
            pass
    return (OBJECT_ID_TAG, str(type(value).__module__), str(type(value).__qualname__), id(value))


def _unfixable_atom(value: Any) -> CanonicalAtoms:
    """値として固定できない値の印（型名だけ。`core/atom_validity` が識別不能と判定する）。"""

    kind = type(value)
    return (UNSUPPORTED_VALUE_TAG, str(kind.__module__), str(kind.__qualname__))


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
    """`value` の意味内容による表現（leaf の値の digest 用）。**`canonical_atom` の atom から作る**。

    読み方は `canonical_atom` の 1 回の走査だけ（Issue #215: 容器の型・要素の対応・閉路・衝突の
    判断を、読み手ごとに別に持たない）。atom との違いは process に依らないことだけ:

    * 状態を読めない object（`object_id`）と値として固定できない印（閉路・衝突）は
      ``("opaque_value", module, qualname)``（`id()` を入れない: digest が run 間で決定的）
    * 型が宣言した key を持たない object（凍結 dataclass・enum・`to_dict`）も従来どおり opaque
    * 型が宣言した key を持つ object は ``("stable", key の表現)``

    opaque な値は値として支えない（`value_key_is_opaque`: digest は名乗らない）。「同じ object か」の
    区別が要る比較側は `canonical_atom` を使う。
    """

    return _value_key_of_atom(canonical_atom(value))


def _value_key_of_atom(atom: CanonicalAtoms) -> CanonicalAtoms:
    tag = atom[0]
    if tag in _SCALAR_TAGS:
        return atom
    if tag in _SEQUENCE_TAGS or tag in _SET_TAGS:
        return (tag, tuple(_value_key_of_atom(item) for item in atom[1]))
    if tag == "dict":
        return ("dict", tuple((_value_key_of_atom(key), _value_key_of_atom(item)) for key, item in atom[1]))
    if tag == "stable":
        return ("stable", _value_key_of_atom(atom[1]))
    if tag in (OBJECT_ID_TAG, UNSUPPORTED_VALUE_TAG):
        return ("opaque_value", atom[1], atom[2])
    if tag in ("dataclass", "enum"):
        return ("opaque_value", atom[1], atom[2])
    # `to_dict` の値（型名を持たない）
    return ("opaque_value", "", tag)


def value_key_is_opaque(key: CanonicalAtoms) -> bool:
    """`canonical_value_key` が値として支えられない部分を **どこかに** 含むか。

    容器の中の opaque も数える（Issue #215）: 中の object が型名だけになった容器を値として支えると、
    別の object を持つ容器と同じ表現になる。値が構造 key の識別不能 token を含むときも同じ
    （`core/atom_validity` の判定。その値は何とも等しくならない）。`canonical_value_key` 以外の印
    （PHI の ``("phi_branches",)`` など）は opaque ではない。
    """

    if type(key) is not tuple or not key:
        return False
    if not atom_validity(key).identified:
        return True
    return _value_key_has_opaque(key)


def _value_key_has_opaque(key: CanonicalAtoms) -> bool:
    if type(key) is not tuple or not key:
        return False
    tag = key[0]
    if tag == "opaque_value":
        return True
    if len(key) != 2:
        return False
    if tag == "dict":
        return any(_value_key_has_opaque(k) or _value_key_has_opaque(v) for k, v in key[1])
    if tag == "stable":
        return _value_key_has_opaque(key[1])
    if tag in _SEQUENCE_TAGS or tag in _SET_TAGS:
        return any(_value_key_has_opaque(item) for item in key[1])
    return False


#: 子を持たない atom の tag
_SCALAR_TAGS = frozenset({"none", "bool", "int", "float", "str", "bytes"})


def _declared_key_raw(value: Any, name: str) -> Any:
    """型が宣言した `stable_key()` / `semantic_key()` の生の戻り値（無ければ・失敗すれば None）。"""

    method = declared_method(type(value), value, name)
    if method is None:
        return None
    try:
        return method()
    except IDENTITY_EVALUATION_ERRORS:
        return None


def semantic_runtime_ref_key(value: Any) -> Optional[CanonicalAtoms]:
    """structural key に載せてよい runtime ref の意味 key（無ければ `None`）。

    任意の object 属性は見ない。debug 用・付随的な runtime object が構造の
    等価性を動かしてよいのは、明示的な安定 key を出しているときだけ。

    **`canonical_atom` の atom から作る**（Issue #215: 読み方・閉路・衝突の判断は `canonical_atom`
    の 1 回の走査だけ）。atom との違いは「意味 key を持つ値」の範囲だけで、従来と同じ:

    * scalar（float を除く）・bytes はその atom、列と dict は要素ごとに同じ規則
    * 型が宣言した `stable_key()` を持つ object は ``("stable_runtime_ref", key の atom)``
    * float・set・宣言した key を持たない object（とそれを含む容器）は意味 key を持たない
    * 意味 key を持たない ref と、値として固定できない印（閉路・要素の衝突）は、値として固定できない
      印（`unsupported_value`）にする: 構造 key の owner がその node を識別不能にする（ref を落として
      意味 key が無い式として扱うと、別の ref の式と同じ key になる）。None は ref が無いときだけ
    """

    if value is None:
        return None
    key = _runtime_key_of_atom(canonical_atom(value))
    if key is not None and not parameter_schema_complete(key):
        # schema の成分が欠けた key（index の無い parameter など）は、別の object に同じ値として現れる。
        # solver の記号を共有しない（`_identity_of`）のに構造 key で等しくすると、別の記号に描画される
        # 式が同じ key になる。値として固定できない印にする
        return _unfixable_atom(value)
    if key is None:
        # ref はあるが意味 key を出さない: 構造 key から ref を落とすと、別の ref の式（SMT では別の
        # 記号になる）と同じ key になる。値として固定できない印にし、構造 key の owner がその node を
        # 識別不能にする（Issue #215。recorded corpus の production の ref はすべて意味 key を持つ）
        return _unfixable_atom(value)
    return key


def _runtime_key_of_atom(atom: CanonicalAtoms) -> Optional[CanonicalAtoms]:
    tag = atom[0]
    if tag == "float" or tag == "none":
        return None
    if tag in _SCALAR_TAGS:
        return atom
    if tag in _SEQUENCE_TAGS:
        items = []
        for item in atom[1]:
            item_key = _runtime_key_of_atom(item)
            if item_key is None:
                return None
            items.append(item_key)
        return (tag, tuple(items))
    if tag == "dict":
        pairs = []
        for key, item in atom[1]:
            key_key = _runtime_key_of_atom(key)
            item_key = _runtime_key_of_atom(item)
            if key_key is None or item_key is None:
                return None
            pairs.append((key_key, item_key))
        ordered = _ordered_by_atom(pairs)
        if ordered is None:
            return (UNSUPPORTED_VALUE_TAG, "builtins", "dict")
        return ("dict", tuple(ordered))
    if tag == "stable":
        return ("stable_runtime_ref", atom[1])
    if tag == UNSUPPORTED_VALUE_TAG:
        return atom
    # set・宣言した key を持たない object（`object_id` / dataclass / enum / `to_dict`）
    return None


# ---------------------------------------------------------------------------
# solver の identity（projection の identity の field の値）
# ---------------------------------------------------------------------------


def identity_value(value: Any) -> Optional[CanonicalAtoms]:
    """identity（SMT の記号・条件 oracle の記号・provenance key・関数名）に使う値。無ければ None。

    **`canonical_atom` の atom そのもの**（Issue #215）。atom は exact な str / int だけを中身に持ち、
    容器の型（list と tuple、dict と組の列、set）・bool と int・float の bit 列・enum の member を
    区別する: atom どうしの `==` は値の区別を落とさない。読む前に Python の値へ畳むと（旧
    `immutable_value`）、`[1]` と `(1,)`、`{"a": 1}` と `(("a", 1),)`、`True` と `1` が同じ identity に
    なり、別の ref が同じ solver symbol を共有した。

    使ってよいのは `core/atom_validity.usable_as_symbol_identity` が受け付けた atom だけ（identified・
    placeholder_free・parameter の schema が完全）: 識別不能 token・状態を読めない object・型名だけの印
    （閉路・衝突）・構造 key の placeholder・成分の欠けた schema（index の無い parameter など）を含む値は、
    別の object と同じ値になり得るので identity を持たない（None）。process の中だけの識別済み token
    （tail token・object identity token）は同じ process の中で同じものを指すので受け付ける。

    **identity の入口はここ 1 つ**（`_identity_of`）: runtime ref の stable / semantic / origin、storage、
    loop summary の Method B key は、すべてここを通って projection の field になる。identity の成分を
    足すときもここを通す（`test_sn3_identity_entries` が全入口を同じ matrix で確かめる）。
    """

    return _identity_of(value)[0]


def _identity_of(value: Any) -> Tuple[Optional[CanonicalAtoms], bool]:
    """(identity の値, 値はあったが identity にできなかったか)。"""

    if value is None:
        return None, False
    atom = canonical_atom(value)
    if usable_as_symbol_identity(atom):
        return atom, False
    return None, True


def identity_view(atom: Any) -> Any:
    """identity の atom を Python の値として読んだ形（**形の検査専用**。比較・hash・記号名に使わない）。

    `("parameter", index, …)` のような schema の先頭や欠けた成分を調べる consumer（solver symbol の
    安全性の判定、parameter ref の判定）のための読み口。list と tuple を区別しないなど値の区別を
    落とすので、identity の等しさは必ず atom で比べる。読めない atom（object の印など）はそのまま返す。
    """

    if type(atom) is not tuple or not atom:
        return atom
    tag = atom[0]
    if tag == "none":
        return None
    if tag == "bool":
        return bool(atom[1])
    if tag in ("int", "str"):
        return atom[1]
    if tag in _SEQUENCE_TAGS or tag in _SET_TAGS:
        return tuple(identity_view(item) for item in atom[1])
    if tag == "dict":
        # dict は (key, value) の組の列として読む（形の検査が入れ子の schema を見落とさない）
        return tuple((identity_view(key), identity_view(item)) for key, item in atom[1])
    if tag == "stable":
        return identity_view(atom[1])
    if tag == "dataclass" and len(atom) == 4:
        return tuple((name, identity_view(item)) for name, item in atom[3])
    return atom


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
    #: `stable_key()` の identity（`identity_value`: 検証済みの atom。固定できなければ None）
    stable_key: Any
    #: `semantic_key()` の identity（`identity_value`）
    semantic_key: Any
    #: `(origin_kind, origin_stable_key)` の identity（`identity_value`。unknown 宣言 identity 用）
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
    #: その key だけ外す）、identity の完全性と、ref を持たない式との区別はこの印で判断する
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
    #: storage の key はあったが値として固定できなかった（identity は None。Issue #215）
    identity_unfixable: bool = False


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
    # identity の field は `identity_value`（`canonical_atom` の atom で、`atom_validity` が identified
    # かつ placeholder_free と判定したもの）だけを持つ（Issue #215）。値を読む前に Python の値へ畳まない:
    # 畳むと容器の型・bool と int などの区別が落ち、それを読む全 consumer（SMT の unknown 記号・条件
    # oracle の記号・provenance key・loop lowering の関数名）で別の ref が同じ identity になる
    stable_raw = _declared_key_raw(runtime_ref, "stable_key")
    semantic_raw = _declared_key_raw(runtime_ref, "semantic_key")
    stable, stable_unfixable = _identity_of(stable_raw)
    semantic, semantic_unfixable = _identity_of(semantic_raw)
    # key を出さない ref も identity を固定できない: index・名前・storage の粗い identity へ退避すると、
    # 構造 key（識別不能にする: `semantic_runtime_ref_key`）とも食い違い、別の ref の式が同じ記号になる
    keyless = stable_raw is None and semantic_raw is None
    origin, origin_unfixable = _stable_origin(runtime_ref)
    address_identity, address_unfixable = _address_object_identity(runtime_ref)
    unfixable = keyless or stable_unfixable or semantic_unfixable or origin_unfixable or address_unfixable
    if unfixable:
        # 一部でも固定できないなら、残りの key（stable・semantic・origin）にも頼らない: consumer は
        # semantic → stable → origin の順に退避するので、固定できない成分を落とした粗い key で別の
        # ref と併合し得る。外したことは `identity_unfixable` に残す
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
    # solver の parameter symbol の identity にもなる（`parameter_storage`）: runtime ref の key と同じ
    # 契約（`identity_value`）。固定できなければ identity を持たず、そのことを印に残す
    identity, unfixable = _identity_of(storage_key)
    return StorageProjection(identity=identity, supported=True, identity_unfixable=unfixable)


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


def _stable_origin(runtime_ref: Any) -> Tuple[Optional[CanonicalAtoms], bool]:
    """(origin の identity, 値はあったが固定できなかったか)。identity は `(origin_kind, origin の key)` の atom。"""

    origin_kind = getattr(runtime_ref, "origin_kind", None)
    origin_ref = getattr(runtime_ref, "origin_ref", None)
    if origin_kind is None or origin_ref is None:
        return None, False
    origin_key = _declared_key_raw(origin_ref, "stable_key")
    if origin_key is None:
        return None, False
    return _identity_of((origin_kind, origin_key))


def _is_parameter_ref(runtime_ref: Any, stable_key: Any) -> bool:
    is_parameter = getattr(runtime_ref, "is_parameter", None)
    if callable(is_parameter):
        try:
            return bool(is_parameter())
        except IDENTITY_EVALUATION_ERRORS:
            return False
    return _parameter_stable_key(stable_key) is not None


def _parameter_stable_key(stable_key: Any) -> Optional[CanonicalAtoms]:
    """`("parameter", …)` 形の stable key の identity（atom のまま返す。形は `identity_view` で調べる）。"""

    view = identity_view(stable_key)
    if type(view) is tuple and view and view[0] == "parameter":
        return stable_key
    return None


def _address_offset(runtime_ref: Any) -> Optional[int]:
    if not isinstance(runtime_ref, AddressValueRef):
        return None
    try:
        return int(runtime_ref.address_offset)
    except IDENTITY_EVALUATION_ERRORS:
        return None


def _address_object_identity(runtime_ref: Any) -> Tuple[Optional[Tuple[str, int, int]], bool]:
    """(名前付き global object のアドレス identity `(symbol, size, offset)`, 値はあったが固定できなかったか)。

    consumer（`render_smt.unknowns`）は 3 つ組を分解して symbol 名と offset を描画に使うので、
    schema（exact な str・int・int）を確かめてから exact な値で持つ（Issue #215: subclass の値・
    別の形の値を identity に入れない）。
    """

    if not isinstance(runtime_ref, AddressValueRef):
        return None, False
    try:
        identity = runtime_ref.global_object_identity()
    except IDENTITY_EVALUATION_ERRORS:
        return None, False
    if identity is None:
        return None, False
    container = read_container(identity)
    if container is None or container[0] != "tuple" or len(container[1]) != 3:
        return None, True
    symbol, size, offset = (live_values.json_scalar(item) for item in container[1])
    if type(symbol) is not str or type(size) is not int or type(offset) is not int:
        return None, True
    return (symbol, size, offset), False


def _lowering_identity(
    expr: Any, runtime_ref: Any, stable_key: Any, semantic_key: Any
) -> Optional[Tuple[Any, ...]]:
    """loop lowering が SMT function 名に使う identity。

    ref の key を使うときは projection の identity（`identity_value` の atom）をそのまま使う。証明が要る
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
        raw_method_b_key = loop_summary_method_b_key(loop_summary)
        if raw_method_b_key is not None:
            # loop summary の Method B key（`runtime_refs/loops.py` が組む）も、他の identity の成分と同じ
            # 入口（`_identity_of`: 値の読み方・妥当性・schema の完全性）を通す。使えなければ記号を共有しない
            method_b_key, method_b_unusable = _identity_of(raw_method_b_key)
            if method_b_unusable:
                return (
                    "opaque_loop_summary_identity",
                    type(runtime_ref).__module__,
                    type(runtime_ref).__qualname__,
                    "method_b_key_unusable",
                    id(runtime_ref),
                    id(loop_summary),
                    id(expr),
                )
            return (
                "loop_summary_method_b_runtime",
                type(runtime_ref).__module__,
                type(runtime_ref).__qualname__,
                ("ref_constant_bias", int(getattr(runtime_ref, "constant_bias", 0) or 0)),
                method_b_key,
            )
        if _declared_key_raw(loop_summary, "stable_key") is None:
            return (
                "opaque_loop_summary_identity",
                type(runtime_ref).__module__,
                type(runtime_ref).__qualname__,
                "unkeyable",
                id(runtime_ref),
                id(loop_summary),
                id(expr),
            )
    # semantic と stable は別の名前空間（atom が偶然等しい別種の key で関数名を共有しない）
    if semantic_key is not None:
        return ("semantic_key", semantic_key)
    if stable_key is not None:
        return ("stable_key", stable_key)
    return (
        "opaque_runtime_ref",
        type(runtime_ref).__module__,
        type(runtime_ref).__qualname__,
        id(runtime_ref),
        id(expr),
    )
