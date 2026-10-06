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


def canonical_atom(value: Any) -> CanonicalAtoms:
    """任意の値を structural key 用の安定な atom へ落とす。

    `stable_key()` が返した list を list のまま抱え込まないよう、container は
    すべて tuple へ畳む。最後の手段の `object_id` だけは process 依存だが、
    これは「同じ object かどうか」しか言っていない（identity digest には
    使わない — `canonical_value_key` を使うこと）。
    """

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
    # 容器は基底型の実装で辿る（subclass の `__iter__` / `items` を呼ばない）
    if issubclass(kind, tuple):
        return ("tuple", tuple(canonical_atom(item) for item in tuple.__iter__(value)))
    if issubclass(kind, list):
        return ("list", tuple(canonical_atom(item) for item in list.__iter__(value)))
    if issubclass(kind, dict) or kind is MappingProxyType:
        pairs = dict.items(value) if issubclass(kind, dict) else value.items()
        items = [(canonical_atom(key), canonical_atom(item)) for key, item in pairs]
        items.sort()
        return ("dict", tuple(items))
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            return ("stable", canonical_atom(stable_key()))
        except IDENTITY_EVALUATION_ERRORS:
            pass
    to_dict = getattr(value, "to_dict", None)
    if callable(to_dict):
        try:
            return ("object_dict", canonical_atom(to_dict()))
        except IDENTITY_EVALUATION_ERRORS:
            pass
    from dataclasses import fields, is_dataclass

    if is_dataclass(value):
        return (
            "dataclass",
            type(value).__module__,
            type(value).__qualname__,
            tuple(
                (field.name, canonical_atom(getattr(value, field.name)))
                for field in fields(value)
            ),
        )
    if issubclass(kind, Enum):
        # 値を持たない enum の member は singleton で、名前が member を識別する（mixin の enum は
        # 上の scalar の規則で基底型の値になる）。属性の辞書（`_value_` など private だけ）に落とすと
        # 同じ enum の全 member が同じ atom になる（Issue #215 C-K1）
        name = live_values.str_value(live_values.instance_state(value, "_name_", None))
        if type(name) is str:
            return ("enum", type(value).__module__, type(value).__qualname__, name)
    obj_dict = getattr(value, "__dict__", None)
    if type(obj_dict) is dict and obj_dict:
        # 公開された属性だけで状態が尽きる object だけを属性の値で表す。private な属性を落とすと、
        # それだけが違う 2 つの object が同じ atom になる（Issue #215 C-K1）。落とすものがあれば
        # 値として識別できない（`object_id`、構造 key では識別不能）
        attributes = list(dict.items(obj_dict))
        if all(type(key) is str and not key.startswith("_") for key, _item in attributes):
            items = [(canonical_atom(key), canonical_atom(item)) for key, item in attributes]
            items.sort()
            return (
                "object_attrs",
                type(value).__module__,
                type(value).__qualname__,
                tuple(items),
            )
    return ("object_id", type(value).__module__, type(value).__qualname__, id(value))


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
    if isinstance(value, bool):
        return ("bool", int(value))
    if isinstance(value, int):
        return ("int", value)
    if isinstance(value, float):
        return ("float", repr(value))
    if isinstance(value, str):
        return ("str", value)
    if isinstance(value, bytes):
        return ("bytes", value.hex())
    if isinstance(value, tuple):
        return ("tuple", tuple(canonical_value_key(item) for item in value))
    if isinstance(value, list):
        return ("list", tuple(canonical_value_key(item) for item in value))
    if isinstance(value, frozenset):
        return ("frozenset", tuple(sorted(canonical_value_key(item) for item in value)))
    if isinstance(value, set):
        return ("set", tuple(sorted(canonical_value_key(item) for item in value)))
    if isinstance(value, (dict, MappingProxyType)):
        items = [
            (canonical_value_key(key), canonical_value_key(item))
            for key, item in value.items()
        ]
        items.sort()
        return ("dict", tuple(items))
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
    """`stable_key()` / `semantic_key()` の戻り値を不変な値へ畳む。

    container は tuple へ、Enum は値へ、`stable_key()` を持つ object はその key へ
    再帰的に落とす。どれでもない object は `UnsupportedSemanticValue` にする
    （生 object を snapshot に残さない）。
    """

    if isinstance(value, IMMUTABLE_SCALARS):
        return value
    if isinstance(value, (tuple, list)):
        return tuple(immutable_value(item) for item in value)
    if isinstance(value, (set, frozenset)):
        return tuple(sorted((immutable_value(item) for item in value), key=repr))
    if isinstance(value, (dict, MappingProxyType)):
        return tuple(
            sorted(
                ((immutable_value(key), immutable_value(item)) for key, item in value.items()),
                key=repr,
            )
        )
    if isinstance(value, Enum):
        return immutable_value(value.value)
    nested = _stable_key_or_none(value)
    if nested is not None:
        return nested
    return UnsupportedSemanticValue(
        type(value).__module__, type(value).__qualname__
    )


def contains_unsupported_value(value: Any) -> bool:
    """`immutable_value` が値として固定できなかったものを含むか。"""

    if isinstance(value, UnsupportedSemanticValue):
        return True
    if isinstance(value, tuple):
        return any(contains_unsupported_value(item) for item in value)
    return False


def _stable_key_or_none(value: Any) -> Any:
    stable_key = getattr(value, "stable_key", None)
    if not callable(stable_key):
        return None
    try:
        key = stable_key()
    except IDENTITY_EVALUATION_ERRORS:
        return None
    return None if key is None else immutable_value(key)


def _semantic_key_or_none(value: Any) -> Any:
    semantic_key = getattr(value, "semantic_key", None)
    if not callable(semantic_key):
        return None
    try:
        key = semantic_key()
    except IDENTITY_EVALUATION_ERRORS:
        return None
    return None if key is None else immutable_value(key)


def semantic_runtime_ref_key(value: Any) -> Optional[CanonicalAtoms]:
    """structural key に載せてよい runtime ref の意味 key（無ければ `None`）。

    任意の object 属性は見ない。debug 用・付随的な runtime object が構造の
    等価性を動かしてよいのは、明示的な安定 key を出しているときだけ。
    """

    if value is None:
        return None
    scalar = live_values.json_scalar(value)
    if (scalar is not live_values.NOT_PLAIN and type(scalar) is not float) or issubclass(type(value), bytes):
        # bool / int / str / bytes（とその subclass）は `canonical_atom` と同じ規則（基底型の slot の
        # exact な値）。float は従来どおり安定 key を出さない値として扱う（意味 key に入れない）
        return canonical_atom(value)
    kind = type(value)
    if issubclass(kind, (tuple, list)):
        items = []
        for item in (tuple.__iter__(value) if issubclass(kind, tuple) else list.__iter__(value)):
            item_key = semantic_runtime_ref_key(item)
            if item_key is None:
                return None
            items.append(item_key)
        return ("tuple" if issubclass(kind, tuple) else "list", tuple(items))
    if issubclass(kind, dict) or kind is MappingProxyType:
        items = []
        for key, item in (dict.items(value) if issubclass(kind, dict) else value.items()):
            key_key = semantic_runtime_ref_key(key)
            item_key = semantic_runtime_ref_key(item)
            if key_key is None or item_key is None:
                return None
            items.append((key_key, item_key))
        items.sort()
        return ("dict", tuple(items))
    stable = _stable_key_or_none(value)
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
    stable = _stable_key_or_none(runtime_ref)
    semantic = _semantic_key_or_none(runtime_ref)
    lowering_identity = _lowering_identity(expr, runtime_ref, stable, semantic)
    return RuntimeRefProjection(
        structural_key=semantic_runtime_ref_key(runtime_ref),
        stable_key=stable,
        semantic_key=semantic,
        stable_origin=_stable_origin(runtime_ref),
        is_parameter_ref=_is_parameter_ref(runtime_ref, stable),
        parameter_stable_key=_parameter_stable_key(stable),
        is_address_value_ref=isinstance(runtime_ref, AddressValueRef),
        address_offset=_address_offset(runtime_ref),
        address_object_identity=_address_object_identity(runtime_ref),
        lowering_identity=lowering_identity,
        loop_lowering=project_loop_lowering(
            expr, runtime_ref, identity=lowering_identity
        ),
        declares_variable_symbol=isinstance(
            runtime_ref, (CanonicalLocation, PostStateReadRef, PostStateValueRef)
        ),
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
    if not callable(getattr(origin_ref, "stable_key", None)):
        return None
    origin_key = _stable_key_or_none(origin_ref)
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
    if callable(getattr(runtime_ref, "stable_key", None)):
        return stable_key
    return (
        "opaque_runtime_ref",
        type(runtime_ref).__module__,
        type(runtime_ref).__qualname__,
        id(runtime_ref),
        id(expr),
    )
