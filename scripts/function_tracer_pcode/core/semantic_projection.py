# -*- coding: utf-8 -*-
"""生 runtime object → immutable な意味値（Issue #22 PR-22-B）。

**この module が「生 object をどう読むか」を決める唯一の場所**。ここから外へ出る
のは pure な value だけで、生 object への参照も、あとから生 object を読み直す
遅延セルも渡さない。

なぜ 1 owner にするか: `runtime_ref.semantic_key()` を「identity として何に使うか」
という判断が、structural key・solver query・unknown 宣言・loop lowering の 4 箇所に
散っていた。同じ問いに 4 つの答えがあると、どれか 1 つを直したときに他が置いて
いかれる（実際 `except` の範囲も 3 通りに分かれていた）。新しい runtime ref 種別を
足すときに触るのもここだけになる。

読み取りの境界（凍結後に何を読んでよいか）:

* `SemanticSnapshot` の pure value — 常に可
* `core/runtime_refs/` の **frozen な value object の構造**（`isinstance` 判定、
  `loop_summary` / `transition_expr` などの下位構造）— 可。これらは凍結
  dataclass で、後から変わらないことが型で保証されている
  （`test_architecture_boundaries.py` が全 ref 種別について固定している）
* 可変な生 object（Ghidra の `data_type_obj`、`StorageInfo`）— **不可**。
  identity は必ずこの module が凍結時に作った値を読む

失敗の扱い: identity が取れないことは「無い」であって例外ではない（従来の
包括捕捉と同じ結果）。ただし捕まえる型は列挙する — 包括捕捉を増やさないため。
"""

from __future__ import annotations

from dataclasses import dataclass
from types import MappingProxyType
from typing import Any, NamedTuple, Optional, Tuple

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
    if isinstance(value, bool):
        return ("bool", int(value))
    if isinstance(value, int):
        return ("int", value)
    if isinstance(value, str):
        return ("str", value)
    if isinstance(value, bytes):
        return ("bytes", value.hex())
    if isinstance(value, tuple):
        return ("tuple", tuple(canonical_atom(item) for item in value))
    if isinstance(value, list):
        return ("list", tuple(canonical_atom(item) for item in value))
    if isinstance(value, (dict, MappingProxyType)):
        items = [(canonical_atom(key), canonical_atom(item)) for key, item in value.items()]
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
    obj_dict = getattr(value, "__dict__", None)
    if isinstance(obj_dict, dict) and obj_dict:
        items = [
            (canonical_atom(key), canonical_atom(item))
            for key, item in obj_dict.items()
            if not str(key).startswith("_")
        ]
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


def immutable_value(value: Any) -> Any:
    """`stable_key()` / `semantic_key()` の戻り値を不変な形へ畳む。

    実装が list や dict を返しても、snapshot がそれをそのまま抱えると「凍結後も
    中身が変わり得る値」を意味として持ってしまう。ここで tuple へ畳んで、以後は
    値としてだけ扱う。
    """

    if isinstance(value, tuple):
        return tuple(immutable_value(item) for item in value)
    if isinstance(value, list):
        return tuple(immutable_value(item) for item in value)
    if isinstance(value, (set, frozenset)):
        return tuple(sorted(immutable_value(item) for item in value))
    if isinstance(value, (dict, MappingProxyType)):
        return tuple(
            sorted(
                (immutable_value(key), immutable_value(item))
                for key, item in value.items()
            )
        )
    return value


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
    if isinstance(value, bool):
        return ("bool", int(value))
    if isinstance(value, int):
        return ("int", value)
    if isinstance(value, str):
        return ("str", value)
    if isinstance(value, bytes):
        return ("bytes", value.hex())
    if isinstance(value, (tuple, list)):
        items = []
        for item in value:
            item_key = semantic_runtime_ref_key(item)
            if item_key is None:
                return None
            items.append(item_key)
        return ("tuple" if isinstance(value, tuple) else "list", tuple(items))
    if isinstance(value, (dict, MappingProxyType)):
        items = []
        for key, item in value.items():
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
        lowering_identity=_lowering_identity(expr, runtime_ref, stable, semantic),
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
