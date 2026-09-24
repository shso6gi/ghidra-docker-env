# -*- coding: utf-8 -*-
"""関数シグネチャと型仮説のデータモデル"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional, List, Dict, Any, Mapping, TYPE_CHECKING, Tuple
from scripts.function_tracer_pcode.core.json_encoding import as_dict, each, mapping_of, materialize, source_converter

if TYPE_CHECKING:
    from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis


def normalize_type_name(type_name: Optional[str]) -> str:
    """型名を比較しやすい形に正規化する。"""
    return (type_name or "").strip().lower()


def get_data_type_display_name(
    data_type_obj: Any = None,
    fallback_name: Optional[str] = None,
) -> Optional[str]:
    """表示用の型名を取得する。"""
    if data_type_obj is not None:
        name = _call_zero_arg(data_type_obj, "getName")
        if name:
            return str(name)
        try:
            return str(data_type_obj)
        except Exception:
            pass
    return fallback_name


def get_data_type_path(data_type_obj: Any = None) -> Optional[str]:
    """DataTypePath を文字列で返す。"""
    path_obj = _call_zero_arg(data_type_obj, "getDataTypePath")
    if path_obj is None:
        return None
    try:
        return str(path_obj)
    except Exception:
        return None


def get_data_type_manager_for_reference(
    data_type_obj: Any = None,
    *,
    program: Any = None,
) -> Any:
    """型参照に紐づく DataTypeManager を取得する。"""
    data_type_manager = _call_zero_arg(data_type_obj, "getDataTypeManager")
    if data_type_manager is not None:
        return data_type_manager
    if program is not None:
        return _call_zero_arg(program, "getDataTypeManager")
    return None


def _resolve_runtime_data_type_obj(
    data_type_obj: Any = None,
    fallback_name: Optional[str] = None,
    *,
    program: Any = None,
) -> Any:
    """解析時に使う DataType object を解決する。"""
    if data_type_obj is not None:
        return data_type_obj
    if program is None or not fallback_name:
        return None
    resolved = resolve_type_spec(
        fallback_name,
        program=program,
    )
    if resolved is None:
        return None
    return resolved.data_type_obj


def _get_base_data_type(data_type_obj: Any = None) -> Any:
    """typedef を剥がした基底 DataType を返す。"""
    current = data_type_obj
    seen: set[int] = set()
    while current is not None and id(current) not in seen:
        seen.add(id(current))
        base = _call_zero_arg(current, "getBaseDataType")
        if base is None or base is current:
            break
        current = base
    return current


def _iter_float_data_types(data_type_manager: Any = None) -> Tuple[Any, ...]:
    """DTM から利用可能な floating-point DataType 候補を列挙する。"""
    if data_type_manager is None:
        return ()
    try:
        from ghidra.program.model.data import AbstractFloatDataType  # type: ignore[import]

        candidates = AbstractFloatDataType.getFloatDataTypes(data_type_manager)
        if candidates is not None:
            return tuple(candidates)
    except Exception:
        pass

    candidates = _call_zero_arg(data_type_manager, "getFloatDataTypes")
    if candidates is None:
        return ()
    try:
        return tuple(candidates)
    except Exception:
        return ()


def is_void_data_type(
    data_type_obj: Any = None,
    fallback_name: Optional[str] = None,
    *,
    program: Any = None,
) -> bool:
    """void 型かどうかを判定する。"""
    resolved = _resolve_runtime_data_type_obj(
        data_type_obj,
        fallback_name,
        program=program,
    )
    if resolved is not None:
        base = _get_base_data_type(resolved) or resolved
        try:
            from ghidra.program.model.data import VoidDataType  # type: ignore[import]

            return bool(VoidDataType.isVoidDataType(base))
        except Exception:
            pass
        length = _call_zero_arg(base, "getLength")
        if length is not None:
            try:
                return int(length) == 0
            except Exception:
                pass
    return False


def is_undefined_data_type(
    data_type_obj: Any = None,
    fallback_name: Optional[str] = None,
    *,
    program: Any = None,
) -> bool:
    """undefined 型かどうかを判定する。"""
    resolved = _resolve_runtime_data_type_obj(
        data_type_obj,
        fallback_name,
        program=program,
    )
    if resolved is not None:
        base = _get_base_data_type(resolved) or resolved
        try:
            from ghidra.program.model.data import Undefined  # type: ignore[import]

            return bool(Undefined.isUndefined(base))
        except Exception:
            pass
        is_undefined = _call_zero_arg(base, "isUndefined")
        if is_undefined is not None:
            return bool(is_undefined)
    return False


def is_composite_data_type(
    data_type_obj: Any = None,
    data_type_name: Optional[str] = None,
) -> bool:
    """配列・構造体・共用体などの複合型か（グローバル varnode が値ではなくオブジェクトを指す型）。"""
    if data_type_obj is not None:
        for probe in ("getNumElements", "getNumComponents", "getComponents"):
            if callable(getattr(data_type_obj, probe, None)):
                return True
        try:
            class_name = str(data_type_obj.getClass().getSimpleName())
        except Exception:
            class_name = type(data_type_obj).__name__
        if any(token in class_name for token in ("Array", "Structure", "Union", "Composite")):
            return True
    name = normalize_type_name(str(data_type_name or ""))
    if not name and data_type_obj is not None:
        name = normalize_type_name(str(data_type_obj))
    if not name:
        return False
    if name.endswith("]"):
        return True
    return name.startswith(("struct ", "union "))


def is_pointer_data_type(
    data_type_obj: Any = None,
    fallback_name: Optional[str] = None,
    *,
    program: Any = None,
) -> bool:
    """pointer 型かどうかを判定する。"""
    resolved = _resolve_runtime_data_type_obj(
        data_type_obj,
        fallback_name,
        program=program,
    )
    if resolved is not None:
        base = _get_base_data_type(resolved) or resolved
        try:
            from ghidra.program.model.data import Pointer  # type: ignore[import]

            if isinstance(base, Pointer):
                return True
        except Exception:
            pass
        is_pointer = _call_zero_arg(base, "isPointer")
        if is_pointer is not None:
            return bool(is_pointer)
        data_type_manager = get_data_type_manager_for_reference(
            base,
            program=program,
        )
        referenced = _call_zero_arg(base, "getDataType")
        if data_type_manager is not None and referenced is not None:
            pointer_candidate = _call_one_arg(data_type_manager, "getPointer", referenced)
            if pointer_candidate is not None:
                equivalent = _call_one_arg(pointer_candidate, "isEquivalent", base)
                if equivalent is not None:
                    return bool(equivalent)
                equivalent = _call_one_arg(base, "isEquivalent", pointer_candidate)
                if equivalent is not None:
                    return bool(equivalent)
    return False


def is_floating_data_type(
    data_type_obj: Any = None,
    fallback_name: Optional[str] = None,
    *,
    program: Any = None,
) -> bool:
    """floating-point 型かどうかを判定する。"""
    resolved = _resolve_runtime_data_type_obj(
        data_type_obj,
        fallback_name,
        program=program,
    )
    if resolved is None:
        return False
    base = _get_base_data_type(resolved) or resolved
    try:
        from ghidra.program.model.data import AbstractFloatDataType  # type: ignore[import]

        if isinstance(base, AbstractFloatDataType):
            return True
    except Exception:
        pass

    data_type_manager = get_data_type_manager_for_reference(
        base,
        program=program,
    )
    for candidate in _iter_float_data_types(data_type_manager):
        equivalent = _call_one_arg(base, "isEquivalent", candidate)
        if equivalent is not None:
            if bool(equivalent):
                return True
            continue
        equivalent = _call_one_arg(candidate, "isEquivalent", base)
        if equivalent is not None and bool(equivalent):
            return True
    return False


def is_integral_data_type(
    data_type_obj: Any = None,
    fallback_name: Optional[str] = None,
    *,
    program: Any = None,
) -> bool:
    """整数スカラ型かどうかを判定する。"""
    resolved = _resolve_runtime_data_type_obj(
        data_type_obj,
        fallback_name,
        program=program,
    )
    if resolved is None:
        return False
    if is_void_data_type(resolved):
        return False
    if is_pointer_data_type(resolved):
        return False
    if is_undefined_data_type(resolved):
        return False
    if is_floating_data_type(resolved):
        return False

    base = _get_base_data_type(resolved) or resolved
    try:
        from ghidra.program.model.data import AbstractIntegerDataType  # type: ignore[import]

        if isinstance(base, AbstractIntegerDataType):
            return True
    except Exception:
        pass

    signed_value = _call_zero_arg(base, "isSigned")
    length = _call_zero_arg(base, "getLength")
    if signed_value is None or length is None:
        return False
    try:
        return int(length) > 0
    except Exception:
        return False


def is_unsigned_data_type(
    data_type_obj: Any = None,
    fallback_name: Optional[str] = None,
    *,
    program: Any = None,
) -> bool:
    """unsigned 型かどうかを判定する。"""
    resolved = _resolve_runtime_data_type_obj(
        data_type_obj,
        fallback_name,
        program=program,
    )
    if is_void_data_type(resolved):
        return False
    if is_pointer_data_type(resolved):
        return False
    if resolved is not None:
        base = _get_base_data_type(resolved) or resolved
        signed_value = _call_zero_arg(base, "isSigned")
        if signed_value is not None:
            return not bool(signed_value)
    return False


def get_declared_type_signedness(
    data_type_obj: Any = None,
    fallback_name: Optional[str] = None,
    fallback_signed: bool = True,
    *,
    program: Any = None,
) -> bool:
    """宣言型の signedness を返す。"""
    resolved = _resolve_runtime_data_type_obj(
        data_type_obj,
        fallback_name,
        program=program,
    )
    if is_void_data_type(resolved):
        return False
    if is_pointer_data_type(resolved):
        return False
    base = _get_base_data_type(resolved) or resolved
    signed_value = _call_zero_arg(base, "isSigned")
    if signed_value is not None:
        return bool(signed_value)
    return fallback_signed


def get_declared_type_size_bytes(
    data_type_obj: Any = None,
    fallback_name: Optional[str] = None,
    fallback_size: Optional[int] = None,
    *,
    program: Any = None,
) -> Optional[int]:
    """宣言型のサイズを返す。"""
    resolved = _resolve_runtime_data_type_obj(
        data_type_obj,
        fallback_name,
        program=program,
    )
    if is_void_data_type(resolved):
        return 0

    base = _get_base_data_type(resolved) or resolved
    length = _call_zero_arg(base, "getLength")
    if length is not None:
        try:
            length = int(length)
            if length >= 0:
                return length
        except Exception:
            pass

    normalized_name = normalize_type_name(
        get_data_type_display_name(resolved, fallback_name)
    )
    if normalized_name in {"bool", "_bool", "boolean"}:
        return 1

    return fallback_size


def get_declared_type_size_bits(
    data_type_obj: Any = None,
    fallback_name: Optional[str] = None,
    fallback_size: Optional[int] = None,
    *,
    program: Any = None,
) -> Optional[int]:
    """宣言型のビット幅を返す。"""
    size_bytes = get_declared_type_size_bytes(
        data_type_obj,
        fallback_name,
        fallback_size=fallback_size,
        program=program,
    )
    if size_bytes is None:
        return None
    return size_bytes * 8


def are_types_equivalent(
    left_obj: Any = None,
    left_name: Optional[str] = None,
    right_obj: Any = None,
    right_name: Optional[str] = None,
) -> bool:
    """2つの型参照が等価かを判定する。"""
    if left_obj is not None and right_obj is not None:
        equivalent = _call_one_arg(left_obj, "isEquivalent", right_obj)
        if equivalent is not None:
            return bool(equivalent)
        left_path = get_data_type_path(left_obj)
        right_path = get_data_type_path(right_obj)
        if left_path and right_path:
            return left_path == right_path

    if left_obj is None or right_obj is None:
        return False
    left_display = normalize_type_name(get_data_type_display_name(left_obj, left_name))
    right_display = normalize_type_name(get_data_type_display_name(right_obj, right_name))
    return bool(left_display) and left_display == right_display


def clone_parameter_descriptor(
    param: Dict[str, Any],
    *,
    include_data_type_obj: bool = True,
) -> Dict[str, Any]:
    """パラメータ記述子を安全に複製する。"""
    cloned: Dict[str, Any] = {}
    for key, value in (param or {}).items():
        if key == "data_type_obj" and not include_data_type_obj:
            continue
        if isinstance(value, dict):
            cloned[key] = dict(value)
        elif isinstance(value, list):
            cloned[key] = list(value)
        else:
            cloned[key] = value
    return cloned


@source_converter
def parameter_descriptor_source(param: Dict[str, Any]) -> Any:
    """`clone_parameter_descriptor(param, include_data_type_obj=False)` と同じ値の JSON source。

    複製を先に作らず、walker が member を 1 つずつ写す（Issue #22 PR-22-D）。
    """

    from scripts.function_tracer_pcode.core.json_encoding import pairs_of

    return pairs_of(
        ((key, value) for key, value in (param or {}).items() if key != "data_type_obj"),
        _parameter_value_source,
    )


def _parameter_value_source(value: Any) -> Any:
    from scripts.function_tracer_pcode.core.json_encoding import as_dict, as_list, raw

    if isinstance(value, dict):
        return as_dict(value)
    if isinstance(value, list):
        return as_list(value)
    return raw(value)


def _call_zero_arg(obj: Any, method_name: str) -> Any:
    """0 引数メソッドを安全に呼び出す。"""
    method = getattr(obj, method_name, None)
    if not callable(method):
        return None
    try:
        return method()
    except Exception:
        return None


def _call_one_arg(obj: Any, method_name: str, arg: Any) -> Any:
    """1 引数メソッドを安全に呼び出す。"""
    method = getattr(obj, method_name, None)
    if not callable(method):
        return None
    try:
        return method(arg)
    except Exception:
        return None


def is_suspicious_undefined_data_type(
    data_type_obj: Any = None,
    *,
    expected_sizes: Optional[List[int]] = None,
) -> bool:
    """Ghidra の Undefined 系で、修正候補とみなす型か。"""
    if data_type_obj is None or not is_undefined_data_type(data_type_obj):
        return False
    if not expected_sizes:
        return True
    size = get_declared_type_size_bytes(data_type_obj)
    return size in set(expected_sizes)


@dataclass(frozen=True)
class ResolvedTypeSpec:
    """Program/ABI 文脈で具体化した型情報。"""

    type_name: str
    data_type_obj: Any = None
    size_bytes: Optional[int] = None
    is_signed: Optional[bool] = None
    source: str = "heuristic"
    data_type_path: Optional[str] = None

    def json_items(self):
        yield "type_name", self.type_name
        yield "source", self.source
        if self.size_bytes is not None:
            yield "size_bytes", self.size_bytes
        if self.is_signed is not None:
            yield "is_signed", self.is_signed
        if self.data_type_path:
            yield "data_type_path", self.data_type_path

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)

    @classmethod
    def from_dict(
        cls,
        payload: Optional[Dict[str, Any]],
        *,
        program: Any = None,
        fallback_signed: bool = True,
    ) -> Optional["ResolvedTypeSpec"]:
        if not isinstance(payload, dict):
            return None
        type_name = payload.get("type_name")
        if not type_name:
            return None

        size_bytes_raw = payload.get("size_bytes")
        size_bytes = None if size_bytes_raw is None else int(size_bytes_raw)
        is_signed_raw = payload.get("is_signed")
        is_signed = None if is_signed_raw is None else bool(is_signed_raw)
        resolved = resolve_type_spec(
            str(type_name),
            program=program,
            fallback_size=size_bytes,
            fallback_signed=is_signed if is_signed is not None else fallback_signed,
        )
        if resolved is not None:
            return cls(
                type_name=resolved.type_name or str(type_name),
                data_type_obj=resolved.data_type_obj,
                size_bytes=resolved.size_bytes if resolved.size_bytes is not None else size_bytes,
                is_signed=resolved.is_signed if resolved.is_signed is not None else is_signed,
                source=str(payload.get("source") or resolved.source or "serialized"),
                data_type_path=resolved.data_type_path or payload.get("data_type_path"),
            )
        return cls(
            type_name=str(type_name),
            data_type_obj=None,
            size_bytes=size_bytes,
            is_signed=is_signed,
            source=str(payload.get("source") or "serialized"),
            data_type_path=payload.get("data_type_path"),
        )


def _resolved_type_spec_from_data_type(
    type_name: str,
    data_type: Any,
    fallback_signed: bool,
    *,
    source: str = "ghidra_datatype",
) -> ResolvedTypeSpec:
    """Ghidra DataType から overlay 用の型情報を抽出する。"""
    resolved_name = get_data_type_display_name(data_type, type_name) or type_name
    size = get_declared_type_size_bytes(data_type, type_name)
    is_signed = get_declared_type_signedness(
        data_type,
        type_name,
        fallback_signed=fallback_signed,
    )
    data_type_path = get_data_type_path(data_type)

    return ResolvedTypeSpec(
        type_name=resolved_name or type_name,
        data_type_obj=data_type,
        size_bytes=size,
        is_signed=is_signed,
        source=source,
        data_type_path=data_type_path,
    )


def resolve_integer_type_spec(
    *,
    size_bytes: int,
    signed: bool,
    program: Any = None,
    data_type_manager: Any = None,
    source: Optional[str] = None,
) -> Optional[ResolvedTypeSpec]:
    """ビット幅と signedness から整数 DataType を解決する。"""
    dtm = data_type_manager or get_data_type_manager_for_reference(program=program)
    if dtm is None or size_bytes <= 0:
        return None

    try:
        from ghidra.program.model.data import AbstractIntegerDataType  # type: ignore[import]

        factory = (
            AbstractIntegerDataType.getSignedDataType
            if signed else
            AbstractIntegerDataType.getUnsignedDataType
        )
        data_type = factory(int(size_bytes), dtm)
    except Exception:
        data_type = None

    if data_type is None:
        canonical_names = {
            (True, 1): ["char", "int8_t"],
            (False, 1): ["unsigned char", "uint8_t"],
            (True, 2): ["short", "int16_t"],
            (False, 2): ["unsigned short", "uint16_t"],
            (True, 4): ["int", "int32_t"],
            (False, 4): ["unsigned int", "uint32_t"],
            (True, 8): ["long", "long long", "int64_t"],
            (False, 8): ["unsigned long", "unsigned long long", "uint64_t"],
        }.get((signed, int(size_bytes)), [])
        for type_name in canonical_names:
            data_type = _lookup_data_type_directly(dtm, type_name)
            if data_type is not None:
                break
        if data_type is None:
            return None

    return _resolved_type_spec_from_data_type(
        get_data_type_display_name(data_type) or "",
        data_type,
        fallback_signed=signed,
        source=source or "ghidra_integer_factory",
    )


def _parse_data_type_with_ghidra(
    data_type_manager: Any,
    type_name: str,
) -> Any:
    """Ghidra DataTypeParser を使って型名を解決する。"""
    try:
        from ghidra.util.data import DataTypeParser  # type: ignore[import]
    except Exception:
        return None

    allowed_types = getattr(DataTypeParser.AllowedDataTypes, "ALL", None)
    try:
        parser = DataTypeParser(data_type_manager, data_type_manager, None, allowed_types)
        return parser.parse(type_name)
    except Exception:
        return None


def _lookup_data_type_directly(
    data_type_manager: Any,
    type_name: str,
) -> Any:
    """DataTypeManager から直接型名を引く。"""
    candidates = [type_name]
    stripped = type_name.strip()
    if stripped and stripped not in candidates:
        candidates.append(stripped)
    if stripped and not stripped.startswith("/"):
        candidates.append(f"/{stripped}")

    for candidate in candidates:
        data_type = _call_one_arg(data_type_manager, "getDataType", candidate)
        if data_type is not None:
            return data_type
        data_type = _call_one_arg(data_type_manager, "findDataType", candidate)
        if data_type is not None:
            return data_type
    return None


def resolve_type_spec(
    type_name: Optional[str],
    *,
    data_type_obj: Any = None,
    program: Any = None,
    fallback_size: Optional[int] = None,
    fallback_signed: bool = True,
) -> Optional[ResolvedTypeSpec]:
    """型名を Program/ABI 文脈で具体化する。"""
    normalized = normalize_type_name(get_data_type_display_name(data_type_obj, type_name))
    if not normalized and data_type_obj is None:
        return None

    if data_type_obj is not None:
        return _resolved_type_spec_from_data_type(
            type_name or normalized,
            data_type_obj,
            fallback_signed=fallback_signed,
        )

    data_type_manager = None
    if program is not None:
        data_type_manager = _call_zero_arg(program, "getDataTypeManager")

    if data_type_manager is not None:
        data_type = _parse_data_type_with_ghidra(data_type_manager, type_name or normalized)
        if data_type is None:
            data_type = _lookup_data_type_directly(data_type_manager, type_name or normalized)
        if data_type is not None:
            return _resolved_type_spec_from_data_type(
                type_name or normalized,
                data_type,
                fallback_signed=fallback_signed,
            )
    return None


def resolve_signed_counterpart_spec(
    type_name: Optional[str],
    *,
    data_type_obj: Any = None,
    program: Any = None,
    fallback_size: Optional[int] = None,
) -> Optional[ResolvedTypeSpec]:
    """unsigned 整数型の signed counterpart を Ghidra API 優先で解決する。"""
    display_name = get_data_type_display_name(data_type_obj, type_name)
    if not display_name and data_type_obj is None:
        return None

    if is_void_data_type(data_type_obj, display_name):
        return None
    if is_pointer_data_type(data_type_obj, display_name):
        return None
    if not is_unsigned_data_type(data_type_obj, display_name):
        return None

    working_type_obj = data_type_obj
    if working_type_obj is None:
        current_spec = resolve_type_spec(
            type_name or display_name,
            program=program,
            fallback_size=fallback_size,
            fallback_signed=False,
        )
        if current_spec is not None:
            working_type_obj = current_spec.data_type_obj
            if fallback_size is None:
                fallback_size = current_spec.size_bytes

    if working_type_obj is not None:
        opposite = _call_zero_arg(working_type_obj, "getOppositeSignednessDataType")
        if opposite is not None and get_declared_type_signedness(
            opposite,
            get_data_type_display_name(opposite),
            fallback_signed=True,
        ):
            return _resolved_type_spec_from_data_type(
                display_name or type_name or "",
                opposite,
                True,
                source="ghidra_opposite_signedness",
            )

    data_type_manager = get_data_type_manager_for_reference(
        working_type_obj,
        program=program,
    )
    size_bytes = get_declared_type_size_bytes(
        working_type_obj,
        display_name or type_name,
        fallback_size=fallback_size,
        program=program,
    )
    if data_type_manager is None or size_bytes is None or size_bytes <= 0:
        return None

    try:
        return resolve_integer_type_spec(
            size_bytes=int(size_bytes),
            signed=True,
            data_type_manager=data_type_manager,
            source="ghidra_integer_factory",
        )
    except Exception:
        return None


def apply_type_name_to_parameter(
    param: Dict[str, Any],
    type_name: str,
    resolved_spec: Optional[ResolvedTypeSpec] = None,
) -> Dict[str, Any]:
    """パラメータ記述子へ型オーバーライドを適用する。"""
    updated = clone_parameter_descriptor(param, include_data_type_obj=True)
    if resolved_spec is None:
        return updated
    updated["data_type"] = (
        resolved_spec.type_name
        if resolved_spec is not None and resolved_spec.type_name
        else type_name
    )
    updated["data_type_obj"] = (
        resolved_spec.data_type_obj
        if resolved_spec is not None
        else updated.get("data_type_obj")
    )

    fallback_size = updated.get("size")
    inferred_size = (
        resolved_spec.size_bytes
        if resolved_spec is not None and resolved_spec.size_bytes is not None
        else fallback_size
    )
    if inferred_size is not None and inferred_size >= 0:
        updated["size"] = inferred_size
        storage = updated.get("storage")
        if isinstance(storage, dict):
            storage = dict(storage)
            storage["size"] = inferred_size
            storage["size_bits"] = inferred_size * 8
            updated["storage"] = storage

    if resolved_spec is not None and resolved_spec.is_signed is not None:
        updated["is_signed"] = resolved_spec.is_signed
    return updated


@dataclass(frozen=True)
class SignatureHypothesis:
    """関数シグネチャへ重ねる仮説的オーバーライド。"""

    return_type_override: Optional[str] = None
    parameter_type_overrides: Dict[int, str] = field(default_factory=dict)
    return_type_override_obj: Any = None
    parameter_type_override_objs: Dict[int, Any] = field(default_factory=dict)
    resolved_return_override: Optional[ResolvedTypeSpec] = None
    resolved_parameter_overrides: Dict[int, ResolvedTypeSpec] = field(default_factory=dict)
    phase: str = ""
    reason: str = ""
    evidence: Dict[str, Any] = field(default_factory=dict)

    def has_changes(self) -> bool:
        return (
            self.return_type_override is not None
            or bool(self.parameter_type_overrides)
        )

    def json_items(self):
        yield "return_type_override", self.return_type_override
        yield "parameter_type_overrides", as_dict(self.parameter_type_overrides)
        if self.resolved_return_override is not None:
            yield "resolved_return_override", self.resolved_return_override
        if self.resolved_parameter_overrides:
            yield "resolved_parameter_overrides", mapping_of(self.resolved_parameter_overrides)
        if self.phase:
            yield "phase", self.phase
        if self.reason:
            yield "reason", self.reason
        if self.evidence:
            yield "evidence", as_dict(self.evidence)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)

    @classmethod
    def from_dict(
        cls,
        payload: Optional[Dict[str, Any]],
        *,
        program: Any = None,
    ) -> "SignatureHypothesis":
        if not isinstance(payload, dict):
            return cls()

        parameter_type_overrides: Dict[int, str] = {}
        for raw_index, override_name in dict(payload.get("parameter_type_overrides") or {}).items():
            try:
                index = int(raw_index)
            except (TypeError, ValueError):
                continue
            if override_name is None:
                continue
            parameter_type_overrides[index] = str(override_name)

        resolved_return_override = ResolvedTypeSpec.from_dict(
            payload.get("resolved_return_override"),
            program=program,
        )
        resolved_parameter_overrides: Dict[int, ResolvedTypeSpec] = {}
        for raw_index, spec_payload in dict(payload.get("resolved_parameter_overrides") or {}).items():
            try:
                index = int(raw_index)
            except (TypeError, ValueError):
                continue
            resolved = ResolvedTypeSpec.from_dict(spec_payload, program=program)
            if resolved is not None:
                resolved_parameter_overrides[index] = resolved

        return cls(
            return_type_override=payload.get("return_type_override"),
            parameter_type_overrides=parameter_type_overrides,
            return_type_override_obj=(
                resolved_return_override.data_type_obj
                if resolved_return_override is not None
                else None
            ),
            parameter_type_override_objs={
                index: spec.data_type_obj
                for index, spec in resolved_parameter_overrides.items()
                if spec.data_type_obj is not None
            },
            resolved_return_override=resolved_return_override,
            resolved_parameter_overrides=resolved_parameter_overrides,
            phase=str(payload.get("phase") or ""),
            reason=str(payload.get("reason") or ""),
            evidence=dict(payload.get("evidence") or {}),
        )

    def describe(self) -> str:
        parts: List[str] = []
        if self.return_type_override is not None:
            parts.append(f"return={self.return_type_override}")
        if self.parameter_type_overrides:
            parts.append(f"params={self.parameter_type_overrides}")
        payload = ", ".join(parts) if parts else "no-op"
        prefix = self.phase or "signature_hypothesis"
        if self.reason:
            return f"{prefix}: {self.reason} ({payload})"
        return f"{prefix}: {payload}"


@dataclass
class FunctionSignature:
    """関数シグネチャ情報"""

    return_type: Optional[str] = None
    return_type_obj: Any = None
    parameters: Optional[List[Dict[str, Any]]] = None

    def format_return_type(self) -> str:
        """戻り値の型をフォーマット"""
        return get_data_type_display_name(self.return_type_obj, self.return_type) or "unknown"

    def format_parameters(self) -> str:
        """引数リストをフォーマット（例: (int a, long b)）"""
        if not self.parameters:
            return "(void)"

        param_strs = []
        for p in self.parameters:
            dtype = get_data_type_display_name(
                p.get("data_type_obj"),
                p.get("data_type", "unknown"),
            ) or "unknown"
            name = p.get("name", "")
            if name:
                param_strs.append(f"{dtype} {name}")
            else:
                param_strs.append(dtype)

        return f"({', '.join(param_strs)})"

    def format_full(self, func_name: str) -> str:
        """完全なシグネチャをフォーマット（例: int func(int a, long b)）"""
        return f"{self.format_return_type()} {func_name}{self.format_parameters()}"

    def json_items(self):
        yield "return_type", self.format_return_type()
        yield "parameters", (
            None if self.parameters is None
            else each(self.parameters, parameter_descriptor_source)
        )

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)

    def clone(self) -> "FunctionSignature":
        return FunctionSignature(
            return_type=self.return_type,
            return_type_obj=self.return_type_obj,
            parameters=[
                clone_parameter_descriptor(param, include_data_type_obj=True)
                for param in (self.parameters or [])
            ],
        )

    def apply_hypothesis(
        self,
        hypothesis: SignatureHypothesis,
    ) -> Tuple["FunctionSignature", bool, bool]:
        """仮説オーバーライドを適用した新しいシグネチャを返す。"""
        updated_return_type = self.return_type
        updated_return_type_obj = self.return_type_obj
        return_changed = False
        param_changed = False

        if (
            hypothesis.return_type_override is not None
            or hypothesis.return_type_override_obj is not None
        ):
            if not are_types_equivalent(
                updated_return_type_obj,
                updated_return_type,
                hypothesis.return_type_override_obj,
                hypothesis.return_type_override,
            ):
                if hypothesis.resolved_return_override is not None:
                    updated_return_type = hypothesis.resolved_return_override.type_name
                    updated_return_type_obj = hypothesis.resolved_return_override.data_type_obj
                else:
                    updated_return_type = hypothesis.return_type_override
                    updated_return_type_obj = hypothesis.return_type_override_obj
                return_changed = True

        updated_params = [
            clone_parameter_descriptor(param, include_data_type_obj=True)
            for param in (self.parameters or [])
        ]
        if updated_params and hypothesis.parameter_type_overrides:
            for index, new_type in sorted(hypothesis.parameter_type_overrides.items()):
                if index < 0 or index >= len(updated_params):
                    continue
                current_type = updated_params[index].get("data_type")
                current_type_obj = updated_params[index].get("data_type_obj")
                if are_types_equivalent(
                    current_type_obj,
                    current_type,
                    hypothesis.parameter_type_override_objs.get(index),
                    new_type,
                ):
                    continue
                resolved_spec = hypothesis.resolved_parameter_overrides.get(index)
                updated_params[index] = apply_type_name_to_parameter(
                    updated_params[index],
                    new_type,
                    resolved_spec=resolved_spec,
                )
                param_changed = True

        return (
            FunctionSignature(
                return_type=updated_return_type,
                return_type_obj=updated_return_type_obj,
                parameters=updated_params,
            ),
            return_changed,
            param_changed,
        )

    @classmethod
    def from_analysis(cls, analysis: "FunctionReturnAnalysis") -> "FunctionSignature":
        """FunctionReturnAnalysisからシグネチャを抽出"""
        return cls(
            return_type=analysis.return_type,
            return_type_obj=getattr(analysis, "return_type_obj", None),
            parameters=[
                clone_parameter_descriptor(param, include_data_type_obj=True)
                for param in (analysis.parameters or [])
            ],
        )


def format_signature_text(payload: Any, func_name: str) -> str:
    """`FunctionSignature.format_full` と同じ text を、表現（出力の signature）から作る。"""

    payload = payload or {}
    parameters = payload.get("parameters") or ()
    if not parameters:
        params = "(void)"
    else:
        parts = []
        for param in parameters:
            param = param if isinstance(param, Mapping) else {}
            dtype = param.get("data_type", "unknown") or "unknown"
            name = param.get("name", "")
            parts.append(f"{dtype} {name}" if name else str(dtype))
        params = f"({', '.join(parts)})"
    return f"{payload.get('return_type') or 'unknown'} {func_name}{params}"
