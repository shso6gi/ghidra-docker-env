# -*- coding: utf-8 -*-
"""Call target references backed by Ghidra objects / addresses."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Optional, Tuple, Union
from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.json_encoding import materialize


_JVM_NOT_RUNNING_MESSAGES = frozenset({
    "JVM is not running",
    "Java Virtual Machine is not running",
})


def _is_jvm_not_running_error(error: Exception) -> bool:
    try:
        from jpype import JVMNotRunning
    except ImportError:
        JVMNotRunning = ()  # type: ignore[assignment]
    return (
        isinstance(error, JVMNotRunning)
        or str(error) in _JVM_NOT_RUNNING_MESSAGES
    )


def _safe_getattr(owner: Any, name: str) -> Any:
    """Read a proxy attribute without leaking JVM-shutdown races."""
    try:
        return getattr(owner, name, None)
    except Exception as error:
        if _is_jvm_not_running_error(error):
            return None
        raise


def _safe_offset(address_or_value: Any) -> Optional[int]:
    if address_or_value is None:
        return None
    if isinstance(address_or_value, int):
        return address_or_value if address_or_value >= 0 else None
    get_offset = _safe_getattr(address_or_value, "getOffset")
    if callable(get_offset):
        try:
            offset = int(get_offset())
            return offset if offset >= 0 else None
        except Exception:
            return None
    try:
        offset = int(address_or_value)
        return offset if offset >= 0 else None
    except Exception:
        return None


def _safe_program_id(owner: Any) -> Optional[int]:
    if owner is None:
        return None

    program = owner
    get_program = _safe_getattr(owner, "getProgram")
    if callable(get_program):
        try:
            program = get_program()
        except Exception:
            program = owner

    get_unique_program_id = _safe_getattr(program, "getUniqueProgramID")
    if callable(get_unique_program_id):
        try:
            return int(get_unique_program_id())
        except Exception:
            return None
    return None


def _safe_bool_method(owner: Any, method_name: str) -> Optional[bool]:
    method = _safe_getattr(owner, method_name)
    if not callable(method):
        return None
    try:
        return bool(method())
    except Exception:
        return None


def _safe_external_library_name(function: Any) -> Optional[str]:
    if function is None:
        return None
    get_external_location = _safe_getattr(function, "getExternalLocation")
    if not callable(get_external_location):
        return None
    try:
        external_location = get_external_location()
    except Exception:
        return None
    if external_location is None:
        return None
    for method_name in ("getLibraryName", "getOriginalImportedName"):
        method = _safe_getattr(external_location, method_name)
        if not callable(method):
            continue
        try:
            value = method()
        except Exception:
            value = None
        if isinstance(value, str) and value:
            return value
    return None


def _safe_thunked_function(function: Any) -> Any:
    if function is None:
        return None
    method = _safe_getattr(function, "getThunkedFunction")
    if not callable(method):
        return None
    for args in ((True,), (False,), ()):
        try:
            thunked = method(*args)
        except Exception:
            continue
        if thunked is not None and thunked is not function:
            return thunked
    return None


@dataclass(frozen=True)
class CallTargetRef:
    """Stable call target identity for runtime analysis."""

    kind: str
    function_name: Optional[str] = None
    program_id: Optional[int] = None
    entry_offset: Optional[int] = None
    address_offset: Optional[int] = None
    display_hint: Optional[str] = None
    is_external: Optional[bool] = None
    library_name: Optional[str] = None
    is_thunk: Optional[bool] = None
    thunked_is_external: Optional[bool] = None
    thunked_library_name: Optional[str] = None
    function_obj: Any = field(default=None, compare=False, hash=False, repr=False)

    def __post_init__(self) -> None:
        if self.kind not in {"function", "code_address", "unknown"}:
            raise ValueError(f"Unsupported call target kind: {self.kind}")

    @classmethod
    def from_function(cls, function) -> "CallTargetRef":
        name = None
        entry_offset = None
        program_id = _safe_program_id(function)
        if function is not None:
            get_name = _safe_getattr(function, "getName")
            if callable(get_name):
                try:
                    name = get_name()
                except Exception:
                    name = None
            get_entry = _safe_getattr(function, "getEntryPoint")
            if callable(get_entry):
                try:
                    entry_offset = _safe_offset(get_entry())
                except Exception:
                    entry_offset = None
        is_external = _safe_bool_method(function, "isExternal")
        library_name = _safe_external_library_name(function)
        is_thunk = _safe_bool_method(function, "isThunk")
        thunked = _safe_thunked_function(function)
        thunked_is_external = _safe_bool_method(thunked, "isExternal") if thunked is not None else None
        thunked_library_name = _safe_external_library_name(thunked) if thunked is not None else None
        return cls(
            kind="function",
            function_name=name,
            program_id=program_id,
            entry_offset=entry_offset,
            address_offset=entry_offset,
            display_hint=name,
            is_external=is_external,
            library_name=library_name,
            is_thunk=is_thunk,
            thunked_is_external=thunked_is_external,
            thunked_library_name=thunked_library_name,
            function_obj=function,
        )

    @classmethod
    def from_code_address(
        cls,
        address_value: int,
        display_hint: Optional[str] = None,
        *,
        program_id: Optional[int] = None,
    ) -> "CallTargetRef":
        normalized = _safe_offset(address_value)
        return cls(
            kind="code_address",
            program_id=program_id,
            address_offset=normalized,
            display_hint=display_hint,
        )

    @classmethod
    def from_name(
        cls,
        function_name: str,
        *,
        program_id: Optional[int] = None,
        entry_offset: Optional[int] = None,
        is_external: Optional[bool] = None,
        library_name: Optional[str] = None,
        is_thunk: Optional[bool] = None,
        thunked_is_external: Optional[bool] = None,
        thunked_library_name: Optional[str] = None,
        function_obj: Any = None,
    ) -> "CallTargetRef":
        return cls(
            kind="function",
            function_name=function_name or None,
            program_id=program_id,
            entry_offset=_safe_offset(entry_offset),
            address_offset=_safe_offset(entry_offset),
            display_hint=function_name or None,
            is_external=is_external,
            library_name=library_name,
            is_thunk=is_thunk,
            thunked_is_external=thunked_is_external,
            thunked_library_name=thunked_library_name,
            function_obj=function_obj,
        )

    @classmethod
    def unknown(cls, display_hint: Optional[str] = None) -> "CallTargetRef":
        return cls(kind="unknown", display_hint=display_hint)

    def is_function(self) -> bool:
        # kind は `__post_init__` が検査した文字列（owner の API で基底型の値として比べる）
        return live_values.str_value(self.kind) == "function"

    def is_code_address(self) -> bool:
        return live_values.str_value(self.kind) == "code_address"

    def is_unknown(self) -> bool:
        return live_values.str_value(self.kind) == "unknown"

    def stable_key(self) -> Tuple[Any, ...]:
        if self.is_function():
            if self.entry_offset is not None:
                return ("function", self.program_id, self.entry_offset)
            if self.is_external is True and self.function_name:
                if not self.library_name:
                    return ("external_function_unscoped", self.function_name, self.program_id)
                return (
                    "external_function",
                    self.library_name,
                    self.function_name,
                    self.program_id,
                )
            if self.function_name:
                return ("function_name_only", self.program_id, self.function_name)
            return ("function", self.program_id, None)
        if self.is_code_address():
            return ("code_address", self.program_id, self.address_offset)
        return ("unknown", self.program_id)

    def analysis_key(self) -> Optional[Tuple[Any, ...]]:
        if self.is_unknown():
            return None
        if self.is_code_address() and self.address_offset is None:
            return None
        if (
            self.is_function()
            and self.entry_offset is None
        ):
            if self.is_external is True and self.function_name and self.library_name:
                return self.stable_key()
            return None
        return self.stable_key()

    def display_name(self) -> str:
        # field は owner の API で読む（出力の入口から live な値として辿られる）
        function_name = self.function_name
        if function_name is not None and live_values.as_bool(function_name):
            return function_name
        display_hint = self.display_hint
        address_offset = self.address_offset
        if self.is_code_address() and address_offset is not None:
            if display_hint is not None and live_values.as_bool(display_hint):
                return display_hint
            return f"ADDR_{live_values.as_int(address_offset):x}"
        entry_offset = self.entry_offset
        if self.is_function() and entry_offset is not None:
            return f"sub_{live_values.as_int(entry_offset):x}"
        if display_hint is not None and live_values.as_bool(display_hint):
            return display_hint
        return "UNKNOWN_FUNC"

    def placeholder_name(self) -> str:
        return self.display_name()

    def json_items(self):
        yield "kind", self.kind
        yield "display_name", self.display_name()
        if self.function_name is not None and live_values.as_bool(self.function_name):
            yield "function_name", self.function_name
        if self.program_id is not None:
            yield "program_id", self.program_id
        if self.entry_offset is not None:
            yield "entry_offset", self.entry_offset
        if self.address_offset is not None:
            yield "address_offset", self.address_offset
        if self.is_external is not None:
            yield "is_external", self.is_external
        if self.library_name is not None and live_values.as_bool(self.library_name):
            yield "library_name", self.library_name
        if self.is_thunk is not None:
            yield "is_thunk", self.is_thunk
        if self.thunked_is_external is not None:
            yield "thunked_is_external", self.thunked_is_external
        if self.thunked_library_name is not None and live_values.as_bool(self.thunked_library_name):
            yield "thunked_library_name", self.thunked_library_name

    def to_dict(self) -> dict:
        return materialize(self)


def coerce_call_target_ref(target: Union["CallTargetRef", str, None]) -> Optional["CallTargetRef"]:
    if live_values.is_kind(target, CallTargetRef):
        return target
    if target is None:
        return None
    return None


def _declared_return_data_type(function_obj: Any) -> Any:
    """関数オブジェクトの宣言戻り型を返す。宣言が無いに等しい型は None にする。

    void / undefined は「型が取れていない」のと区別できないので、authority には
    しない。
    """
    if function_obj is None:
        return None
    getter = _safe_getattr(function_obj, "getReturnType")
    if not callable(getter):
        return None
    try:
        return_type = getter()
    except Exception:
        return None
    if return_type is None:
        return None
    from scripts.function_tracer_pcode.core.signature import (
        is_undefined_data_type,
        is_void_data_type,
    )

    try:
        if is_void_data_type(return_type) or is_undefined_data_type(return_type):
            return None
    except Exception:
        return None
    return return_type


def call_target_declared_return_data_types(target_ref: Any) -> Tuple[Any, ...]:
    """call target の宣言戻り型候補を返す。

    thunk の場合、Ghidra 上は wrapper 側と thunk target 側の双方が宣言を持ち得る。
    ``CallTargetRef`` が external 分類で両方を記録している（``is_external`` と
    ``thunked_is_external``）のと同じ方針で、ここでも双方を候補として返し、
    どちらを authority とするかは呼び出し側が決める。thunk target を先に置く。

    void / undefined の宣言と、取得できなかった宣言は候補に含めない。
    """
    function_obj = _safe_getattr(target_ref, "function_obj")
    if function_obj is None:
        return ()
    declarations: list = []
    for candidate in (_safe_thunked_function(function_obj), function_obj):
        declared = _declared_return_data_type(candidate)
        if declared is not None:
            declarations.append(declared)
    return tuple(declarations)


def call_target_returns_floating_value(target_ref: Any) -> bool:
    """call target の宣言戻り型が浮動小数点型かどうかを typed provenance から返す。

    シンボル名（``log`` / ``sqrt`` 等）は根拠にしない。

    thunk では thunk target の宣言を authority とし、thunk target 側の宣言が
    取れない場合だけ wrapper 側の宣言を使う。両方に宣言があって浮動小数点かどうかで
    食い違う場合は、どちらを信じるべきかが決まらないので証拠にしない（False）。
    宣言が 1 つも取れない場合も False（fail-closed）。
    """
    declarations = call_target_declared_return_data_types(target_ref)
    if not declarations:
        return False
    from scripts.function_tracer_pcode.core.signature import is_floating_data_type

    verdicts = set()
    for declared in declarations:
        try:
            verdicts.add(bool(is_floating_data_type(declared)))
        except Exception:
            return False
    if len(verdicts) != 1:
        # wrapper と thunk target の宣言が食い違う。曖昧なまま float 側に倒さない。
        return False
    return verdicts.pop()
