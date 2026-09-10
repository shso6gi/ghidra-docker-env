# -*- coding: utf-8 -*-
"""Call target references backed by Ghidra objects / addresses."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Optional, Tuple, Union


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
        return self.kind == "function"

    def is_code_address(self) -> bool:
        return self.kind == "code_address"

    def is_unknown(self) -> bool:
        return self.kind == "unknown"

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
        if self.function_name:
            return self.function_name
        if self.is_code_address() and self.address_offset is not None:
            return self.display_hint or f"ADDR_{self.address_offset:x}"
        if self.is_function() and self.entry_offset is not None:
            return f"sub_{self.entry_offset:x}"
        if self.display_hint:
            return self.display_hint
        return "UNKNOWN_FUNC"

    def placeholder_name(self) -> str:
        return self.display_name()

    def to_dict(self) -> dict:
        result = {
            "kind": self.kind,
            "display_name": self.display_name(),
        }
        if self.function_name:
            result["function_name"] = self.function_name
        if self.program_id is not None:
            result["program_id"] = self.program_id
        if self.entry_offset is not None:
            result["entry_offset"] = self.entry_offset
        if self.address_offset is not None:
            result["address_offset"] = self.address_offset
        if self.is_external is not None:
            result["is_external"] = self.is_external
        if self.library_name:
            result["library_name"] = self.library_name
        if self.is_thunk is not None:
            result["is_thunk"] = self.is_thunk
        if self.thunked_is_external is not None:
            result["thunked_is_external"] = self.thunked_is_external
        if self.thunked_library_name:
            result["thunked_library_name"] = self.thunked_library_name
        return result


def coerce_call_target_ref(target: Union["CallTargetRef", str, None]) -> Optional["CallTargetRef"]:
    if isinstance(target, CallTargetRef):
        return target
    if target is None:
        return None
    return None


def call_target_declared_return_data_type(target_ref: Any) -> Any:
    """解決済み call target の宣言戻り型 DataType を返す（得られなければ None）。"""
    function_obj = _safe_getattr(target_ref, "function_obj")
    if function_obj is None:
        return None
    for candidate in (function_obj, _safe_thunked_function(function_obj)):
        if candidate is None:
            continue
        getter = _safe_getattr(candidate, "getReturnType")
        if not callable(getter):
            continue
        try:
            return_type = getter()
        except Exception:
            continue
        if return_type is not None:
            return return_type
    return None


def call_target_returns_floating_value(target_ref: Any) -> bool:
    """call target の宣言戻り型が浮動小数点型かどうかを typed provenance から返す。

    シンボル名（``log`` / ``sqrt`` 等）は根拠にしない。宣言型が取得できない場合は
    False を返す（fail-closed）。
    """
    return_type = call_target_declared_return_data_type(target_ref)
    if return_type is None:
        return False
    from scripts.function_tracer_pcode.core.signature import is_floating_data_type

    try:
        return bool(is_floating_data_type(return_type))
    except Exception:
        return False
