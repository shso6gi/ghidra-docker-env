# -*- coding: utf-8 -*-
"""Call target references backed by Ghidra objects / addresses."""

from __future__ import annotations

from dataclasses import dataclass, field
import re
from typing import Any, Optional, Tuple, Union


_RAW_CODE_TARGET_PATTERN = re.compile(r"ADDR_([0-9a-fA-F]+)")


def _safe_offset(address_or_value: Any) -> Optional[int]:
    if address_or_value is None:
        return None
    if isinstance(address_or_value, int):
        return address_or_value if address_or_value >= 0 else None
    get_offset = getattr(address_or_value, "getOffset", None)
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


@dataclass(frozen=True)
class CallTargetRef:
    """Stable call target identity for runtime analysis."""

    kind: str
    function_name: Optional[str] = None
    entry_offset: Optional[int] = None
    address_offset: Optional[int] = None
    display_hint: Optional[str] = None
    function_obj: Any = field(default=None, compare=False, hash=False, repr=False)

    def __post_init__(self) -> None:
        if self.kind not in {"function", "code_address", "unknown"}:
            raise ValueError(f"Unsupported call target kind: {self.kind}")

    @classmethod
    def from_function(cls, function) -> "CallTargetRef":
        name = None
        entry_offset = None
        if function is not None:
            get_name = getattr(function, "getName", None)
            if callable(get_name):
                try:
                    name = get_name()
                except Exception:
                    name = None
            get_entry = getattr(function, "getEntryPoint", None)
            if callable(get_entry):
                try:
                    entry_offset = _safe_offset(get_entry())
                except Exception:
                    entry_offset = None
        return cls(
            kind="function",
            function_name=name,
            entry_offset=entry_offset,
            address_offset=entry_offset,
            display_hint=name,
            function_obj=function,
        )

    @classmethod
    def from_code_address(
        cls,
        address_value: int,
        display_hint: Optional[str] = None,
    ) -> "CallTargetRef":
        normalized = _safe_offset(address_value)
        return cls(
            kind="code_address",
            address_offset=normalized,
            display_hint=display_hint,
        )

    @classmethod
    def from_name(
        cls,
        function_name: str,
        *,
        entry_offset: Optional[int] = None,
        function_obj: Any = None,
    ) -> "CallTargetRef":
        return cls(
            kind="function",
            function_name=function_name or None,
            entry_offset=_safe_offset(entry_offset),
            address_offset=_safe_offset(entry_offset),
            display_hint=function_name or None,
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
                return ("function", self.entry_offset)
            if self.function_name:
                return ("function_name", self.function_name)
        if self.is_code_address():
            return ("code_address", self.address_offset)
        return ("unknown", self.display_hint)

    def analysis_key(self) -> Optional[Tuple[Any, ...]]:
        if self.is_unknown():
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
        if self.entry_offset is not None:
            result["entry_offset"] = self.entry_offset
        if self.address_offset is not None:
            result["address_offset"] = self.address_offset
        return result


def coerce_call_target_ref(target: Union["CallTargetRef", str, None]) -> Optional["CallTargetRef"]:
    if isinstance(target, CallTargetRef):
        return target
    if target is None:
        return None
    if isinstance(target, str):
        if not target or target == "UNKNOWN_FUNC":
            return CallTargetRef.unknown(target or None)
        match = _RAW_CODE_TARGET_PATTERN.fullmatch(target)
        if match:
            try:
                return CallTargetRef.from_code_address(int(match.group(1), 16), display_hint=target)
            except Exception:
                return CallTargetRef.unknown(target)
        return CallTargetRef.from_name(target)
    return None
