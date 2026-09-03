"""Descriptors and small helpers shared by the P-code tracer and its mixins."""

from __future__ import annotations

from dataclasses import dataclass
import inspect
from typing import Callable, Optional, Any
from scripts.function_tracer_pcode.core import StorageInfo


def _callable_accepts_positional_args(fn: Callable, count: int) -> bool:
    try:
        signature = inspect.signature(fn)
    except (TypeError, ValueError):
        return True
    positional_count = 0
    for param in signature.parameters.values():
        if param.kind == inspect.Parameter.VAR_POSITIONAL:
            return True
        if param.kind in {
            inspect.Parameter.POSITIONAL_ONLY,
            inspect.Parameter.POSITIONAL_OR_KEYWORD,
        }:
            positional_count += 1
    return positional_count >= count


@dataclass(frozen=True)
class ParameterStorageDescriptor:
    """Storage-backed parameter identity collected from Ghidra objects."""

    name: str
    index: int
    size_bytes: int
    is_signed: bool
    data_type: Optional[str]
    data_type_obj: Any
    storage_info: Optional[StorageInfo]
