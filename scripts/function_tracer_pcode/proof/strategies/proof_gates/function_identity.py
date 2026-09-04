"""Deterministic function identity, signature keys and identity freezing."""

from __future__ import annotations

from typing import Any, Mapping, Optional, Tuple
from scripts.function_tracer_pcode.core import FunctionReturnAnalysis


def _impl__deterministic_function_identity(
    cls,
    analysis: FunctionReturnAnalysis,
) -> Tuple[Any, ...]:
    binary_id = getattr(analysis, "binary_id", None)
    normalized_binary_id = str(binary_id).strip() if binary_id is not None and str(binary_id).strip() else "unknown_binary"
    binary_name = getattr(analysis, "binary_name", None)
    normalized_binary_name = str(binary_name).strip() if binary_name is not None and str(binary_name).strip() else "unknown_binary_name"
    language_id = (
        getattr(analysis, "language_id", None)
        or getattr(analysis, "program_language_id", None)
        or getattr(analysis, "architecture_language_id", None)
    )
    normalized_language_id = str(language_id).strip() if language_id is not None and str(language_id).strip() else "unknown_language"
    compiler_artifact = (
        getattr(analysis, "compiler_artifact_identity", None)
        or getattr(analysis, "compiler_spec_id", None)
        or getattr(analysis, "compiler_id", None)
    )
    normalized_compiler = (
        str(compiler_artifact).strip()
        if compiler_artifact is not None and str(compiler_artifact).strip()
        else "unknown_compiler_artifact"
    )
    calling_convention = (
        getattr(analysis, "calling_convention", None)
        or getattr(analysis, "calling_convention_name", None)
    )
    normalized_calling_convention = (
        str(calling_convention).strip()
        if calling_convention is not None and str(calling_convention).strip()
        else "unknown_calling_convention"
    )
    return (
        "function_identity",
        ("identity_schema_version", cls._RETURN_COVERAGE_TARGET_SCHEMA_VERSION),
        (
            "binary_identity",
            ("binary_id", normalized_binary_id),
            ("binary_name", normalized_binary_name),
            ("language_id", normalized_language_id),
            ("compiler_artifact", normalized_compiler),
        ),
        ("function_name", cls._identity_freeze(getattr(analysis, "function_name", None))),
        ("entry_offset", cls._analysis_entry_offset(analysis)),
        ("entry_point", cls._identity_freeze(getattr(analysis, "entry_point", None))),
        ("signature", cls._normalized_function_signature_key(analysis)),
        ("calling_convention", normalized_calling_convention),
    )


def _impl__analysis_entry_offset(cls, analysis: FunctionReturnAnalysis) -> Optional[int]:
    function_ref = getattr(analysis, "function_ref", None)
    for value in (
        getattr(function_ref, "entry_offset", None),
        getattr(function_ref, "address_offset", None),
        getattr(analysis, "entry_point", None),
    ):
        try:
            return int(str(value), 0)
        except (TypeError, ValueError):
            continue
    return None


def _impl__normalized_function_signature_key(
    cls,
    analysis: FunctionReturnAnalysis,
) -> Tuple[Any, ...]:
    parameters = []
    for param in getattr(analysis, "parameters", ()) or ():
        if isinstance(param, Mapping):
            param_index = param.get("index")
            try:
                param_index = int(param_index)
            except (TypeError, ValueError):
                param_index = None
            parameters.append(
                (
                    "parameter",
                    ("index", param_index),
                    ("name", cls._identity_freeze(param.get("name"))),
                    ("data_type", cls._identity_freeze(param.get("data_type"))),
                    ("size", cls._identity_freeze(param.get("size"))),
                    ("is_signed", cls._identity_freeze(param.get("is_signed"))),
                    ("storage", cls._identity_freeze(param.get("storage"))),
                )
            )
        else:
            parameters.append(("parameter", cls._identity_freeze(param)))
    parameters.sort(key=repr)
    return (
        "function_signature",
        ("return_type", cls._identity_freeze(getattr(analysis, "return_type", None))),
        ("return_storage", cls._identity_freeze(cls._return_storage_static_key(analysis))),
        ("parameters", tuple(parameters)),
    )


def _impl__return_storage_static_key(analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    surface = None
    surface_getter = getattr(analysis, "get_comparison_surface", None)
    if callable(surface_getter):
        try:
            surface = surface_getter()
        except (AttributeError, TypeError, ValueError, RecursionError):
            surface = None
    return (
        "return_storage",
        getattr(surface, "kind", None),
        getattr(surface, "explicit_bit_width", None),
        getattr(surface, "use_sign_extension", None),
        getattr(analysis, "return_type", None),
    )


def _impl__identity_freeze(cls, value: Any) -> Any:
    if isinstance(value, Mapping):
        return tuple(
            (str(key), cls._identity_freeze(item))
            for key, item in sorted(value.items(), key=lambda item: str(item[0]))
        )
    if isinstance(value, (tuple, list)):
        return tuple(cls._identity_freeze(item) for item in value)
    if isinstance(value, (set, frozenset)):
        return tuple(sorted((cls._identity_freeze(item) for item in value), key=repr))
    if isinstance(value, bool):
        return bool(value)
    if isinstance(value, int):
        return int(value)
    if isinstance(value, str):
        return str(value)
    if value is None:
        return None
    if isinstance(value, float):
        return ("float", repr(value))
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            return cls._identity_freeze(stable_key())
        except (AttributeError, TypeError, ValueError, RecursionError):
            pass
    return ("opaque", type(value).__module__, type(value).__qualname__)
