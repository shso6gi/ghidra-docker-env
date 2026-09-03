"""Callee parameter identities, explicit/format argument evidence and data-type name classification."""

from __future__ import annotations

from typing import Dict, List, Optional, Sequence, Set, Tuple
from scripts.function_tracer_pcode.analysis.effects._shared import (
    AddressValueRef,
    Expression,
    ExpressionType,
    _FIXED_PREFIX_FORMAT_CALL_TARGETS,
)
from scripts.function_tracer_pcode.analysis.effects._api import (
    _address_ref_is_readonly_format_data,
    _call_input_storages_for_explicit_args,
    _coerce_storage_info,
    _data_type_name_has_pointer_marker,
    _data_type_name_is_undefined,
    _enumerate_constant_expression_branches,
    _explicit_call_argument_window_matches_storage,
    _expression_has_format_pointer_evidence,
    _expressions_equivalent,
    _normalize_type_display_name,
    _normalized_fixed_prefix_target_name,
    _parameter_descriptor_from_expression,
    _parameter_descriptor_looks_pointer,
    _parameter_descriptors_share_identity,
    _parameter_identity_keys_from_descriptor,
    _resolve_call_target_name,
    _resolve_parameter_descriptor,
    _storage_matches_parameter,
    canonicalize_location,
)


def _impl__call_evidence_callee_param_identities(
    callee_parameters: Sequence[Dict],
) -> Tuple[Tuple[object, ...], ...]:
    identities: List[Tuple[object, ...]] = []
    for param in callee_parameters or ():
        param_keys = sorted(_parameter_identity_keys_from_descriptor(param), key=repr)
        if not param_keys:
            return ()
        identities.append(tuple(param_keys))
    return tuple(identities)


def _impl__callee_param_identities_are_object_proven(
    identities: Sequence[Tuple[object, ...]],
) -> bool:
    for identity in identities or ():
        if not identity:
            return False
        if identity[0] == "callee_parameter_ordinal":
            return False
    return True


def _impl__expression_declares_pointer_type(expr: Expression) -> bool:
    return _parameter_descriptor_looks_pointer(_parameter_descriptor_from_expression(expr))


def _impl__explicit_argument_is_safe_immediate_for_callee_param(
    expr: Optional[Expression],
    callee_param: Optional[Dict],
    caller_parameters: Sequence[Dict],
) -> bool:
    if expr is None or callee_param is None:
        return False
    if expr.expr_type != ExpressionType.CONSTANT:
        return False
    callee_storage = _coerce_storage_info(callee_param.get("storage"))
    if callee_storage is None:
        return False
    for caller_param in caller_parameters or ():
        caller_storage = _coerce_storage_info(caller_param.get("storage"))
        if caller_storage is not None and _storage_matches_parameter(caller_storage, callee_storage):
            return False
    try:
        expr_size = int(getattr(expr, "size", 0) or 0)
    except Exception:
        expr_size = 0
    try:
        param_size = int((callee_param or {}).get("size") or 0)
    except Exception:
        param_size = 0
    if expr_size > 0 and param_size > 0 and expr_size > param_size:
        return False
    return True


def _impl__fixed_prefix_argument_window_has_evidence(
    call_op,
    tracer,
    callee_parameters: Sequence[Dict],
    explicit_args: Sequence[Expression],
    selected: Sequence[Expression],
    format_index: int,
) -> bool:
    param_storages = [
        _coerce_storage_info(callee_param.get("storage"))
        for callee_param in callee_parameters
    ]
    input_storages = _call_input_storages_for_explicit_args(call_op, tracer, explicit_args)
    if input_storages is not None and any(storage is not None for storage in input_storages):
        if (
            not any(storage is None for storage in param_storages)
            and _explicit_call_argument_window_matches_storage(
                input_storages[:len(selected)],
                selected,
                param_storages,
            )
        ):
            return True

    if format_index < 0 or format_index >= len(selected):
        return False
    return _expression_has_format_pointer_evidence(selected[format_index], tracer)


def _impl__expression_has_format_pointer_evidence(
    expr: Optional[Expression],
    tracer=None,
    seen: Optional[Set[int]] = None,
) -> bool:
    if expr is None:
        return False
    if seen is None:
        seen = set()
    expr_id = id(expr)
    if expr_id in seen:
        return False
    seen.add(expr_id)
    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, AddressValueRef):
        return _address_ref_is_readonly_format_data(runtime_ref)
    if expr.expr_type == ExpressionType.PHI and expr.value:
        return all(
            _expression_has_format_pointer_evidence(value, tracer, set(seen))
            for _condition, value in expr.value
        )
    if expr.expr_type != ExpressionType.CONSTANT:
        return False

    try:
        address_value = int(expr.value)
    except Exception:
        return False
    resolver = getattr(tracer, "_make_address_runtime_ref_for_offset", None)
    if not callable(resolver):
        return False
    try:
        resolved_ref = resolver(
            address_value,
            display_name=f"format_string_{address_value:x}",
            require_ghidra_evidence=True,
        )
    except Exception:
        return False
    return isinstance(resolved_ref, AddressValueRef) and _address_ref_is_readonly_format_data(resolved_ref)


def _impl__address_ref_is_readonly_format_data(runtime_ref: AddressValueRef) -> bool:
    return runtime_ref.is_readonly_memory() and getattr(runtime_ref, "can_execute", None) is False


def _impl__fixed_prefix_format_recovery_spec(
    call_op,
    tracer,
    callee_parameters: Sequence[Dict],
) -> Optional[Tuple[int, int]]:
    target_name = _normalized_fixed_prefix_target_name(_resolve_call_target_name(tracer, call_op))
    spec = _FIXED_PREFIX_FORMAT_CALL_TARGETS.get(target_name)
    if spec is None:
        return None
    fixed_prefix_len, format_index = spec
    if len(callee_parameters or ()) != fixed_prefix_len:
        return None
    if format_index < 0 or format_index >= fixed_prefix_len:
        return None
    format_param = (callee_parameters or ())[format_index] or {}
    if not _parameter_descriptor_looks_pointer(format_param):
        return None
    return spec


def _impl__normalized_fixed_prefix_target_name(target_name: Optional[str]) -> str:
    if not target_name:
        return ""
    normalized = str(target_name).strip().lower()
    normalized = normalized.split("@", 1)[0]
    normalized = normalized.rsplit("::", 1)[-1]
    while normalized.startswith("_"):
        normalized = normalized[1:]
    return normalized


def _impl__explicit_argument_matches_preferred(
    expr: Optional[Expression],
    preferred: Optional[Expression],
    caller_parameters: Sequence[Dict],
    callee_param: Optional[Dict],
) -> bool:
    if expr is None or preferred is None:
        return False
    if _expressions_equivalent(expr, preferred):
        return True
    expr_param = _resolve_parameter_descriptor(expr, caller_parameters)
    preferred_param = _resolve_parameter_descriptor(preferred, caller_parameters)
    if _parameter_descriptors_share_identity(expr_param, preferred_param):
        return True
    expr_size = max(1, int(expr.size or (callee_param or {}).get("size") or 8))
    preferred_size = max(1, int(preferred.size or (callee_param or {}).get("size") or 8))
    expr_location = canonicalize_location(expr, caller_parameters, size=expr_size)
    preferred_location = canonicalize_location(preferred, caller_parameters, size=preferred_size)
    return expr_location is not None and expr_location == preferred_location


def _impl__should_preserve_explicit_indirect_target_argument(
    expr: Optional[Expression],
    callee_param: Optional[Dict],
) -> bool:
    if expr is None or not _parameter_descriptor_looks_pointer(callee_param):
        return False
    if expr.expr_type == ExpressionType.PHI:
        return True
    return bool(_enumerate_constant_expression_branches(expr))


def _impl__normalize_type_display_name(type_name: Optional[str]) -> str:
    return " ".join(str(type_name or "").strip().lower().split())


def _impl__data_type_name_has_pointer_marker(type_name: Optional[str]) -> bool:
    normalized = _normalize_type_display_name(type_name)
    return bool(normalized and ("*" in normalized or " pointer" in normalized))


def _impl__data_type_name_is_undefined(type_name: Optional[str]) -> bool:
    normalized = _normalize_type_display_name(type_name)
    return bool(normalized and normalized.startswith("undefined"))


def _impl__data_type_name_is_explicit_scalar(type_name: Optional[str]) -> bool:
    normalized = _normalize_type_display_name(type_name)
    if not normalized:
        return False
    if _data_type_name_has_pointer_marker(normalized) or _data_type_name_is_undefined(normalized):
        return False
    for qualifier in ("const ", "volatile ", "restrict "):
        while normalized.startswith(qualifier):
            normalized = normalized[len(qualifier):].strip()
    scalar_names = {
        "bool",
        "_bool",
        "boolean",
        "char",
        "signed char",
        "unsigned char",
        "byte",
        "sbyte",
        "ubyte",
        "uchar",
        "short",
        "short int",
        "signed short",
        "signed short int",
        "unsigned short",
        "unsigned short int",
        "ushort",
        "int",
        "signed",
        "signed int",
        "unsigned",
        "unsigned int",
        "uint",
        "long",
        "long int",
        "signed long",
        "signed long int",
        "unsigned long",
        "unsigned long int",
        "ulong",
        "long long",
        "long long int",
        "signed long long",
        "signed long long int",
        "unsigned long long",
        "unsigned long long int",
        "longlong",
        "ulonglong",
        "size_t",
        "ssize_t",
        "int8_t",
        "uint8_t",
        "int16_t",
        "uint16_t",
        "int32_t",
        "uint32_t",
        "int64_t",
        "uint64_t",
        "float",
        "double",
        "long double",
    }
    return normalized in scalar_names or normalized.startswith("enum ")
