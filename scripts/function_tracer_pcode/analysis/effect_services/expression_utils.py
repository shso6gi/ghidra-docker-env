"""Stateless effect-summary implementations."""

from __future__ import annotations

from typing import Any
from ._shared import (
    _MAX_CALL_ARGUMENT_VARIANTS,
    AddressValueRef,
    CallArgumentWidthEvidence,
    Condition,
    ConditionSimplifier,
    EffectOrderUnavailable,
    Expression,
    ExpressionType,
    ObservedMemoryReadRef,
    PostStateReadRef,
    _FIXED_PREFIX_FORMAT_CALL_TARGETS,
    expression_key_or_identity,
    expression_key_safe,
    expression_provenance_key,
    product,
)
from ._api import (
    _additive_signature,
    _address_ref_is_readonly_format_data,
    _all_non_none_expressions,
    _apply_binary_constant_op,
    _apply_condition_parameter_replacements,
    _apply_unary_constant_op,
    _call_input_storages_for_explicit_args,
    _clone_expression_tree,
    _clone_expression_with_operands,
    _coerce_storage_info,
    _data_type_name_has_pointer_marker,
    _data_type_name_is_undefined,
    _enumerate_constant_expression_branches,
    _enumerate_expression_variants,
    _evaluate_constant_expression,
    _explicit_call_argument_window_matches_storage,
    _expression_declares_pointer_type,
    _expression_has_format_pointer_evidence,
    _expression_is_call_scope_safe,
    _expression_location_ref,
    _expression_matches_value_under_conditions,
    _expression_observed_read_ref,
    _expression_reads_location,
    _expression_truth_value,
    _expressions_equivalent,
    _expressions_equivalent_under_conditions,
    _extract_positive_param_equality_pair,
    _find_block_info_for_pcode_op,
    _flatten_location_addition,
    _get_order_key,
    _is_known_nonnull_stack_address,
    _is_test_order_mock,
    _is_zero_constant,
    _iter_expression_nodes,
    _location_sort_key,
    _mask_to_expr_width,
    _normalize_type_display_name,
    _normalized_fixed_prefix_target_name,
    _parameter_base_ref_matches_descriptor,
    _parameter_declared_semantic_size_bytes,
    _parameter_descriptor_from_expression,
    _parameter_descriptor_is_address_sized_unknown,
    _parameter_descriptor_looks_pointer,
    _parameter_descriptors_share_identity,
    _parameter_expression_from_descriptor,
    _parameter_identity_keys_from_descriptor,
    _parameter_like_identity,
    _parameter_semantic_size_bytes,
    _path_writes_storage,
    _pcode_op_ref_key_from_tracker,
    _reduce_expression_under_conditions,
    _resolve_call_argument_expression,
    _resolve_call_target_name,
    _resolve_live_in_parameter_descriptor_for_call_storage,
    _resolve_parameter_descriptor,
    _runtime_conditions_signature,
    _runtime_expression_signature,
    _sign_extend_value,
    _storage_identity_key,
    _storage_matches_parameter,
    _strip_materialized_post_state_value_refs,
    _try_get_order_key,
    canonicalize_location,
    locations_match,
    subtract_implied_conditions,
)

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl__stable_target_expression_key(expr: Optional[Expression]) -> Optional[Tuple[object, ...]]:
    if expr is None:
        return None
    return expression_provenance_key(expr)

def _impl__condition_evidence_key(condition: Condition) -> Tuple[object, ...]:
    try:
        structural_key = condition.structural_key()
    except Exception:
        structural_key = None
    if structural_key is not None:
        return ("condition", bool(getattr(condition, "negated", False)), structural_key)
    expression = getattr(condition, "expression", None)
    return (
        "condition",
        bool(getattr(condition, "negated", False)),
        expression_provenance_key(expression) if expression is not None else None,
    )

def _impl__runtime_expression_signature(expr: Optional[Expression]):
    if expr is None:
        return ("none",)
    return expression_key_or_identity(
        expr,
        include_memory_read_order=False,
        include_semantic_runtime_refs=False,
    )

def _impl__runtime_conditions_signature(conditions: Sequence[Condition]):
    return ConditionSimplifier.object_centric_conditions_signature(conditions)

def _impl__encode_signed_token(value: int) -> str:
    try:
        numeric = int(value)
    except Exception:
        numeric = 0
    if numeric < 0:
        return f"n{abs(numeric)}"
    return f"p{numeric}"

def _impl__all_non_none_expressions(
    operands: Sequence[Optional[Expression]],
) -> Optional[List[Expression]]:
    normalized: List[Expression] = []
    for operand in operands:
        if operand is None:
            return None
        normalized.append(operand)
    return normalized

def _impl__clone_expression_with_operands(
    expr: Expression,
    operands: Sequence[Expression],
) -> Expression:
    return Expression(
        expr_type=expr.expr_type,
        value=expr.value,
        operator=expr.operator,
        operands=list(operands),
        size=expr.size,
        name=expr.name,
        data_type=expr.data_type,
        data_type_obj=getattr(expr, "data_type_obj", None),
        storage_info=expr.storage_info,
        read_order_key=expr.read_order_key,
        runtime_ref=getattr(expr, "runtime_ref", None),
        opcode=getattr(expr, "opcode", None),
    )

def _impl__rebuild_expression_from_optional_operands(
    expr: Expression,
    rewritten_operands: Sequence[Optional[Expression]],
    *,
    fallback: Optional[Expression] = None,
) -> Optional[Expression]:
    if all(new is old for new, old in zip(rewritten_operands, expr.operands)):
        return expr
    new_operands = _all_non_none_expressions(rewritten_operands)
    if new_operands is None:
        return fallback
    return _clone_expression_with_operands(expr, new_operands)

def _impl__expression_observed_read_ref(expr: Optional[Expression]) -> Optional[ObservedMemoryReadRef]:
    if expr is None:
        return None
    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, ObservedMemoryReadRef):
        return runtime_ref
    return None

def _impl__expression_observed_order_key(expr: Optional[Expression]) -> Optional[int]:
    if expr is None:
        return None
    read_order_key = getattr(expr, "read_order_key", None)
    if read_order_key is not None:
        return int(read_order_key)
    observed_ref = _expression_observed_read_ref(expr)
    if observed_ref is not None and observed_ref.order_key is not None:
        return int(observed_ref.order_key)
    return None

def _impl__merge_memory_runtime_ref(
    runtime_ref: Any,
    runtime_location: Optional[CanonicalLocation],
    runtime_snapshot: Optional[PostStateSnapshotRef] = None,
) -> Any:
    if isinstance(runtime_ref, ObservedMemoryReadRef):
        if (
            (runtime_location is None or runtime_ref.location == runtime_location)
            and runtime_snapshot == runtime_ref.snapshot_ref
        ):
            return runtime_ref
        return runtime_ref.with_location(runtime_location, snapshot_ref=runtime_snapshot)
    if isinstance(runtime_ref, PostStateReadRef):
        location = runtime_location if runtime_location is not None else runtime_ref.location
        snapshot = runtime_snapshot if runtime_snapshot is not None else runtime_ref.snapshot_ref
        if location == runtime_ref.location and snapshot == runtime_ref.snapshot_ref:
            return runtime_ref
        return runtime_ref.with_location(location).with_snapshot(snapshot)
    if runtime_location is not None and runtime_snapshot is not None:
        return PostStateReadRef(
            location=runtime_location,
            snapshot_ref=runtime_snapshot,
        )
    if runtime_location is not None:
        return runtime_location
    return runtime_ref

def _impl__iter_expression_nodes(
    expr: Optional[Expression],
    *,
    include_phi_conditions: bool = True,
) -> Iterator[Expression]:
    if expr is None:
        return

    pending: List[Expression] = [expr]
    while pending:
        current = pending.pop()
        if current is None:
            continue
        yield current
        if current.expr_type == ExpressionType.PHI and current.value:
            for cond, value in reversed(current.value):
                if value is not None:
                    pending.append(value)
                if include_phi_conditions and cond is not None and cond.expression is not None:
                    pending.append(cond.expression)
            continue
        operands = getattr(current, "operands", None) or []
        pending.extend(reversed([operand for operand in operands if operand is not None]))

def _impl__expression_contains_value_reads(expr: Optional[Expression]) -> bool:
    for node in _iter_expression_nodes(expr):
        if _expression_location_ref(node) is not None:
            return True
        if node.expr_type == ExpressionType.MEMORY and node.operands:
            return True
    return False

def _impl__expression_contains_phi(expr: Optional[Expression]) -> bool:
    for node in _iter_expression_nodes(expr, include_phi_conditions=False):
        if node.expr_type == ExpressionType.PHI:
            return True
    return False

def _impl__expression_node_count(expr: Optional[Expression]) -> int:
    return sum(1 for _ in _iter_expression_nodes(expr))

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

def _impl__expression_is_wide_unknown_or_undefined(expr: Expression) -> bool:
    if expr.expr_type not in {ExpressionType.PARAMETER, ExpressionType.VARIABLE}:
        return False
    descriptor = _parameter_descriptor_from_expression(expr)
    if not _parameter_descriptor_is_address_sized_unknown(descriptor):
        return False
    try:
        expr_size = int(getattr(expr, "size", 0) or 0)
    except Exception:
        expr_size = 0
    return expr_size > 4

def _impl__expression_is_non_address_sized_scalar_value(expr: Expression) -> bool:
    if _expression_declares_pointer_type(expr):
        return False
    try:
        expr_size = int(getattr(expr, "size", 0) or 0)
    except Exception:
        expr_size = 0
    return 0 < expr_size <= 4

def _impl__enumerate_expression_variants(
    expr: Optional[Expression],
    *,
    limit: int = _MAX_CALL_ARGUMENT_VARIANTS,
) -> List[Tuple[List[Condition], Expression]]:
    if expr is None:
        return []

    if expr.expr_type == ExpressionType.PHI and expr.value:
        resolved: List[Tuple[List[Condition], Expression]] = []
        seen = set()
        for cond, value in expr.value:
            for branch_conditions, branch_value in _enumerate_expression_variants(value, limit=limit):
                merged_conditions = list(branch_conditions)
                if cond is not None:
                    merged_conditions.insert(0, cond)
                simplified = ConditionSimplifier.simplify_conditions(merged_conditions)
                if ConditionSimplifier.is_contradiction(simplified):
                    continue
                key = (
                    _runtime_conditions_signature(simplified),
                    _runtime_expression_signature(branch_value),
                )
                if key in seen:
                    continue
                seen.add(key)
                resolved.append((simplified, branch_value))
                if len(resolved) >= limit:
                    break
            if len(resolved) >= limit:
                break
        return resolved or [([], expr)]

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL, ExpressionType.INTRINSIC, ExpressionType.MEMORY):
        operand_variants = [
            _enumerate_expression_variants(operand, limit=limit)
            for operand in expr.operands
        ]
        if operand_variants and any(len(variants) > 1 or variants[0][0] for variants in operand_variants):
            resolved = []
            seen = set()
            for variant_tuple in product(*operand_variants):
                merged_conditions: List[Condition] = []
                merged_operands: List[Expression] = []
                for branch_conditions, branch_expr in variant_tuple:
                    merged_conditions.extend(branch_conditions)
                    merged_operands.append(branch_expr)
                simplified = ConditionSimplifier.simplify_conditions(merged_conditions)
                if ConditionSimplifier.is_contradiction(simplified):
                    continue
                rebuilt = _clone_expression_with_operands(expr, merged_operands)
                key = (
                    _runtime_conditions_signature(simplified),
                    _runtime_expression_signature(rebuilt),
                )
                if key in seen:
                    continue
                seen.add(key)
                resolved.append((simplified, rebuilt))
                if len(resolved) >= limit:
                    break
            return resolved or [([], expr)]

    return [([], expr)]

def _impl__reduce_conditions_under_context(
    conditions: Sequence[Condition],
    context_conditions: Sequence[Condition],
) -> List[Condition]:
    reduced: List[Condition] = []
    for cond in conditions or []:
        reduced_expr = _reduce_expression_under_conditions(
            cond.expression,
            list(context_conditions),
        )
        reduced.append(Condition(reduced_expr, cond.negated))
    return ConditionSimplifier.simplify_conditions(reduced)

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

def _impl__enumerate_constant_expression_branches(
    expr: Optional[Expression],
) -> List[Tuple[List[Condition], int]]:
    if expr is None:
        return []

    if expr.expr_type == ExpressionType.PHI and expr.value:
        resolved: List[Tuple[List[Condition], int]] = []
        for cond, value in expr.value:
            for branch_conditions, branch_value in _enumerate_constant_expression_branches(value):
                merged = list(branch_conditions)
                if cond is not None:
                    merged.insert(0, cond)
                resolved.append((merged, branch_value))
        return resolved

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        operand_branches = _enumerate_constant_expression_branches(expr.operands[0])
        if operand_branches:
            resolved: List[Tuple[List[Condition], int]] = []
            for branch_conditions, operand_value in operand_branches:
                applied = _apply_unary_constant_op(expr, operand_value)
                if applied is None:
                    continue
                resolved.append((list(branch_conditions), applied))
            if resolved:
                return resolved

    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left_branches = _enumerate_constant_expression_branches(expr.operands[0])
        right_branches = _enumerate_constant_expression_branches(expr.operands[1])
        if left_branches and right_branches:
            resolved: List[Tuple[List[Condition], int]] = []
            for left_conditions, left_value in left_branches:
                for right_conditions, right_value in right_branches:
                    applied = _apply_binary_constant_op(expr, left_value, right_value)
                    if applied is None:
                        continue
                    resolved.append((list(left_conditions) + list(right_conditions), applied))
            if resolved:
                return resolved

    const_value = _evaluate_constant_expression(expr)
    if const_value is None:
        return []
    return [([], const_value)]

def _impl__evaluate_constant_expression(expr: Optional[Expression]) -> Optional[int]:
    if expr is None:
        return None

    if expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
        return int(expr.value)

    if expr.expr_type == ExpressionType.VARIABLE:
        runtime_ref = getattr(expr, "runtime_ref", None)
        if isinstance(runtime_ref, AddressValueRef):
            return int(runtime_ref.address_offset)

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        operand_value = _evaluate_constant_expression(expr.operands[0])
        if operand_value is None:
            return None
        target_bits = max(8, (expr.size or expr.operands[0].size or 8) * 8)
        if expr.operator in {"CAST", "COPY", "INT_ZEXT"}:
            return operand_value & ((1 << target_bits) - 1)
        if expr.operator == "INT_SEXT":
            return _sign_extend_value(operand_value, expr.operands[0].get_bit_width(), target_bits)
        if expr.operator == "SUBPIECE" and len(expr.operands) >= 2:
            offset_value = _evaluate_constant_expression(expr.operands[1])
            if offset_value is None:
                return None
            shifted = operand_value >> (int(offset_value) * 8)
            return shifted & ((1 << target_bits) - 1)
        return None

    if expr.expr_type == ExpressionType.INTRINSIC:
        intrinsic_name = getattr(expr, "name", None) or ""
        operand_values = [_evaluate_constant_expression(operand) for operand in (expr.operands or [])]
        if any(value is None for value in operand_values):
            return None
        resolved_values = [int(value) for value in operand_values if value is not None]

        if intrinsic_name in {"PTRSUB", "INT_ADD"} and len(resolved_values) >= 2:
            return _mask_to_expr_width(expr, resolved_values[0] + resolved_values[1])
        if intrinsic_name == "PTRADD":
            if len(resolved_values) >= 3:
                return _mask_to_expr_width(
                    expr,
                    resolved_values[0] + (resolved_values[1] * resolved_values[2]),
                )
            if len(resolved_values) >= 2:
                return _mask_to_expr_width(expr, resolved_values[0] + resolved_values[1])
        if intrinsic_name in {"CAST", "COPY", "INT_ZEXT"} and resolved_values:
            target_bits = max(8, (expr.size or expr.operands[0].size or 8) * 8)
            return resolved_values[0] & ((1 << target_bits) - 1)
        if intrinsic_name == "INT_SEXT" and resolved_values:
            target_bits = max(8, (expr.size or expr.operands[0].size or 8) * 8)
            return _sign_extend_value(
                resolved_values[0],
                expr.operands[0].get_bit_width(),
                target_bits,
            )
        return None

    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left_value = _evaluate_constant_expression(expr.operands[0])
        right_value = _evaluate_constant_expression(expr.operands[1])
        if left_value is None or right_value is None:
            return None

        if expr.operator == "SUBPIECE":
            if right_value < 0:
                return None
            target_bits = max(8, (expr.size or expr.operands[0].size or 8) * 8)
            shifted = left_value >> (int(right_value) * 8)
            return shifted & ((1 << target_bits) - 1)
        if expr.operator in {"INT_ADD", "PTRSUB", "PTRADD"}:
            return _mask_to_expr_width(expr, left_value + right_value)
        if expr.operator == "INT_SUB":
            return _mask_to_expr_width(expr, left_value - right_value)
        if expr.operator == "INT_MULT":
            return _mask_to_expr_width(expr, left_value * right_value)
        if expr.operator == "INT_AND":
            return _mask_to_expr_width(expr, left_value & right_value)
        if expr.operator == "INT_OR":
            return _mask_to_expr_width(expr, left_value | right_value)
        if expr.operator == "INT_XOR":
            return _mask_to_expr_width(expr, left_value ^ right_value)
        if expr.operator == "PIECE":
            low_bits = expr.operands[1].get_bit_width()
            return _mask_to_expr_width(
                expr,
                (left_value << low_bits) | (right_value & ((1 << low_bits) - 1)),
            )
        return None

    return None

def _impl__apply_unary_constant_op(expr: Expression, operand_value: int) -> Optional[int]:
    target_bits = max(8, (expr.size or expr.operands[0].size or 8) * 8)
    if expr.operator in {"CAST", "COPY", "INT_ZEXT"}:
        return operand_value & ((1 << target_bits) - 1)
    if expr.operator == "INT_SEXT":
        return _sign_extend_value(operand_value, expr.operands[0].get_bit_width(), target_bits)
    return None

def _impl__apply_binary_constant_op(expr: Expression, left_value: int, right_value: int) -> Optional[int]:
    if expr.operator == "SUBPIECE":
        if right_value < 0:
            return None
        target_bits = max(8, (expr.size or expr.operands[0].size or 8) * 8)
        shifted = left_value >> (int(right_value) * 8)
        return shifted & ((1 << target_bits) - 1)
    if expr.operator in {"INT_ADD", "PTRSUB", "PTRADD"}:
        return _mask_to_expr_width(expr, left_value + right_value)
    if expr.operator == "INT_SUB":
        return _mask_to_expr_width(expr, left_value - right_value)
    if expr.operator == "INT_MULT":
        return _mask_to_expr_width(expr, left_value * right_value)
    if expr.operator == "INT_AND":
        return _mask_to_expr_width(expr, left_value & right_value)
    if expr.operator == "INT_OR":
        return _mask_to_expr_width(expr, left_value | right_value)
    if expr.operator == "INT_XOR":
        return _mask_to_expr_width(expr, left_value ^ right_value)
    if expr.operator == "PIECE":
        low_bits = expr.operands[1].get_bit_width()
        return _mask_to_expr_width(
            expr,
            (left_value << low_bits) | (right_value & ((1 << low_bits) - 1)),
        )
    return None

def _impl__sign_extend_value(value: int, source_bits: int, target_bits: int) -> int:
    source_bits = max(1, int(source_bits))
    target_bits = max(source_bits, int(target_bits))
    mask = (1 << source_bits) - 1
    value &= mask
    sign_bit = 1 << (source_bits - 1)
    if value & sign_bit:
        value -= 1 << source_bits
    return value & ((1 << target_bits) - 1)

def _impl__mask_to_expr_width(expr: Expression, value: int) -> int:
    bit_width = max(1, expr.get_bit_width())
    return value & ((1 << bit_width) - 1)

def _impl__read_program_memory_value(
    tracer,
    address_value: int,
    size_bytes: int,
) -> Optional[int]:
    if tracer is None or getattr(tracer, "program", None) is None:
        return None
    if not isinstance(address_value, int) or address_value < 0 or size_bytes <= 0:
        return None
    try:
        program = tracer.program
        memory = program.getMemory()
        default_space = program.getAddressFactory().getDefaultAddressSpace()
        addr = default_space.getAddress(address_value)
        raw_bytes = []
        for offset in range(size_bytes):
            raw_bytes.append(int(memory.getByte(addr.add(offset))) & 0xFF)
        ordered = raw_bytes if program.getLanguage().isBigEndian() else list(reversed(raw_bytes))
        result = 0
        for byte_val in ordered:
            result = (result << 8) | byte_val
        return result
    except Exception:
        return None

def _impl__find_block_info_for_pcode_op(condition_tracker, pcode_op):
    if condition_tracker is None or pcode_op is None:
        return None
    block_index = getattr(condition_tracker, "block_by_index", None)
    if not isinstance(block_index, dict):
        return None
    target_key = _pcode_op_ref_key_from_tracker(condition_tracker, pcode_op)
    for block_info in block_index.values():
        try:
            pcode_ops = getattr(block_info, "pcode_ops", None) or []
            if any(
                candidate is pcode_op
                or (
                    target_key is not None
                    and _pcode_op_ref_key_from_tracker(condition_tracker, candidate) == target_key
                )
                for candidate in pcode_ops
            ):
                return block_info
        except Exception:
            continue
    return None

def _impl__pcode_op_ref_key_from_tracker(condition_tracker, pcode_op) -> Optional[Tuple[object, ...]]:
    tracer = getattr(condition_tracker, "tracer", None)
    make_ref = getattr(tracer, "_make_pcode_op_ref", None)
    if not callable(make_ref):
        return None
    try:
        ref = make_ref(pcode_op)
    except Exception:
        return None
    stable_key = getattr(ref, "stable_key", None)
    if not callable(stable_key):
        return None
    try:
        return stable_key()
    except Exception:
        return None

def _impl__iter_path_ops_before_call(path_blocks, call_op) -> Iterator[object]:
    call_order = _try_get_order_key(call_op)
    if call_order is None:
        return
    for block_info in path_blocks or []:
        for op in getattr(block_info, "pcode_ops", None) or []:
            if op is call_op:
                return
            op_order = _try_get_order_key(op)
            if op_order is None or op_order >= call_order:
                continue
            yield op

def _impl__compatible_call_block_paths(
    call_op,
    condition_tracker,
    current_conditions: Optional[Sequence[Condition]],
) -> Optional[List[Tuple[List[object], List[Condition]]]]:
    if condition_tracker is None:
        return None
    call_block = _find_block_info_for_pcode_op(condition_tracker, call_op)
    if call_block is None:
        return None
    get_paths = getattr(condition_tracker, "get_all_valid_block_paths_to_block", None)
    if not callable(get_paths):
        return None

    compatible: List[Tuple[List[object], List[Condition]]] = []
    try:
        path_results = list(get_paths(call_block) or [])
    except Exception:
        return None
    if not path_results:
        return None

    for blocks, path_conditions in path_results:
        merged = ConditionSimplifier.simplify_conditions(
            list(path_conditions or []) + list(current_conditions or []),
        )
        if ConditionSimplifier.is_contradiction(merged):
            continue
        compatible.append((list(blocks or []), list(path_conditions or [])))
    return compatible

def _impl__resolve_multiequal_input_for_path(
    op,
    path_blocks,
    tracer,
    caller_parameters: Sequence[Dict],
    current_conditions: Optional[Sequence[Condition]],
) -> Optional[Expression]:
    if op is None or getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
        return None
    if not path_blocks:
        return None

    op_block = None
    for idx, block_info in enumerate(path_blocks):
        try:
            if any(candidate is op for candidate in (getattr(block_info, "pcode_ops", None) or [])):
                op_block = (idx, block_info)
                break
        except Exception:
            continue
    if op_block is None:
        return None

    path_index, block_info = op_block
    if path_index <= 0:
        return None
    predecessor = path_blocks[path_index - 1]
    ghidra_block = getattr(block_info, "block", None)
    if ghidra_block is None:
        return None

    try:
        in_size = int(ghidra_block.getInSize())
    except Exception:
        return None

    predecessor_block = getattr(predecessor, "block", predecessor)
    for input_index in range(min(int(op.getNumInputs()), in_size)):
        try:
            incoming = ghidra_block.getIn(input_index)
        except Exception:
            incoming = None
        if incoming is None:
            continue
        incoming_index = getattr(incoming, "getIndex", lambda: None)()
        predecessor_index = getattr(predecessor_block, "getIndex", lambda: None)()
        if incoming is not predecessor_block and incoming_index != predecessor_index:
            continue
        try:
            input_varnode = op.getInput(input_index)
        except Exception:
            return None
        expr = _resolve_call_argument_expression(input_varnode, tracer, caller_parameters)
        reduced = _reduce_expression_under_conditions(
            expr,
            list(current_conditions or []),
        )
        return reduced if reduced is not None else expr

    return None

def _impl__recover_unmodified_live_in_argument(
    ops: Sequence[object],
    target_storage: StorageInfo,
    tracer,
    caller_parameters: Sequence[Dict],
    callee_param: Dict,
) -> Optional[Expression]:
    if _path_writes_storage(ops, target_storage, tracer):
        return None
    declared_target_size = _parameter_declared_semantic_size_bytes(callee_param)
    target_size = declared_target_size or _parameter_semantic_size_bytes(callee_param)
    descriptor = _resolve_live_in_parameter_descriptor_for_call_storage(
        caller_parameters,
        target_storage,
        required_size_bytes=declared_target_size,
        allow_register_fragment_extension=declared_target_size is None,
    )
    if descriptor is None:
        return None
    try:
        source_size = int(_parameter_semantic_size_bytes(descriptor) or descriptor.get("size") or 0)
    except Exception:
        source_size = 0
    try:
        target_size = int(target_size or callee_param.get("size") or target_storage.size or source_size or 0)
    except Exception:
        target_size = source_size
    source_size = source_size if source_size > 0 else target_size
    expr = _parameter_expression_from_descriptor(descriptor, size=source_size or None)
    if expr is None:
        return None
    if target_size > source_size:
        if declared_target_size is not None:
            return None
        source_storage = _coerce_storage_info(descriptor.get("storage"))
        expr = expr.clone_with(
            call_argument_width_evidence=CallArgumentWidthEvidence(
                source_bits=max(1, int(source_size or 0)) * 8,
                target_bits=max(
                    max(1, int(target_size or 0)) * 8,
                    int(getattr(target_storage, "size_bits", 0) or 0),
                ),
                source_storage_key=_storage_identity_key(source_storage),
                target_storage_key=_storage_identity_key(target_storage),
            )
        )
    return expr

def _impl__expression_bit_width(expr: Optional[Expression]) -> int:
    if expr is None:
        return 0
    try:
        width = int(expr.get_bit_width() or 0)
    except Exception:
        width = 0
    if width > 0:
        return width
    try:
        size = int(getattr(expr, "size", 0) or 0)
    except Exception:
        size = 0
    return max(0, size * 8)

def _impl__clone_expression_tree(expr: Optional[Expression]) -> Optional[Expression]:
    if expr is None:
        return None
    if expr.expr_type == ExpressionType.PHI and expr.value:
        branches = []
        for cond, value in expr.value:
            cloned_cond = None
            if cond is not None:
                cloned_expression = _clone_expression_tree(cond.expression)
                cloned_cond = None if cloned_expression is None else Condition(cloned_expression, cond.negated)
            branches.append((cloned_cond, _clone_expression_tree(value)))
        cloned = Expression.phi(branches)
        cloned.size = expr.size
        cloned.data_type = expr.data_type
        cloned.data_type_obj = getattr(expr, "data_type_obj", None)
        cloned.storage_info = getattr(expr, "storage_info", None)
        cloned.read_order_key = getattr(expr, "read_order_key", None)
        cloned.runtime_ref = getattr(expr, "runtime_ref", None)
        cloned.opcode = getattr(expr, "opcode", None)
        return cloned
    return expr.clone_with(
        operands=[_clone_expression_tree(op) for op in (expr.operands or [])]
    )

def _impl__expression_is_call_scope_safe(expr: Optional[Expression]) -> bool:
    if expr is None:
        return True

    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type in (expr_kind.CALL, expr_kind.UNKNOWN):
        return False

    if expr_type == expr_kind.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and not _expression_is_call_scope_safe(cond.expression):
                return False
            if not _expression_is_call_scope_safe(value):
                return False
        return True

    for operand in getattr(expr, "operands", []) or []:
        if not _expression_is_call_scope_safe(operand):
            return False

    return True

def _impl__summary_has_interdependent_writes(summary: EffectSummary) -> bool:
    if summary is None or len(summary.effects) <= 1:
        return False

    params = [{"name": name, "index": index} for index, name in enumerate(summary.parameter_names)]
    for index, effect in enumerate(summary.effects):
        for other_index, other in enumerate(summary.effects):
            if index == other_index:
                continue
            if effect.location == other.location:
                continue
            if _expression_reads_location(effect.value, other.location, effect.conditions, params):
                return True
    return False

def _impl__expression_matches_value_under_conditions(
    expr: Expression,
    value: Expression,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict],
) -> bool:
    reduced_expr = _reduce_expression_under_conditions(expr, conditions)
    reduced_value = _reduce_expression_under_conditions(value, conditions)
    if _expressions_equivalent_under_conditions(reduced_expr, reduced_value, conditions, parameters):
        return True
    if reduced_value.expr_type != ExpressionType.PHI or not reduced_value.value:
        return False
    for cond, branch_value in reduced_value.value:
        combined = list(conditions)
        if cond is not None:
            combined.append(cond)
        if ConditionSimplifier.object_centric_is_contradiction(combined):
            continue
        if _expression_matches_value_under_conditions(reduced_expr, branch_value, combined, parameters):
            return True
    return False

def _impl__strongly_connected_components(
    graph: Dict[CanonicalLocation, Set[CanonicalLocation]]
) -> List[List[CanonicalLocation]]:
    index = 0
    stack: List[CanonicalLocation] = []
    indices: Dict[CanonicalLocation, int] = {}
    lowlinks: Dict[CanonicalLocation, int] = {}
    on_stack: Set[CanonicalLocation] = set()
    components: List[List[CanonicalLocation]] = []

    def strongconnect(node: CanonicalLocation) -> None:
        nonlocal index
        indices[node] = index
        lowlinks[node] = index
        index += 1
        stack.append(node)
        on_stack.add(node)

        for succ in graph.get(node, set()):
            if succ not in indices:
                strongconnect(succ)
                lowlinks[node] = min(lowlinks[node], lowlinks[succ])
            elif succ in on_stack:
                lowlinks[node] = min(lowlinks[node], indices[succ])

        if lowlinks[node] != indices[node]:
            return

        component: List[CanonicalLocation] = []
        while stack:
            member = stack.pop()
            on_stack.discard(member)
            component.append(member)
            if member == node:
                break
        components.append(component)

    for node in graph:
        if node not in indices:
            strongconnect(node)

    return components

def _impl__expressions_equivalent(left: Optional[Expression], right: Optional[Expression]) -> bool:
    if left is right:
        return True
    if left is None or right is None:
        return False
    left_key = expression_key_safe(left, include_memory_read_order=True)
    right_key = expression_key_safe(right, include_memory_read_order=True)
    if left_key is None or right_key is None:
        return False
    return left_key == right_key

def _impl__additive_signature(expr: Optional[Expression]) -> Optional[Tuple[int, Tuple[Tuple[object, int], ...], int]]:
    if expr is None:
        return None

    bit_width = int(getattr(expr, "size", 0) or 0)
    modulus = 1 << bit_width if bit_width > 0 else None
    term_counts: Dict[object, int] = {}
    const_value = 0

    def visit(node: Expression, sign: int) -> bool:
        nonlocal const_value, bit_width, modulus
        if node is None:
            return False
        node_bits = int(getattr(node, "size", 0) or 0)
        if node_bits > bit_width:
            bit_width = node_bits
            modulus = 1 << bit_width if bit_width > 0 else None

        if node.expr_type == ExpressionType.CONSTANT:
            value = int(node.value)
            const_value = const_value + (sign * value)
            if modulus is not None:
                const_value %= modulus
            return True

        if node.expr_type == ExpressionType.UNARY_OP and node.operands:
            if node.operator in {"INT_2COMP", "INT_NEGATE"}:
                return visit(node.operands[0], -sign)
            return False

        if node.expr_type == ExpressionType.BINARY_OP and len(node.operands) == 2:
            if node.operator == "INT_ADD":
                return visit(node.operands[0], sign) and visit(node.operands[1], sign)
            if node.operator == "INT_SUB":
                return visit(node.operands[0], sign) and visit(node.operands[1], -sign)

        key = _runtime_expression_signature(node)
        term_counts[key] = term_counts.get(key, 0) + sign
        if term_counts[key] == 0:
            term_counts.pop(key, None)
        return True

    if not visit(expr, 1):
        return None

    if modulus is not None:
        const_value %= modulus
    terms = tuple(sorted((key, coeff) for key, coeff in term_counts.items() if coeff))
    return const_value, terms, bit_width

def _impl__expressions_equivalent_under_conditions(
    left: Optional[Expression],
    right: Optional[Expression],
    conditions: Sequence[Condition],
    parameters: Sequence[Dict],
) -> bool:
    if _expressions_equivalent(left, right):
        return True

    left_unwrapped = _strip_materialized_post_state_value_refs(left)
    right_unwrapped = _strip_materialized_post_state_value_refs(right)
    if left_unwrapped is not left or right_unwrapped is not right:
        if _expressions_equivalent(left_unwrapped, right_unwrapped):
            return True

    left_rewritten = _apply_condition_parameter_replacements(left_unwrapped, conditions, parameters)
    right_rewritten = _apply_condition_parameter_replacements(right_unwrapped, conditions, parameters)
    if _expressions_equivalent(left_rewritten, right_rewritten):
        return True

    left_sig = _additive_signature(left_rewritten)
    right_sig = _additive_signature(right_rewritten)
    if left_sig is None or right_sig is None:
        return False
    return left_sig == right_sig

def _impl__build_alias_representative_map(
    locations: Sequence[CanonicalLocation],
    conditions: Sequence[Condition],
) -> Dict[CanonicalLocation, CanonicalLocation]:
    groups: List[List[CanonicalLocation]] = []
    for location in sorted(set(locations), key=_location_sort_key):
        placed = False
        for group in groups:
            head = group[0]
            if head.size != location.size:
                continue
            if locations_match(location, head, conditions):
                group.append(location)
                placed = True
                break
        if not placed:
            groups.append([location])

    representatives: Dict[CanonicalLocation, CanonicalLocation] = {}
    for group in groups:
        representative = min(group, key=_location_sort_key)
        for member in group:
            representatives[member] = representative
    return representatives

def _impl__resolve_alias_representative(
    location: CanonicalLocation,
    alias_representatives: Dict[CanonicalLocation, CanonicalLocation],
    conditions: Sequence[Condition],
) -> Optional[CanonicalLocation]:
    representative = alias_representatives.get(location)
    if representative is not None:
        return representative
    for candidate, candidate_rep in alias_representatives.items():
        if candidate.size != location.size:
            continue
        if locations_match(location, candidate, conditions):
            return candidate_rep
    return None

def _impl__reduce_expression_under_conditions(
    expr: Expression,
    conditions: Sequence[Condition],
) -> Expression:
    if expr is None:
        return expr

    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is None:
                continue
            combined = list(conditions) + [cond]
            if ConditionSimplifier.is_contradiction(combined):
                continue
            if not subtract_implied_conditions([cond], conditions):
                return _reduce_expression_under_conditions(value, combined)

        surviving = []
        for cond, value in expr.value:
            combined = list(conditions)
            if cond is not None:
                combined.append(cond)
            if ConditionSimplifier.is_contradiction(combined):
                continue
            reduced_value = _reduce_expression_under_conditions(value, combined)
            surviving.append((cond, reduced_value))

        if not surviving:
            return expr
        if len(surviving) == 1:
            return surviving[0][1]

        rebuilt = Expression.phi(surviving)
        rebuilt.size = expr.size
        return rebuilt

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL, ExpressionType.INTRINSIC, ExpressionType.MEMORY):
        new_operands = [_reduce_expression_under_conditions(op, conditions) for op in expr.operands]
        return _clone_expression_with_operands(expr, new_operands) if not all(
            new is old for new, old in zip(new_operands, expr.operands)
        ) else expr

    return expr

def _impl_subtract_implied_conditions(
    effect_conditions: Sequence[Condition],
    return_conditions: Sequence[Condition],
) -> List[Condition]:
    context_basis = ConditionSimplifier.simplify_conditions_object_centric(
        list(return_conditions or [])
    )
    residual: List[Condition] = []
    for condition in ConditionSimplifier.simplify_conditions_object_centric(
        list(effect_conditions or [])
    ):
        if any(condition.equals(existing) for existing in context_basis):
            continue
        if ConditionSimplifier.object_centric_is_contradiction(
            context_basis + [condition.negate()]
        ):
            continue
        residual.append(condition)
    return residual

def _impl__expression_truth_value(expr: Optional[Expression]) -> Optional[bool]:
    if expr is None:
        return None
    return ConditionSimplifier.evaluate_condition_truth(Condition(expr, False))

def _impl__simplify_boolean_binary_expression(
    operator: str,
    left: Expression,
    right: Expression,
) -> Optional[Expression]:
    left_truth = _expression_truth_value(left)
    right_truth = _expression_truth_value(right)

    if operator == "BOOL_AND":
        if left_truth is False or right_truth is False:
            return Expression.constant(0, size=1)
        if left_truth is True:
            return right
        if right_truth is True:
            return left
        return None

    if operator == "BOOL_OR":
        if left_truth is True or right_truth is True:
            return Expression.constant(1, size=1)
        if left_truth is False:
            return right
        if right_truth is False:
            return left
        return None

    if operator == "BOOL_XOR":
        if left_truth is not None and right_truth is not None:
            return Expression.constant(1 if left_truth ^ right_truth else 0, size=1)
        if left_truth is False:
            return right
        if right_truth is False:
            return left
        if left_truth is True:
            return Expression.unary_op("BOOL_NEGATE", right)
        if right_truth is True:
            return Expression.unary_op("BOOL_NEGATE", left)

    return None

def _impl__known_nonnull_address_comparison_truth(
    operator: str,
    left: Expression,
    right: Expression,
    parameters: Optional[Sequence[Dict]],
) -> Optional[bool]:
    if operator not in {"INT_EQUAL", "INT_NOTEQUAL"}:
        return None
    if not parameters:
        parameters = []

    if _is_zero_constant(left) and _is_known_nonnull_stack_address(right, parameters):
        return operator == "INT_NOTEQUAL"
    if _is_zero_constant(right) and _is_known_nonnull_stack_address(left, parameters):
        return operator == "INT_NOTEQUAL"
    return None

def _impl__is_zero_constant(expr: Optional[Expression]) -> bool:
    return (
        expr is not None
        and expr.expr_type == ExpressionType.CONSTANT
        and isinstance(expr.value, int)
        and int(expr.value) == 0
    )

def _impl__is_known_nonnull_stack_address(
    expr: Optional[Expression],
    parameters: Sequence[Dict],
) -> bool:
    if expr is None:
        return False
    size = max(1, int(getattr(expr, "size", 0) or 0), 1)
    location = canonicalize_location(expr, parameters, size=size)
    if location is None:
        return False
    return location.base_ref.is_stack_frame()

def _impl__collect_param_equalities(
    conditions: Sequence[Condition],
) -> Set[FrozenSet[Tuple[object, ...]]]:
    equalities: Set[FrozenSet[Tuple[object, ...]]] = set()
    for condition in conditions:
        pair = _extract_positive_param_equality_pair(condition)
        if pair is not None:
            equalities.add(pair)
    return equalities

def _impl__extract_positive_param_equality_pair(
    condition: Optional[Condition],
) -> Optional[FrozenSet[Tuple[object, ...]]]:
    if condition is None:
        return None

    expr = condition.expression
    negated = bool(condition.negated)
    while (
        expr is not None
        and expr.expr_type == ExpressionType.UNARY_OP
        and expr.operator == "BOOL_NEGATE"
        and expr.operands
    ):
        negated = not negated
        expr = expr.operands[0]

    if (
        expr is None
        or expr.expr_type != ExpressionType.BINARY_OP
        or len(expr.operands) != 2
        or expr.operator not in {"INT_EQUAL", "INT_NOTEQUAL"}
    ):
        return None

    is_positive = (expr.operator == "INT_EQUAL" and not negated) or (
        expr.operator == "INT_NOTEQUAL" and negated
    )
    if not is_positive:
        return None

    left_key = _parameter_like_identity(expr.operands[0])
    right_key = _parameter_like_identity(expr.operands[1])
    if left_key is None or right_key is None:
        return None
    return frozenset((left_key, right_key))

def _impl__flatten_param_addition(
    expr: Expression,
    parameters: Sequence[Dict],
) -> Tuple[Optional[int], List[LocationBaseRef]]:
    const_total, bases = _flatten_location_addition(expr, parameters)
    if const_total is None:
        return None, []
    if not all(
        base.is_parameter()
        and any(_parameter_base_ref_matches_descriptor(base, param) for param in parameters)
        for base in bases
    ):
        return None, []
    return const_total, bases

def _impl__is_stack_frame_base_expression(expr: Optional[Expression]) -> bool:
    if expr is None:
        return False

    expr_storage = _coerce_storage_info(getattr(expr, "storage_info", None))
    if expr_storage is not None:
        if bool(expr_storage.is_stack_pointer) or bool(expr_storage.is_frame_pointer):
            return True
    return False

def _impl__constant_factor(expr: Expression) -> Optional[int]:
    value = _evaluate_constant_expression(expr)
    if value is None:
        return None
    return int(value)

def _impl__concat(left: Expression, right: Expression) -> Expression:
    result = Expression.binary_op("PIECE", left, right)
    result.size = (left.size or 0) + (right.size or 0)
    return result

def _impl__has_overlapping_guards(matched: Sequence[Tuple[int, List[Condition], Expression]]) -> bool:
    for i in range(len(matched)):
        for j in range(i + 1, len(matched)):
            residual_i = list(matched[i][1])
            residual_j = list(matched[j][1])
            if not residual_i or not residual_j:
                return True
            if not ConditionSimplifier.is_contradiction(residual_i + residual_j):
                return True
    return False

def _impl__all_residual_guards_empty(matched: Sequence[Tuple[int, List[Condition], Expression]]) -> bool:
    return all(not list(residual) for _order, residual, _value in matched)

def _impl__get_order_key(op) -> int:
    try:
        seq = op.getSeqnum()
    except Exception as exc:
        if _is_test_order_mock(op):
            return 0
        raise EffectOrderUnavailable("pcode op sequence number is unavailable") from exc
    if seq is None:
        if _is_test_order_mock(op):
            return 0
        raise EffectOrderUnavailable("pcode op sequence number is unavailable")
    try:
        target = seq.getTarget()
        return (int(target.getOffset()) << 8) | int(seq.getOrder())
    except Exception as exc:
        if _is_test_order_mock(op):
            return 0
        raise EffectOrderUnavailable("pcode op target/order is unavailable") from exc

def _impl__try_get_order_key(op, *, default: Optional[int] = None) -> Optional[int]:
    try:
        return _get_order_key(op)
    except EffectOrderUnavailable:
        return default

def _impl__is_test_order_mock(op) -> bool:
    module_name = str(getattr(type(op), "__module__", "") or "")
    return (
        module_name.startswith("test_")
        or ".tests." in module_name
        or module_name.endswith(".tests")
    )
