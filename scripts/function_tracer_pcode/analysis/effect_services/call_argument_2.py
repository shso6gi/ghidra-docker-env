"""Stateless effect-summary implementations."""

from __future__ import annotations

from typing import Any, Dict, Optional, Sequence, Set, Tuple
from ._shared import (
    CanonicalLocation,
    Condition,
    Expression,
    ExpressionType,
    LocationBaseRef,
    PostStateReadRef,
    StorageInfo,
)
from ._api import (
    _collect_parameter_replacements_from_conditions,
    _expression_contains_parameter_identity,
    _expressions_equivalent,
    _normalize_parameter_index,
    _parameter_base_ref,
    _parameter_expression_from_descriptor,
    _parameter_identity_key_from_base_ref,
    _parameter_identity_keys_from_expression,
    _recover_parameter_expression_from_varnode,
    _resolve_parameter_descriptor,
    _resolve_parameter_descriptor_from_identity,
    _stack_location_key,
    _try_get_order_key,
    substitute_expression,
)

def _impl__parameter_expression_from_varnode(varnode, tracer, parameters: Sequence[Dict]) -> Optional[Expression]:
    try:
        high_var = varnode.getHigh()
    except Exception:
        high_var = None
    try:
        def_op = varnode.getDef()
    except Exception:
        def_op = None

    storage_info = tracer._get_storage_info_from_varnode(varnode)

    # Defined varnodes can reuse a parameter-like HighSymbol after register allocation.
    # Recovering passthrough parameters is handled by the recursive caller, so avoid
    # directly relabeling call-defined temporaries as live-in parameters here.
    if def_op is not None:
        return None

    if high_var is not None:
        symbol = high_var.getSymbol()
        if symbol is not None:
            try:
                symbol_name = symbol.getName()
            except Exception:
                symbol_name = None
            try:
                symbol_index = symbol.getCategoryIndex() if symbol.isParameter() else None
            except Exception:
                symbol_index = None
            if symbol_index is None:
                try:
                    symbol_index = high_var.getSlot()
                except Exception:
                    symbol_index = None
            descriptor = _resolve_parameter_descriptor_from_identity(
                parameters,
                parameter_ref=_parameter_base_ref(name=symbol_name, index=symbol_index),
                parameter_index=symbol_index,
                storage_info=storage_info,
            )
            if descriptor is not None:
                return _parameter_expression_from_descriptor(descriptor, size=varnode.getSize())

    probe = Expression.variable(
        getattr(high_var, "getName", lambda: None)() or f"var_{id(varnode):x}",
        size=varnode.getSize(),
        storage_info=storage_info,
    )
    descriptor = _resolve_parameter_descriptor(probe, parameters)
    if descriptor is None:
        return None
    return _parameter_expression_from_descriptor(descriptor, size=varnode.getSize())

def _impl__recover_parameter_from_stack_load(
    load_op,
    tracer,
    parameters: Sequence[Dict],
    depth: int,
    seen: Set[int],
) -> Optional[Expression]:
    location = _stack_location_key(load_op.getInput(1), size=load_op.getOutput().getSize() if load_op.getOutput() else 0)
    if location is None:
        return None

    load_order = _try_get_order_key(load_op)
    if load_order is None:
        return None
    best_candidate = None
    best_order = None
    for op in tracer.get_all_pcode_ops():
        op_order = _try_get_order_key(op)
        if op_order is None or op_order >= load_order:
            continue

        output = op.getOutput()
        if output is not None:
            output_location = _stack_location_key(output, size=output.getSize())
            if output_location == location:
                if best_order is None or op_order > best_order:
                    best_candidate = ("output", op)
                    best_order = op_order

        if op.getMnemonic() == "STORE" and op.getNumInputs() >= 3:
            store_location = _stack_location_key(op.getInput(1), size=op.getInput(2).getSize())
            if store_location == location:
                if best_order is None or op_order > best_order:
                    best_candidate = ("store", op)
                    best_order = op_order

    if best_candidate is None:
        return None

    kind, op = best_candidate
    if kind == "output" and op.getNumInputs() >= 1:
        return _recover_parameter_expression_from_varnode(
            op.getInput(0),
            tracer,
            parameters,
            depth=depth,
            seen=seen,
        )

    if kind == "store" and op.getNumInputs() >= 3:
        return _recover_parameter_expression_from_varnode(
            op.getInput(2),
            tracer,
            parameters,
            depth=depth,
            seen=seen,
        )

    return None

def _impl__expression_contains_parameter_identity(
    expr: Optional[Expression],
    identities: Set[Tuple[object, ...]],
    parameters: Sequence[Dict],
) -> bool:
    if expr is None:
        return False
    if identities.intersection(_parameter_identity_keys_from_expression(expr, parameters)):
        return True
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and _expression_contains_parameter_identity(
                cond.expression,
                identities,
                parameters,
            ):
                return True
            if _expression_contains_parameter_identity(value, identities, parameters):
                return True
        return False
    return any(
        _expression_contains_parameter_identity(op, identities, parameters)
        for op in getattr(expr, "operands", []) or []
    )

def _impl__collect_parameter_replacements_from_conditions(
    conditions: Sequence[Condition],
    parameters: Sequence[Dict],
) -> Dict[Tuple[object, ...], Expression]:
    replacements: Dict[Tuple[object, ...], Expression] = {}
    for cond in conditions or []:
        if cond is None or cond.negated:
            continue
        expr = getattr(cond, "expression", None)
        if (
            expr is None
            or expr.expr_type != ExpressionType.BINARY_OP
            or expr.operator != "INT_EQUAL"
            or len(expr.operands) != 2
        ):
            continue
        left, right = expr.operands
        left_keys = _parameter_identity_keys_from_expression(left, parameters)
        right_keys = _parameter_identity_keys_from_expression(right, parameters)
        if left_keys and not _expression_contains_parameter_identity(right, left_keys, parameters):
            for key in left_keys:
                replacements[key] = right
            continue
        if right_keys and not _expression_contains_parameter_identity(left, right_keys, parameters):
            for key in right_keys:
                replacements[key] = left
    return replacements

def _impl__apply_condition_parameter_replacements(
    expr: Optional[Expression],
    conditions: Sequence[Condition],
    parameters: Sequence[Dict],
) -> Optional[Expression]:
    if expr is None:
        return None
    replacements = _collect_parameter_replacements_from_conditions(conditions, parameters)
    if not replacements:
        return expr

    current = expr
    for _ in range(4):
        rewritten = substitute_expression(current, replacements, parameters)
        if _expressions_equivalent(rewritten, current):
            break
        current = rewritten
    return current

def _impl__lookup_parameter_replacement(
    expr: Optional[Expression],
    replacements: Dict[Tuple[object, ...], Expression],
    parameters: Optional[Sequence[Dict]],
) -> Optional[Expression]:
    if expr is None or not replacements or parameters is None:
        return None
    for key in _parameter_identity_keys_from_expression(expr, parameters):
        replacement = replacements.get(key)
        if replacement is not None:
            return replacement
    return None

def _impl__parameter_like_identity(expr: Optional[Expression]) -> Optional[Tuple[object, ...]]:
    current = expr
    while (
        current is not None
        and current.expr_type == ExpressionType.UNARY_OP
        and current.operator in {"INT_ZEXT", "INT_SEXT", "INT_2COMP"}
        and current.operands
    ):
        current = current.operands[0]

    if current is None:
        return None
    if current.expr_type == ExpressionType.PARAMETER:
        param_index = _normalize_parameter_index(getattr(current, "value", None))
        if param_index is not None:
            return ("parameter", param_index)
    runtime_ref = getattr(current, "runtime_ref", None)
    if isinstance(runtime_ref, LocationBaseRef):
        return _parameter_identity_key_from_base_ref(runtime_ref)
    if isinstance(runtime_ref, (CanonicalLocation, PostStateReadRef)):
        location_ref = runtime_ref.location if isinstance(runtime_ref, PostStateReadRef) else runtime_ref
        return _parameter_identity_key_from_base_ref(location_ref.base_ref)
    return None

def _impl__resolve_parameter_name(expr: Expression, parameters: Sequence[Dict]) -> Optional[str]:
    if expr is None:
        return None

    descriptor = _resolve_parameter_descriptor(expr, parameters)
    if descriptor is None:
        return None
    name = descriptor.get("name")
    return str(name) if isinstance(name, str) and name else None

def _impl__coerce_storage_info(storage: Optional[object]) -> Optional[StorageInfo]:
    if storage is None:
        return None
    if isinstance(storage, StorageInfo):
        return storage
    if isinstance(storage, dict):
        try:
            return StorageInfo(
                is_register=bool(storage.get("is_register", False)),
                space_name=str(storage.get("space_name", "")),
                space_id=storage.get("space_id"),
                offset=int(storage.get("offset", 0)),
                size=int(storage.get("size", 0)),
                size_bits=int(storage.get("size_bits", 0)),
                register_name=storage.get("register_name"),
                register_offset=storage.get("register_offset"),
                register_size=storage.get("register_size"),
                register_size_bits=storage.get("register_size_bits"),
                base_register_name=storage.get("base_register_name"),
                base_register_offset=int(storage.get("base_register_offset", 0)),
                base_register_size=int(storage.get("base_register_size", 0)),
                base_register_size_bits=int(storage.get("base_register_size_bits", 0)),
                bit_offset_in_base=int(storage.get("bit_offset_in_base", 0)),
                is_stack_pointer=bool(storage.get("is_stack_pointer", False)),
                is_frame_pointer=bool(storage.get("is_frame_pointer", False)),
            )
        except Exception:
            return None
    return None

def _impl__storage_matches_parameter(expr_storage: StorageInfo, param_storage: StorageInfo) -> bool:
    if expr_storage.is_register and param_storage.is_register:
        if expr_storage.shares_base_register_with(param_storage):
            expr_low = expr_storage.bit_offset_in_base
            expr_high = expr_low + max(0, int(expr_storage.size_bits or 0))
            param_low = param_storage.bit_offset_in_base
            param_high = param_low + max(0, int(param_storage.size_bits or 0))
            if expr_high <= expr_low or param_high <= param_low:
                return expr_storage.register_identity_key() == param_storage.register_identity_key()
            # Only treat a register-backed value as "the same parameter" when all
            # of the value's bits are contained within the parameter fragment.
            # Mere overlap is too permissive on architectures like MIPS64 where
            # `a0` and `a0_lo` share a base register but mean different things.
            return param_low <= expr_low and expr_high <= param_high
        return expr_storage.register_identity_key() == param_storage.register_identity_key()

    return (
        expr_storage.space_id == param_storage.space_id
        and expr_storage.offset == param_storage.offset
        and expr_storage.size == param_storage.size
    )
