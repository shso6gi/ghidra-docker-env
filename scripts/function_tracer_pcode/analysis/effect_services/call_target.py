"""Stateless effect-summary implementations."""

from __future__ import annotations

from typing import Any, Callable, Dict, List, Optional, Sequence, Tuple
from ._shared import (
    CallTargetRef,
    Condition,
    ConditionNormalizer,
    ConditionSimplifier,
    Expression,
    ExpressionType,
    coerce_call_target_ref,
    concretize_readonly_loads,
)
from ._api import (
    _call_target_ref_analysis_key,
    _deduplicate_resolved_call_targets,
    _enumerate_constant_expression_branches,
    _resolve_call_target_ref,
    _resolve_function_ref_by_value,
    _resolve_function_ref_from_address,
    resolve_call_targets,
)

def _impl__resolve_call_targets_for_effect_summary(
    tracer,
    op,
    path_conditions: Sequence[Condition],
    parameters: Sequence[Dict],
    *,
    read_memory_value: Optional[Callable[[int, int], Optional[int]]] = None,
    image_base: Optional[int] = None,
    debug: bool = False,
) -> List[Tuple[CallTargetRef, List[Condition], str]]:
    path_conditions_list = list(path_conditions or ())
    try:
        resolved = resolve_call_targets(
            tracer,
            op,
            conditions=path_conditions_list,
            parameters=list(parameters or ()),
            read_memory_value=read_memory_value,
            image_base=image_base,
            debug=debug,
        )
    except Exception:
        resolved = []
    if resolved:
        return [
            (target_ref, list(target_conditions or ()), "path_sensitive")
            for target_ref, target_conditions in resolved
        ]

    # Target identity recovery should not depend on a caller path being simple
    # enough for readonly-load concretization. Re-resolve without the path
    # context, then reapply the original path when the caller combines
    # path_conditions + target_conditions below.
    if path_conditions_list:
        try:
            resolved = resolve_call_targets(
                tracer,
                op,
                conditions=[],
                parameters=list(parameters or ()),
                read_memory_value=read_memory_value,
                image_base=image_base,
                debug=debug,
            )
        except Exception:
            resolved = []
        if resolved:
            return [
                (target_ref, list(target_conditions or ()), "pathless_target_resolution")
                for target_ref, target_conditions in resolved
            ]

    target_ref = _resolve_call_target_ref(tracer, op)
    if target_ref is not None:
        return [(target_ref, [], "pcode_target_ref")]
    return []

def _impl__call_target_ref_is_resolved(target_ref: Optional[CallTargetRef]) -> bool:
    return _call_target_ref_analysis_key(target_ref) is not None

def _impl__call_target_ref_analysis_key(target_ref: Optional[CallTargetRef]) -> Optional[Tuple[object, ...]]:
    if target_ref is None:
        return None
    is_unknown = getattr(target_ref, "is_unknown", None)
    if callable(is_unknown):
        try:
            if is_unknown():
                return None
        except Exception:
            return None
    analysis_key = getattr(target_ref, "analysis_key", None)
    if callable(analysis_key):
        try:
            return analysis_key()
        except Exception:
            return None
    stable_key = getattr(target_ref, "stable_key", None)
    if not callable(stable_key):
        return None
    try:
        return stable_key()
    except Exception:
        return None

def _impl__resolve_call_target_ref(tracer, op) -> Optional[CallTargetRef]:
    if op is None or op.getNumInputs() < 1:
        return None

    mnemonic = op.getMnemonic()
    if mnemonic not in {"CALL", "CALLIND"}:
        return None

    try:
        target_varnode = op.getInput(0)
    except Exception:
        return None
    if target_varnode is None:
        return None

    resolver = getattr(tracer, "resolve_call_target_ref", None)
    if callable(resolver):
        resolved = resolver(
            target_varnode,
            allow_containing=True,
            allow_code_address=True,
        )
        resolved_ref = coerce_call_target_ref(resolved)
        if resolved_ref is not None:
            return resolved_ref

    address = None
    try:
        address = target_varnode.getAddress()
    except Exception:
        address = None

    resolved_from_address = _resolve_function_ref_from_address(tracer, address, allow_containing=True)
    if resolved_from_address is not None:
        return resolved_from_address

    traced_target = tracer.trace_varnode(target_varnode, use_cache=False)
    if traced_target.expr_type != ExpressionType.CONSTANT:
        return None

    try:
        target_value = int(traced_target.value)
    except Exception:
        return None

    resolved_from_value = _resolve_function_ref_by_value(tracer, target_value, exact=False)
    if resolved_from_value is not None:
        return resolved_from_value
    return CallTargetRef.from_code_address(target_value)

def _impl__resolve_call_target_expression(tracer, op) -> Optional[Expression]:
    if op is None or op.getNumInputs() < 1:
        return None
    try:
        target_varnode = op.getInput(0)
    except Exception:
        return None
    if target_varnode is None:
        return None
    try:
        return tracer.trace_varnode(target_varnode, use_cache=False)
    except Exception:
        return None

def _impl__resolve_call_target_name(tracer, op) -> Optional[str]:
    target_ref = _resolve_call_target_ref(tracer, op)
    if target_ref is None:
        return None
    return target_ref.display_name()

def _impl_resolve_call_targets(
    tracer,
    op,
    conditions: Optional[Sequence[Condition]] = None,
    parameters: Optional[Sequence[Dict]] = None,
    read_memory_value: Optional[Callable[[int, int], Optional[int]]] = None,
    image_base: Optional[int] = None,
    debug: bool = False,
) -> List[Tuple[CallTargetRef, List[Condition]]]:
    """Resolve CALL/CALLIND targets into finite (callee_ref, branch_conditions) pairs."""
    direct_target = _resolve_call_target_ref(tracer, op)
    if direct_target is not None and direct_target.is_function():
        return [(direct_target, [])]

    if op is None or op.getNumInputs() < 1:
        return []

    target_varnode = op.getInput(0)
    target_expr = tracer.trace_varnode(target_varnode, use_cache=False)
    if debug:
        print(f"[CallTargetResolver] traced target expr: {target_expr.to_string()}")

    if read_memory_value is not None:
        try:
            target_expr = concretize_readonly_loads(
                target_expr,
                list(conditions or []),
                list(parameters or []),
                read_memory_value,
                image_base=image_base,
                debug=debug,
            )
        except Exception:
            if debug:
                print("[CallTargetResolver] readonly target concretization failed")
    if debug:
        print(f"[CallTargetResolver] rewritten target expr: {target_expr.to_string()}")

    resolved: List[Tuple[CallTargetRef, List[Condition]]] = []
    for branch_conditions, address_value in _enumerate_constant_expression_branches(target_expr):
        target_ref = _resolve_function_ref_by_value(tracer, address_value, exact=True)
        if target_ref is None:
            target_ref = CallTargetRef.from_code_address(address_value)
        simplified = ConditionSimplifier.simplify_conditions(branch_conditions)
        resolved.append((target_ref, simplified))
        if debug:
            cond_strs = [cond.to_string() for cond in simplified]
            print(
                "[CallTargetResolver] resolved indirect target "
                f"0x{address_value:x} -> {target_ref.display_name()} under {cond_strs}"
            )

    if resolved:
        return _deduplicate_resolved_call_targets(resolved)

    if direct_target is not None and not direct_target.is_unknown():
        return [(direct_target, [])]
    return []

def _impl__deduplicate_resolved_call_targets(
    targets: Sequence[Tuple[CallTargetRef, List[Condition]]],
) -> List[Tuple[CallTargetRef, List[Condition]]]:
    deduped: List[Tuple[CallTargetRef, List[Condition]]] = []
    seen = set()
    for target_ref, conditions in targets:
        key = (
            target_ref.stable_key(),
            ConditionNormalizer.conditions_signature(conditions),
        )
        if key in seen:
            continue
        seen.add(key)
        deduped.append((target_ref, list(conditions)))
    return deduped

def _impl__resolve_function_ref_from_address(
    tracer,
    address,
    *,
    allow_containing: bool = True,
) -> Optional[CallTargetRef]:
    if tracer is None or getattr(tracer, "program", None) is None or address is None:
        return None
    try:
        func_manager = tracer.program.getFunctionManager()
        if func_manager is None:
            return None
        get_function_at = getattr(func_manager, "getFunctionAt", None)
        if callable(get_function_at):
            func = get_function_at(address)
            if func is not None:
                return CallTargetRef.from_function(func)
        get_referenced_function = getattr(func_manager, "getReferencedFunction", None)
        if callable(get_referenced_function):
            func = get_referenced_function(address)
            if func is not None:
                return CallTargetRef.from_function(func)
        if allow_containing:
            get_function_containing = getattr(func_manager, "getFunctionContaining", None)
            if callable(get_function_containing):
                func = get_function_containing(address)
                if func is not None:
                    return CallTargetRef.from_function(func)
    except Exception:
        return None
    return None

def _impl__resolve_function_ref_by_value(
    tracer,
    address_value: int,
    *,
    exact: bool = False,
) -> Optional[CallTargetRef]:
    try:
        if not isinstance(address_value, int) or address_value < 0:
            return None
        default_space = tracer.program.getAddressFactory().getDefaultAddressSpace()
        addr = default_space.getAddress(address_value)
    except Exception:
        return None
    return _resolve_function_ref_from_address(tracer, addr, allow_containing=not exact)
