"""Stateless effect-summary implementations."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.core import (
    AddressValueRef,
    CanonicalLocation,
    Condition,
    Expression,
    ExpressionType,
    LocationBaseRef,
    LocationStep,
    ObservedMemoryReadRef,
    PTRADD_OPCODE,
    PTRSUB_OPCODE,
    PostStateReadRef,
    PostStateSnapshotRef,
    PostStateValueRef,
)
from scripts.function_tracer_pcode.analysis.effects._shared import (
    ConditionSimplifier,
    StoreEffect,
)
from scripts.function_tracer_pcode.analysis.effects._api import (
    _build_alias_representative_map,
    _callee_argument_index_for_location_base,
    _callee_location_base_matches_ref,
    _canonicalize_address_expression,
    _canonicalize_expression_for_effect_value_identity,
    _coerce_callee_parameter_refs,
    _coerce_storage_info,
    _collect_definite_active_effects,
    _collect_param_equalities,
    _constant_factor,
    _expression_location_ref,
    _expression_matches_value_under_conditions,
    _expression_reads_location,
    _expression_truth_value,
    _extract_location_root_and_steps,
    _flatten_location_addition,
    _global_object_root_for_constant,
    _address_root_is_stack_frame,
    _is_stack_frame_base_expression,
    _iter_expression_nodes,
    _known_nonnull_address_comparison_truth,
    _location_sort_key,
    _location_step_sequence,
    _lookup_parameter_replacement,
    _merge_memory_runtime_ref,
    _normalize_canonical_location,
    _normalize_effect_locations_for_parameters,
    _normalize_location_steps,
    _normalize_parameter_index,
    _parameter_base_ref,
    _parameter_base_ref_matches_descriptor,
    _parameter_identity_key_from_base_ref,
    _post_state_read_name,
    _rebuild_expression_from_optional_operands,
    _reduce_expression_under_conditions,
    _resolve_alias_representative,
    _resolve_location_base_with_offset,
    _resolve_parameter_descriptor,
    _rewrite_expression_with_replayed_state,
    _simplify_boolean_binary_expression,
    _simplify_substituted_expression,
    _storage_base_ref,
    canonicalize_expr_read_location,
    canonicalize_location,
    locations_match,
    memory_expression_for_location,
    post_state_read_expression_for_location,
    substitute_condition,
    substitute_expression,
    subtract_implied_conditions,
)

def _impl__canonicalize_expression_for_effect_value_identity(
    expr: Optional[Expression],
    parameters: Sequence[Dict],
) -> Optional[Expression]:
    if expr is None:
        return None

    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        location = canonicalize_expr_read_location(expr, parameters)
        if location is not None:
            return post_state_read_expression_for_location(
                location,
                parameters,
                symbolic=True,
            )

    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, PostStateValueRef):
        expr = expr.clone_with(runtime_ref=None)

    if expr.expr_type == ExpressionType.PHI and expr.value:
        changed = False
        rewritten_branches = []
        for cond, value in expr.value:
            rewritten_cond = cond
            cond_expr = getattr(cond, "expression", None) if cond is not None else None
            if cond_expr is not None:
                canonicalized_cond_expr = _canonicalize_expression_for_effect_value_identity(
                    cond_expr,
                    parameters,
                )
                if canonicalized_cond_expr is not cond_expr:
                    rewritten_cond = Condition(canonicalized_cond_expr, cond.negated)
                    changed = True
            rewritten_value = _canonicalize_expression_for_effect_value_identity(
                value,
                parameters,
            )
            rewritten_branches.append((rewritten_cond, rewritten_value))
            changed = changed or (rewritten_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(rewritten_branches)
        rebuilt.size = expr.size
        return rebuilt

    operands = getattr(expr, "operands", None) or []
    rewritten_operands = [
        _canonicalize_expression_for_effect_value_identity(operand, parameters)
        for operand in operands
    ]
    if all(new is old for new, old in zip(rewritten_operands, operands)):
        return expr
    rebuilt = _rebuild_expression_from_optional_operands(
        expr,
        rewritten_operands,
        fallback=expr,
    )
    return rebuilt if rebuilt is not None else expr

def _impl__display_name_for_location_base(base_ref: LocationBaseRef) -> str:
    return base_ref.display_name()

def _impl__expression_location_ref(expr: Optional[Expression]) -> Optional[CanonicalLocation]:
    if expr is None:
        return None
    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, PostStateValueRef):
        return runtime_ref.location
    if isinstance(runtime_ref, PostStateReadRef):
        return runtime_ref.location
    if isinstance(runtime_ref, CanonicalLocation):
        return runtime_ref
    if isinstance(runtime_ref, ObservedMemoryReadRef):
        return runtime_ref.location
    return None

def _impl__memory_expr_with_runtime_location(
    address: Expression,
    size: int,
    *,
    read_order_key: Optional[int] = None,
    runtime_location: Optional[CanonicalLocation] = None,
    runtime_snapshot: Optional[PostStateSnapshotRef] = None,
    runtime_ref: Any = None,
) -> Expression:
    return Expression.memory(
        address,
        size=max(1, int(size or 0)),
        read_order_key=read_order_key,
        runtime_ref=_merge_memory_runtime_ref(runtime_ref, runtime_location, runtime_snapshot),
    )

def _impl_expression_contains_complex_location_reads(
    expr: Optional[Expression],
    parameters: Sequence[Dict],
) -> bool:
    for node in _iter_expression_nodes(expr):
        location_ref = _expression_location_ref(node)
        if location_ref is not None:
            return True
        if node.expr_type != ExpressionType.MEMORY or not node.operands:
            continue
        location = canonicalize_location(node.operands[0], parameters, size=node.size)
        if location is not None and getattr(location, "steps", ()):
            return True
    return False

def _impl__count_object_centric_location_reads(expr: Optional[Expression]) -> int:
    return sum(
        1
        for node in _iter_expression_nodes(expr)
        if _expression_location_ref(node) is not None
    )

def _impl__stack_location_key(varnode, size: int = 0) -> Optional[Tuple[str, int, int]]:
    if varnode is None:
        return None
    try:
        addr = varnode.getAddress()
        space = addr.getAddressSpace()
        if space is None or space.getName() != "stack":
            return None
        return ("stack", int(varnode.getOffset()), int(size or varnode.getSize()))
    except Exception:
        return None

def _impl_canonicalize_param_location(
    addr_expr: Expression,
    parameters: Sequence[Dict],
    size: int = 4,
) -> Optional[CanonicalLocation]:
    canonical = _canonicalize_address_expression(addr_expr, parameters, size=size)
    if canonical is None:
        return None
    if not canonical.base_ref.is_parameter():
        return None
    if not any(_parameter_base_ref_matches_descriptor(canonical.base_ref, param) for param in parameters):
        return None
    return canonical

def _impl_canonicalize_location(
    addr_expr: Expression,
    parameters: Sequence[Dict],
    size: int = 4,
) -> Optional[CanonicalLocation]:
    return _canonicalize_address_expression(addr_expr, parameters, size=size)

def _impl_substitute_location(
    location: CanonicalLocation,
    callee_params: Sequence[object],
    call_args: Sequence[Expression],
    caller_params: Sequence[Dict],
) -> Optional[CanonicalLocation]:
    if not (location.base_ref.is_parameter() or location.base_ref.is_storage()):
        return None
    callee_refs = _coerce_callee_parameter_refs(callee_params)
    arg_index = _callee_argument_index_for_location_base(location.base_ref, callee_refs)
    if arg_index is None or arg_index >= len(call_args):
        return None
    actual_addr = call_args[arg_index]
    caller_location = canonicalize_location(actual_addr, caller_params, size=location.size)
    if caller_location is None:
        return None
    composed_steps = _location_step_sequence(caller_location) + list(location.steps)
    return _normalize_canonical_location(
        CanonicalLocation(
            base_ref=caller_location.base_ref,
            offset=location.offset,
            size=location.size,
            steps=tuple(composed_steps),
        )
    )

def _impl__callee_argument_index_for_location_base(
    location_base: Optional[LocationBaseRef],
    callee_refs: Sequence[Optional[LocationBaseRef]],
) -> Optional[int]:
    if location_base is None:
        return None
    location_index = (
        _normalize_parameter_index(location_base.parameter_index)
        if location_base.is_parameter()
        else None
    )
    if location_index is not None and location_index < len(callee_refs):
        if _callee_location_base_matches_ref(location_base, callee_refs[location_index]):
            return location_index
    matches = [
        index
        for index, callee_ref in enumerate(callee_refs or [])
        if _callee_location_base_matches_ref(location_base, callee_ref)
    ]
    if len(matches) != 1:
        return None
    return matches[0]

def _impl__callee_location_base_matches_ref(
    location_base: Optional[LocationBaseRef],
    callee_ref: Optional[LocationBaseRef],
) -> bool:
    if location_base is None or callee_ref is None:
        return False
    location_key = _parameter_identity_key_from_base_ref(location_base)
    callee_key = _parameter_identity_key_from_base_ref(callee_ref)
    if location_key is not None and callee_key is not None and location_key == callee_key:
        return True
    if not (location_base.is_parameter() and callee_ref.is_parameter()):
        return False
    location_index = _normalize_parameter_index(location_base.parameter_index)
    callee_index = _normalize_parameter_index(callee_ref.parameter_index)
    if location_index is None or callee_index is None or location_index != callee_index:
        return False
    return (
        (location_base.owner_program_id is None and location_base.owner_entry_offset is None)
        or (callee_ref.owner_program_id is None and callee_ref.owner_entry_offset is None)
    )

def _impl__find_unique_effect_location_for_value(
    expr: Expression,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
) -> Optional[CanonicalLocation]:
    normalized_return_conditions = ConditionSimplifier.simplify_conditions_object_centric(list(return_conditions))
    normalized_expr = _canonicalize_expression_for_effect_value_identity(expr, parameters)
    if normalized_expr is None:
        return None
    matched_location: Optional[CanonicalLocation] = None
    for effect in effects:
        normalized_effect_conditions = ConditionSimplifier.simplify_conditions_object_centric(list(effect.conditions))
        if ConditionSimplifier.object_centric_is_contradiction(normalized_return_conditions + normalized_effect_conditions):
            continue
        if subtract_implied_conditions(normalized_effect_conditions, normalized_return_conditions):
            continue
        normalized_effect_value = _canonicalize_expression_for_effect_value_identity(
            effect.value,
            parameters,
        )
        if normalized_effect_value is None:
            continue
        if not _expression_matches_value_under_conditions(
            normalized_expr,
            normalized_effect_value,
            normalized_return_conditions + normalized_effect_conditions,
            parameters,
        ):
            continue
        if matched_location is None:
            matched_location = effect.location
            continue
        if matched_location != effect.location:
            return None
    return matched_location

def _impl_canonicalize_expr_read_location(expr: Expression, parameters: Sequence[Dict]) -> Optional[CanonicalLocation]:
    if expr is None:
        return None
    synthetic_location = _expression_location_ref(expr)
    if synthetic_location is not None:
        return synthetic_location
    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        return canonicalize_location(expr.operands[0], parameters, size=expr.size)
    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left = canonicalize_expr_read_location(expr.operands[0], parameters)
        right = canonicalize_expr_read_location(expr.operands[1], parameters)
        if left is None:
            return right
        if right is None:
            return left
        if left == right:
            return left
        return None
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        return canonicalize_expr_read_location(expr.operands[0], parameters)
    return None

def _impl__expression_reads_location(
    expr: Optional[Expression],
    location: CanonicalLocation,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict],
) -> bool:
    if expr is None:
        return False
    synthetic_location = _expression_location_ref(expr)
    if synthetic_location is not None:
        return locations_match(synthetic_location, location, conditions)
    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        read_location = canonicalize_location(expr.operands[0], parameters, size=expr.size)
        if read_location is None:
            return False
        return locations_match(read_location, location, conditions)
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            combined = list(conditions)
            if cond is not None:
                combined.append(cond)
            if _expression_reads_location(value, location, combined, parameters):
                return True
        return False
    for operand in getattr(expr, "operands", []) or []:
        if _expression_reads_location(operand, location, conditions, parameters):
            return True
    return False

def _impl__latest_definite_effect_value_for_location(
    location: CanonicalLocation,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
) -> Optional[Expression]:
    effects = _normalize_effect_locations_for_parameters(effects, parameters)
    normalized_return_conditions = ConditionSimplifier.simplify_conditions_object_centric(list(return_conditions))
    latest_effect: Optional[StoreEffect] = None
    for effect in effects:
        normalized_effect_conditions = ConditionSimplifier.simplify_conditions_object_centric(list(effect.conditions))
        if effect.location.size != location.size:
            continue
        if ConditionSimplifier.object_centric_is_contradiction(normalized_return_conditions + normalized_effect_conditions):
            continue
        if not locations_match(
            location,
            effect.location,
            normalized_return_conditions + normalized_effect_conditions,
        ):
            continue
        residual = subtract_implied_conditions(normalized_effect_conditions, normalized_return_conditions)
        if residual:
            continue
        if latest_effect is None or effect.order_key > latest_effect.order_key:
            latest_effect = effect
    return latest_effect.value if latest_effect is not None else None

def _impl__should_preserve_composite_location_wrapper(
    expr: Expression,
    expr_location: Optional[CanonicalLocation],
    parameters: Sequence[Dict],
    *,
    preserve_composite_location_wrappers: bool,
) -> bool:
    if not preserve_composite_location_wrappers or expr_location is None:
        return False
    for operand in expr.operands:
        operand_location = canonicalize_expr_read_location(operand, parameters)
        if operand_location != expr_location:
            continue
        if operand.expr_type != ExpressionType.MEMORY:
            return True
    return False

def _impl__replay_definite_active_effects_for_location(
    location: CanonicalLocation,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
) -> Optional[Expression]:
    effects = _normalize_effect_locations_for_parameters(effects, parameters)
    normalized_return_conditions = ConditionSimplifier.simplify_conditions_object_centric(
        list(return_conditions)
    )
    tracked_locations = sorted(
        {location, *[effect.location for effect in effects]},
        key=_location_sort_key,
    )
    alias_representatives = _build_alias_representative_map(
        tracked_locations,
        normalized_return_conditions,
    )
    if not alias_representatives:
        return None

    state: Dict[CanonicalLocation, Expression] = {}
    for representative in sorted(set(alias_representatives.values()), key=_location_sort_key):
        base_expr = memory_expression_for_location(representative, parameters)
        if base_expr is None:
            return None
        state[representative] = base_expr

    active_effects = _collect_definite_active_effects(normalized_return_conditions, effects)
    active_effects.sort(key=lambda effect: effect.order_key)
    for effect in active_effects:
        target_rep = _resolve_alias_representative(
            effect.location,
            alias_representatives,
            normalized_return_conditions,
        )
        if target_rep is None:
            continue
        replayed_value = _rewrite_expression_with_replayed_state(
            effect.value,
            normalized_return_conditions,
            state,
            alias_representatives,
            parameters,
        )
        if replayed_value is None:
            continue
        reduced_value = _reduce_expression_under_conditions(replayed_value, normalized_return_conditions)
        state[target_rep] = reduced_value if reduced_value is not None else replayed_value

    target_rep = _resolve_alias_representative(
        location,
        alias_representatives,
        normalized_return_conditions,
    )
    if target_rep is None:
        return None
    return state.get(target_rep)

def _impl__location_sort_key(location: CanonicalLocation) -> Tuple[Tuple[object, ...], Tuple[Tuple[str, int], ...], int, int]:
    normalized = _normalize_canonical_location(location)
    step_key = tuple((step.kind, int(step.value)) for step in normalized.steps)
    return (tuple(repr(part) for part in normalized.base_ref.stable_key()), step_key, normalized.offset, normalized.size)

def _impl_memory_expression_for_location(
    location: CanonicalLocation,
    parameters: Sequence[Dict],
) -> Expression:
    location = _normalize_canonical_location(location)
    param = next(
        (item for item in parameters if _parameter_base_ref_matches_descriptor(location.base_ref, item)),
        None,
    )
    if param is None:
        return Expression.variable(
            _post_state_read_name(location),
            size=max(1, location.size),
            runtime_ref=location,
        )

    try:
        param_index = int(param.get("index", -1))
    except Exception:
        param_index = -1

    try:
        param_size = int(param.get("size", 8))
    except Exception:
        param_size = 8
    param_size = max(1, param_size)

    base = Expression.parameter(
        location.base_ref.parameter_name or location.base_param,
        param_index,
        param.get("data_type"),
        param.get("data_type_obj"),
        param_size,
        storage_info=_coerce_storage_info(param.get("storage")),
        runtime_ref=_parameter_base_ref(
            name=location.base_ref.parameter_name or location.base_param,
            index=param_index,
        ),
    )
    addr: Expression = base
    for step in location.steps:
        if step.kind == "offset":
            addr = Expression.binary_op(
                "INT_ADD",
                addr,
                Expression.constant(step.value, max(1, addr.size or param_size)),
            )
            addr.size = max(1, addr.size or param_size)
            continue
        addr = Expression.memory(addr, size=max(1, int(step.value)))
    if location.offset != 0:
        addr = Expression.binary_op(
            "INT_ADD",
            addr,
            Expression.constant(location.offset, max(1, addr.size or param_size)),
        )
        addr.size = max(1, addr.size or param_size)

    return Expression.memory(addr, size=location.size)

def _impl_locations_match(
    left: CanonicalLocation,
    right: CanonicalLocation,
    conditions: Sequence[Condition],
) -> bool:
    left = _normalize_canonical_location(left)
    right = _normalize_canonical_location(right)
    if left.offset != right.offset:
        return False
    if left.steps != right.steps:
        return False
    if left.base_ref == right.base_ref:
        return True
    if not left.base_ref.is_parameter() or not right.base_ref.is_parameter():
        return False
    left_key = _parameter_identity_key_from_base_ref(left.base_ref)
    right_key = _parameter_identity_key_from_base_ref(right.base_ref)
    if left_key is None or right_key is None:
        return False
    equalities = _collect_param_equalities(conditions)
    return frozenset((left_key, right_key)) in equalities

def _impl_substitute_condition(
    condition: Condition,
    replacements: Dict[Tuple[object, ...], Expression],
    parameters: Optional[Sequence[Dict]] = None,
) -> Condition:
    return Condition(
        substitute_expression(condition.expression, replacements, parameters),
        condition.negated,
    )

def _impl_substitute_expression(
    expr: Expression,
    replacements: Dict[Tuple[object, ...], Expression],
    parameters: Optional[Sequence[Dict]] = None,
) -> Expression:
    replacement = _lookup_parameter_replacement(expr, replacements, parameters)
    if replacement is not None:
        return _simplify_substituted_expression(replacement, parameters)

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL, ExpressionType.INTRINSIC, ExpressionType.MEMORY):
        new_operands = [substitute_expression(op, replacements, parameters) for op in expr.operands]
        if all(new is old for new, old in zip(new_operands, expr.operands)):
            return _simplify_substituted_expression(expr, parameters)
        # Issue #281: field と runtime ref の扱いは `derive_with_operands` が決める。ref を保てなければ
        # `OperandDerivationRefused` が上がる。callee の元の node は caller の文脈では別の値なので、ここで
        # 元の node に戻してはいけない: 境界（呼び出しの展開・effect の置き換え）が展開をまるごとやめる
        rebuilt = expr.derive_with_operands(new_operands)
        return _simplify_substituted_expression(rebuilt, parameters)

    if expr.expr_type == ExpressionType.PHI and expr.value:
        branches = []
        changed = False
        for cond, value in expr.value:
            new_cond = substitute_condition(cond, replacements, parameters) if cond is not None else None
            new_value = substitute_expression(value, replacements, parameters)
            branches.append((new_cond, new_value))
            changed = changed or (new_cond is not cond or new_value is not value)
        if not changed:
            return _simplify_substituted_expression(expr, parameters)
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return _simplify_substituted_expression(rebuilt, parameters)

    return expr

def _impl__simplify_substituted_expression(
    expr: Expression,
    parameters: Optional[Sequence[Dict]] = None,
) -> Expression:
    if expr is None:
        return expr

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "BOOL_NEGATE" and expr.operands:
        truth_value = _expression_truth_value(expr.operands[0])
        if truth_value is not None:
            return Expression.constant(0 if truth_value else 1, size=1)
        return expr

    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left = expr.operands[0]
        right = expr.operands[1]

        if expr.operator in {"INT_EQUAL", "INT_NOTEQUAL"}:
            known_truth = _known_nonnull_address_comparison_truth(
                expr.operator,
                left,
                right,
                parameters,
            )
            if known_truth is not None:
                return Expression.constant(1 if known_truth else 0, size=1)

        if expr.operator in {"BOOL_AND", "BOOL_OR", "BOOL_XOR"}:
            simplified_bool = _simplify_boolean_binary_expression(expr.operator, left, right)
            if simplified_bool is not None:
                return simplified_bool
        return expr

    if expr.expr_type == ExpressionType.PHI and expr.value:
        simplified_branches = []
        changed = False
        for cond, value in expr.value:
            if cond is None:
                simplified_branches.append((None, value))
                continue
            truth_value = ConditionSimplifier.evaluate_condition_truth(cond)
            if truth_value is False:
                changed = True
                continue
            if truth_value is True:
                return value
            simplified_branches.append((cond, value))

        if not simplified_branches:
            return expr
        if len(simplified_branches) == 1:
            only_cond, only_value = simplified_branches[0]
            if only_cond is None or changed:
                return only_value
        if not changed and len(simplified_branches) == len(expr.value):
            return expr
        rebuilt = Expression.phi(simplified_branches)
        rebuilt.size = expr.size
        return rebuilt

    return expr

def _impl__normalize_location_steps(steps: Sequence[LocationStep]) -> Tuple[LocationStep, ...]:
    normalized: List[LocationStep] = []
    for step in steps:
        if step.kind == "offset" and int(step.value) == 0:
            continue
        if normalized and normalized[-1].kind == "offset" and step.kind == "offset":
            combined = normalized[-1].value + int(step.value)
            normalized[-1] = LocationStep("offset", combined)
            if normalized[-1].value == 0:
                normalized.pop()
            continue
        normalized.append(LocationStep(step.kind, int(step.value)))
    return tuple(normalized)

def _impl__location_step_sequence(location: CanonicalLocation) -> List[LocationStep]:
    steps: List[LocationStep] = list(getattr(location, "steps", ()) or ())
    if int(getattr(location, "offset", 0) or 0) != 0:
        steps.append(LocationStep("offset", int(location.offset)))
    return list(_normalize_location_steps(steps))

def _impl__normalize_canonical_location(location: CanonicalLocation) -> CanonicalLocation:
    normalized_steps = list(_normalize_location_steps(_location_step_sequence(location)))
    final_offset = 0
    if normalized_steps and normalized_steps[-1].kind == "offset":
        final_offset = int(normalized_steps.pop().value)
    return CanonicalLocation(
        base_ref=location.base_ref,
        offset=final_offset,
        size=max(1, int(location.size or 0)),
        steps=tuple(normalized_steps),
    )

def _impl__canonicalize_address_expression(
    expr: Expression,
    parameters: Sequence[Dict],
    size: int,
) -> Optional[CanonicalLocation]:
    parsed = _extract_location_root_and_steps(expr, parameters)
    if parsed is None:
        return None
    base_ref, steps = parsed
    return _normalize_canonical_location(
        CanonicalLocation(
            base_ref=base_ref,
            offset=0,
            size=max(1, int(size or 0)),
            steps=tuple(steps),
        )
    )

def _impl__global_object_root_for_constant(
    expr: Optional[Expression],
) -> Optional[Tuple[LocationBaseRef, List[LocationStep]]]:
    """Global-object base of a constant address carrying an ``AddressValueRef``.

    The tracer attaches an ``AddressValueRef`` (symbol, containing data
    object, block permissions) to constant addresses it derives from Ghidra;
    a constant inside a writable, non-volatile named data object canonicalises
    to ``LocationBaseRef.global_object`` plus the offset inside the object.
    Bare constants without Ghidra evidence stay unresolved (``None``).
    """

    if expr is None or expr.expr_type != ExpressionType.CONSTANT:
        return None
    runtime_ref = getattr(expr, "runtime_ref", None)
    if not isinstance(runtime_ref, AddressValueRef):
        return None
    identity = runtime_ref.global_object_identity()
    if identity is None:
        return None
    symbol_name, object_size, offset = identity
    base_ref = LocationBaseRef.global_object(
        symbol_name,
        object_size,
        space_name=runtime_ref.space_name,
    )
    steps: List[LocationStep] = []
    if int(offset) != 0:
        steps.append(LocationStep("offset", int(offset)))
    return base_ref, steps


def _impl_expression_reads_global_object(expr: Optional[Expression]) -> bool:
    """True when ``expr`` contains a memory read of a named writable global."""

    if expr is None:
        return False
    for node in _iter_expression_nodes(expr):
        if node.expr_type != ExpressionType.MEMORY or not node.operands:
            continue
        parsed = _extract_location_root_and_steps(node.operands[0], ())
        if parsed is not None and parsed[0].is_global():
            return True
    return False


def _impl_expression_reads_unidentified_writable_memory(expr: Optional[Expression]) -> bool:
    """True when ``expr`` reads writable memory at a constant address that has
    no global-object identity (stripped symbol, no data item, ...).

    Such a read is keyed by the absolute address only, which differs between
    binaries, so a surface built on it cannot unify.  Reads of *named* globals
    are rendered against a shared symbolic base address and are fine.
    """

    if expr is None:
        return False
    for node in _iter_expression_nodes(expr):
        if node.expr_type != ExpressionType.MEMORY or not node.operands:
            continue
        address = node.operands[0]
        while (
            address is not None
            and address.expr_type == ExpressionType.BINARY_OP
            and address.operator == "INDIRECT"
            and address.operands
        ):
            address = address.operands[0]
        if address is None or address.expr_type != ExpressionType.CONSTANT:
            continue
        runtime_ref = getattr(address, "runtime_ref", None)
        if not isinstance(runtime_ref, AddressValueRef):
            continue
        if runtime_ref.can_write is not True:
            continue
        if runtime_ref.global_object_identity() is None:
            return True
    return False


def _impl__address_root_is_stack_frame(expr: Optional[Expression]) -> bool:
    """True when the address expression is rooted at the stack/frame pointer.

    Used to prove that a store whose exact location cannot be canonicalised
    (symbolic index into a stack array, ...) still targets the current frame,
    which dies with the function and is therefore not observable.
    """

    seen = 0
    current = expr
    while current is not None and seen < 64:
        seen += 1
        if _is_stack_frame_base_expression(current):
            return True
        storage = _coerce_storage_info(getattr(current, "storage_info", None))
        if storage is not None and not storage.is_register and storage.space_name == "stack":
            return True
        expr_type = current.expr_type
        operands = list(getattr(current, "operands", None) or [])
        if expr_type == ExpressionType.UNARY_OP and current.operator in {"INT_ZEXT", "INT_SEXT", "CAST", "COPY"} and operands:
            current = operands[0]
            continue
        if expr_type == ExpressionType.BINARY_OP and current.operator in {
            "INT_ADD", "INT_SUB", "SUBPIECE",
        } and operands:
            current = operands[0]
            continue
        if expr_type == ExpressionType.INTRINSIC and (
            getattr(current, "name", None) in {"PTRADD", "PTRSUB"}
            or getattr(current, "opcode", None) in {PTRADD_OPCODE, PTRSUB_OPCODE}
        ) and operands:
            current = operands[0]
            continue
        if expr_type == ExpressionType.PHI and current.value:
            return all(
                _address_root_is_stack_frame(value) for _cond, value in current.value
            )
        return False
    return False


def _impl_classify_store_address(
    addr_expr: Optional[Expression],
    parameters: Sequence[Dict],
    size: int,
) -> Tuple[str, Optional[CanonicalLocation]]:
    """Classify the target of a memory write for the effect summary.

    Returns ``(kind, location)`` with ``kind`` one of ``"parameter"``
    (parameter-based memory, modelled), ``"global"`` (named writable global
    object, modelled), ``"stack_frame"`` (dies with the frame, excluded) or
    ``"unresolved"`` (observable or possibly observable memory whose identity
    could not be established: the caller must fail closed).
    """

    location = canonicalize_location(addr_expr, parameters, size=size)
    if location is not None:
        base_ref = location.base_ref
        if base_ref.is_parameter():
            if any(_parameter_base_ref_matches_descriptor(base_ref, param) for param in parameters):
                return "parameter", location
            return "unresolved", None
        if base_ref.is_global():
            return "global", location
        if base_ref.is_stack_frame():
            return "stack_frame", location
        return "unresolved", None
    if _address_root_is_stack_frame(addr_expr):
        return "stack_frame", None
    return "unresolved", None


def _impl__extract_location_root_and_steps(
    expr: Expression,
    parameters: Sequence[Dict],
) -> Optional[Tuple[LocationBaseRef, List[LocationStep]]]:
    if expr is None:
        return None

    if expr.expr_type == ExpressionType.CONSTANT:
        return _global_object_root_for_constant(expr)

    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INDIRECT":
        # ``INDIRECT(c, op)`` is the decompiler's "value after op" of the
        # varnode that held the constant address ``c``.  A constant that
        # carries a Ghidra object identity was loaded from a read-only pointer
        # slot (GOT); no op can change it, so the address is still ``c``.
        # Any other INDIRECT base stays unresolved.
        parsed = _extract_location_root_and_steps(expr.operands[0], parameters) if expr.operands else None
        if parsed is not None and parsed[0].is_global():
            return parsed
        return None

    if expr.expr_type == ExpressionType.PHI and expr.value:
        # Branch-merged address: usable only when every branch names the same
        # global object (otherwise the target is genuinely path dependent).
        resolved = None
        for _cond, value in expr.value:
            parsed = _extract_location_root_and_steps(value, parameters)
            if parsed is None or not parsed[0].is_global():
                return None
            key = (parsed[0].stable_key(), tuple(step.stable_key() for step in parsed[1]))
            if resolved is None:
                resolved = (key, parsed)
            elif resolved[0] != key:
                return None
        return resolved[1] if resolved is not None else None

    if expr.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE):
        resolved_base = _resolve_location_base_with_offset(expr, parameters)
        if resolved_base is None:
            return None
        base_ref, base_offset = resolved_base
        steps: List[LocationStep] = []
        if int(base_offset) != 0:
            steps.append(LocationStep("offset", int(base_offset)))
        return base_ref, steps

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_ZEXT", "INT_SEXT"} and expr.operands:
        return _extract_location_root_and_steps(expr.operands[0], parameters)

    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "SUBPIECE"
        and len(expr.operands) == 2
    ):
        source, offset = expr.operands
        if offset.expr_type == ExpressionType.CONSTANT and offset.value == 0:
            return _extract_location_root_and_steps(source, parameters)

    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        parsed = _extract_location_root_and_steps(expr.operands[0], parameters)
        if parsed is None:
            return None
        base_ref, steps = parsed
        steps = list(steps)
        steps.append(LocationStep("deref", max(1, int(expr.size or 0))))
        return base_ref, steps

    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "INT_ADD"
        and len(expr.operands) == 2
    ):
        left_const = _constant_factor(expr.operands[0])
        right_const = _constant_factor(expr.operands[1])
        if left_const is not None:
            parsed = _extract_location_root_and_steps(expr.operands[1], parameters)
            if parsed is None:
                return None
            base_ref, steps = parsed
            steps = list(steps)
            steps.append(LocationStep("offset", int(left_const)))
            return base_ref, steps
        if right_const is not None:
            parsed = _extract_location_root_and_steps(expr.operands[0], parameters)
            if parsed is None:
                return None
            base_ref, steps = parsed
            steps = list(steps)
            steps.append(LocationStep("offset", int(right_const)))
            return base_ref, steps
        return None

    if expr.expr_type == ExpressionType.INTRINSIC:
        mnemonic = getattr(expr, "name", None) or ""
        opcode = getattr(expr, "opcode", None)
        operands = getattr(expr, "operands", None) or []

        if (opcode == PTRSUB_OPCODE or mnemonic == "PTRSUB") and len(operands) == 2:
            base_parsed = _extract_location_root_and_steps(operands[0], parameters)
            offset_value = _constant_factor(operands[1])
            if base_parsed is None or offset_value is None:
                return None
            base_ref, steps = base_parsed
            steps = list(steps)
            if int(offset_value) != 0:
                steps.append(LocationStep("offset", int(offset_value)))
            return base_ref, steps

        if (opcode == PTRADD_OPCODE or mnemonic == "PTRADD") and len(operands) == 3:
            base_parsed = _extract_location_root_and_steps(operands[0], parameters)
            index_value = _constant_factor(operands[1])
            elem_value = _constant_factor(operands[2])
            if base_parsed is None or index_value is None or elem_value is None:
                return None
            base_ref, steps = base_parsed
            delta = int(index_value) * int(elem_value)
            steps = list(steps)
            if delta != 0:
                steps.append(LocationStep("offset", delta))
            return base_ref, steps

    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "INT_MULT"
        and len(expr.operands) == 2
    ):
        left_const = _constant_factor(expr.operands[0])
        right_const = _constant_factor(expr.operands[1])
        if left_const == 1:
            return _extract_location_root_and_steps(expr.operands[1], parameters)
        if right_const == 1:
            return _extract_location_root_and_steps(expr.operands[0], parameters)

    return None

def _impl__flatten_location_addition(
    expr: Expression,
    parameters: Sequence[Dict],
) -> Tuple[Optional[int], List[LocationBaseRef]]:
    if expr.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE):
        resolved_base = _resolve_location_base_with_offset(expr, parameters)
        if resolved_base is not None:
            base_ref, base_offset = resolved_base
            return base_offset, [base_ref]

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_ZEXT", "INT_SEXT"} and expr.operands:
        return _flatten_location_addition(expr.operands[0], parameters)

    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "SUBPIECE"
        and len(expr.operands) == 2
    ):
        source, offset = expr.operands
        if offset.expr_type == ExpressionType.CONSTANT and offset.value == 0:
            return _flatten_location_addition(source, parameters)

    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "INT_ADD"
        and len(expr.operands) == 2
    ):
        left_const, left_bases = _flatten_location_addition(expr.operands[0], parameters)
        right_const, right_bases = _flatten_location_addition(expr.operands[1], parameters)
        if left_const is None or right_const is None:
            return None, []
        return left_const + right_const, left_bases + right_bases

    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "INT_MULT"
        and len(expr.operands) == 2
    ):
        left_const = _constant_factor(expr.operands[0])
        right_const = _constant_factor(expr.operands[1])
        if left_const == 1:
            return _flatten_location_addition(expr.operands[1], parameters)
        if right_const == 1:
            return _flatten_location_addition(expr.operands[0], parameters)

    if expr.expr_type == ExpressionType.INTRINSIC:
        mnemonic = getattr(expr, "name", None) or ""
        opcode = getattr(expr, "opcode", None)
        operands = getattr(expr, "operands", None) or []

        if (opcode == PTRSUB_OPCODE or mnemonic == "PTRSUB") and len(operands) == 2:
            base_const, base_bases = _flatten_location_addition(operands[0], parameters)
            offset_value = _constant_factor(operands[1])
            if base_const is None or offset_value is None:
                return None, []
            return int(base_const) + int(offset_value), base_bases

        if (opcode == PTRADD_OPCODE or mnemonic == "PTRADD") and len(operands) == 3:
            base_const, base_bases = _flatten_location_addition(operands[0], parameters)
            index_value = _constant_factor(operands[1])
            elem_value = _constant_factor(operands[2])
            if base_const is None or index_value is None or elem_value is None:
                return None, []
            return int(base_const) + (int(index_value) * int(elem_value)), base_bases

    if expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
        return expr.value, []

    return None, []

def _impl__resolve_location_base_with_offset(
    expr: Expression,
    parameters: Sequence[Dict],
) -> Optional[Tuple[LocationBaseRef, int]]:
    param = _resolve_parameter_descriptor(expr, parameters)
    if param is not None:
        return _parameter_base_ref(
            name=param.get("name"),
            index=param.get("index"),
        ), 0

    if _is_stack_frame_base_expression(expr):
        return LocationBaseRef.stack_frame(), 0

    expr_storage = _coerce_storage_info(getattr(expr, "storage_info", None))
    if expr_storage is None:
        return None
    if not expr_storage.is_register and (expr_storage.space_name == "stack" or expr_storage.is_stack_pointer):
        return LocationBaseRef.stack_frame(), int(expr_storage.offset)
    base_ref = _storage_base_ref(expr_storage)
    if base_ref is None:
        return None
    return base_ref, 0
