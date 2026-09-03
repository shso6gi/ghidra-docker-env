"""Stateless effect-summary implementations."""

from __future__ import annotations

from typing import Any, Dict, FrozenSet, Optional, Sequence
from scripts.function_tracer_pcode.analysis.effects._shared import (
    AddressValueRef,
    CanonicalLocation,
    Condition,
    ConditionSimplifier,
    EffectSummary,
    Expression,
    ExpressionType,
    ObservedMemoryReadRef,
    PostStateReadRef,
    PostStateSnapshotRef,
    PostStateValueRef,
    StoreEffect,
    re,
)
from scripts.function_tracer_pcode.analysis.effects._api import (
    _all_residual_guards_empty,
    _attach_materialized_post_state_value_ref,
    _bind_location_to_parameter_identity,
    _build_alias_representative_map,
    _clone_expression_with_operands,
    _collect_definite_active_effects,
    _collect_named_parameter_names,
    _compute_effect_cycle_components,
    _count_object_centric_location_reads,
    _count_observed_loads,
    _encode_signed_token,
    _expression_contains_observed_loads,
    _expression_contains_phi,
    _expression_contains_value_reads,
    _expression_is_materialized_post_state_value,
    _expression_location_ref,
    _expression_matches_value_under_conditions,
    _expression_node_count,
    _expression_observed_order_key,
    _expression_observed_read_ref,
    _expression_post_state_snapshot_ref,
    _expression_post_state_value_ref,
    _expression_reads_location,
    _expression_symbolic_post_state_location_ref,
    _expressions_equivalent,
    _expressions_equivalent_under_conditions,
    _find_matching_effect_value,
    _find_unique_effect_location_for_value,
    _has_overlapping_guards,
    _iter_expression_nodes,
    _latest_definite_effect_value_for_location,
    _location_sort_key,
    _matches_existing_effect_value,
    _materialize_existing_effect_value_carrier,
    _memory_expr_with_runtime_location,
    _normalize_canonical_location,
    _normalize_effect_locations_for_parameters,
    _post_state_read_name,
    _read_program_memory_value,
    _rebuild_expression_from_optional_operands,
    _reduce_expression_under_conditions,
    _replay_definite_active_effects_for_location,
    _resolve_alias_representative,
    _resolve_existing_root_post_state_read,
    _resolve_function_ref_by_value,
    _rewrite_canonical_location_read,
    _rewrite_definite_post_state_subexpressions,
    _rewrite_expression_with_replayed_state,
    _should_preserve_composite_location_wrapper,
    _strip_materialized_post_state_value_refs,
    _strip_symbolic_post_state_runtime_refs,
    _summary_has_interdependent_writes,
    canonicalize_expr_read_location,
    canonicalize_location,
    canonicalize_post_state_subexpressions,
    collapse_equivalent_post_state_subexpressions,
    collapse_post_state_expr_to_canonical_memory,
    collapse_post_state_expr_to_canonical_read,
    default_post_state_snapshot_ref,
    expression_contains_complex_location_reads,
    expression_contains_post_state_reads,
    expression_matches_stale_post_state_replay,
    locations_match,
    lower_post_state_expression_for_smt,
    memory_expression_for_location,
    post_state_read_expression_for_location,
    promote_effect_subexpressions_to_post_state_reads,
    promote_effect_value_carrier_to_post_state_read,
    promote_effect_value_match_to_post_state_read,
    promote_observed_loads_to_post_state_reads,
    resolve_definite_post_state_read_for_location,
    rewrite_loads_from_effects,
    rewrite_observed_loads_from_effects,
    subtract_implied_conditions,
)

def _impl_default_post_state_snapshot_ref() -> PostStateSnapshotRef:
    return PostStateSnapshotRef.function_return()

def _impl__strip_materialized_post_state_value_refs(
    expr: Optional[Expression],
) -> Optional[Expression]:
    if expr is None:
        return None

    runtime_ref = getattr(expr, "runtime_ref", None)
    stripped_runtime_ref = None if isinstance(runtime_ref, PostStateValueRef) else runtime_ref

    if expr.expr_type == ExpressionType.PHI and expr.value:
        changed = stripped_runtime_ref != runtime_ref
        branches = []
        for cond, value in expr.value:
            new_value = _strip_materialized_post_state_value_refs(value)
            branches.append((cond, new_value))
            changed = changed or (new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt.clone_with(runtime_ref=stripped_runtime_ref)

    operands = getattr(expr, "operands", None) or []
    rewritten_operands = [
        _strip_materialized_post_state_value_refs(operand)
        for operand in operands
    ]
    if (
        stripped_runtime_ref == runtime_ref
        and all(new is old for new, old in zip(rewritten_operands, operands))
    ):
        return expr
    rebuilt = _rebuild_expression_from_optional_operands(
        expr,
        rewritten_operands,
        fallback=expr,
    )
    if rebuilt is None:
        return expr.clone_with(runtime_ref=stripped_runtime_ref)
    return rebuilt.clone_with(runtime_ref=stripped_runtime_ref)

def _impl__strip_symbolic_post_state_runtime_refs(
    expr: Optional[Expression],
) -> Optional[Expression]:
    if expr is None:
        return None

    runtime_ref = getattr(expr, "runtime_ref", None)
    stripped_runtime_ref = None if isinstance(runtime_ref, (CanonicalLocation, PostStateReadRef)) else runtime_ref

    if expr.expr_type == ExpressionType.PHI and expr.value:
        changed = stripped_runtime_ref != runtime_ref
        branches = []
        for cond, value in expr.value:
            new_value = _strip_symbolic_post_state_runtime_refs(value)
            branches.append((cond, new_value))
            changed = changed or (new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt.clone_with(runtime_ref=stripped_runtime_ref)

    operands = getattr(expr, "operands", None) or []
    rewritten_operands = [
        _strip_symbolic_post_state_runtime_refs(operand)
        for operand in operands
    ]
    if (
        stripped_runtime_ref == runtime_ref
        and all(new is old for new, old in zip(rewritten_operands, operands))
    ):
        return expr
    rebuilt = _rebuild_expression_from_optional_operands(
        expr,
        rewritten_operands,
        fallback=expr,
    )
    if rebuilt is None:
        return expr.clone_with(runtime_ref=stripped_runtime_ref)
    return rebuilt.clone_with(runtime_ref=stripped_runtime_ref)

def _impl__materialize_existing_effect_value_carrier(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
) -> Optional[Expression]:
    if expr is None:
        return None
    if expr.expr_type not in (
        ExpressionType.BINARY_OP,
        ExpressionType.UNARY_OP,
        ExpressionType.CALL,
        ExpressionType.INTRINSIC,
    ):
        return expr
    location = _find_unique_effect_location_for_value(
        expr,
        return_conditions,
        effects,
        parameters,
    )
    if location is None:
        return expr
    stripped = _strip_symbolic_post_state_runtime_refs(expr)
    if stripped is None or expression_contains_post_state_reads(stripped):
        return expr
    return _attach_materialized_post_state_value_ref(stripped, location)

def _impl__expression_post_state_value_ref(expr: Optional[Expression]) -> Optional[PostStateValueRef]:
    if expr is None:
        return None
    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, PostStateValueRef):
        return runtime_ref
    return None

def _impl__expression_post_state_read_ref(expr: Optional[Expression]) -> Optional[PostStateReadRef]:
    if expr is None:
        return None
    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, PostStateReadRef):
        return runtime_ref
    return None

def _impl__expression_is_materialized_post_state_value(expr: Optional[Expression]) -> bool:
    return _expression_post_state_value_ref(expr) is not None

def _impl__expression_symbolic_post_state_location_ref(
    expr: Optional[Expression],
) -> Optional[CanonicalLocation]:
    if expr is None:
        return None
    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, PostStateReadRef):
        return runtime_ref.location
    if isinstance(runtime_ref, CanonicalLocation):
        return runtime_ref
    return None

def _impl__expression_post_state_snapshot_ref(
    expr: Optional[Expression],
) -> Optional[PostStateSnapshotRef]:
    if expr is None:
        return None
    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, PostStateValueRef):
        return runtime_ref.snapshot_ref
    if isinstance(runtime_ref, PostStateReadRef):
        return runtime_ref.snapshot_ref
    if isinstance(runtime_ref, ObservedMemoryReadRef):
        return runtime_ref.snapshot_ref
    return None

def _impl__attach_materialized_post_state_value_ref(
    expr: Optional[Expression],
    location: Optional[CanonicalLocation],
    snapshot_ref: Optional[PostStateSnapshotRef] = None,
) -> Optional[Expression]:
    if expr is None or location is None:
        return expr
    normalized_location = _normalize_canonical_location(location)
    if snapshot_ref is None:
        snapshot_ref = _expression_post_state_snapshot_ref(expr)
    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        return Expression.memory(
            expr.operands[0],
            size=max(1, int(expr.size or 0)),
            read_order_key=expr.read_order_key,
            runtime_ref=PostStateValueRef(
                location=normalized_location,
                snapshot_ref=snapshot_ref,
            ),
        )
    runtime_ref = getattr(expr, "runtime_ref", None)
    desired_ref = PostStateValueRef(
        location=normalized_location,
        snapshot_ref=snapshot_ref,
    )
    if runtime_ref == desired_ref:
        return expr
    return expr.clone_with(runtime_ref=desired_ref)

def _impl__post_state_read_name(location: CanonicalLocation) -> str:
    normalized = _normalize_canonical_location(location)
    tokens = [
        "poststate",
        re.sub(r"[^0-9A-Za-z_]", "_", normalized.base_ref.display_name() or "loc").strip("_") or "loc",
    ]
    for step in normalized.steps:
        prefix = "off" if step.kind == "offset" else "deref"
        tokens.append(f"{prefix}_{_encode_signed_token(step.value)}")
    if normalized.offset != 0:
        tokens.append(f"tail_{_encode_signed_token(normalized.offset)}")
    tokens.append(f"size_{max(1, int(normalized.size or 0))}")
    return "_".join(tokens)

def _impl_expression_contains_post_state_reads(expr: Optional[Expression]) -> bool:
    for node in _iter_expression_nodes(expr):
        if _expression_symbolic_post_state_location_ref(node) is not None:
            return True
    return False

def _impl__expression_contains_observed_loads(expr: Optional[Expression]) -> bool:
    for node in _iter_expression_nodes(expr):
        if node.expr_type == ExpressionType.MEMORY and _expression_observed_order_key(node) is not None:
            return True
    return False

def _impl__count_observed_loads(expr: Optional[Expression]) -> int:
    count = 0
    for node in _iter_expression_nodes(expr):
        if node.expr_type == ExpressionType.MEMORY and _expression_observed_order_key(node) is not None:
            count += 1
    return count

def _impl_should_attempt_root_post_state_collapse(expr: Optional[Expression]) -> bool:
    """
    Root object-state collapse is only sound after we've left the observed-load
    timeline behind. A traced observed read still denotes a concrete runtime
    snapshot, so keep that shape until a later object-centric stage rewrites it.
    """
    return expr is not None and not _expression_contains_observed_loads(expr)

def _impl__materialize_function_pointer_argument(
    expr: Expression,
    tracer,
    varnode,
) -> Expression:
    if expr is None or expr.expr_type != ExpressionType.CONSTANT:
        return expr

    try:
        address_value = int(expr.value)
    except Exception:
        return expr

    direct_target = _resolve_function_ref_by_value(tracer, address_value, exact=False)
    if direct_target is not None:
        return expr

    try:
        pointer_size = int(tracer.program.getDefaultPointerSize())
    except Exception:
        pointer_size = int(getattr(varnode, "getSize", lambda: 0)() or expr.size or 0)
    if pointer_size <= 0:
        return expr

    loaded_value = _read_program_memory_value(tracer, address_value, pointer_size)
    if loaded_value is None:
        return expr

    resolved_target = _resolve_function_ref_by_value(tracer, loaded_value, exact=False)
    if resolved_target is None:
        return expr

    return Expression.constant(
        loaded_value,
        size=max(expr.size or 0, pointer_size),
        runtime_ref=AddressValueRef(
            address_offset=loaded_value,
            source="readonly_function_pointer",
            display_hint=resolved_target.display_name(),
            can_execute=True,
        ),
    )

def _impl_rewrite_loads_from_effects(
    expr: Expression,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    max_order_key: Optional[int] = None,
    blocked_locations: Optional[Sequence[CanonicalLocation]] = None,
    cycle_components: Optional[Dict[CanonicalLocation, FrozenSet[CanonicalLocation]]] = None,
    preserve_symbolic_fallback: bool = True,
) -> Expression:
    if expr is None:
        return expr

    active_blocked_locations = list(blocked_locations or [])
    active_cycle_components = cycle_components
    if active_cycle_components is None:
        active_cycle_components = _compute_effect_cycle_components(effects, parameters)

    synthetic_location = _expression_location_ref(expr)
    if expr.expr_type == ExpressionType.VARIABLE and synthetic_location is not None:
        fallback_expr = post_state_read_expression_for_location(
            synthetic_location,
            parameters,
            symbolic=preserve_symbolic_fallback,
        )
        if fallback_expr is None:
            fallback_expr = expr
        return _rewrite_canonical_location_read(
            fallback_expr,
            fallback_expr,
            synthetic_location,
            return_conditions,
            effects,
            parameters,
            max_order_key=max_order_key,
            blocked_locations=active_blocked_locations,
            cycle_components=active_cycle_components,
            definite_post_state=True,
            preserve_symbolic_fallback=preserve_symbolic_fallback,
        )

    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        synthetic_location = _expression_location_ref(expr)
        symbolic_post_state_location = _expression_symbolic_post_state_location_ref(expr)
        rewritten_addr = rewrite_loads_from_effects(
            expr.operands[0],
            return_conditions,
            effects,
            parameters,
            max_order_key=max_order_key,
            blocked_locations=active_blocked_locations,
            cycle_components=active_cycle_components,
            preserve_symbolic_fallback=preserve_symbolic_fallback,
        )
        location = canonicalize_location(rewritten_addr, parameters, size=expr.size)
        candidate = _memory_expr_with_runtime_location(
            rewritten_addr,
            expr.size,
            read_order_key=expr.read_order_key,
            runtime_location=synthetic_location,
            runtime_ref=getattr(expr, "runtime_ref", None),
        )
        if location is None:
            return candidate
        fallback_expr = candidate
        if not preserve_symbolic_fallback:
            concrete_fallback = memory_expression_for_location(location, parameters)
            if concrete_fallback is not None:
                fallback_expr = concrete_fallback
        return _rewrite_canonical_location_read(
            candidate,
            fallback_expr,
            location,
            return_conditions,
            effects,
            parameters,
            max_order_key=max_order_key,
            blocked_locations=active_blocked_locations,
            cycle_components=active_cycle_components,
            definite_post_state=(
                symbolic_post_state_location is not None
                and _expression_observed_read_ref(expr) is None
            ),
            preserve_symbolic_fallback=preserve_symbolic_fallback,
        )

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL, ExpressionType.INTRINSIC):
        if _expression_is_materialized_post_state_value(expr):
            return expr
        expr_location = canonicalize_expr_read_location(expr, parameters)
        if expr_location is not None:
            matching_effect = _find_matching_effect_value(
                expr,
                expr_location,
                return_conditions,
                effects,
                parameters,
                max_order_key=max_order_key,
            )
            if matching_effect is not None:
                effect_order, matched_value = matching_effect
                if not expression_contains_post_state_reads(expr):
                    return expr

                materialized_value = rewrite_loads_from_effects(
                    matched_value,
                    return_conditions,
                    effects,
                    parameters,
                    max_order_key=effect_order,
                    blocked_locations=active_blocked_locations,
                    cycle_components=active_cycle_components,
                    preserve_symbolic_fallback=preserve_symbolic_fallback,
                )
                if materialized_value is not None and not expression_contains_post_state_reads(materialized_value):
                    materialized_value = _attach_materialized_post_state_value_ref(
                        materialized_value,
                        expr_location,
                    )
                return materialized_value
        new_operands = [
            rewrite_loads_from_effects(
                op,
                return_conditions,
                effects,
                parameters,
                max_order_key=max_order_key,
                blocked_locations=active_blocked_locations,
                cycle_components=active_cycle_components,
                preserve_symbolic_fallback=preserve_symbolic_fallback,
            )
            for op in expr.operands
        ]
        return _clone_expression_with_operands(expr, new_operands) if not all(
            new is old for new, old in zip(new_operands, expr.operands)
        ) else expr

    if expr.expr_type == ExpressionType.PHI and expr.value:
        branches = []
        changed = False
        for cond, value in expr.value:
            combined_conditions = list(return_conditions)
            if cond is not None:
                combined_conditions.append(cond)
            new_value = rewrite_loads_from_effects(
                value,
                combined_conditions,
                effects,
                parameters,
                max_order_key=max_order_key,
                blocked_locations=active_blocked_locations,
                cycle_components=active_cycle_components,
                preserve_symbolic_fallback=preserve_symbolic_fallback,
            )
            branches.append((cond, new_value))
            changed = changed or (new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt

    return expr

def _impl_rewrite_location_read_from_effects(
    location: CanonicalLocation,
    fallback_expr: Expression,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    max_order_key: Optional[int] = None,
    blocked_locations: Optional[Sequence[CanonicalLocation]] = None,
    cycle_components: Optional[Dict[CanonicalLocation, FrozenSet[CanonicalLocation]]] = None,
    definite_post_state: bool = False,
    preserve_symbolic_fallback: bool = True,
) -> Expression:
    location = _bind_location_to_parameter_identity(location, parameters)
    effects = _normalize_effect_locations_for_parameters(effects, parameters)
    candidate = memory_expression_for_location(location, parameters)
    if candidate is None:
        return fallback_expr
    return _rewrite_canonical_location_read(
        candidate,
        fallback_expr,
        location,
        return_conditions,
        effects,
        parameters,
        max_order_key=max_order_key,
        blocked_locations=blocked_locations,
        cycle_components=cycle_components,
        definite_post_state=definite_post_state,
        preserve_symbolic_fallback=preserve_symbolic_fallback,
    )

def _impl__rewrite_canonical_location_read(
    candidate_expr: Expression,
    fallback_expr: Expression,
    location: CanonicalLocation,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    max_order_key: Optional[int] = None,
    blocked_locations: Optional[Sequence[CanonicalLocation]] = None,
    cycle_components: Optional[Dict[CanonicalLocation, FrozenSet[CanonicalLocation]]] = None,
    definite_post_state: bool = False,
    preserve_symbolic_fallback: bool = True,
) -> Expression:
    normalized_return_conditions = ConditionSimplifier.simplify_conditions_object_centric(list(return_conditions))
    active_blocked_locations = list(blocked_locations or [])
    active_cycle_components = cycle_components
    if active_cycle_components is None:
        active_cycle_components = _compute_effect_cycle_components(effects, parameters)

    if _matches_existing_effect_value(
        candidate_expr,
        location,
        normalized_return_conditions,
        effects,
        parameters,
        max_order_key=max_order_key,
    ):
        return candidate_expr

    for blocked_location in active_blocked_locations:
        if blocked_location.size != location.size:
            continue
        if locations_match(location, blocked_location, normalized_return_conditions):
            return fallback_expr

    matched = []
    for effect in effects:
        normalized_effect_conditions = ConditionSimplifier.simplify_conditions_object_centric(list(effect.conditions))
        if max_order_key is not None and effect.order_key >= max_order_key:
            continue
        if effect.location.size != location.size:
            continue
        if ConditionSimplifier.object_centric_is_contradiction(normalized_return_conditions + normalized_effect_conditions):
            continue
        if not locations_match(location, effect.location, normalized_return_conditions + normalized_effect_conditions):
            continue
        residual = subtract_implied_conditions(normalized_effect_conditions, normalized_return_conditions)
        matched.append((effect.order_key, residual, effect.value))

    if not matched:
        return fallback_expr

    if definite_post_state and _all_residual_guards_empty(matched):
        if not (
            len(effects) > 1
            and _summary_has_interdependent_writes(
                EffectSummary(
                    parameter_names=_collect_named_parameter_names(parameters),
                    effects=list(effects),
                )
            )
        ):
            replayed_state = _replay_definite_active_effects_for_location(
                location,
                normalized_return_conditions,
                effects,
                parameters,
            )
            if replayed_state is not None:
                if not expression_contains_post_state_reads(replayed_state):
                    replayed_state = _attach_materialized_post_state_value_ref(
                        replayed_state,
                        location,
                    )
                return replayed_state

    if _has_overlapping_guards(matched):
        return fallback_expr

    matched.sort(key=lambda item: item[0], reverse=True)
    branches = []
    for effect_order, residual, value in matched:
        preserved_locations = list(active_cycle_components.get(location, frozenset()))
        if location not in preserved_locations:
            preserved_locations.append(location)
        next_blocked_locations = active_blocked_locations + preserved_locations
        rewritten_value = rewrite_loads_from_effects(
            value,
            normalized_return_conditions,
            effects,
            parameters,
            max_order_key=effect_order,
            blocked_locations=next_blocked_locations,
            cycle_components=active_cycle_components,
            preserve_symbolic_fallback=preserve_symbolic_fallback,
        )
        if residual:
            branches.append((Condition.combine_and(residual), rewritten_value))
        else:
            return rewritten_value

    branches.append((None, fallback_expr))
    resolved = Expression.phi(branches)
    resolved.size = max(candidate_expr.size or 0, fallback_expr.size or 0, location.size)
    return resolved

def _impl_rewrite_observed_loads_from_effects(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
) -> Optional[Expression]:
    """
    Rewrite raw observed LOAD expressions into pre-state equivalents.

    This pass is intentionally narrower than rewrite_loads_from_effects():
    it only rewrites MEMORY leaves that still carry concrete LOAD provenance
    from the traced op, either via ``read_order_key`` or a structured
    ``ObservedMemoryReadRef`` runtime object.
    """
    if expr is None:
        return None

    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        rewritten_addr = rewrite_observed_loads_from_effects(
            expr.operands[0],
            return_conditions,
            effects,
            parameters,
        )
        current = expr
        if rewritten_addr is not expr.operands[0]:
            current = _memory_expr_with_runtime_location(
                rewritten_addr if rewritten_addr is not None else expr.operands[0],
                expr.size,
                read_order_key=expr.read_order_key,
                runtime_location=_expression_location_ref(expr),
                runtime_ref=getattr(expr, "runtime_ref", None),
            )

        max_order_key = _expression_observed_order_key(current)
        if max_order_key is None:
            return current

        rewritten = rewrite_loads_from_effects(
            current,
            return_conditions,
            effects,
            parameters,
            max_order_key=max_order_key,
        )
        return rewritten

    if expr.expr_type in (
        ExpressionType.BINARY_OP,
        ExpressionType.UNARY_OP,
        ExpressionType.CALL,
        ExpressionType.INTRINSIC,
    ):
        rewritten_operands = [
            rewrite_observed_loads_from_effects(
                op,
                return_conditions,
                effects,
                parameters,
            )
            for op in expr.operands
        ]
        rebuilt = _rebuild_expression_from_optional_operands(
            expr,
            rewritten_operands,
            fallback=expr,
        )
        return rebuilt if rebuilt is not None else expr

    if expr.expr_type == ExpressionType.PHI and expr.value:
        changed = False
        branches = []
        for cond, value in expr.value:
            combined_conditions = list(return_conditions)
            if cond is not None:
                combined_conditions.append(cond)
            new_value = rewrite_observed_loads_from_effects(
                value,
                combined_conditions,
                effects,
                parameters,
            )
            branches.append((cond, new_value))
            changed = changed or (new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt

    return expr

def _impl_promote_observed_loads_to_post_state_reads(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    *,
    symbolic_post_state: bool = False,
    snapshot_ref: Optional[PostStateSnapshotRef] = None,
    _address_context: bool = False,
) -> Optional[Expression]:
    """Rewrite observed LOAD leaves into shared post-state read objects.

    This is intentionally object-centric: every promoted leaf is rebound to the
    same post-state snapshot so later passes can reason about correlations
    across multiple reads from the same state, rather than treating each LOAD
    as an unrelated arithmetic leaf.
    """
    if expr is None:
        return None

    shared_snapshot = snapshot_ref or _expression_post_state_snapshot_ref(expr) or default_post_state_snapshot_ref()

    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        rewritten_addr = promote_observed_loads_to_post_state_reads(
            expr.operands[0],
            return_conditions,
            effects,
            parameters,
            symbolic_post_state=symbolic_post_state,
            snapshot_ref=shared_snapshot,
            _address_context=True,
        )
        current = expr
        if rewritten_addr is not expr.operands[0]:
            current = _memory_expr_with_runtime_location(
                rewritten_addr if rewritten_addr is not None else expr.operands[0],
                expr.size,
                read_order_key=expr.read_order_key,
                runtime_location=_expression_location_ref(expr),
                runtime_snapshot=_expression_post_state_snapshot_ref(expr) or shared_snapshot,
                runtime_ref=getattr(expr, "runtime_ref", None),
            )
        if _address_context:
            return current
        if _expression_observed_order_key(current) is None:
            return current
        location = canonicalize_expr_read_location(current, parameters)
        if location is None:
            return current
        promoted = post_state_read_expression_for_location(
            location,
            parameters,
            symbolic=symbolic_post_state,
            snapshot_ref=shared_snapshot,
        )
        if symbolic_post_state:
            return promoted
        lowered = lower_post_state_expression_for_smt(
            promoted,
            return_conditions,
            effects,
            parameters,
        )
        return lowered if lowered is not None else promoted

    if expr.expr_type in (
        ExpressionType.BINARY_OP,
        ExpressionType.UNARY_OP,
        ExpressionType.CALL,
        ExpressionType.INTRINSIC,
    ):
        rewritten_operands = [
            promote_observed_loads_to_post_state_reads(
                operand,
                return_conditions,
                effects,
                parameters,
                symbolic_post_state=symbolic_post_state,
                snapshot_ref=shared_snapshot,
                _address_context=_address_context,
            )
            for operand in expr.operands
        ]
        rebuilt = _rebuild_expression_from_optional_operands(
            expr,
            rewritten_operands,
            fallback=expr,
        )
        return rebuilt if rebuilt is not None else expr

    if expr.expr_type == ExpressionType.PHI and expr.value:
        changed = False
        branches = []
        for cond, value in expr.value:
            combined_conditions = list(return_conditions)
            if cond is not None:
                combined_conditions.append(cond)
            new_value = promote_observed_loads_to_post_state_reads(
                value,
                combined_conditions,
                effects,
                parameters,
                symbolic_post_state=symbolic_post_state,
                snapshot_ref=shared_snapshot,
                _address_context=_address_context,
            )
            branches.append((cond, new_value))
            changed = changed or (new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt

    return expr

def _impl_resolve_definite_post_state_read_for_location(
    location: CanonicalLocation,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    *,
    symbolic_post_state: bool = False,
) -> Optional[Expression]:
    location = _bind_location_to_parameter_identity(
        _normalize_canonical_location(location),
        parameters,
    )
    normalized_return_conditions = ConditionSimplifier.simplify_conditions_object_centric(list(return_conditions))
    active_effects = [
        StoreEffect(
            location=_bind_location_to_parameter_identity(effect.location, parameters),
            value=effect.value,
            conditions=list(effect.conditions or []),
            order_key=effect.order_key,
            provenance=effect.provenance,
        )
        for effect in _collect_definite_active_effects(normalized_return_conditions, effects)
    ]
    tracked_locations = sorted(
        {location, *[effect.location for effect in active_effects]},
        key=_location_sort_key,
    )
    alias_representatives = _build_alias_representative_map(
        tracked_locations,
        normalized_return_conditions,
    )
    if not alias_representatives:
        return None

    target_rep = _resolve_alias_representative(
        location,
        alias_representatives,
        normalized_return_conditions,
    )
    if target_rep is None:
        return None

    replayed = _replay_definite_active_effects_for_location(
        target_rep,
        normalized_return_conditions,
        active_effects,
        parameters,
    )
    if replayed is None:
        return None

    return post_state_read_expression_for_location(
        target_rep,
        parameters,
        symbolic=symbolic_post_state,
    )

def _impl_expression_matches_stale_post_state_replay(
    expr: Optional[Expression],
    target_post_state: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
) -> bool:
    if expr is None or target_post_state is None:
        return False

    target_location = _expression_location_ref(target_post_state)
    if target_location is None:
        target_location = canonicalize_expr_read_location(target_post_state, parameters)
    if target_location is None:
        return False

    normalized_return_conditions = ConditionSimplifier.simplify_conditions_object_centric(
        list(return_conditions)
    )
    active_effects = _collect_definite_active_effects(normalized_return_conditions, effects)
    if not active_effects:
        return False

    tracked_locations = sorted(
        {target_location, *[effect.location for effect in active_effects]},
        key=_location_sort_key,
    )
    alias_representatives = _build_alias_representative_map(
        tracked_locations,
        normalized_return_conditions,
    )
    if not alias_representatives:
        return False

    target_rep = _resolve_alias_representative(
        target_location,
        alias_representatives,
        normalized_return_conditions,
    )
    if target_rep is None:
        return False

    final_raw_state: Dict[CanonicalLocation, Expression] = {}
    for representative in sorted(set(alias_representatives.values()), key=_location_sort_key):
        final_value = _replay_definite_active_effects_for_location(
            representative,
            normalized_return_conditions,
            active_effects,
            parameters,
        )
        if final_value is None:
            return False
        reduced_final_value = _reduce_expression_under_conditions(
            final_value,
            normalized_return_conditions,
        )
        final_raw_state[representative] = (
            reduced_final_value if reduced_final_value is not None else final_value
        )

    def _matches_candidate(candidate: Optional[Expression]) -> bool:
        if candidate is None:
            return False
        reduced = _reduce_expression_under_conditions(candidate, normalized_return_conditions)
        normalized_candidate = reduced if reduced is not None else candidate
        return _expressions_equivalent_under_conditions(
            expr,
            normalized_candidate,
            normalized_return_conditions,
            parameters,
        )

    ordered_active_effects = sorted(active_effects, key=lambda effect: effect.order_key)
    for effect in ordered_active_effects:
        effect_rep = _resolve_alias_representative(
            effect.location,
            alias_representatives,
            normalized_return_conditions,
        )
        if effect_rep != target_rep:
            continue
        stale_candidate = _rewrite_expression_with_replayed_state(
            effect.value,
            normalized_return_conditions,
            final_raw_state,
            alias_representatives,
            parameters,
        )
        if _matches_candidate(stale_candidate):
            return True

    replayed_state = dict(final_raw_state)
    for effect in ordered_active_effects:
        effect_rep = _resolve_alias_representative(
            effect.location,
            alias_representatives,
            normalized_return_conditions,
        )
        if effect_rep is None:
            continue
        replayed_value = _rewrite_expression_with_replayed_state(
            effect.value,
            normalized_return_conditions,
            replayed_state,
            alias_representatives,
            parameters,
        )
        if replayed_value is None:
            continue
        reduced_value = _reduce_expression_under_conditions(
            replayed_value,
            normalized_return_conditions,
        )
        replayed_state[effect_rep] = reduced_value if reduced_value is not None else replayed_value

    full_replay = replayed_state.get(target_rep)
    return _matches_candidate(full_replay)

def _impl_promote_effect_value_match_to_post_state_read(
    expr: Optional[Expression],
    location: CanonicalLocation,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    *,
    symbolic_post_state: bool = False,
) -> Optional[Expression]:
    if expr is None:
        return None
    effects = _normalize_effect_locations_for_parameters(effects, parameters)

    normalized_return_conditions = ConditionSimplifier.simplify_conditions_object_centric(
        list(return_conditions)
    )
    if not _expression_reads_location(expr, location, normalized_return_conditions, parameters):
        return None

    matched_definite_effect = False
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
        residual = subtract_implied_conditions(
            normalized_effect_conditions,
            normalized_return_conditions,
        )
        if residual:
            continue
        if _expression_matches_value_under_conditions(
            expr,
            effect.value,
            normalized_return_conditions + normalized_effect_conditions,
            parameters,
        ):
            matched_definite_effect = True
            break

    if not matched_definite_effect:
        return None

    post_state_read = resolve_definite_post_state_read_for_location(
        location,
        normalized_return_conditions,
        effects,
        parameters,
        symbolic_post_state=symbolic_post_state,
    )
    if post_state_read is None:
        return None

    lowered_post_state_read = lower_post_state_expression_for_smt(
        post_state_read,
        normalized_return_conditions,
        effects,
        parameters,
    )
    if lowered_post_state_read is None:
        return None
    if not _expressions_equivalent_under_conditions(
        lowered_post_state_read,
        expr,
        normalized_return_conditions,
        parameters,
    ):
        return None

    return post_state_read

def _impl_promote_effect_value_carrier_to_post_state_read(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    *,
    symbolic_post_state: bool = False,
) -> Optional[Expression]:
    if expr is None:
        return None

    location = _find_unique_effect_location_for_value(
        expr,
        return_conditions,
        effects,
        parameters,
    )
    if location is None:
        return None

    normalized_return_conditions = ConditionSimplifier.simplify_conditions_object_centric(list(return_conditions))
    if not _expression_reads_location(expr, location, normalized_return_conditions, parameters):
        return None

    return resolve_definite_post_state_read_for_location(
        location,
        normalized_return_conditions,
        effects,
        parameters,
        symbolic_post_state=symbolic_post_state,
    )

def _impl_collapse_post_state_expr_to_canonical_memory(
    expr: Optional[Expression],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    return_conditions: Optional[Sequence[Condition]] = None,
) -> Optional[Expression]:
    return collapse_post_state_expr_to_canonical_read(
        expr,
        effects,
        parameters,
        return_conditions=return_conditions,
        symbolic_post_state=False,
    )

def _impl_collapse_post_state_expr_to_canonical_read(
    expr: Optional[Expression],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    return_conditions: Optional[Sequence[Condition]] = None,
    *,
    symbolic_post_state: bool = False,
) -> Optional[Expression]:
    if expr is None or not effects or not parameters:
        return None
    if not _expression_contains_value_reads(expr):
        return None

    active_conditions = list(return_conditions or [])
    resolved_root = _resolve_existing_root_post_state_read(
        expr,
        active_conditions,
        effects,
        parameters,
        symbolic_post_state=symbolic_post_state,
    )
    if resolved_root is not None:
        return resolved_root

    expr_is_memory = expr.expr_type == ExpressionType.MEMORY and bool(expr.operands)
    normalized_expr = expr
    candidate_effects = list(effects)
    memory_location = None

    if expr_is_memory:
        memory_location = canonicalize_location(expr.operands[0], parameters, size=expr.size)
        if memory_location is None:
            return None
        if expr.read_order_key is not None:
            candidate_effects = [effect for effect in effects if effect.order_key < expr.read_order_key]
            rewritten_observed = rewrite_observed_loads_from_effects(
                expr,
                active_conditions,
                effects,
                parameters,
            )
            if rewritten_observed is not None:
                normalized_expr = rewritten_observed
        else:
            if _replay_definite_active_effects_for_location(
                memory_location,
                active_conditions,
                effects,
                parameters,
            ) is None:
                return None

    reduced_expr = _reduce_expression_under_conditions(normalized_expr, active_conditions)
    normalized_expr = reduced_expr if reduced_expr is not None else normalized_expr

    locations = sorted(
        {effect.location for effect in candidate_effects},
        key=_location_sort_key,
    )
    same_location_fallback: Optional[Expression] = None
    for location in locations:
        candidate = post_state_read_expression_for_location(
            location,
            parameters,
            symbolic=symbolic_post_state,
        )
        if candidate is None:
            continue
        if expr_is_memory and expr.read_order_key is None:
            latest_value = _latest_definite_effect_value_for_location(
                location,
                active_conditions,
                candidate_effects,
                parameters,
            )
            if latest_value is not None:
                normalized_latest_value = _reduce_expression_under_conditions(latest_value, active_conditions)
                if _expressions_equivalent_under_conditions(
                    normalized_expr,
                    normalized_latest_value,
                    active_conditions,
                    parameters,
                ):
                    return candidate
            if memory_location is not None and locations_match(location, memory_location, active_conditions):
                same_location_fallback = candidate
        rewritten = rewrite_loads_from_effects(
            candidate,
            active_conditions,
            candidate_effects,
            parameters,
        )
        normalized_rewritten = _reduce_expression_under_conditions(rewritten, active_conditions)
        if expr_is_memory and expr.read_order_key is None:
            if _expressions_equivalent_under_conditions(
                normalized_expr,
                normalized_rewritten,
                active_conditions,
                parameters,
            ):
                return candidate
        if _expressions_equivalent_under_conditions(
            normalized_expr,
            normalized_rewritten,
            active_conditions,
            parameters,
        ):
            return candidate
        replayed = _replay_definite_active_effects_for_location(
            location,
            active_conditions,
            candidate_effects,
            parameters,
        )
        if replayed is None:
            continue
        normalized_replayed = _reduce_expression_under_conditions(replayed, active_conditions)
        if _expressions_equivalent_under_conditions(
            normalized_expr,
            normalized_replayed,
            active_conditions,
            parameters,
        ):
            if expr_is_memory and expr.read_order_key is not None:
                final_replayed = _replay_definite_active_effects_for_location(
                    location,
                    active_conditions,
                    effects,
                    parameters,
                )
                if final_replayed is not None:
                    normalized_final_replayed = _reduce_expression_under_conditions(final_replayed, active_conditions)
                    if not _expressions_equivalent_under_conditions(
                        normalized_replayed,
                        normalized_final_replayed,
                        active_conditions,
                        parameters,
                    ):
                        continue
            return candidate
    if same_location_fallback is not None:
        return same_location_fallback
    return None

def _impl__resolve_existing_root_post_state_read(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    *,
    symbolic_post_state: bool = False,
) -> Optional[Expression]:
    root_location = _expression_location_ref(expr)
    if root_location is None:
        return None
    return resolve_definite_post_state_read_for_location(
        root_location,
        return_conditions,
        effects,
        parameters,
        symbolic_post_state=symbolic_post_state,
    )

def _impl_promote_effect_subexpressions_to_post_state_reads(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    *,
    symbolic_post_state: bool = False,
    _address_context: bool = False,
) -> Optional[Expression]:
    if expr is None:
        return None

    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        rewritten_addr = promote_effect_subexpressions_to_post_state_reads(
            expr.operands[0],
            return_conditions,
            effects,
            parameters,
            symbolic_post_state=symbolic_post_state,
            _address_context=True,
        )
        rebuilt_memory = expr
        if rewritten_addr is not expr.operands[0]:
            rebuilt_memory = _memory_expr_with_runtime_location(
                rewritten_addr if rewritten_addr is not None else expr.operands[0],
                expr.size,
                read_order_key=expr.read_order_key,
                runtime_location=_expression_location_ref(expr),
                runtime_ref=getattr(expr, "runtime_ref", None),
            )
        if _address_context:
            return rebuilt_memory
        location = canonicalize_expr_read_location(rebuilt_memory, parameters)
        if location is None:
            return rebuilt_memory
        promoted = promote_effect_value_match_to_post_state_read(
            rebuilt_memory,
            location,
            return_conditions,
            effects,
            parameters,
            symbolic_post_state=symbolic_post_state,
        )
        return promoted if promoted is not None else rebuilt_memory

    if expr.expr_type in (
        ExpressionType.BINARY_OP,
        ExpressionType.UNARY_OP,
        ExpressionType.CALL,
        ExpressionType.INTRINSIC,
    ):
        rewritten_operands = [
            promote_effect_subexpressions_to_post_state_reads(
                operand,
                return_conditions,
                effects,
                parameters,
                symbolic_post_state=symbolic_post_state,
                _address_context=_address_context,
            )
            for operand in expr.operands
        ]
        rebuilt = _rebuild_expression_from_optional_operands(
            expr,
            rewritten_operands,
            fallback=expr,
        )
        current = rebuilt if rebuilt is not None else expr
        if _address_context:
            return current
        location = canonicalize_expr_read_location(current, parameters)
        if location is None:
            return current
        promoted = promote_effect_value_match_to_post_state_read(
            current,
            location,
            return_conditions,
            effects,
            parameters,
            symbolic_post_state=symbolic_post_state,
        )
        return promoted if promoted is not None else current

    if expr.expr_type == ExpressionType.PHI and expr.value:
        changed = False
        branches = []
        for cond, value in expr.value:
            combined_conditions = list(return_conditions)
            if cond is not None:
                combined_conditions.append(cond)
            new_value = promote_effect_subexpressions_to_post_state_reads(
                value,
                combined_conditions,
                effects,
                parameters,
                symbolic_post_state=symbolic_post_state,
                _address_context=_address_context,
            )
            branches.append((cond, new_value))
            changed = changed or (new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt

    return expr

def _impl_collapse_equivalent_post_state_subexpressions(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    *,
    symbolic_post_state: bool = False,
    _address_context: bool = False,
) -> Optional[Expression]:
    if expr is None:
        return None

    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        rewritten_addr = collapse_equivalent_post_state_subexpressions(
            expr.operands[0],
            return_conditions,
            effects,
            parameters,
            symbolic_post_state=symbolic_post_state,
            _address_context=True,
        )
        rebuilt_memory = expr
        if rewritten_addr is not expr.operands[0]:
            rebuilt_memory = _memory_expr_with_runtime_location(
                rewritten_addr if rewritten_addr is not None else expr.operands[0],
                expr.size,
                read_order_key=expr.read_order_key,
                runtime_location=_expression_location_ref(expr),
                runtime_ref=getattr(expr, "runtime_ref", None),
            )
        if _address_context:
            return rebuilt_memory
        current = rebuilt_memory
    elif expr.expr_type in (
        ExpressionType.BINARY_OP,
        ExpressionType.UNARY_OP,
        ExpressionType.CALL,
        ExpressionType.INTRINSIC,
    ):
        rewritten_operands = [
            collapse_equivalent_post_state_subexpressions(
                operand,
                return_conditions,
                effects,
                parameters,
                symbolic_post_state=symbolic_post_state,
                _address_context=_address_context,
            )
            for operand in expr.operands
        ]
        rebuilt = _rebuild_expression_from_optional_operands(
            expr,
            rewritten_operands,
            fallback=expr,
        )
        current = rebuilt if rebuilt is not None else expr
        if _address_context:
            return current
    elif expr.expr_type == ExpressionType.PHI and expr.value:
        changed = False
        branches = []
        for cond, value in expr.value:
            combined_conditions = list(return_conditions)
            if cond is not None:
                combined_conditions.append(cond)
            new_value = collapse_equivalent_post_state_subexpressions(
                value,
                combined_conditions,
                effects,
                parameters,
                symbolic_post_state=symbolic_post_state,
                _address_context=_address_context,
            )
            branches.append((cond, new_value))
            changed = changed or (new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt
    else:
        return expr

    location = canonicalize_expr_read_location(current, parameters)
    if location is None:
        return current
    post_state_read = resolve_definite_post_state_read_for_location(
        location,
        return_conditions,
        effects,
        parameters,
        symbolic_post_state=symbolic_post_state,
    )
    if post_state_read is None:
        return current
    if _expressions_equivalent_under_conditions(
        current,
        post_state_read,
        return_conditions,
        parameters,
    ):
        return post_state_read
    return current

def _impl_collapse_pruned_post_state_memory_leaf_to_canonical_memory(
    expr: Optional[Expression],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    return_conditions: Optional[Sequence[Condition]] = None,
) -> Optional[Expression]:
    """
    Resolve a bare MEMORY leaf back to the canonical post-state location.

    This is only sound when the leaf is known to come from a pruned post-state
    PHI/MULTIEQUAL, such as a nested MULTIEQUAL that a prior simplifier already
    reduced to one surviving branch.
    """
    return collapse_post_state_expr_to_canonical_memory(
        expr,
        effects,
        parameters,
        return_conditions=return_conditions,
    )

def _impl_canonicalize_post_state_subexpressions(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    *,
    symbolic_post_state: bool = False,
    allow_memory_leaf_collapse: bool = False,
    _collapse_current: bool = False,
) -> Optional[Expression]:
    if expr is None:
        return None

    if allow_memory_leaf_collapse or (
        _collapse_current and expr.expr_type != ExpressionType.MEMORY
    ):
        collapsed = collapse_post_state_expr_to_canonical_read(
            expr,
            effects,
            parameters,
            return_conditions=return_conditions,
            symbolic_post_state=symbolic_post_state,
        )
        if collapsed is not None:
            return collapsed

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL, ExpressionType.INTRINSIC, ExpressionType.MEMORY):
        rewritten_operands = [
            canonicalize_post_state_subexpressions(
                op,
                return_conditions,
                effects,
                parameters,
                symbolic_post_state=symbolic_post_state,
                allow_memory_leaf_collapse=False,
                _collapse_current=True,
            )
            for op in expr.operands
        ]
        rebuilt = _rebuild_expression_from_optional_operands(
            expr,
            rewritten_operands,
            fallback=expr,
        )
        return rebuilt if rebuilt is not None else expr

    if expr.expr_type == ExpressionType.PHI and expr.value:
        changed = False
        branches = []
        for cond, value in expr.value:
            combined_conditions = list(return_conditions)
            if cond is not None:
                combined_conditions.append(cond)
            new_value = canonicalize_post_state_subexpressions(
                value,
                combined_conditions,
                effects,
                parameters,
                symbolic_post_state=symbolic_post_state,
                allow_memory_leaf_collapse=False,
                _collapse_current=True,
            )
            branches.append((cond, new_value))
            changed = changed or (new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt

    return expr

def _impl_normalize_post_state_expression(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    *,
    prefer_canonical_post_state: bool = True,
    symbolic_post_state: bool = False,
    preserve_composite_location_wrappers: bool = False,
) -> Optional[Expression]:
    """
    Normalize equivalent post-state expressions to a stable canonical form.

    The pipeline may derive semantically equivalent results in two shapes:
    1. canonical post-state memory (e.g. MEM[param])
    2. pre-state expressions reconstructed from guarded store effects

    Converting both shapes through the same canonicalization step keeps
    equivalent branches comparable across architectures and optimization levels.
    """
    if expr is None:
        return None

    shared_snapshot = _expression_post_state_snapshot_ref(expr) or default_post_state_snapshot_ref()
    allow_observed_snapshot_promotion = _count_observed_loads(expr) >= 2

    def _normalize_candidate(candidate_expr: Expression) -> Expression:
        if prefer_canonical_post_state and symbolic_post_state:
            carrier_post_state_read = promote_effect_value_carrier_to_post_state_read(
                candidate_expr,
                return_conditions,
                effects,
                parameters,
                symbolic_post_state=True,
            )
            if carrier_post_state_read is not None:
                return carrier_post_state_read

        if (
            allow_observed_snapshot_promotion
            and prefer_canonical_post_state
            and symbolic_post_state
            and _expression_contains_observed_loads(candidate_expr)
        ):
            promoted_observed = promote_observed_loads_to_post_state_reads(
                candidate_expr,
                return_conditions,
                effects,
                parameters,
                symbolic_post_state=True,
                snapshot_ref=shared_snapshot,
            )
            if promoted_observed is not None:
                candidate_expr = promoted_observed

        early_materialized = _materialize_existing_effect_value_carrier(
            candidate_expr,
            return_conditions,
            effects,
            parameters,
        )
        if (
            early_materialized is not None
            and early_materialized is not candidate_expr
            and _expression_contains_observed_loads(candidate_expr)
        ):
            reduced_early = _reduce_expression_under_conditions(
                early_materialized,
                return_conditions,
            )
            return reduced_early if reduced_early is not None else early_materialized

        normalized = candidate_expr

        if prefer_canonical_post_state:
            canonicalized = canonicalize_post_state_subexpressions(
                normalized,
                return_conditions,
                effects,
                parameters,
                symbolic_post_state=symbolic_post_state,
                allow_memory_leaf_collapse=True,
            )
            if canonicalized is not None:
                normalized = canonicalized

            promoted = promote_effect_subexpressions_to_post_state_reads(
                normalized,
                return_conditions,
                effects,
                parameters,
                symbolic_post_state=symbolic_post_state,
            )
            if promoted is not None:
                normalized = promoted

            collapsed_equivalent = collapse_equivalent_post_state_subexpressions(
                normalized,
                return_conditions,
                effects,
                parameters,
                symbolic_post_state=symbolic_post_state,
            )
            if collapsed_equivalent is not None:
                normalized = collapsed_equivalent

        materialized_effect_value = _materialize_existing_effect_value_carrier(
            normalized,
            return_conditions,
            effects,
            parameters,
        )
        if materialized_effect_value is not None:
            normalized = materialized_effect_value

        post_state_promoted = (
            expression_contains_post_state_reads(normalized)
            and not expression_contains_post_state_reads(candidate_expr)
        )
        candidate_location = canonicalize_expr_read_location(candidate_expr, parameters)
        if prefer_canonical_post_state and candidate_location is not None:
            stale_post_state_read = resolve_definite_post_state_read_for_location(
                candidate_location,
                return_conditions,
                effects,
                parameters,
                symbolic_post_state=symbolic_post_state,
            )
            if expression_matches_stale_post_state_replay(
                candidate_expr,
                stale_post_state_read,
                return_conditions,
                effects,
                parameters,
            ):
                return stale_post_state_read
        candidate_is_stale_effect_carrier = False
        if candidate_location is not None and candidate_expr.expr_type in (
            ExpressionType.BINARY_OP,
            ExpressionType.UNARY_OP,
            ExpressionType.CALL,
            ExpressionType.INTRINSIC,
        ):
            candidate_is_stale_effect_carrier = (
                promote_effect_value_match_to_post_state_read(
                    candidate_expr,
                    candidate_location,
                    return_conditions,
                    effects,
                    parameters,
                    symbolic_post_state=symbolic_post_state,
                )
                is not None
            )
        candidate_is_composite_observed = (
            candidate_expr.expr_type in (
                ExpressionType.BINARY_OP,
                ExpressionType.UNARY_OP,
                ExpressionType.CALL,
                ExpressionType.INTRINSIC,
            )
            and _expression_contains_observed_loads(candidate_expr)
        )

        if not prefer_canonical_post_state or (
            _expressions_equivalent(normalized, candidate_expr)
            and not post_state_promoted
        ):
            if not candidate_is_stale_effect_carrier and not candidate_is_composite_observed:
                rewritten_definite = _rewrite_definite_post_state_subexpressions(
                    normalized,
                    return_conditions,
                    effects,
                    parameters,
                    preserve_composite_location_wrappers=preserve_composite_location_wrappers,
                )
                if rewritten_definite is not None:
                    normalized = rewritten_definite

        if (
            expression_contains_complex_location_reads(normalized, parameters)
            and not expression_contains_post_state_reads(normalized)
        ):
            rewritten_post_state = rewrite_loads_from_effects(
                normalized,
                return_conditions,
                effects,
                parameters,
            )
            if rewritten_post_state is not None:
                normalized = rewritten_post_state

        reduced = _reduce_expression_under_conditions(normalized, return_conditions)
        return reduced if reduced is not None else normalized

    observed_normalized = None
    if allow_observed_snapshot_promotion and _expression_contains_observed_loads(expr):
        rewritten_observed = promote_observed_loads_to_post_state_reads(
            expr,
            return_conditions,
            effects,
            parameters,
            symbolic_post_state=symbolic_post_state,
            snapshot_ref=shared_snapshot,
        )
        if rewritten_observed is None or _expressions_equivalent(rewritten_observed, expr):
            rewritten_observed = rewrite_observed_loads_from_effects(
                expr,
                return_conditions,
                effects,
                parameters,
            )
        if (
            rewritten_observed is not None
            and not _expressions_equivalent(rewritten_observed, expr)
        ):
            observed_normalized = _normalize_candidate(rewritten_observed)

    normalized = _normalize_candidate(expr)

    if observed_normalized is not None:
        normalized_rank = (
            1 if expression_contains_post_state_reads(normalized) else 0,
            _count_object_centric_location_reads(normalized),
            1 if not _expression_contains_phi(normalized) else 0,
            -_expression_node_count(normalized),
        )
        observed_rank = (
            1 if expression_contains_post_state_reads(observed_normalized) else 0,
            _count_object_centric_location_reads(observed_normalized),
            1 if not _expression_contains_phi(observed_normalized) else 0,
            -_expression_node_count(observed_normalized),
        )
        if observed_rank > normalized_rank:
            return observed_normalized
        if (
            observed_rank == normalized_rank
            and not _expressions_equivalent(observed_normalized, expr)
            and not _expression_contains_observed_loads(normalized)
            and not _expression_contains_observed_loads(expr)
        ):
            return observed_normalized

    return normalized

def _impl_lower_post_state_expression_for_smt(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
) -> Optional[Expression]:
    """
    Materialize symbolic post-state reads into guarded pre-state expressions.

    The analysis pipeline may keep post-state reads in a symbolic canonical form
    so architecture-specific expansion differences can still be merged safely.
    Before SMT lowering, we replay the relevant effect summary under the active
    return conditions to recover a path-sensitive expression.
    """
    if expr is None:
        return None

    materialized_effect_value = _materialize_existing_effect_value_carrier(
        expr,
        return_conditions,
        effects,
        parameters,
    )
    if (
        materialized_effect_value is not None
        and materialized_effect_value is not expr
        and not expression_contains_post_state_reads(materialized_effect_value)
    ):
        reduced_materialized = _reduce_expression_under_conditions(
            materialized_effect_value,
            return_conditions,
        )
        return (
            reduced_materialized
            if reduced_materialized is not None
            else materialized_effect_value
        )

    lowered = rewrite_loads_from_effects(
        expr,
        return_conditions,
        effects,
        parameters,
        preserve_symbolic_fallback=False,
    )
    reduced = _reduce_expression_under_conditions(lowered, return_conditions)
    return reduced if reduced is not None else lowered

def _impl_lower_post_state_expression_for_smt_if_needed(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
) -> Optional[Expression]:
    if expr is None or not expression_contains_post_state_reads(expr):
        return expr
    lowered = lower_post_state_expression_for_smt(
        expr,
        return_conditions,
        effects,
        parameters,
    )
    return lowered if lowered is not None else expr

def _impl__rewrite_definite_post_state_subexpressions(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    rewrite_memory_leaf: bool = False,
    preserve_composite_location_wrappers: bool = False,
) -> Optional[Expression]:
    """
    Replay definite active effects into post-state subexpressions.

    This is intentionally conservative: a MEMORY leaf is rewritten only when
    the current path conditions imply the relevant store effects. That keeps
    raw pre-state loads intact while still normalizing pruned post-state loads
    that lost their original read-order metadata during PHI simplification.
    """
    if expr is None:
        return None

    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        rewritten_addr = _rewrite_definite_post_state_subexpressions(
            expr.operands[0],
            return_conditions,
            effects,
            parameters,
            rewrite_memory_leaf=True,
            preserve_composite_location_wrappers=preserve_composite_location_wrappers,
        )
        current = expr
        if rewritten_addr is not expr.operands[0]:
            current = _memory_expr_with_runtime_location(
                rewritten_addr if rewritten_addr is not None else expr.operands[0],
                expr.size,
                read_order_key=expr.read_order_key,
                runtime_location=_expression_location_ref(expr),
                runtime_ref=getattr(expr, "runtime_ref", None),
            )

        if not rewrite_memory_leaf:
            return current

        location = canonicalize_location(current.operands[0], parameters, size=current.size)
        if location is None:
            return current

        active_effects = _collect_definite_active_effects(return_conditions, effects)
        if len(active_effects) > 1 and _summary_has_interdependent_writes(
            EffectSummary(
                parameter_names=_collect_named_parameter_names(parameters),
                effects=list(active_effects),
            )
        ):
            return current

        replayed = _replay_definite_active_effects_for_location(
            location,
            return_conditions,
            active_effects,
            parameters,
        )
        if replayed is None:
            return current

        reduced_replayed = _reduce_expression_under_conditions(replayed, return_conditions)
        resolved = reduced_replayed if reduced_replayed is not None else replayed
        if not expression_contains_post_state_reads(resolved):
            resolved = _attach_materialized_post_state_value_ref(resolved, location)
        return current if _expressions_equivalent(current, resolved) else resolved

    if expr.expr_type in (
        ExpressionType.BINARY_OP,
        ExpressionType.UNARY_OP,
        ExpressionType.CALL,
        ExpressionType.INTRINSIC,
    ):
        expr_location = canonicalize_expr_read_location(expr, parameters)
        if expr_location is not None and _matches_existing_effect_value(
            expr,
            expr_location,
            return_conditions,
            effects,
            parameters,
        ) and not expression_contains_post_state_reads(expr):
            return expr
        rewritten_operands = [
            _rewrite_definite_post_state_subexpressions(
                operand,
                return_conditions,
                effects,
                parameters,
                rewrite_memory_leaf=True,
                preserve_composite_location_wrappers=preserve_composite_location_wrappers,
            )
            for operand in expr.operands
        ]
        if _should_preserve_composite_location_wrapper(
            expr,
            expr_location,
            parameters,
            preserve_composite_location_wrappers=preserve_composite_location_wrappers,
        ):
            return expr
        rebuilt = _rebuild_expression_from_optional_operands(
            expr,
            rewritten_operands,
            fallback=expr,
        )
        return rebuilt if rebuilt is not None else expr

    if expr.expr_type == ExpressionType.PHI and expr.value:
        changed = False
        branches = []
        for cond, value in expr.value:
            combined_conditions = list(return_conditions)
            if cond is not None:
                combined_conditions.append(cond)
            new_value = _rewrite_definite_post_state_subexpressions(
                value,
                combined_conditions,
                effects,
                parameters,
                rewrite_memory_leaf=True,
                preserve_composite_location_wrappers=preserve_composite_location_wrappers,
            )
            branches.append((cond, new_value))
            changed = changed or (new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt

    return expr

def _impl_materialize_definite_post_state_expression(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    *,
    preserve_composite_location_wrappers: bool = False,
) -> Optional[Expression]:
    if expr is None:
        return None
    rewritten = _rewrite_definite_post_state_subexpressions(
        expr,
        return_conditions,
        effects,
        parameters,
        rewrite_memory_leaf=True,
        preserve_composite_location_wrappers=preserve_composite_location_wrappers,
    )
    return rewritten if rewritten is not None else expr

def _impl__rewrite_expression_with_replayed_state(
    expr: Optional[Expression],
    conditions: Sequence[Condition],
    state: Dict[CanonicalLocation, Expression],
    alias_representatives: Dict[CanonicalLocation, CanonicalLocation],
    parameters: Sequence[Dict],
) -> Optional[Expression]:
    if expr is None:
        return None

    synthetic_location = _expression_location_ref(expr)
    if expr.expr_type == ExpressionType.VARIABLE and synthetic_location is not None:
        representative = _resolve_alias_representative(
            synthetic_location,
            alias_representatives,
            conditions,
        )
        if representative is not None and representative in state:
            return state[representative]
        fallback = memory_expression_for_location(synthetic_location, parameters)
        return fallback if fallback is not None else expr

    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        rewritten_addr = _rewrite_expression_with_replayed_state(
            expr.operands[0],
            conditions,
            state,
            alias_representatives,
            parameters,
        )
        current = _memory_expr_with_runtime_location(
            rewritten_addr if rewritten_addr is not None else expr.operands[0],
            expr.size,
            read_order_key=expr.read_order_key,
            runtime_location=synthetic_location,
            runtime_ref=getattr(expr, "runtime_ref", None),
        )
        location = canonicalize_location(current.operands[0], parameters, size=expr.size)
        if location is None:
            return current
        representative = _resolve_alias_representative(
            location,
            alias_representatives,
            conditions,
        )
        if representative is not None and representative in state:
            return state[representative]
        fallback = memory_expression_for_location(location, parameters)
        return fallback if fallback is not None else current

    if expr.expr_type in (
        ExpressionType.BINARY_OP,
        ExpressionType.UNARY_OP,
        ExpressionType.CALL,
        ExpressionType.INTRINSIC,
    ):
        rewritten_operands = [
            _rewrite_expression_with_replayed_state(
                operand,
                conditions,
                state,
                alias_representatives,
                parameters,
            )
            for operand in expr.operands
        ]
        rebuilt = _rebuild_expression_from_optional_operands(
            expr,
            rewritten_operands,
            fallback=expr,
        )
        return rebuilt if rebuilt is not None else expr

    if expr.expr_type == ExpressionType.PHI and expr.value:
        changed = False
        branches = []
        for cond, value in expr.value:
            combined_conditions = list(conditions)
            if cond is not None:
                combined_conditions.append(cond)
            new_value = _rewrite_expression_with_replayed_state(
                value,
                combined_conditions,
                state,
                alias_representatives,
                parameters,
            )
            branches.append((cond, new_value))
            changed = changed or (new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt

    return expr

def _impl_post_state_read_expression_for_location(
    location: CanonicalLocation,
    parameters: Sequence[Dict],
    *,
    symbolic: bool = False,
    snapshot_ref: Optional[PostStateSnapshotRef] = None,
) -> Expression:
    location = _normalize_canonical_location(location)
    location = _bind_location_to_parameter_identity(location, parameters)
    snapshot_ref = snapshot_ref or default_post_state_snapshot_ref()
    concrete_expr = memory_expression_for_location(location, parameters)
    if concrete_expr is not None and concrete_expr.expr_type == ExpressionType.MEMORY and concrete_expr.operands:
        if not symbolic:
            return concrete_expr
        return _memory_expr_with_runtime_location(
            concrete_expr.operands[0],
            concrete_expr.size,
            read_order_key=concrete_expr.read_order_key,
            runtime_location=location,
            runtime_snapshot=snapshot_ref,
            runtime_ref=PostStateReadRef(
                location=location,
                snapshot_ref=snapshot_ref,
            ),
        )
    if not symbolic:
        return Expression.variable(
            _post_state_read_name(location),
            size=max(1, location.size),
            runtime_ref=location,
        )
    return Expression.variable(
        _post_state_read_name(location),
        size=max(1, location.size),
        runtime_ref=PostStateReadRef(
            location=location,
            snapshot_ref=snapshot_ref,
        ),
    )
