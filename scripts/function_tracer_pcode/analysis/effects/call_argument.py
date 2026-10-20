"""Call-argument evidence: parameter binding, storage descriptors and width validation."""

from __future__ import annotations

from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple
import re
from itertools import product
from scripts.function_tracer_pcode.core import (
    CallTargetRef,
    CanonicalLocation,
    Condition,
    Expression,
    ExpressionType,
    LocationBaseRef,
    PostStateReadRef,
    PostStateValueRef,
    StorageInfo,
    value_identity,
)
from scripts.function_tracer_pcode.core.signature import (
    get_declared_type_size_bytes,
    is_integral_data_type,
    is_pointer_data_type,
    is_undefined_data_type,
)
from scripts.function_tracer_pcode.analysis.effects._shared import (
    CallArgumentEvidence,
    CallArgumentWidthEvidence,
    ConditionSimplifier,
    EffectSummary,
    StoreEffect,
    _MAX_CALL_ARGUMENT_VARIANTS,
)
from scripts.function_tracer_pcode.analysis.effects._api import (
    _bind_location_to_parameter_refs,
    _call_argument_available_bits,
    _call_argument_evidence_incomplete_reason,
    _call_argument_evidence_storage_key,
    _call_argument_may_expose_parameter_memory,
    _call_argument_needs_partial_width_validation,
    _call_argument_prefix_compatible,
    _call_argument_recovery_status,
    _call_argument_semantic_rank,
    _call_argument_width_evidence,
    _call_arguments_width_safe_for_effect_summary,
    _call_evidence_callee_param_identities,
    _call_input_storage_is_constant_argument,
    _call_input_storages_for_explicit_args,
    _call_inputs_have_object_storage,
    _call_target_ref_is_resolved,
    _callee_param_identities_are_object_proven,
    _callee_parameter_identity_keys,
    _clone_expression_tree,
    _coerce_argument_to_callee_parameter,
    _coerce_callee_parameter_ref,
    _coerce_callee_parameter_refs,
    _coerce_storage_info,
    _compatible_call_block_paths,
    _data_type_name_has_pointer_marker,
    _data_type_name_is_explicit_scalar,
    _data_type_name_is_undefined,
    _enumerate_expression_variants,
    _explicit_argument_is_safe_immediate_for_callee_param,
    _explicit_argument_matches_callee_parameter_identity,
    _explicit_argument_matches_preferred,
    _explicit_call_argument_window_matches_parameter_identity,
    _explicit_call_argument_window_matches_storage,
    _expression_bit_width,
    _expression_declares_pointer_type,
    _expression_directly_matches_parameter,
    _expression_is_non_address_sized_scalar_value,
    _expression_is_wide_unknown_or_undefined,
    _expression_maps_to_parameter,
    _expression_may_be_parameter_memory_address,
    _expression_uses_parameter_beyond_width,
    _expressions_equivalent,
    _extract_location_root_and_steps,
    _fixed_prefix_argument_window_has_evidence,
    _fixed_prefix_format_recovery_spec,
    _has_ambiguous_storage_windows,
    _has_target_specific_call_argument_evidence,
    _iter_path_ops_before_call,
    _location_uses_parameter,
    _matching_explicit_call_argument_storage_windows,
    _materialize_function_pointer_argument,
    _merge_call_argument_evidence,
    _merge_recoverable_partial_call_argument_evidence,
    _normalize_call_argument_expression,
    _normalize_call_argument_recovery_status,
    _normalize_parameter_index,
    _parameter_base_ref,
    _parameter_base_ref_from_expression,
    _parameter_base_ref_matches_descriptor,
    _parameter_declared_semantic_size_bytes,
    _parameter_descriptor_is_address_sized_unknown,
    _parameter_descriptor_is_proven_non_pointer_scalar,
    _parameter_descriptor_looks_pointer,
    _parameter_descriptor_may_expose_parameter_memory,
    _parameter_descriptor_storage_size_bytes,
    _parameter_descriptor_type_name,
    _parameter_expression_from_descriptor,
    _parameter_expression_from_varnode,
    _parameter_identity_key_from_base_ref,
    _parameter_identity_keys_from_descriptor,
    _parameter_identity_keys_from_expression,
    _parameter_refs_from_descriptors,
    _parameter_semantic_size_bytes,
    _parameter_storage_covers_required_width,
    _parameter_type_is_unknown,
    _preserve_complete_call_argument_evidence,
    _recover_call_argument_candidate_from_op,
    _recover_call_argument_from_storage,
    _recover_parameter_expression_from_varnode,
    _recover_parameter_from_stack_load,
    _recover_preferred_call_argument_expression,
    _recover_unmodified_live_in_argument,
    _reduce_expression_under_conditions,
    _register_storage_contains,
    _resolve_call_argument_expression,
    _resolve_multiequal_input_for_path,
    _resolve_parameter_descriptor,
    _resolve_parameter_descriptor_from_identity,
    _runtime_conditions_signature,
    _runtime_expression_signature,
    _select_aligned_explicit_call_arguments,
    _select_best_storage_candidate,
    _select_explicit_call_arguments_by_dependency_tail,
    _select_explicit_call_arguments_by_fixed_prefix,
    _select_explicit_call_arguments_by_input_storage,
    _select_explicit_call_arguments_by_semantic_window,
    _select_explicit_call_arguments_by_storage_window,
    _should_prefer_explicit_call_argument,
    _should_preserve_explicit_indirect_target_argument,
    _stack_varnode_matches_storage,
    _storage_base_ref,
    _storage_identity_key,
    _storage_info_from_base_ref,
    _storage_info_from_identity_key,
    _storage_match_rank,
    _storage_matches_parameter,
    _try_get_order_key,
    _varnode_storage_match_rank,
    canonicalize_location,
    canonicalize_param_location,
)
from scripts.function_tracer_pcode.analysis.effects._api import (
    _collect_parameter_replacements_from_conditions,
    _expression_contains_parameter_identity,
    _stack_location_key,
    substitute_expression,
)


def _impl__collect_named_parameter_names(parameters: Sequence[Dict]) -> List[str]:
    return [
        str(name)
        for param in parameters
        for name in [param.get("name")]
        if isinstance(name, str) and name
    ]


def _impl__storage_base_ref(
    storage: Optional[StorageInfo],
    *,
    allow_register: bool = False,
) -> Optional[LocationBaseRef]:
    storage = _coerce_storage_info(storage)
    if storage is None or (storage.is_register and not allow_register):
        return None
    space_name = re.sub(r"[^0-9A-Za-z_]", "_", str(storage.space_name or "mem"))
    return LocationBaseRef.storage(
        space_id=storage.space_id,
        space_name=space_name,
        offset=int(storage.offset),
        size=max(1, int(storage.size or 0)),
        storage_identity_key=storage.storage_identity_key(),
        display_hint=f"{space_name}@{int(storage.offset)}:{max(1, int(storage.size or 0))}",
    )


def _impl__record_call_argument_evidence(
    evidence: Dict[Tuple[object, ...], CallArgumentEvidence],
    tracer,
    op,
    target_ref: Optional[CallTargetRef],
    callee_parameters: Sequence[Dict],
    args: Sequence[Expression],
    path_conditions: Sequence[Condition],
    *,
    coverage_complete: bool,
    sources: Optional[Sequence[str]] = None,
    reason: Optional[str] = None,
    recovery_status: Optional[str] = None,
) -> None:
    make_ref = getattr(tracer, "_make_pcode_op_ref", None)
    if not callable(make_ref):
        return
    ref = make_ref(op)
    if ref is None:
        return
    key = ref.stable_key()
    target_specific_key = _call_argument_evidence_storage_key(key, target_ref)
    target_is_resolved = _call_target_ref_is_resolved(target_ref)
    param_identities = _call_evidence_callee_param_identities(callee_parameters)
    identities_are_proven = (
        len(param_identities) == len(callee_parameters or ())
        and _callee_param_identities_are_object_proven(param_identities)
    )
    evidence_complete = bool(coverage_complete) and target_is_resolved and identities_are_proven
    arity_complete = evidence_complete and len(args or ()) == len(param_identities)
    requested_status = _normalize_call_argument_recovery_status(recovery_status)
    if arity_complete:
        status = CallArgumentEvidence.RECOVERY_COMPLETE
    elif (
        requested_status == CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL
        and target_is_resolved
        and identities_are_proven
        and 0 < len(args or ()) < len(param_identities)
    ):
        status = CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL
    else:
        status = CallArgumentEvidence.RECOVERY_INCONCLUSIVE
    args_tuple = (
        tuple(args or ())
        if arity_complete or status == CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL
        else ()
    )
    source_tuple = tuple(sources or ()) if args_tuple else ()
    if len(source_tuple) != len(args_tuple):
        source_tuple = tuple("reaching_def" for _arg in args_tuple)
    new_evidence = CallArgumentEvidence(
        pcode_op_ref=ref,
        target_ref=target_ref,
        callee_param_identities=param_identities,
        arguments=args_tuple,
        sources=source_tuple,
        path_conditions=(tuple(path_conditions or ()),),
        coverage_complete=arity_complete,
        recovery_status=status,
        reason=(
            reason
            or (
                None
                if arity_complete
                else (
                    "argument_recovery_recoverable_partial"
                    if status == CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL
                    else _call_argument_evidence_incomplete_reason(
                        target_is_resolved,
                        identities_are_proven,
                    )
                )
            )
        ),
    )
    previous = evidence.get(key)
    if previous is None:
        if target_specific_key is not None:
            current_for_target = evidence.get(target_specific_key)
            if current_for_target is not None:
                evidence[target_specific_key] = _merge_call_argument_evidence(
                    current_for_target,
                    new_evidence,
                )
                return
            if _has_target_specific_call_argument_evidence(evidence, key):
                evidence[target_specific_key] = new_evidence
                return
        evidence[key] = new_evidence
        return
    if not previous.target_matches(target_ref):
        previous_target_key = _call_argument_evidence_storage_key(key, previous.target_ref)
        if previous_target_key is not None:
            previous_for_target = evidence.get(previous_target_key)
            evidence[previous_target_key] = (
                _merge_call_argument_evidence(previous_for_target, previous)
                if previous_for_target is not None
                else previous
            )
        if target_specific_key is not None:
            current_for_target = evidence.get(target_specific_key)
            evidence[target_specific_key] = (
                _merge_call_argument_evidence(current_for_target, new_evidence)
                if current_for_target is not None
                else new_evidence
            )
            if previous_target_key is not None:
                evidence.pop(key, None)
            return
    evidence[key] = _merge_call_argument_evidence(previous, new_evidence)


def _impl__has_target_specific_call_argument_evidence(
    evidence: Mapping[Tuple[object, ...], CallArgumentEvidence],
    pcode_key: Tuple[object, ...],
) -> bool:
    for key in evidence:
        if (
            isinstance(key, tuple)
            and len(key) == 3
            and key[0] == "call_argument_evidence"
            and key[1] == pcode_key
            and isinstance(key[2], tuple)
            and len(key[2]) == 2
            and key[2][0] == "target"
        ):
            return True
    return False


def _impl__call_argument_evidence_storage_key(
    pcode_key: Optional[Tuple[object, ...]],
    target_ref: Optional[CallTargetRef],
) -> Optional[Tuple[object, ...]]:
    if pcode_key is None or not _call_target_ref_is_resolved(target_ref):
        return None
    try:
        target_key = target_ref.stable_key()
    except Exception:
        return None
    return ("call_argument_evidence", pcode_key, ("target", target_key))


def _impl__merge_call_argument_evidence(
    previous: CallArgumentEvidence,
    current: CallArgumentEvidence,
) -> CallArgumentEvidence:
    path_conditions = tuple(previous.path_conditions or ()) + tuple(current.path_conditions or ())
    target_and_params_match = (
        previous.target_matches(current.target_ref)
        and previous.callee_param_identities == current.callee_param_identities
    )
    if (
        previous.is_usable()
        and current.is_usable()
        and target_and_params_match
        and len(previous.arguments) == len(current.arguments)
        and all(
            _expressions_equivalent(left, right)
            for left, right in zip(previous.arguments, current.arguments)
        )
    ):
        return CallArgumentEvidence(
            pcode_op_ref=previous.pcode_op_ref,
            target_ref=previous.target_ref or current.target_ref,
            callee_param_identities=previous.callee_param_identities,
            arguments=previous.arguments,
            sources=previous.sources,
            path_conditions=path_conditions,
            coverage_complete=True,
            recovery_status=CallArgumentEvidence.RECOVERY_COMPLETE,
            reason=None,
            abi_argument_slots=previous.abi_argument_slots or current.abi_argument_slots,
            fresh_argument_refs=previous.fresh_argument_refs or current.fresh_argument_refs,
        )
    if target_and_params_match:
        preserved = _preserve_complete_call_argument_evidence(previous, current, path_conditions)
        if preserved is not None:
            return preserved
        if previous.is_recoverable_partial() and current.is_recoverable_partial():
            merged_partial = _merge_recoverable_partial_call_argument_evidence(
                previous,
                current,
                path_conditions,
            )
            if merged_partial is not None:
                return merged_partial
    return CallArgumentEvidence(
        pcode_op_ref=previous.pcode_op_ref,
        target_ref=previous.target_ref or current.target_ref,
        callee_param_identities=previous.callee_param_identities or current.callee_param_identities,
        arguments=(),
        sources=(),
        path_conditions=path_conditions,
        coverage_complete=False,
        recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
        reason=current.reason or previous.reason or "argument_evidence_path_conflict",
        abi_argument_slots=previous.abi_argument_slots or current.abi_argument_slots,
        fresh_argument_refs=previous.fresh_argument_refs or current.fresh_argument_refs,
    )


def _impl__preserve_complete_call_argument_evidence(
    previous: CallArgumentEvidence,
    current: CallArgumentEvidence,
    path_conditions: Tuple[Tuple[Condition, ...], ...],
) -> Optional[CallArgumentEvidence]:
    if previous.is_usable() and current.is_recoverable_partial():
        complete = previous
        partial = current
    elif current.is_usable() and previous.is_recoverable_partial():
        complete = current
        partial = previous
    else:
        return None
    if not _call_argument_prefix_compatible(partial.arguments, complete.arguments):
        return None
    return CallArgumentEvidence(
        pcode_op_ref=complete.pcode_op_ref,
        target_ref=complete.target_ref,
        callee_param_identities=complete.callee_param_identities,
        arguments=complete.arguments,
        sources=complete.sources,
        path_conditions=path_conditions,
        coverage_complete=True,
        recovery_status=CallArgumentEvidence.RECOVERY_COMPLETE,
        reason=None,
        abi_argument_slots=complete.abi_argument_slots or partial.abi_argument_slots,
        fresh_argument_refs=complete.fresh_argument_refs or partial.fresh_argument_refs,
    )


def _impl__merge_recoverable_partial_call_argument_evidence(
    previous: CallArgumentEvidence,
    current: CallArgumentEvidence,
    path_conditions: Tuple[Tuple[Condition, ...], ...],
) -> Optional[CallArgumentEvidence]:
    if _call_argument_prefix_compatible(previous.arguments, current.arguments):
        kept = previous if len(previous.arguments) >= len(current.arguments) else current
    elif _call_argument_prefix_compatible(current.arguments, previous.arguments):
        kept = current if len(current.arguments) >= len(previous.arguments) else previous
    else:
        return None
    return CallArgumentEvidence(
        pcode_op_ref=kept.pcode_op_ref,
        target_ref=kept.target_ref,
        callee_param_identities=kept.callee_param_identities,
        arguments=kept.arguments,
        sources=kept.sources,
        path_conditions=path_conditions,
        coverage_complete=False,
        recovery_status=CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL,
        reason=kept.reason or "argument_recovery_recoverable_partial",
        abi_argument_slots=kept.abi_argument_slots,
        fresh_argument_refs=kept.fresh_argument_refs,
    )


def _impl__call_argument_prefix_compatible(
    prefix: Sequence[Expression],
    full: Sequence[Expression],
) -> bool:
    if len(prefix or ()) > len(full or ()):
        return False
    return all(
        _expressions_equivalent(left, right)
        for left, right in zip(prefix or (), full or ())
    )


def _impl__call_argument_evidence_incomplete_reason(
    target_is_resolved: bool,
    identities_are_proven: bool,
) -> str:
    if not target_is_resolved:
        return "call_target_unresolved"
    if not identities_are_proven:
        return "callee_parameter_identity_unproven"
    return "argument_recovery_incomplete"


def _impl__normalize_call_argument_recovery_status(status: Optional[str]) -> str:
    if status in {
        CallArgumentEvidence.RECOVERY_COMPLETE,
        CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL,
        CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
    }:
        return str(status)
    return CallArgumentEvidence.RECOVERY_COMPLETE


def _impl__call_argument_recovery_is_complete(
    callee_parameters: Sequence[Dict],
    args: Sequence[Expression],
) -> bool:
    return _call_argument_recovery_status(callee_parameters, args) == CallArgumentEvidence.RECOVERY_COMPLETE


def _impl__call_argument_recovery_status(
    callee_parameters: Sequence[Dict],
    args: Sequence[Expression],
) -> str:
    if not callee_parameters:
        return CallArgumentEvidence.RECOVERY_COMPLETE
    recovered_count = len(args or ())
    if recovered_count >= len(callee_parameters):
        return CallArgumentEvidence.RECOVERY_COMPLETE
    if recovered_count > 0:
        return CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL
    return CallArgumentEvidence.RECOVERY_INCONCLUSIVE


def _impl__call_arguments_may_expose_parameter_memory(
    args: Sequence[Expression],
    parameters: Sequence[Dict],
    callee_parameters: Optional[Sequence[Dict]] = None,
) -> bool:
    return any(
        _call_argument_may_expose_parameter_memory(
            arg,
            parameters,
            callee_param=(
                callee_parameters[index]
                if callee_parameters is not None and index < len(callee_parameters)
                else None
            ),
        )
        for index, arg in enumerate(args or ())
    )


def _impl__call_argument_may_expose_parameter_memory(
    expr: Optional[Expression],
    parameters: Sequence[Dict],
    *,
    callee_param: Optional[Dict] = None,
) -> bool:
    if expr is None:
        return True
    if expr.expr_type == ExpressionType.UNKNOWN:
        return True
    if expr.expr_type == ExpressionType.PHI:
        return any(
            _call_argument_may_expose_parameter_memory(
                value,
                parameters,
                callee_param=callee_param,
            )
            for _condition, value in (expr.value or ())
        )
    if _expression_may_be_parameter_memory_address(expr, parameters):
        return True
    if callee_param is not None and _parameter_descriptor_is_proven_non_pointer_scalar(callee_param):
        return False
    return False


def _impl__expression_may_be_parameter_memory_address(
    expr: Optional[Expression],
    parameters: Sequence[Dict],
) -> bool:
    if expr is None:
        return False
    if _expression_declares_pointer_type(expr):
        return True
    if _expression_is_wide_unknown_or_undefined(expr):
        return True
    parsed = _extract_location_root_and_steps(expr, parameters)
    if parsed is None:
        return False
    base_ref, steps = parsed
    if any(getattr(step, "kind", None) == "deref" for step in (steps or ())):
        return False
    for param in parameters or ():
        if _parameter_base_ref_matches_descriptor(base_ref, param):
            if _parameter_descriptor_looks_pointer(param):
                return True
            if _expression_is_non_address_sized_scalar_value(expr):
                return False
            return _parameter_descriptor_may_expose_parameter_memory(param)
    return False


def _impl__parameter_descriptor_from_expression(expr: Optional[Expression]) -> Dict:
    if expr is None:
        return {}
    return {
        "name": getattr(expr, "name", None),
        "index": getattr(expr, "value", -1) if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER else -1,
        "size": getattr(expr, "size", 0),
        "data_type": getattr(expr, "data_type", None),
        "data_type_obj": getattr(expr, "data_type_obj", None),
        "storage": getattr(expr, "storage_info", None),
    }


def _impl__infer_call_argument_sources(
    args: Sequence[Expression],
    explicit_args: Sequence[Expression],
) -> Tuple[str, ...]:
    sources: List[str] = []
    for arg in args or ():
        if any(_expressions_equivalent(arg, explicit) for explicit in explicit_args or ()):
            sources.append("explicit_input")
        elif getattr(arg, "expr_type", None) == ExpressionType.PARAMETER:
            sources.append("live_in_unmodified")
        else:
            sources.append("reaching_def")
    return tuple(sources)


def _impl__recover_call_argument_expressions(
    call_op,
    tracer,
    caller_parameters: Sequence[Dict],
    callee_parameters: Sequence[Dict],
    explicit_args: Sequence[Expression],
    *,
    condition_tracker=None,
    current_conditions: Optional[Sequence[Condition]] = None,
) -> List[Expression]:
    if not callee_parameters:
        return list(explicit_args)

    aligned_explicit_args = _select_aligned_explicit_call_arguments(
        call_op,
        tracer,
        caller_parameters,
        callee_parameters,
        explicit_args,
        condition_tracker=condition_tracker,
        current_conditions=current_conditions,
    )
    if aligned_explicit_args is None:
        return []
    explicit_args = aligned_explicit_args
    recovered_args: List[Expression] = []
    for index, callee_param in enumerate(callee_parameters):
        explicit = explicit_args[index] if index < len(explicit_args) else None
        if explicit is not None and _should_preserve_explicit_indirect_target_argument(explicit, callee_param):
            recovered_args.append(explicit)
            continue
        if explicit is not None and _expression_maps_to_parameter(explicit, caller_parameters):
            recovered_args.append(explicit)
            continue
        explicit_size = (
            explicit.size
            if explicit is not None and getattr(explicit, "size", 0)
            else callee_param.get("size")
        )
        if explicit is not None and _should_prefer_explicit_call_argument(
            explicit,
            caller_parameters,
            size=explicit_size,
        ):
            recovered_args.append(explicit)
            continue

        recovered = _recover_call_argument_from_storage(
            call_op,
            tracer,
            caller_parameters,
            callee_param,
            condition_tracker=condition_tracker,
            current_conditions=current_conditions,
        )
        if recovered is not None:
            recovered_args.append(
                _normalize_call_argument_expression(recovered, index, caller_parameters)
            )
        elif explicit is not None:
            recovered_args.append(explicit)
    return recovered_args


def _impl__enumerate_call_argument_variants(
    args: Sequence[Expression],
    *,
    limit: int = _MAX_CALL_ARGUMENT_VARIANTS,
) -> List[Tuple[List[Condition], List[Expression]]]:
    if not args:
        return [([], [])]

    per_arg_variants = [
        _enumerate_expression_variants(arg, limit=limit)
        for arg in args
    ]
    combined: List[Tuple[List[Condition], List[Expression]]] = []
    seen = set()
    for variant_tuple in product(*per_arg_variants):
        merged_conditions: List[Condition] = []
        merged_args: List[Expression] = []
        for branch_conditions, branch_expr in variant_tuple:
            merged_conditions.extend(branch_conditions)
            merged_args.append(branch_expr)
        simplified = ConditionSimplifier.simplify_conditions(merged_conditions)
        if ConditionSimplifier.is_contradiction(simplified):
            continue
        key = (
            _runtime_conditions_signature(simplified),
            tuple(_runtime_expression_signature(arg) for arg in merged_args),
        )
        if key in seen:
            continue
        seen.add(key)
        combined.append((simplified, merged_args))
        if len(combined) >= limit:
            break
    return combined or [([], list(args))]


def _impl__select_aligned_explicit_call_arguments(
    call_op,
    tracer,
    caller_parameters: Sequence[Dict],
    callee_parameters: Sequence[Dict],
    explicit_args: Sequence[Expression],
    *,
    condition_tracker=None,
    current_conditions: Optional[Sequence[Condition]] = None,
) -> Optional[List[Expression]]:
    explicit = list(explicit_args)
    if len(explicit) <= len(callee_parameters):
        return explicit

    if len(callee_parameters) == 1 and explicit:
        explicit_keys = tuple(
            value_identity(item) for item in explicit
        )
        if (
            len(set(explicit_keys)) == 1
            and _expression_maps_to_parameter(explicit[0], caller_parameters)
        ):
            return [explicit[0]]

    storage_aligned = _select_explicit_call_arguments_by_input_storage(
        call_op,
        tracer,
        callee_parameters,
        explicit,
    )
    if storage_aligned is not None:
        return storage_aligned

    storage_window_aligned = _select_explicit_call_arguments_by_storage_window(
        call_op,
        tracer,
        callee_parameters,
        explicit,
    )
    if storage_window_aligned is not None:
        return storage_window_aligned

    if len(callee_parameters or ()) == 1 and _has_ambiguous_storage_windows(
        call_op,
        tracer,
        callee_parameters,
        explicit,
    ):
        return None

    semantic_window_aligned = _select_explicit_call_arguments_by_semantic_window(
        callee_parameters,
        explicit,
        caller_parameters,
    )
    if semantic_window_aligned is not None:
        return semantic_window_aligned

    dependency_tail_aligned = _select_explicit_call_arguments_by_dependency_tail(
        call_op,
        tracer,
        callee_parameters,
        explicit,
    )
    if dependency_tail_aligned is not None:
        return dependency_tail_aligned

    fixed_prefix_aligned = _select_explicit_call_arguments_by_fixed_prefix(
        call_op,
        tracer,
        callee_parameters,
        explicit,
        caller_parameters,
    )
    if fixed_prefix_aligned is not None:
        return fixed_prefix_aligned

    preferred_args = [
        _recover_preferred_call_argument_expression(
            call_op,
            tracer,
            caller_parameters,
            callee_param,
            index,
            condition_tracker=condition_tracker,
            current_conditions=current_conditions,
        )
        for index, callee_param in enumerate(callee_parameters)
    ]

    if any(preferred is None for preferred in preferred_args):
        return None

    selected: List[Expression] = []
    used_indexes: Set[int] = set()
    for preferred, callee_param in zip(preferred_args, callee_parameters):
        matches = [
            index for index, expr in enumerate(explicit)
            if index not in used_indexes
            and _explicit_argument_matches_preferred(
                expr,
                preferred,
                caller_parameters,
                callee_param,
            )
        ]
        if len(matches) != 1:
            return None
        used_indexes.add(matches[0])
        selected.append(explicit[matches[0]])
    return selected


def _impl__select_explicit_call_arguments_by_semantic_window(
    callee_parameters: Sequence[Dict],
    explicit_args: Sequence[Expression],
    caller_parameters: Sequence[Dict],
) -> Optional[List[Expression]]:
    callee_count = len(callee_parameters or ())
    explicit = list(explicit_args or ())
    if callee_count <= 0 or len(explicit) <= callee_count:
        return None

    matching_windows: List[int] = []
    for start in range(0, len(explicit) - callee_count + 1):
        window = explicit[start:start + callee_count]
        if _explicit_call_argument_window_matches_parameter_identity(
            window,
            callee_parameters,
            caller_parameters,
        ):
            matching_windows.append(start)

    if len(matching_windows) != 1:
        return None
    start = matching_windows[0]
    return explicit[start:start + callee_count]


def _impl__explicit_call_argument_window_matches_parameter_identity(
    explicit_args: Sequence[Expression],
    callee_parameters: Sequence[Dict],
    caller_parameters: Sequence[Dict],
) -> bool:
    if len(explicit_args) != len(callee_parameters):
        return False

    strong_identity_matches = 0
    for explicit_arg, callee_param in zip(explicit_args, callee_parameters):
        if explicit_arg is None:
            return False
        if _explicit_argument_matches_callee_parameter_identity(
            explicit_arg,
            caller_parameters,
            callee_param,
        ):
            strong_identity_matches += 1
            continue
        if _explicit_argument_is_safe_immediate_for_callee_param(
            explicit_arg,
            callee_param,
            caller_parameters,
        ):
            continue
        return False
    return strong_identity_matches > 0


def _impl__explicit_argument_matches_callee_parameter_identity(
    expr: Optional[Expression],
    caller_parameters: Sequence[Dict],
    callee_param: Optional[Dict],
) -> bool:
    if expr is None or callee_param is None:
        return False
    caller_param = _resolve_parameter_descriptor(expr, caller_parameters)
    if caller_param is None:
        return False
    caller_storage = _coerce_storage_info(caller_param.get("storage"))
    callee_storage = _coerce_storage_info(callee_param.get("storage"))
    if caller_storage is None or callee_storage is None:
        return False
    return _storage_matches_parameter(caller_storage, callee_storage)


def _impl__select_explicit_call_arguments_by_fixed_prefix(
    call_op,
    tracer,
    callee_parameters: Sequence[Dict],
    explicit_args: Sequence[Expression],
    caller_parameters: Sequence[Dict],
) -> Optional[List[Expression]]:
    callee_count = len(callee_parameters or ())
    if callee_count <= 0 or len(explicit_args or ()) <= callee_count:
        return None
    format_spec = _fixed_prefix_format_recovery_spec(call_op, tracer, callee_parameters)
    if format_spec is None:
        return None
    fixed_prefix_len, _format_index = format_spec
    if callee_count != fixed_prefix_len:
        return None

    selected = list(explicit_args[:callee_count])
    if not _fixed_prefix_argument_window_has_evidence(
        call_op,
        tracer,
        callee_parameters,
        explicit_args,
        selected,
        _format_index,
    ):
        return None
    for expr, callee_param in zip(selected, callee_parameters):
        if expr is None:
            return None
        effective_size = int(getattr(expr, "size", 0) or callee_param.get("size") or 0)
        if effective_size <= 0:
            effective_size = 8
        if _should_prefer_explicit_call_argument(
            expr,
            caller_parameters,
            size=effective_size,
        ):
            continue
        return None
    return selected


def _impl__select_explicit_call_arguments_by_input_storage(
    call_op,
    tracer,
    callee_parameters: Sequence[Dict],
    explicit_args: Sequence[Expression],
) -> Optional[List[Expression]]:
    try:
        input_count = int(call_op.getNumInputs())
    except Exception:
        return None
    if input_count <= 1:
        return None
    if len(explicit_args) != input_count - 1:
        return None

    get_input = getattr(call_op, "getInput", None)
    get_storage = getattr(tracer, "_get_storage_info_from_varnode", None)
    if not callable(get_input) or not callable(get_storage):
        return None

    input_storages: List[Optional[StorageInfo]] = []
    for index in range(1, input_count):
        try:
            varnode = get_input(index)
        except Exception:
            return None
        try:
            input_storages.append(_coerce_storage_info(get_storage(varnode)))
        except Exception:
            input_storages.append(None)

    selected: List[Expression] = []
    used_indexes: Set[int] = set()
    for callee_param in callee_parameters:
        param_storage = _coerce_storage_info(callee_param.get("storage"))
        if param_storage is None:
            return None
        matches = [
            index for index, input_storage in enumerate(input_storages)
            if index not in used_indexes
            and input_storage is not None
            and _storage_matches_parameter(input_storage, param_storage)
        ]
        if len(matches) != 1:
            return None
        used_indexes.add(matches[0])
        selected.append(explicit_args[matches[0]])
    return selected


def _impl__select_explicit_call_arguments_by_storage_window(
    call_op,
    tracer,
    callee_parameters: Sequence[Dict],
    explicit_args: Sequence[Expression],
) -> Optional[List[Expression]]:
    try:
        input_count = int(call_op.getNumInputs())
    except Exception:
        return None
    if input_count <= 1:
        return None
    if len(explicit_args) != input_count - 1:
        return None
    callee_count = len(callee_parameters or ())
    if callee_count <= 0 or len(explicit_args) <= callee_count:
        return None

    get_input = getattr(call_op, "getInput", None)
    get_storage = getattr(tracer, "_get_storage_info_from_varnode", None)
    if not callable(get_input) or not callable(get_storage):
        return None

    input_storages: List[Optional[StorageInfo]] = []
    for index in range(1, input_count):
        try:
            varnode = get_input(index)
        except Exception:
            return None
        try:
            input_storages.append(_coerce_storage_info(get_storage(varnode)))
        except Exception:
            input_storages.append(None)

    param_storages = [
        _coerce_storage_info(callee_param.get("storage"))
        for callee_param in callee_parameters
    ]
    if any(storage is None for storage in param_storages):
        return None

    matching_windows = _matching_explicit_call_argument_storage_windows(
        input_storages,
        explicit_args,
        param_storages,
    )

    if len(matching_windows) != 1:
        return None
    start = matching_windows[0]
    return list(explicit_args[start:start + callee_count])


def _impl__matching_explicit_call_argument_storage_windows(
    input_storages: Sequence[Optional[StorageInfo]],
    explicit_args: Sequence[Expression],
    param_storages: Sequence[Optional[StorageInfo]],
) -> List[int]:
    callee_count = len(param_storages or ())
    if callee_count <= 0 or len(input_storages) != len(explicit_args):
        return []
    matching_windows: List[int] = []
    for start in range(0, len(explicit_args) - callee_count + 1):
        if _explicit_call_argument_window_matches_storage(
            input_storages[start:start + callee_count],
            explicit_args[start:start + callee_count],
            param_storages,
        ):
            matching_windows.append(start)
    return matching_windows


def _impl__explicit_call_argument_window_matches_storage(
    input_storages: Sequence[Optional[StorageInfo]],
    explicit_args: Sequence[Expression],
    param_storages: Sequence[Optional[StorageInfo]],
) -> bool:
    if len(input_storages) != len(param_storages):
        return False
    for input_storage, explicit_arg, param_storage in zip(
        input_storages,
        explicit_args,
        param_storages,
    ):
        if param_storage is None:
            return False
        if _call_input_storage_is_constant_argument(input_storage, explicit_arg):
            continue
        if input_storage is None:
            return False
        if not _storage_matches_parameter(input_storage, param_storage):
            return False
    return True


def _impl__call_input_storage_is_constant_argument(
    input_storage: Optional[StorageInfo],
    explicit_arg: Optional[Expression],
) -> bool:
    if explicit_arg is None or explicit_arg.expr_type != ExpressionType.CONSTANT:
        return False
    if input_storage is None:
        return False
    return (
        not bool(getattr(input_storage, "is_register", False))
        and str(getattr(input_storage, "space_name", "") or "").lower() == "const"
    )


def _impl__select_explicit_call_arguments_by_dependency_tail(
    call_op,
    tracer,
    callee_parameters: Sequence[Dict],
    explicit_args: Sequence[Expression],
) -> Optional[List[Expression]]:
    try:
        input_count = int(call_op.getNumInputs())
    except Exception:
        return None
    if input_count <= 1 or len(explicit_args) != input_count - 1:
        return None
    callee_count = len(callee_parameters or ())
    if callee_count <= 0 or len(explicit_args) <= callee_count:
        return None
    if not _call_inputs_have_object_storage(call_op, tracer, explicit_args):
        return None
    if _has_ambiguous_storage_windows(call_op, tracer, callee_parameters, explicit_args):
        return None

    hidden_prefix = list(explicit_args[:-callee_count])
    selected_tail = list(explicit_args[-callee_count:])
    selected_tail_storages = _call_input_storages_for_explicit_args(
        call_op,
        tracer,
        explicit_args,
    )
    if selected_tail_storages is None:
        return None
    selected_tail_storages = selected_tail_storages[-callee_count:]
    param_storages = [
        _coerce_storage_info(callee_param.get("storage"))
        for callee_param in callee_parameters
    ]
    if len(selected_tail_storages) != callee_count or any(
        storage is None for storage in param_storages
    ):
        return None
    if not _explicit_call_argument_window_matches_storage(
        selected_tail_storages,
        selected_tail,
        param_storages,
    ):
        return None

    for hidden_index, hidden_arg in enumerate(hidden_prefix):
        if hidden_arg is None:
            return None
        if hidden_index >= len(selected_tail):
            return None
        if not _expressions_equivalent(hidden_arg, selected_tail[hidden_index]):
            return None
    return selected_tail


def _impl__call_input_storages_for_explicit_args(
    call_op,
    tracer,
    explicit_args: Sequence[Expression],
) -> Optional[List[Optional[StorageInfo]]]:
    get_input = getattr(call_op, "getInput", None)
    get_storage = getattr(tracer, "_get_storage_info_from_varnode", None)
    if not callable(get_input) or not callable(get_storage):
        return None
    try:
        input_count = int(call_op.getNumInputs())
    except Exception:
        return None
    if input_count <= 1 or len(explicit_args) != input_count - 1:
        return None

    input_storages: List[Optional[StorageInfo]] = []
    for index in range(1, input_count):
        try:
            varnode = get_input(index)
        except Exception:
            return None
        try:
            input_storages.append(_coerce_storage_info(get_storage(varnode)))
        except Exception:
            input_storages.append(None)
    return input_storages


def _impl__call_inputs_have_object_storage(
    call_op,
    tracer,
    explicit_args: Sequence[Expression],
) -> bool:
    input_storages = _call_input_storages_for_explicit_args(call_op, tracer, explicit_args)
    if input_storages is None:
        return False
    for storage in input_storages:
        if storage is not None:
            return True
    return False


def _impl__has_ambiguous_storage_windows(
    call_op,
    tracer,
    callee_parameters: Sequence[Dict],
    explicit_args: Sequence[Expression],
) -> bool:
    input_storages = _call_input_storages_for_explicit_args(call_op, tracer, explicit_args)
    if input_storages is None:
        return False

    param_storages = [
        _coerce_storage_info(callee_param.get("storage"))
        for callee_param in callee_parameters
    ]
    if any(storage is None for storage in param_storages):
        return False
    return (
        len(
            _matching_explicit_call_argument_storage_windows(
                input_storages,
                explicit_args,
                param_storages,
            )
        )
        > 1
    )


def _impl__recover_preferred_call_argument_expression(
    call_op,
    tracer,
    caller_parameters: Sequence[Dict],
    callee_param: Dict,
    index: int,
    *,
    condition_tracker=None,
    current_conditions: Optional[Sequence[Condition]] = None,
) -> Optional[Expression]:
    preferred = _recover_call_argument_from_storage(
        call_op,
        tracer,
        caller_parameters,
        callee_param,
        condition_tracker=condition_tracker,
        current_conditions=current_conditions,
    )
    if preferred is None:
        return None
    return _normalize_call_argument_expression(preferred, index, caller_parameters)


def _impl__should_prefer_explicit_call_argument(
    expr: Optional[Expression],
    caller_parameters: Sequence[Dict],
    size: Optional[int] = None,
) -> bool:
    if expr is None:
        return False
    if expr.expr_type == ExpressionType.PHI:
        return True
    if expr.expr_type in {ExpressionType.CONSTANT, ExpressionType.MEMORY, ExpressionType.CALL, ExpressionType.INTRINSIC}:
        return True
    if expr.expr_type in {ExpressionType.BINARY_OP, ExpressionType.UNARY_OP}:
        return True

    try:
        effective_size = int(size or expr.size or 0)
    except Exception:
        effective_size = 0
    if effective_size <= 0:
        effective_size = 8
    return canonicalize_location(expr, caller_parameters, size=effective_size) is not None


def _impl__parameter_descriptor_looks_pointer(param: Optional[Dict]) -> bool:
    if not param:
        return False
    type_name = _parameter_descriptor_type_name(param)
    if _data_type_name_has_pointer_marker(type_name):
        return True
    return bool(
        is_pointer_data_type(
            param.get("data_type_obj"),
            type_name,
        )
    )


def _impl__parameter_descriptor_may_expose_parameter_memory(param: Optional[Dict]) -> bool:
    if not param:
        return True
    if _parameter_descriptor_looks_pointer(param):
        return True
    if _parameter_descriptor_is_proven_non_pointer_scalar(param):
        return False
    return _parameter_descriptor_is_address_sized_unknown(param)


def _impl__parameter_descriptor_is_proven_non_pointer_scalar(param: Optional[Dict]) -> bool:
    if not param or _parameter_descriptor_looks_pointer(param):
        return False
    type_name = _parameter_descriptor_type_name(param)
    data_type_obj = param.get("data_type_obj")
    if data_type_obj is not None and is_integral_data_type(data_type_obj, type_name):
        return True
    return _data_type_name_is_explicit_scalar(type_name)


def _impl__parameter_descriptor_is_address_sized_unknown(param: Optional[Dict]) -> bool:
    if not param:
        return True
    type_name = _parameter_descriptor_type_name(param)
    data_type_obj = param.get("data_type_obj")
    type_is_unknown = not type_name and data_type_obj is None
    type_is_undefined = bool(
        is_undefined_data_type(data_type_obj, type_name)
        or _data_type_name_is_undefined(type_name)
    )
    if not (type_is_unknown or type_is_undefined):
        return True
    storage_size = _parameter_descriptor_storage_size_bytes(param)
    if storage_size <= 0:
        return True
    return storage_size in {4, 8}


def _impl__parameter_descriptor_storage_size_bytes(param: Dict) -> int:
    try:
        param_size = int(param.get("size") or 0)
    except Exception:
        param_size = 0
    if param_size > 0:
        return param_size
    storage = _coerce_storage_info(param.get("storage"))
    if storage is not None:
        try:
            storage_size = int(storage.size or storage.register_size or 0)
        except Exception:
            storage_size = 0
        if storage_size > 0:
            return storage_size
    declared_size = get_declared_type_size_bytes(
        param.get("data_type_obj"),
        _parameter_descriptor_type_name(param),
        fallback_size=None,
    )
    try:
        return int(declared_size or 0)
    except Exception:
        return 0


def _impl__parameter_descriptor_type_name(param: Optional[Dict]) -> Optional[str]:
    if not param:
        return None
    for key in ("data_type", "type_name", "data_type_name"):
        value = param.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return None


def _impl__call_argument_semantic_rank(
    expr: Optional[Expression],
    caller_parameters: Sequence[Dict],
    callee_param: Optional[Dict],
) -> int:
    if expr is None:
        return -1

    callee_expects_pointer = _parameter_descriptor_looks_pointer(callee_param)
    try:
        effective_size = int((callee_param or {}).get("size") or expr.size or 0)
    except Exception:
        effective_size = 0
    if effective_size <= 0:
        effective_size = max(1, int(expr.size or 8))

    caller_param = _resolve_parameter_descriptor(expr, caller_parameters)
    caller_param_is_pointer = _parameter_descriptor_looks_pointer(caller_param)

    if expr.expr_type == ExpressionType.CONSTANT and int(getattr(expr, "value", 1)) == 0:
        return 3 if callee_expects_pointer else 1

    location = canonicalize_location(expr, caller_parameters, size=effective_size)
    if callee_expects_pointer:
        if location is not None:
            if location.base_ref.is_stack_frame():
                return 8
            if location.base_ref.is_storage():
                return 7
            if caller_param is not None:
                return 6 if caller_param_is_pointer else 1
            return 5
        if caller_param is not None:
            return 6 if caller_param_is_pointer else 1
        return 0

    return 0


def _impl__resolve_call_argument_expression(
    varnode,
    tracer,
    parameters: Sequence[Dict],
    depth: int = 0,
    seen: Optional[Set[int]] = None,
) -> Expression:
    try:
        def_op = varnode.getDef()
    except Exception:
        def_op = None

    expr = tracer.trace_varnode(varnode, use_cache=False)
    expr = _materialize_function_pointer_argument(expr, tracer, varnode)
    if expr.expr_type == ExpressionType.PARAMETER:
        return expr
    if (
        def_op is None
        and canonicalize_param_location(
            expr,
            parameters,
            size=max(1, getattr(varnode, "getSize", lambda: 0)()),
        )
        is not None
    ):
        return expr

    recovered = _recover_parameter_expression_from_varnode(
        varnode,
        tracer,
        parameters,
        depth=depth,
        seen=seen,
    )
    if recovered is not None:
        return recovered
    return expr


def _impl__recover_call_argument_candidate_from_op(
    op,
    target_storage: StorageInfo,
    tracer,
    caller_parameters: Sequence[Dict],
    callee_param: Dict,
    *,
    path_blocks=None,
    current_conditions: Optional[Sequence[Condition]] = None,
) -> Optional[Tuple[Expression, int, int]]:
    output = getattr(op, "getOutput", lambda: None)()
    output_rank = _varnode_storage_match_rank(output, target_storage, tracer)
    if output is not None and output_rank > 0:
        candidate_expr = _resolve_multiequal_input_for_path(
            op,
            path_blocks,
            tracer,
            caller_parameters,
            current_conditions,
        )
        if candidate_expr is None:
            candidate_expr = _resolve_call_argument_expression(output, tracer, caller_parameters)
        reduced = _reduce_expression_under_conditions(
            candidate_expr,
            list(current_conditions or []),
        )
        candidate_expr = reduced if reduced is not None else candidate_expr
        semantic_rank = _call_argument_semantic_rank(
            candidate_expr,
            caller_parameters,
            callee_param,
        )
        return candidate_expr, output_rank, semantic_rank

    if (
        not target_storage.is_register
        and getattr(op, "getMnemonic", lambda: None)() == "STORE"
        and getattr(op, "getNumInputs", lambda: 0)() >= 3
    ):
        try:
            store_target = op.getInput(1)
        except Exception:
            store_target = None
        if _stack_varnode_matches_storage(store_target, target_storage):
            try:
                store_value = op.getInput(2)
            except Exception:
                store_value = None
            if store_value is not None:
                candidate_expr = _resolve_call_argument_expression(store_value, tracer, caller_parameters)
                reduced = _reduce_expression_under_conditions(
                    candidate_expr,
                    list(current_conditions or []),
                )
                candidate_expr = reduced if reduced is not None else candidate_expr
                semantic_rank = _call_argument_semantic_rank(
                    candidate_expr,
                    caller_parameters,
                    callee_param,
                )
                return candidate_expr, 3, semantic_rank

    return None


def _impl__select_best_storage_candidate(
    ops: Sequence[object],
    target_storage: StorageInfo,
    tracer,
    caller_parameters: Sequence[Dict],
    callee_param: Dict,
    *,
    path_blocks=None,
    current_conditions: Optional[Sequence[Condition]] = None,
) -> Optional[Expression]:
    best_candidate = None
    best_order = None
    best_rank = -1
    best_semantic_rank = -1

    for op in ops:
        candidate = _recover_call_argument_candidate_from_op(
            op,
            target_storage,
            tracer,
            caller_parameters,
            callee_param,
            path_blocks=path_blocks,
            current_conditions=current_conditions,
        )
        if candidate is None:
            continue
        candidate_expr, rank, semantic_rank = candidate
        op_order = _try_get_order_key(op)
        if op_order is None:
            continue
        if (
            semantic_rank > best_semantic_rank
            or (
                semantic_rank == best_semantic_rank
                and (
                    rank > best_rank
                    or (rank == best_rank and (best_order is None or op_order > best_order))
                )
            )
        ):
            best_candidate = candidate_expr
            best_order = op_order
            best_rank = rank
            best_semantic_rank = semantic_rank

    return best_candidate


def _impl__recover_call_argument_from_storage(
    call_op,
    tracer,
    caller_parameters: Sequence[Dict],
    callee_param: Dict,
    *,
    condition_tracker=None,
    current_conditions: Optional[Sequence[Condition]] = None,
) -> Optional[Expression]:
    target_storage = _coerce_storage_info(callee_param.get("storage"))
    if target_storage is None:
        return None

    compatible_paths = _compatible_call_block_paths(
        call_op,
        condition_tracker,
        current_conditions,
    )
    if not compatible_paths:
        return None

    path_candidates: List[Tuple[List[Condition], Expression]] = []
    for path_blocks, path_conditions in compatible_paths:
        merged_conditions = ConditionSimplifier.simplify_conditions(
            list(path_conditions or []) + list(current_conditions or []),
        )
        if ConditionSimplifier.is_contradiction(merged_conditions):
            continue
        path_ops = list(_iter_path_ops_before_call(path_blocks, call_op))
        candidate = _select_best_storage_candidate(
            path_ops,
            target_storage,
            tracer,
            caller_parameters,
            callee_param,
            path_blocks=path_blocks,
            current_conditions=current_conditions,
        )
        if candidate is None:
            candidate = _recover_unmodified_live_in_argument(
                path_ops,
                target_storage,
                tracer,
                caller_parameters,
                callee_param,
            )
        if candidate is not None:
            path_candidates.append((list(merged_conditions), candidate))
        else:
            return None
    if not path_candidates:
        return None
    chosen = path_candidates[0][1]
    if all(_expressions_equivalent(chosen, candidate) for _conds, candidate in path_candidates[1:]):
        return chosen

    branch_candidates: List[Tuple[Condition, Expression]] = []
    seen_signatures: Set[Tuple[object, ...]] = set()
    for conditions, candidate in path_candidates:
        if not conditions:
            return None
        branch_condition = Condition.combine_and(conditions)
        if branch_condition is None:
            return None
        signature = _runtime_conditions_signature(conditions)
        if signature in seen_signatures:
            return None
        seen_signatures.add(signature)
        branch_candidates.append((branch_condition, candidate))

    if len(branch_candidates) < 2:
        return None
    for left_index in range(len(path_candidates)):
        left_conditions = path_candidates[left_index][0]
        for right_conditions, _candidate in path_candidates[left_index + 1:]:
            if not ConditionSimplifier.is_contradiction(
                list(left_conditions) + list(right_conditions)
            ):
                return None
    result = Expression.phi(branch_candidates)
    result.size = max(
        int(getattr(candidate, "size", 0) or 0)
        for _condition, candidate in branch_candidates
    )
    return result


def _impl__resolve_live_in_parameter_descriptor_for_call_storage(
    caller_parameters: Sequence[Dict],
    target_storage: StorageInfo,
    *,
    required_size_bytes: Optional[int] = None,
    allow_register_fragment_extension: bool = False,
) -> Optional[Dict]:
    required_bits = max(0, int(required_size_bytes or 0) * 8)
    descriptor = _resolve_parameter_descriptor_from_identity(
        caller_parameters,
        storage_info=target_storage,
    )
    if descriptor is not None and _parameter_storage_covers_required_width(
        descriptor,
        required_bits,
    ):
        return descriptor
    if target_storage is None or not getattr(target_storage, "is_register", False):
        return None

    matches: List[Dict] = []
    for parameter in caller_parameters or []:
        parameter_storage = _coerce_storage_info(parameter.get("storage"))
        if parameter_storage is None or not getattr(parameter_storage, "is_register", False):
            continue
        if (
            required_bits > 0
            and int(getattr(parameter_storage, "size_bits", 0) or 0) < required_bits
            and not allow_register_fragment_extension
        ):
            continue
        if _register_storage_contains(target_storage, parameter_storage):
            matches.append(parameter)

    return matches[0] if len(matches) == 1 else None


def _impl__parameter_semantic_size_bytes(param: Optional[Dict]) -> Optional[int]:
    if not isinstance(param, dict):
        return None
    declared = get_declared_type_size_bytes(
        param.get("data_type_obj"),
        param.get("data_type"),
        fallback_size=None,
    )
    if declared is not None and int(declared) > 0:
        return int(declared)
    try:
        size = int(param.get("size") or 0)
    except Exception:
        size = 0
    return size if size > 0 else None


def _impl__parameter_declared_semantic_size_bytes(param: Optional[Dict]) -> Optional[int]:
    if not isinstance(param, dict) or _parameter_type_is_unknown(param):
        return None
    declared = get_declared_type_size_bytes(
        param.get("data_type_obj"),
        param.get("data_type"),
        fallback_size=None,
    )
    try:
        declared_size = int(declared or 0)
    except Exception:
        declared_size = 0
    if declared_size <= 0:
        try:
            declared_size = int(param.get("size") or 0)
        except Exception:
            declared_size = 0
    return declared_size if declared_size > 0 else None


def _impl__parameter_storage_covers_required_width(
    parameter: Dict,
    required_bits: int,
) -> bool:
    if required_bits <= 0:
        return True
    parameter_storage = _coerce_storage_info(parameter.get("storage"))
    if parameter_storage is None:
        return False
    return int(getattr(parameter_storage, "size_bits", 0) or 0) >= required_bits


def _impl__parameter_type_is_unknown(param: Optional[Dict]) -> bool:
    if not isinstance(param, dict):
        return True
    type_obj = param.get("data_type_obj")
    type_name = param.get("data_type")
    if is_undefined_data_type(type_obj, type_name):
        return True
    normalized = str(type_name or "").strip().lower()
    return not normalized or normalized.startswith("undefined")


def _impl__call_argument_width_evidence(expr: Optional[Expression]) -> Optional[CallArgumentWidthEvidence]:
    evidence = getattr(expr, "call_argument_width_evidence", None)
    return evidence if isinstance(evidence, CallArgumentWidthEvidence) else None


def _impl__call_argument_needs_partial_width_validation(expr: Optional[Expression]) -> bool:
    evidence = _call_argument_width_evidence(expr)
    return bool(evidence is not None and evidence.is_partial())


def _impl__call_argument_available_bits(expr: Optional[Expression]) -> int:
    evidence = _call_argument_width_evidence(expr)
    if evidence is not None and int(evidence.source_bits or 0) > 0:
        return int(evidence.source_bits)
    return _expression_bit_width(expr)


def _impl__call_arguments_width_safe_for_effect_summary(
    effect_summary: Optional[EffectSummary],
    callee_parameters: Sequence[Dict],
    args: Sequence[Expression],
) -> bool:
    if effect_summary is None:
        return True
    for index, (callee_param, arg) in enumerate(zip(callee_parameters or [], args or [])):
        if not _call_argument_needs_partial_width_validation(arg):
            continue
        available_bits = _call_argument_available_bits(arg)
        if available_bits <= 0:
            return False
        for effect in effect_summary.effects or []:
            if _location_uses_parameter(effect.location, callee_param):
                return False
            if _expression_uses_parameter_beyond_width(
                effect.value,
                callee_param,
                available_bits,
                callee_parameters,
            ):
                return False
            for condition in effect.conditions or []:
                if _expression_uses_parameter_beyond_width(
                    getattr(condition, "expression", None),
                    callee_param,
                    available_bits,
                    callee_parameters,
                ):
                    return False
    return True


def _impl__call_arguments_width_safe_for_callee_analysis(
    callee_analysis,
    args: Sequence[Expression],
) -> bool:
    callee_parameters = list(getattr(callee_analysis, "parameters", []) or [])
    for callee_param, arg in zip(callee_parameters, args or []):
        if not _call_argument_needs_partial_width_validation(arg):
            continue
        available_bits = _call_argument_available_bits(arg)
        if available_bits <= 0:
            return False
        for ret in getattr(callee_analysis, "returns", []) or []:
            if _expression_uses_parameter_beyond_width(
                getattr(ret, "value", None),
                callee_param,
                available_bits,
                callee_parameters,
            ):
                return False
            for condition in getattr(ret, "conditions", []) or []:
                if _expression_uses_parameter_beyond_width(
                    getattr(condition, "expression", None),
                    callee_param,
                    available_bits,
                    callee_parameters,
                ):
                    return False
        effect_summary = getattr(callee_analysis, "effect_summary", None)
        if not _call_arguments_width_safe_for_effect_summary(
            effect_summary,
            callee_parameters,
            args,
        ):
            return False
    return True


def _impl__expression_uses_parameter_beyond_width(
    expr: Optional[Expression],
    callee_param: Dict,
    available_bits: int,
    parameters: Sequence[Dict],
) -> bool:
    if expr is None:
        return False

    runtime_ref = getattr(expr, "runtime_ref", None)
    location = None
    if isinstance(runtime_ref, CanonicalLocation):
        location = runtime_ref
    elif isinstance(runtime_ref, (PostStateReadRef, PostStateValueRef)):
        location = getattr(runtime_ref, "location", None)
    if _location_uses_parameter(location, callee_param):
        return True

    if _expression_directly_matches_parameter(expr, callee_param, parameters):
        return _expression_bit_width(expr) > int(available_bits or 0)

    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "SUBPIECE" and len(expr.operands) == 2:
        source, offset = expr.operands
        offset_value = getattr(offset, "value", None) if offset.expr_type == ExpressionType.CONSTANT else None
        if offset_value == 0 and _expression_directly_matches_parameter(source, callee_param, parameters):
            return _expression_bit_width(expr) > int(available_bits or 0)

    if expr.expr_type == ExpressionType.PHI and expr.value:
        for condition, value in expr.value:
            if condition is not None and _expression_uses_parameter_beyond_width(
                getattr(condition, "expression", None),
                callee_param,
                available_bits,
                parameters,
            ):
                return True
            if _expression_uses_parameter_beyond_width(value, callee_param, available_bits, parameters):
                return True
        return False

    for operand in getattr(expr, "operands", []) or []:
        if _expression_uses_parameter_beyond_width(operand, callee_param, available_bits, parameters):
            return True
    return False


def _impl__expression_directly_matches_parameter(
    expr: Optional[Expression],
    callee_param: Dict,
    parameters: Sequence[Dict],
) -> bool:
    if expr is None:
        return False
    return bool(
        _parameter_identity_keys_from_expression(expr, parameters).intersection(
            _parameter_identity_keys_from_descriptor(callee_param)
        )
    )


def _impl__location_uses_parameter(
    location: Optional[CanonicalLocation],
    callee_param: Dict,
) -> bool:
    if location is None:
        return False
    return _parameter_base_ref_matches_descriptor(getattr(location, "base_ref", None), callee_param)


def _impl__register_storage_contains(container: StorageInfo, fragment: StorageInfo) -> bool:
    if (
        container is None
        or fragment is None
        or not getattr(container, "is_register", False)
        or not getattr(fragment, "is_register", False)
    ):
        return False
    if not container.shares_base_register_with(fragment):
        return False
    container_low = int(getattr(container, "bit_offset_in_base", 0) or 0)
    container_high = container_low + int(getattr(container, "size_bits", 0) or 0)
    fragment_low = int(getattr(fragment, "bit_offset_in_base", 0) or 0)
    fragment_high = fragment_low + int(getattr(fragment, "size_bits", 0) or 0)
    if container_high <= container_low or fragment_high <= fragment_low:
        return False
    return container_low <= fragment_low and fragment_high <= container_high


def _impl__path_writes_storage(
    ops: Sequence[object],
    target_storage: StorageInfo,
    tracer,
) -> bool:
    for op in ops or []:
        output = getattr(op, "getOutput", lambda: None)()
        if output is not None and _varnode_storage_match_rank(output, target_storage, tracer) > 0:
            return True
        if (
            not target_storage.is_register
            and getattr(op, "getMnemonic", lambda: None)() == "STORE"
            and getattr(op, "getNumInputs", lambda: 0)() >= 3
        ):
            try:
                store_target = op.getInput(1)
            except Exception:
                store_target = None
            if _stack_varnode_matches_storage(store_target, target_storage):
                return True
    return False


def _impl__varnode_matches_storage(varnode, target_storage: StorageInfo, tracer) -> bool:
    return _varnode_storage_match_rank(varnode, target_storage, tracer) > 0


def _impl__varnode_storage_match_rank(varnode, target_storage: StorageInfo, tracer) -> int:
    varnode_storage = tracer._get_storage_info_from_varnode(varnode)
    if varnode_storage is not None:
        return _storage_match_rank(varnode_storage, target_storage)
    if target_storage.is_register:
        return 0
    return 3 if _stack_varnode_matches_storage(varnode, target_storage) else 0


def _impl__stack_varnode_matches_storage(varnode, target_storage: StorageInfo) -> bool:
    if varnode is None:
        return False
    try:
        addr = varnode.getAddress()
        space = addr.getAddressSpace()
        if space is None:
            return False
        return (
            (
                target_storage.space_id is not None
                and int(space.getSpaceID()) == int(target_storage.space_id)
            )
            and int(varnode.getOffset()) == target_storage.offset
            and int(varnode.getSize()) == target_storage.size
        )
    except Exception:
        return False


def _impl__storage_infos_match(left: StorageInfo, right: StorageInfo) -> bool:
    return _storage_match_rank(left, right) > 0


def _impl__storage_match_rank(left: StorageInfo, right: StorageInfo) -> int:
    if left.is_register or right.is_register:
        if not (left.is_register and right.is_register):
            return 0
        if left.shares_base_register_with(right):
            if (
                left.bit_offset_in_base == right.bit_offset_in_base
                and left.size_bits == right.size_bits
                and left.size == right.size
            ):
                return 3
            if left.register_identity_key() == right.register_identity_key():
                return 2
            if left.bit_range_overlaps_with(right):
                return 1
            return 0
        return 2 if left.register_identity_key() == right.register_identity_key() else 0
    return 3 if (
        left.space_id == right.space_id
        and left.offset == right.offset
        and left.size == right.size
    ) else 0


def _impl__normalize_call_argument_expression(
    expr: Expression,
    arg_index: int,
    parameters: Sequence[Dict],
) -> Expression:
    if expr is None:
        return expr

    descriptor = _resolve_parameter_descriptor(expr, parameters)
    if descriptor is not None:
        return _parameter_expression_from_descriptor(descriptor, size=expr.size or None) or expr

    if expr.expr_type not in (ExpressionType.PARAMETER, ExpressionType.VARIABLE, ExpressionType.UNKNOWN):
        return expr
    if getattr(expr, "operands", None):
        return expr
    return expr


def _impl__expression_maps_to_parameter(expr: Optional[Expression], parameters: Sequence[Dict]) -> bool:
    if expr is None:
        return False
    if _resolve_parameter_descriptor(expr, parameters) is not None:
        return True
    size = expr.size or 0
    try:
        size = int(size)
    except Exception:
        size = 0
    if size <= 0:
        size = 8
    return canonicalize_param_location(expr, parameters, size=size) is not None


def _impl__normalize_parameter_index(value: Optional[object]) -> Optional[int]:
    try:
        if value is None:
            return None
        normalized = int(value)
    except Exception:
        return None
    return normalized if normalized >= 0 else None


def _impl__storage_identity_key(storage: Optional[StorageInfo]) -> Optional[Tuple[object, ...]]:
    storage = _coerce_storage_info(storage)
    if storage is None:
        return None
    return storage.storage_identity_key()


def _impl__parameter_identity_key_from_base_ref(
    base_ref: Optional[LocationBaseRef],
) -> Optional[Tuple[object, ...]]:
    if base_ref is None:
        return None
    if base_ref.is_storage():
        storage_identity_key = getattr(base_ref, "storage_identity_key", None)
        if storage_identity_key is not None:
            return tuple(storage_identity_key)
        size = max(1, int(base_ref.storage_size or 0))
        space_name = str(base_ref.storage_space or "")
        space_id = base_ref.storage_space_id
        offset = int(base_ref.storage_offset or 0)
        is_register = space_name.lower() == "register"
        storage = StorageInfo(
            is_register=is_register,
            space_name=space_name,
            space_id=space_id,
            offset=offset,
            size=size,
            size_bits=size * 8,
            register_offset=offset if is_register else 0,
            register_size=size if is_register else 0,
            register_size_bits=(size * 8) if is_register else 0,
            base_register_offset=offset if is_register else 0,
            base_register_size=size if is_register else 0,
            base_register_size_bits=(size * 8) if is_register else 0,
        )
        return _storage_identity_key(storage)
    if not base_ref.is_parameter():
        return None
    if base_ref.parameter_index is None:
        return None
    if base_ref.owner_program_id is not None or base_ref.owner_entry_offset is not None:
        return (
            "parameter",
            base_ref.owner_program_id,
            base_ref.owner_entry_offset,
            int(base_ref.parameter_index),
        )
    return ("parameter", int(base_ref.parameter_index))


def _impl__parameter_identity_keys_from_descriptor(param: Optional[Dict]) -> Set[Tuple[object, ...]]:
    if not param:
        return set()
    keys: Set[Tuple[object, ...]] = set()
    param_index = _normalize_parameter_index(param.get("index"))
    if param_index is not None:
        owner_program_id = param.get("owner_program_id")
        owner_entry_offset = param.get("owner_entry_offset")
        if owner_program_id is not None or owner_entry_offset is not None:
            keys.add(("parameter", owner_program_id, owner_entry_offset, param_index))
        keys.add(("parameter", param_index))
    storage_key = _storage_identity_key(_coerce_storage_info(param.get("storage")))
    if storage_key is not None:
        keys.add(storage_key)
    return keys


def _impl__parameter_identity_keys_from_expression(
    expr: Optional[Expression],
    parameters: Sequence[Dict],
) -> Set[Tuple[object, ...]]:
    if expr is None:
        return set()

    keys: Set[Tuple[object, ...]] = set()
    explicit_parameter_identity = False
    explicit_scoped_parameter_identity = False

    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, LocationBaseRef):
        base_key = _parameter_identity_key_from_base_ref(runtime_ref)
        if base_key is not None:
            keys.add(base_key)
            param_index = _normalize_parameter_index(runtime_ref.parameter_index)
            if param_index is not None:
                keys.add(("parameter", param_index))
            explicit_parameter_identity = True
            explicit_scoped_parameter_identity = len(base_key) > 2
    elif isinstance(runtime_ref, (CanonicalLocation, PostStateReadRef)):
        location_ref = runtime_ref.location if isinstance(runtime_ref, PostStateReadRef) else runtime_ref
        base_key = _parameter_identity_key_from_base_ref(location_ref.base_ref)
        if base_key is not None and not location_ref.steps and int(location_ref.offset) == 0:
            keys.add(base_key)
            param_index = _normalize_parameter_index(location_ref.base_ref.parameter_index)
            if param_index is not None:
                keys.add(("parameter", param_index))
            explicit_parameter_identity = True
            explicit_scoped_parameter_identity = len(base_key) > 2

    if expr.expr_type == ExpressionType.PARAMETER and not explicit_parameter_identity:
        param_index = _normalize_parameter_index(getattr(expr, "value", None))
        if param_index is not None:
            keys.add(("parameter", param_index))

    storage_key = _storage_identity_key(_coerce_storage_info(getattr(expr, "storage_info", None)))
    if storage_key is not None and not explicit_scoped_parameter_identity:
        keys.add(storage_key)

    if not explicit_scoped_parameter_identity:
        descriptor = _resolve_parameter_descriptor(expr, parameters)
        keys.update(_parameter_identity_keys_from_descriptor(descriptor))
    return keys


def _impl__parameter_descriptors_share_identity(left: Optional[Dict], right: Optional[Dict]) -> bool:
    if not left or not right:
        return False
    return bool(
        _parameter_identity_keys_from_descriptor(left).intersection(
            _parameter_identity_keys_from_descriptor(right)
        )
    )


def _impl__callee_parameter_identity_keys(
    param: object,
    param_ref: Optional[LocationBaseRef],
) -> Set[Tuple[object, ...]]:
    keys: Set[Tuple[object, ...]] = set()
    ref_key = _parameter_identity_key_from_base_ref(param_ref)
    if ref_key is not None:
        keys.add(ref_key)
    if isinstance(param, dict):
        keys.update(_parameter_identity_keys_from_descriptor(param))
    return keys


def _impl__parameter_base_ref_matches_descriptor(
    base_ref: Optional[LocationBaseRef],
    param: Optional[Dict],
) -> bool:
    base_key = _parameter_identity_key_from_base_ref(base_ref)
    if base_key is None or not param:
        return False
    if base_key in _parameter_identity_keys_from_descriptor(param):
        return True
    if base_ref is not None and base_ref.is_storage():
        base_storage = _storage_info_from_base_ref(base_ref)
        param_storage = _coerce_storage_info(param.get("storage"))
        if base_storage is not None and param_storage is not None:
            return _storage_matches_parameter(base_storage, param_storage)
    return False


def _impl__storage_info_from_base_ref(base_ref: Optional[LocationBaseRef]) -> Optional[StorageInfo]:
    if base_ref is None or not base_ref.is_storage():
        return None
    storage_identity_key = getattr(base_ref, "storage_identity_key", None)
    if storage_identity_key is not None:
        parsed = _storage_info_from_identity_key(tuple(storage_identity_key))
        if parsed is not None:
            return parsed
    size = max(1, int(base_ref.storage_size or 0))
    space_name = str(base_ref.storage_space or "")
    offset = int(base_ref.storage_offset or 0)
    is_register = space_name.lower() == "register"
    return StorageInfo(
        is_register=is_register,
        space_name=space_name,
        space_id=base_ref.storage_space_id,
        offset=offset,
        size=size,
        size_bits=size * 8,
        register_offset=offset if is_register else 0,
        register_size=size if is_register else 0,
        register_size_bits=(size * 8) if is_register else 0,
        base_register_offset=offset if is_register else 0,
        base_register_size=size if is_register else 0,
        base_register_size_bits=(size * 8) if is_register else 0,
    )


def _impl__storage_info_from_identity_key(identity_key: Tuple[object, ...]) -> Optional[StorageInfo]:
    try:
        if not identity_key:
            return None
        if identity_key[0] == "register_storage" and len(identity_key) >= 6:
            _tag, space_id, base_offset, base_bits, bit_offset, size_bits = identity_key[:6]
            size_bits = int(size_bits)
            base_bits = int(base_bits)
            return StorageInfo(
                is_register=True,
                space_name="register",
                space_id=int(space_id),
                offset=int(base_offset),
                size=max(1, (size_bits + 7) // 8),
                size_bits=size_bits,
                register_offset=int(base_offset),
                register_size=max(1, (size_bits + 7) // 8),
                register_size_bits=size_bits,
                base_register_offset=int(base_offset),
                base_register_size=max(1, (base_bits + 7) // 8),
                base_register_size_bits=base_bits,
                bit_offset_in_base=int(bit_offset),
            )
        if identity_key[0] == "memory_storage" and len(identity_key) >= 4:
            _tag, space_id, offset, size = identity_key[:4]
            size = max(1, int(size))
            return StorageInfo(
                is_register=False,
                space_id=int(space_id),
                offset=int(offset),
                size=size,
                size_bits=size * 8,
            )
    except Exception:
        return None
    return None


def _impl__coerce_callee_parameter_ref(param: object, index: int) -> Optional[LocationBaseRef]:
    if isinstance(param, LocationBaseRef) and param.is_storage():
        return param
    if isinstance(param, LocationBaseRef) and param.is_parameter():
        normalized_index = _normalize_parameter_index(param.parameter_index)
        if normalized_index is not None:
            return LocationBaseRef.parameter(
                param.parameter_name,
                index=normalized_index,
                owner_program_id=param.owner_program_id,
                owner_entry_offset=param.owner_entry_offset,
            )
        return None
    if isinstance(param, dict):
        normalized_index = _normalize_parameter_index(param.get("index"))
        if normalized_index is not None:
            return _parameter_base_ref(
                name=param.get("name"),
                index=normalized_index,
                owner_program_id=param.get("owner_program_id"),
                owner_entry_offset=param.get("owner_entry_offset"),
            )
        storage_ref = _storage_base_ref(param.get("storage"), allow_register=True)
        if storage_ref is not None:
            return storage_ref
        return None
    return None


def _impl__parameter_refs_from_descriptors(
    parameters: Sequence[Dict],
) -> List[LocationBaseRef]:
    refs: List[LocationBaseRef] = []
    for index, param in enumerate(parameters or []):
        ref = _coerce_callee_parameter_ref(param, index)
        if ref is not None:
            refs.append(ref)
    return refs


def _impl__coerce_callee_parameter_refs(params: Sequence[object]) -> List[Optional[LocationBaseRef]]:
    return [_coerce_callee_parameter_ref(param, index) for index, param in enumerate(params)]


def _impl__coerce_argument_to_callee_parameter(
    arg: Optional[Expression],
    callee_param: object,
) -> Optional[Expression]:
    if arg is None:
        return None

    descriptor = callee_param if isinstance(callee_param, dict) else None
    target_size = None
    is_signed = True
    target_size_is_declared = False
    if descriptor is not None:
        try:
            declared_size = _parameter_declared_semantic_size_bytes(descriptor)
            target_size = int(declared_size or _parameter_semantic_size_bytes(descriptor) or descriptor.get("size") or 0)
            target_size_is_declared = declared_size is not None
        except Exception:
            target_size = None
        try:
            is_signed = bool(descriptor.get("is_signed", True))
        except Exception:
            is_signed = True

        storage = _coerce_storage_info(descriptor.get("storage"))
        if (not target_size or target_size <= 0) and storage is not None:
            try:
                target_size = int(storage.size or 0)
            except Exception:
                target_size = None

    if not target_size or target_size <= 0:
        cloned = _clone_expression_tree(arg)
        return cloned if cloned is not None else arg

    cloned = _clone_expression_tree(arg)
    if cloned is None:
        return arg

    current_size = int(getattr(cloned, "size", 0) or 0)
    if current_size <= 0 or current_size == target_size:
        cloned.size = target_size
        return cloned

    if current_size > target_size:
        narrowed = Expression.binary_op(
            "SUBPIECE",
            cloned,
            Expression.constant(0, size=max(1, current_size)),
        )
        narrowed.size = target_size
        return narrowed

    if descriptor is not None and not target_size_is_declared and _parameter_type_is_unknown(descriptor):
        return cloned

    widened = Expression.unary_op(
        "INT_SEXT" if is_signed else "INT_ZEXT",
        cloned,
    )
    widened.size = target_size
    return widened


def _impl__build_parameter_replacements(
    callee_params: Sequence[object],
    args: Sequence[Expression],
) -> Dict[Tuple[object, ...], Expression]:
    replacements: Dict[Tuple[object, ...], Expression] = {}
    for param, param_ref, arg in zip(callee_params, _coerce_callee_parameter_refs(callee_params), args):
        identity_keys = _callee_parameter_identity_keys(param, param_ref)
        if identity_keys:
            coerced_arg = _coerce_argument_to_callee_parameter(arg, param)
            if coerced_arg is not None:
                for key in identity_keys:
                    replacements[key] = coerced_arg
                key = _parameter_identity_key_from_base_ref(param_ref)
                if key is not None:
                    replacements[key] = coerced_arg
                param_index = (
                    _normalize_parameter_index(param_ref.parameter_index)
                    if param_ref is not None and param_ref.is_parameter()
                    else None
                )
                if param_index is not None:
                    replacements.setdefault(("parameter", param_index), coerced_arg)
    return replacements


def _impl__parameter_base_ref(
    *,
    name: Optional[object] = None,
    index: Optional[object] = None,
    owner_program_id: Optional[object] = None,
    owner_entry_offset: Optional[object] = None,
) -> LocationBaseRef:
    normalized_name = str(name) if isinstance(name, str) and name else None
    normalized_owner_program_id = None
    normalized_owner_entry_offset = None
    try:
        if owner_program_id is not None:
            normalized_owner_program_id = int(owner_program_id)
    except Exception:
        normalized_owner_program_id = None
    try:
        if owner_entry_offset is not None:
            normalized_owner_entry_offset = int(owner_entry_offset)
    except Exception:
        normalized_owner_entry_offset = None
    return LocationBaseRef(
        kind="parameter",
        parameter_name=normalized_name,
        parameter_index=_normalize_parameter_index(index),
        owner_program_id=normalized_owner_program_id,
        owner_entry_offset=normalized_owner_entry_offset,
        display_hint=normalized_name,
    )


def _impl__bind_location_to_parameter_refs(
    location: CanonicalLocation,
    parameter_refs: Sequence[LocationBaseRef],
) -> CanonicalLocation:
    base_ref = getattr(location, "base_ref", None)
    if not isinstance(base_ref, LocationBaseRef) or not base_ref.is_parameter():
        return location
    if base_ref.parameter_index is not None:
        return location
    return location


def _impl__bind_location_to_parameter_identity(
    location: CanonicalLocation,
    parameters: Sequence[Dict],
) -> CanonicalLocation:
    return _bind_location_to_parameter_refs(
        location,
        _parameter_refs_from_descriptors(parameters),
    )


def _impl__normalize_effect_locations_for_parameters(
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
) -> List[StoreEffect]:
    parameter_refs = _parameter_refs_from_descriptors(parameters)
    return [
        StoreEffect(
            location=_bind_location_to_parameter_refs(effect.location, parameter_refs),
            value=effect.value,
            conditions=list(effect.conditions or []),
            order_key=effect.order_key,
            provenance=effect.provenance,
        )
        for effect in (effects or [])
    ]


def _impl__parameter_base_ref_from_expression(expr: Optional[Expression]) -> Optional[LocationBaseRef]:
    if expr is None:
        return None

    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, LocationBaseRef) and runtime_ref.is_parameter():
        return runtime_ref
    if isinstance(runtime_ref, (CanonicalLocation, PostStateReadRef)):
        location_ref = runtime_ref.location if isinstance(runtime_ref, PostStateReadRef) else runtime_ref
        if location_ref.base_ref.is_parameter() and not location_ref.steps and int(location_ref.offset) == 0:
            return location_ref.base_ref

    if expr.expr_type == ExpressionType.PARAMETER:
        return _parameter_base_ref(name=expr.name, index=expr.value)
    return None


def _impl__resolve_parameter_descriptor_from_identity(
    parameters: Sequence[Dict],
    *,
    parameter_ref: Optional[LocationBaseRef] = None,
    parameter_index: Optional[object] = None,
    storage_info: Optional[StorageInfo] = None,
) -> Optional[Dict]:
    best_param: Optional[Dict] = None
    best_score: Optional[int] = None
    ambiguous = False

    normalized_index = _normalize_parameter_index(parameter_index)

    for param in parameters:
        score = 0
        param_index = _normalize_parameter_index(param.get("index"))

        if parameter_ref is not None and _parameter_base_ref_matches_descriptor(parameter_ref, param):
            score += 100
        if normalized_index is not None and param_index is not None and normalized_index == param_index:
            score += 80
        if storage_info is not None:
            param_storage = _coerce_storage_info(param.get("storage"))
            if param_storage is not None and _storage_matches_parameter(storage_info, param_storage):
                score += 40

        if score <= 0:
            continue
        if best_score is None or score > best_score:
            best_param = param
            best_score = score
            ambiguous = False
            continue
        if score == best_score:
            ambiguous = True

    if ambiguous:
        return None
    return best_param


def _impl__resolve_parameter_descriptor(
    expr: Optional[Expression],
    parameters: Sequence[Dict],
) -> Optional[Dict]:
    if expr is None:
        return None
    return _resolve_parameter_descriptor_from_identity(
        parameters,
        parameter_ref=_parameter_base_ref_from_expression(expr),
        parameter_index=getattr(expr, "value", None) if expr.expr_type == ExpressionType.PARAMETER else None,
        storage_info=_coerce_storage_info(getattr(expr, "storage_info", None)),
    )


def _impl__parameter_expression_from_descriptor(param: Dict, size: Optional[int] = None) -> Optional[Expression]:
    name = param.get("name")
    if not name:
        return None
    try:
        param_index = int(param.get("index", -1))
    except Exception:
        param_index = -1
    try:
        param_size = int(size or param.get("size", 8))
    except Exception:
        param_size = 8
    param_size = max(1, param_size)
    return Expression.parameter(
        name,
        param_index,
        param.get("data_type"),
        param.get("data_type_obj"),
        param_size,
        storage_info=_coerce_storage_info(param.get("storage")),
        runtime_ref=_parameter_base_ref(
            name=name,
            index=param_index,
            owner_program_id=param.get("owner_program_id"),
            owner_entry_offset=param.get("owner_entry_offset"),
        ),
    )


def _impl__recover_parameter_expression_from_varnode(
    varnode,
    tracer,
    parameters: Sequence[Dict],
    depth: int = 0,
    seen: Optional[Set[int]] = None,
) -> Optional[Expression]:
    if varnode is None or depth > 12:
        return None

    if seen is None:
        seen = set()
    varnode_id = id(varnode)
    if varnode_id in seen:
        return None
    seen.add(varnode_id)

    direct = _parameter_expression_from_varnode(varnode, tracer, parameters)
    if direct is not None:
        return direct

    def_op = varnode.getDef()
    if def_op is None:
        return None

    mnemonic = def_op.getMnemonic()
    if mnemonic in {"COPY", "CAST", "INT_ZEXT", "INT_SEXT"} and def_op.getNumInputs() >= 1:
        return _recover_parameter_expression_from_varnode(
            def_op.getInput(0),
            tracer,
            parameters,
            depth=depth + 1,
            seen=seen,
        )

    if mnemonic == "SUBPIECE" and def_op.getNumInputs() >= 2:
        offset_expr = tracer.trace_varnode(def_op.getInput(1), use_cache=False)
        if offset_expr.expr_type == ExpressionType.CONSTANT and int(offset_expr.value) == 0:
            return _recover_parameter_expression_from_varnode(
                def_op.getInput(0),
                tracer,
                parameters,
                depth=depth + 1,
                seen=seen,
            )

    if mnemonic == "PIECE" and def_op.getNumInputs() >= 2:
        for index in range(def_op.getNumInputs()):
            recovered = _recover_parameter_expression_from_varnode(
                def_op.getInput(index),
                tracer,
                parameters,
                depth=depth + 1,
                seen=seen,
            )
            if recovered is not None:
                return recovered

    if mnemonic == "LOAD" and def_op.getNumInputs() >= 2:
        recovered = _recover_parameter_from_stack_load(
            def_op,
            tracer,
            parameters,
            depth=depth + 1,
            seen=seen,
        )
        if recovered is not None:
            return recovered

    return None


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
