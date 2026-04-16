# -*- coding: utf-8 -*-
"""Simple parameter-derived memory effect summaries."""

from __future__ import annotations

import binascii
from dataclasses import dataclass, field
from itertools import product
import re
from typing import Callable, Dict, FrozenSet, Iterable, List, Optional, Sequence, Set, Tuple, overload

from ..model import (
    AddressValueRef,
    CallTargetRef,
    CanonicalLocation,
    Condition,
    Expression,
    ExpressionType,
    LocationBaseRef,
    LocationStep,
    ObservedMemoryReadRef,
    StorageInfo,
    expression_key_or_identity,
    expression_key_safe,
)
from ..model.signature import is_pointer_data_type
from .condition import ConditionSimplifier
from .condition.normalizer import ConditionNormalizer
from .memory_resolver import concretize_readonly_loads

@dataclass
class StoreEffect:
    location: CanonicalLocation
    value: Expression
    conditions: List[Condition]
    order_key: int


@dataclass
class EffectSummary:
    parameter_names: List[str]
    effects: List[StoreEffect]
    synthetic_expr: Optional[Expression] = None
    has_unsupported_call: bool = False
    parameter_refs: List[LocationBaseRef] = field(default_factory=list)

    def __post_init__(self) -> None:
        if self.parameter_refs:
            self.parameter_refs = [
                _coerce_callee_parameter_ref(ref, index)
                for index, ref in enumerate(self.parameter_refs)
            ]
            return
        self.parameter_refs = [
            LocationBaseRef.parameter(name, index=index)
            for index, name in enumerate(self.parameter_names)
        ]


_MAX_CALL_ARGUMENT_VARIANTS = 16


def _runtime_expression_signature(expr: Optional[Expression]):
    if expr is None:
        return ("none",)
    return expression_key_or_identity(
        expr,
        include_memory_read_order=False,
        include_semantic_runtime_refs=False,
    )


def _runtime_conditions_signature(conditions: Sequence[Condition]):
    return ConditionNormalizer.conditions_signature(conditions)


def _encode_signed_token(value: int) -> str:
    try:
        numeric = int(value)
    except Exception:
        numeric = 0
    if numeric < 0:
        return f"n{abs(numeric)}"
    return f"p{numeric}"


def _collect_named_parameter_names(parameters: Sequence[Dict]) -> List[str]:
    return [
        str(name)
        for param in parameters
        for name in [param.get("name")]
        if isinstance(name, str) and name
    ]


def _all_non_none_expressions(
    operands: Sequence[Optional[Expression]],
) -> Optional[List[Expression]]:
    normalized: List[Expression] = []
    for operand in operands:
        if operand is None:
            return None
        normalized.append(operand)
    return normalized


def _clone_expression_with_operands(
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
    )


def _rebuild_expression_from_optional_operands(
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


def _display_name_for_location_base(base_ref: LocationBaseRef) -> str:
    return base_ref.display_name()


def _storage_base_ref(storage: Optional[StorageInfo]) -> Optional[LocationBaseRef]:
    storage = _coerce_storage_info(storage)
    if storage is None or storage.is_register:
        return None
    space_name = re.sub(r"[^0-9A-Za-z_]", "_", str(storage.space_name or "mem"))
    return LocationBaseRef.storage(
        space_name=space_name,
        offset=int(storage.offset),
        size=max(1, int(storage.size or 0)),
        display_hint=f"{space_name}@{int(storage.offset)}:{max(1, int(storage.size or 0))}",
    )


def _expression_location_ref(expr: Optional[Expression]) -> Optional[CanonicalLocation]:
    if expr is None:
        return None
    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, CanonicalLocation):
        return runtime_ref
    if isinstance(runtime_ref, ObservedMemoryReadRef):
        return runtime_ref.location
    return None


def _expression_observed_read_ref(expr: Optional[Expression]) -> Optional[ObservedMemoryReadRef]:
    if expr is None:
        return None
    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, ObservedMemoryReadRef):
        return runtime_ref
    return None


def _expression_observed_order_key(expr: Optional[Expression]) -> Optional[int]:
    if expr is None:
        return None
    read_order_key = getattr(expr, "read_order_key", None)
    if read_order_key is not None:
        return int(read_order_key)
    observed_ref = _expression_observed_read_ref(expr)
    if observed_ref is not None and observed_ref.order_key is not None:
        return int(observed_ref.order_key)
    return None


def _merge_memory_runtime_ref(
    runtime_ref: Any,
    runtime_location: Optional[CanonicalLocation],
) -> Any:
    if isinstance(runtime_ref, ObservedMemoryReadRef):
        if runtime_location is None or runtime_ref.location == runtime_location:
            return runtime_ref
        return runtime_ref.with_location(runtime_location)
    if runtime_location is not None:
        return runtime_location
    return runtime_ref


def _memory_expr_with_runtime_location(
    address: Expression,
    size: int,
    *,
    read_order_key: Optional[int] = None,
    runtime_location: Optional[CanonicalLocation] = None,
    runtime_ref: Any = None,
) -> Expression:
    return Expression.memory(
        address,
        size=max(1, int(size or 0)),
        read_order_key=read_order_key,
        runtime_ref=_merge_memory_runtime_ref(runtime_ref, runtime_location),
    )


def _serialize_location(location: CanonicalLocation) -> str:
    normalized = _normalize_canonical_location(location)
    step_tokens = []
    for step in normalized.steps:
        prefix = "o" if step.kind == "offset" else "d"
        token = _encode_signed_token(step.value) if step.kind == "offset" else str(int(step.value))
        step_tokens.append(f"{prefix}:{token}")
    return "|".join(
        [
            normalized.base_param,
            ";".join(step_tokens),
            _encode_signed_token(normalized.offset),
            str(max(1, int(normalized.size or 0))),
        ]
    )


def _synthetic_location_read_name(location: CanonicalLocation) -> str:
    payload = _serialize_location(location)
    encoded = binascii.hexlify(payload.encode("utf-8")).decode("ascii")
    return f"__locread__{encoded}"


def expression_contains_post_state_reads(expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    if _expression_location_ref(expr) is not None:
        return True
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and expression_contains_post_state_reads(cond.expression):
                return True
            if expression_contains_post_state_reads(value):
                return True
        return False
    for operand in getattr(expr, "operands", []) or []:
        if expression_contains_post_state_reads(operand):
            return True
    return False


def expression_contains_synthetic_location_reads(expr: Optional[Expression]) -> bool:
    """Backward-compatible alias for object-centric post-state read detection."""
    return expression_contains_post_state_reads(expr)


def expression_contains_complex_location_reads(
    expr: Optional[Expression],
    parameters: Sequence[Dict],
) -> bool:
    if expr is None:
        return False
    synthetic_location = _expression_location_ref(expr)
    if synthetic_location is not None:
        return True
    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        location = canonicalize_location(expr.operands[0], parameters, size=expr.size)
        if location is not None and getattr(location, "steps", ()):
            return True
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and expression_contains_complex_location_reads(cond.expression, parameters):
                return True
            if expression_contains_complex_location_reads(value, parameters):
                return True
        return False
    for operand in getattr(expr, "operands", []) or []:
        if expression_contains_complex_location_reads(operand, parameters):
            return True
    return False


def _expression_contains_observed_loads(expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    if expr.expr_type == ExpressionType.MEMORY and _expression_observed_order_key(expr) is not None:
        return True
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and _expression_contains_observed_loads(cond.expression):
                return True
            if _expression_contains_observed_loads(value):
                return True
        return False
    for operand in getattr(expr, "operands", []) or []:
        if _expression_contains_observed_loads(operand):
            return True
    return False


def _expression_contains_phi(expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    if expr.expr_type == ExpressionType.PHI:
        return True
    if expr.expr_type == ExpressionType.PHI and expr.value:
        return True
    for operand in getattr(expr, "operands", []) or []:
        if _expression_contains_phi(operand):
            return True
    return False


def _count_object_centric_location_reads(expr: Optional[Expression]) -> int:
    if expr is None:
        return 0
    count = 1 if _expression_location_ref(expr) is not None else 0
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None:
                count += _count_object_centric_location_reads(cond.expression)
            count += _count_object_centric_location_reads(value)
        return count
    for operand in getattr(expr, "operands", []) or []:
        count += _count_object_centric_location_reads(operand)
    return count


def _expression_node_count(expr: Optional[Expression]) -> int:
    if expr is None:
        return 0
    count = 1
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None:
                count += _expression_node_count(cond.expression)
            count += _expression_node_count(value)
        return count
    for operand in getattr(expr, "operands", []) or []:
        count += _expression_node_count(operand)
    return count


def summarize_store_effects(
    block_infos: Iterable,
    tracer,
    condition_tracker,
    parameters: Sequence[Dict],
    direct_call_summary: Optional[Callable[[CallTargetRef, Sequence[Expression]], Optional["EffectSummary"]]] = None,
    direct_call_expander: Optional[Callable[[CallTargetRef, Sequence[Expression]], Optional[Sequence[object]]]] = None,
    resolve_callee_parameters: Optional[Callable[[CallTargetRef], Sequence[Dict]]] = None,
    debug: bool = False,
) -> EffectSummary:
    parameter_names = _collect_named_parameter_names(parameters)
    effects: List[StoreEffect] = []
    has_unsupported_call = False

    for block_info in block_infos:
        path_sets = condition_tracker.get_all_valid_paths_to_block(block_info)
        if not path_sets:
            path_sets = [[]]

        for op in block_info.pcode_ops:
            mnemonic = op.getMnemonic()

            if mnemonic == "STORE" and op.getNumInputs() >= 3:
                addr_expr = tracer.trace_varnode(op.getInput(1), use_cache=False)
                location = canonicalize_param_location(addr_expr, parameters, size=op.getInput(2).getSize())
                if location is None:
                    continue
                value_effects = _resolve_store_value_effects(
                    op,
                    tracer,
                    parameters,
                    direct_call_expander=direct_call_expander,
                    resolve_callee_parameters=resolve_callee_parameters,
                )
                for path_conditions in path_sets:
                    for value_expr, value_conditions in value_effects:
                        simplified = ConditionSimplifier.simplify_conditions(
                            list(path_conditions) + list(value_conditions)
                        )
                        effects.append(
                            StoreEffect(
                                location=location,
                                value=value_expr,
                                conditions=simplified,
                                order_key=_get_order_key(op),
                            )
                        )
                continue

            if mnemonic not in {"CALL", "CALLIND"} or direct_call_summary is None or op.getNumInputs() < 1:
                continue

            target_ref = _resolve_call_target_ref(tracer, op)
            if target_ref is None:
                has_unsupported_call = True
                continue
            target_label = target_ref.display_name()
            explicit_args = [
                _normalize_call_argument_expression(
                    _resolve_call_argument_expression(op.getInput(i), tracer, parameters),
                    i - 1,
                    parameters,
                )
                for i in range(1, op.getNumInputs())
            ]
            callee_parameters = (
                list(resolve_callee_parameters(target_ref) or [])
                if resolve_callee_parameters
                else []
            )
            args = _recover_call_argument_expressions(
                op,
                tracer,
                parameters,
                callee_parameters,
                explicit_args,
            )
            if debug:
                explicit_dump = ", ".join(arg.to_string() for arg in explicit_args)
                recovered_dump = ", ".join(arg.to_string() for arg in args)
                print(
                    "[EffectSummary] call arguments: "
                    f"target={target_label} explicit=[{explicit_dump}] recovered=[{recovered_dump}]"
                )
            for path_conditions in path_sets:
                normalized_path_conditions = ConditionSimplifier.simplify_conditions(list(path_conditions))
                path_reduced_args = [
                    _reduce_expression_under_conditions(arg, normalized_path_conditions)
                    for arg in args
                ]
                arg_variants = _enumerate_call_argument_variants(path_reduced_args)
                if debug and len(arg_variants) > 1:
                    print(
                        "[EffectSummary] enumerated call argument variants: "
                        f"target={target_label} count={len(arg_variants)}"
                    )
                for variant_conditions, variant_args in arg_variants:
                    active_conditions = ConditionSimplifier.simplify_conditions(
                        list(normalized_path_conditions) + list(variant_conditions)
                    )
                    callee_summary = direct_call_summary(target_ref, variant_args)
                    if callee_summary is None:
                        has_unsupported_call = True
                        continue
                    if not callee_summary.effects:
                        if callee_summary.has_unsupported_call:
                            has_unsupported_call = True
                        elif debug:
                            print(
                                "[EffectSummary] effect-free callee summary: "
                                f"target={target_label}"
                            )
                        continue
                    if not is_call_effect_summary_allowed(callee_summary):
                        has_unsupported_call = True
                        continue

                    for effect in callee_summary.effects:
                        substitution_args = _choose_effect_substitution_args(
                            effect.location,
                            callee_summary.parameter_refs,
                            variant_args,
                            parameters,
                        )
                        substituted_location = substitute_location(
                            effect.location,
                            callee_summary.parameter_refs,
                            substitution_args,
                            parameters,
                        )
                        if substituted_location is None:
                            if debug:
                                arg_dump = ", ".join(arg.to_string() for arg in substitution_args)
                                print(
                                    "[EffectSummary] skip substituted effect: "
                                    f"callee_loc={effect.location} args=[{arg_dump}]"
                                )
                            continue
                        substitutions = _build_parameter_replacements(
                            callee_summary.parameter_refs,
                            substitution_args,
                        )
                        substituted_value = substitute_expression(effect.value, substitutions, parameters)
                        substituted_value = _reduce_expression_under_conditions(
                            substituted_value,
                            active_conditions,
                        )
                        substituted_conditions = [
                            substitute_condition(cond, substitutions, parameters)
                            for cond in effect.conditions
                        ]
                        substituted_conditions = _reduce_conditions_under_context(
                            substituted_conditions,
                            active_conditions,
                        )
                        merged_conditions = ConditionSimplifier.simplify_conditions(
                            list(active_conditions) + substituted_conditions
                        )
                        substituted_value = _reduce_expression_under_conditions(
                            substituted_value,
                            merged_conditions,
                        )
                        if debug:
                            cond_dump = ", ".join(cond.to_string() for cond in substituted_conditions)
                            variant_dump = ", ".join(cond.to_string() for cond in variant_conditions)
                            merged_dump = ", ".join(cond.to_string() for cond in merged_conditions)
                            print(
                                "[EffectSummary] substituted effect: "
                                f"callee_loc={effect.location} caller_loc={substituted_location} "
                                f"value={substituted_value.to_string()} conditions=[{cond_dump}] "
                                f"arg_variant_conditions=[{variant_dump}] merged_conditions=[{merged_dump}]"
                            )
                        effects.append(
                            StoreEffect(
                                location=substituted_location,
                                value=substituted_value,
                                conditions=merged_conditions,
                                order_key=_get_order_key(op),
                            )
                        )

    synthetic_expr = build_void_effect_summary_expr(effects)
    if debug:
        print(
            f"[EffectSummary] collected {len(effects)} effects "
            f"for params={parameter_names}"
        )
    return EffectSummary(
        parameter_names=parameter_names,
        effects=effects,
        synthetic_expr=synthetic_expr,
        has_unsupported_call=has_unsupported_call,
    )


def _resolve_store_value_effects(
    store_op,
    tracer,
    parameters: Sequence[Dict],
    *,
    direct_call_expander: Optional[Callable[[CallTargetRef, Sequence[Expression]], Optional[Sequence[object]]]] = None,
    resolve_callee_parameters: Optional[Callable[[CallTargetRef], Sequence[Dict]]] = None,
) -> List[Tuple[Expression, List[Condition]]]:
    value_varnode = store_op.getInput(2)
    resolved = _resolve_direct_call_value_effects(
        value_varnode,
        tracer,
        parameters,
        direct_call_expander=direct_call_expander,
        resolve_callee_parameters=resolve_callee_parameters,
    )
    if resolved:
        return resolved
    return [(tracer.trace_varnode(value_varnode, use_cache=False), [])]


def _resolve_direct_call_value_effects(
    value_varnode,
    tracer,
    parameters: Sequence[Dict],
    *,
    direct_call_expander: Optional[Callable[[CallTargetRef, Sequence[Expression]], Optional[Sequence[object]]]] = None,
    resolve_callee_parameters: Optional[Callable[[CallTargetRef], Sequence[Dict]]] = None,
) -> List[Tuple[Expression, List[Condition]]]:
    if direct_call_expander is None or value_varnode is None:
        return []

    try:
        def_op = value_varnode.getDef()
    except Exception:
        def_op = None
    if def_op is None or def_op.getMnemonic() not in {"CALL", "CALLIND"}:
        return []

    target_ref = _resolve_call_target_ref(tracer, def_op)
    if target_ref is None:
        return []

    explicit_args = [
        _normalize_call_argument_expression(
            _resolve_call_argument_expression(def_op.getInput(i), tracer, parameters),
            i - 1,
            parameters,
        )
        for i in range(1, def_op.getNumInputs())
    ]
    callee_parameters = (
        list(resolve_callee_parameters(target_ref) or [])
        if resolve_callee_parameters is not None
        else []
    )
    args = _recover_call_argument_expressions(
        def_op,
        tracer,
        parameters,
        callee_parameters,
        explicit_args,
    )

    expanded = direct_call_expander(target_ref, args)
    if not expanded:
        return []

    resolved: List[Tuple[Expression, List[Condition]]] = []
    for item in expanded:
        value = getattr(item, "value", None)
        conditions = getattr(item, "conditions", None)
        if not isinstance(value, Expression):
            continue
        if not _expression_is_call_scope_safe(value):
            continue
        normalized_conditions = ConditionSimplifier.simplify_conditions(list(conditions or []))
        if ConditionSimplifier.is_contradiction(normalized_conditions):
            continue
        resolved.append((value, normalized_conditions))
    return resolved


def _recover_call_argument_expressions(
    call_op,
    tracer,
    caller_parameters: Sequence[Dict],
    callee_parameters: Sequence[Dict],
    explicit_args: Sequence[Expression],
) -> List[Expression]:
    if not callee_parameters:
        return list(explicit_args)

    explicit_args = _select_aligned_explicit_call_arguments(
        call_op,
        tracer,
        caller_parameters,
        callee_parameters,
        explicit_args,
    )
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
        )
        if recovered is None:
            recovered = _parameter_expression_from_matching_storage(
                callee_param,
                caller_parameters,
                size=(explicit.size if explicit is not None else None),
            )
        if recovered is None and index < len(caller_parameters):
            recovered = _parameter_expression_from_descriptor(
                caller_parameters[index],
                size=(explicit.size if explicit is not None else callee_param.get("size")),
            )

        if recovered is not None:
            recovered_args.append(
                _normalize_call_argument_expression(recovered, index, caller_parameters)
            )
        elif explicit is not None:
            recovered_args.append(explicit)
    return recovered_args


def _enumerate_call_argument_variants(
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


def _enumerate_expression_variants(
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

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL, ExpressionType.MEMORY):
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


def _reduce_conditions_under_context(
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


def _select_aligned_explicit_call_arguments(
    call_op,
    tracer,
    caller_parameters: Sequence[Dict],
    callee_parameters: Sequence[Dict],
    explicit_args: Sequence[Expression],
) -> List[Expression]:
    explicit = list(explicit_args)
    if len(explicit) <= len(callee_parameters):
        return explicit

    preferred_args = [
        _recover_preferred_call_argument_expression(
            call_op,
            tracer,
            caller_parameters,
            callee_param,
            index,
        )
        for index, callee_param in enumerate(callee_parameters)
    ]

    total_explicit = len(explicit)
    total_params = len(callee_parameters)
    best_scores: Dict[Tuple[int, int], int] = {}
    best_paths: Dict[Tuple[int, int], Tuple[int, ...]] = {}

    def solve(explicit_index: int, param_index: int) -> int:
        key = (explicit_index, param_index)
        if key in best_scores:
            return best_scores[key]

        remaining_explicit = total_explicit - explicit_index
        remaining_params = total_params - param_index
        if remaining_explicit < remaining_params:
            best_scores[key] = -10**9
            best_paths[key] = ()
            return best_scores[key]
        if param_index >= total_params:
            skip_score = -2 * remaining_explicit
            best_scores[key] = skip_score
            best_paths[key] = ()
            return skip_score
        if explicit_index >= total_explicit:
            best_scores[key] = -10**9
            best_paths[key] = ()
            return best_scores[key]

        skip_penalty = -1 if param_index == 0 else -6
        skip_score = skip_penalty + solve(explicit_index + 1, param_index)
        take_tail_score = solve(explicit_index + 1, param_index + 1)
        if take_tail_score <= -10**8:
            take_score = take_tail_score
        else:
            take_score = _score_call_argument_alignment(
                explicit[explicit_index],
                caller_parameters,
                callee_parameters[param_index],
                preferred_args[param_index],
                explicit_index,
                param_index,
                total_explicit,
                total_params,
            ) + take_tail_score

        if take_score > skip_score:
            best_scores[key] = take_score
            best_paths[key] = (explicit_index,) + best_paths.get(
                (explicit_index + 1, param_index + 1),
                (),
            )
        else:
            best_scores[key] = skip_score
            best_paths[key] = best_paths.get((explicit_index + 1, param_index), ())
        return best_scores[key]

    solve(0, 0)
    selected_indices = list(best_paths.get((0, 0), ()))
    if len(selected_indices) != total_params:
        return explicit[:total_params]
    return [explicit[index] for index in selected_indices]


def _recover_preferred_call_argument_expression(
    call_op,
    tracer,
    caller_parameters: Sequence[Dict],
    callee_param: Dict,
    index: int,
) -> Optional[Expression]:
    preferred = _recover_call_argument_from_storage(
        call_op,
        tracer,
        caller_parameters,
        callee_param,
    )
    if preferred is None:
        preferred = _parameter_expression_from_matching_storage(
            callee_param,
            caller_parameters,
            size=callee_param.get("size"),
        )
    if preferred is None and index < len(caller_parameters):
        caller_param = caller_parameters[index]
        caller_storage = _coerce_storage_info(caller_param.get("storage"))
        callee_storage = _coerce_storage_info(callee_param.get("storage"))
        if (
            caller_storage is not None
            and callee_storage is not None
            and _storage_infos_match(caller_storage, callee_storage)
        ):
            preferred = _parameter_expression_from_descriptor(
                caller_param,
                size=callee_param.get("size"),
            )
    if preferred is None:
        return None
    return _normalize_call_argument_expression(preferred, index, caller_parameters)


def _score_call_argument_alignment(
    expr: Optional[Expression],
    caller_parameters: Sequence[Dict],
    callee_param: Optional[Dict],
    preferred: Optional[Expression],
    explicit_index: int,
    param_index: int,
    total_explicit: int,
    total_params: int,
) -> int:
    if expr is None:
        return -10**6

    score = _call_argument_semantic_rank(expr, caller_parameters, callee_param) * 5
    score += _call_argument_position_bias(
        explicit_index,
        param_index,
        total_explicit,
        total_params,
    )
    expr_param = _resolve_parameter_descriptor(expr, caller_parameters)
    preferred_param = _resolve_parameter_descriptor(preferred, caller_parameters) if preferred is not None else None

    if preferred is not None:
        if _expressions_equivalent(expr, preferred):
            score += 100
        elif _parameter_descriptors_share_identity(expr_param, preferred_param):
            score += 85
        else:
            expr_size = max(1, int(expr.size or (callee_param or {}).get("size") or 8))
            preferred_size = max(1, int(preferred.size or (callee_param or {}).get("size") or 8))
            expr_location = canonicalize_location(expr, caller_parameters, size=expr_size)
            preferred_location = canonicalize_location(preferred, caller_parameters, size=preferred_size)
            if expr_location is not None and expr_location == preferred_location:
                score += 70

    if expr_param is not None:
        score += 15
        caller_param = expr_param
        if caller_param is not None and callee_param is not None:
            caller_storage = _coerce_storage_info(caller_param.get("storage"))
            callee_storage = _coerce_storage_info(callee_param.get("storage"))
            if (
                caller_storage is not None
                and callee_storage is not None
                and _storage_infos_match(caller_storage, callee_storage)
            ):
                score += 45
            try:
                if int(caller_param.get("index", -1)) == int(callee_param.get("index", -2)):
                    score += 10
            except Exception:
                pass
    elif expr.expr_type == ExpressionType.CONSTANT:
        if _parameter_descriptor_looks_pointer(callee_param):
            try:
                score += 10 if int(expr.value) == 0 else -5
            except Exception:
                score += 0
        else:
            score += 12
    elif expr.expr_type == ExpressionType.PHI:
        score += 16
    elif expr.expr_type == ExpressionType.CALL:
        score += 12
    elif expr.expr_type in {ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.MEMORY}:
        score += 5

    try:
        callee_size = int((callee_param or {}).get("size") or 0)
    except Exception:
        callee_size = 0
    try:
        expr_size = int(expr.size or 0)
    except Exception:
        expr_size = 0
    if callee_size > 0 and expr_size == callee_size:
        score += 2

    return score


def _call_argument_position_bias(
    explicit_index: int,
    param_index: int,
    total_explicit: int,
    total_params: int,
) -> int:
    extra_prefix = total_explicit - total_params
    if extra_prefix <= 0:
        return 0

    expected_index = extra_prefix + param_index
    delta = explicit_index - expected_index
    if delta == 0:
        return 90
    if delta < 0:
        return -35 * abs(delta)
    return -18 * delta


def _should_preserve_explicit_indirect_target_argument(
    expr: Optional[Expression],
    callee_param: Optional[Dict],
) -> bool:
    if expr is None or not _parameter_descriptor_looks_pointer(callee_param):
        return False
    if expr.expr_type == ExpressionType.PHI:
        return True
    return bool(_enumerate_constant_expression_branches(expr))


def _should_prefer_explicit_call_argument(
    expr: Optional[Expression],
    caller_parameters: Sequence[Dict],
    size: Optional[int] = None,
) -> bool:
    if expr is None:
        return False
    if expr.expr_type == ExpressionType.PHI:
        return True
    if expr.expr_type in {ExpressionType.CONSTANT, ExpressionType.MEMORY, ExpressionType.CALL}:
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


def _parameter_descriptor_looks_pointer(param: Optional[Dict]) -> bool:
    if not param:
        return False
    return bool(
        is_pointer_data_type(
            param.get("data_type_obj"),
            None,
        )
    )


def _call_argument_semantic_rank(
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


def _resolve_call_target_ref(tracer, op) -> Optional[CallTargetRef]:
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
        if resolved is not None:
            return resolved
    else:
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


def _resolve_call_target_name(tracer, op) -> Optional[str]:
    target_ref = _resolve_call_target_ref(tracer, op)
    if target_ref is None:
        return None
    return target_ref.display_name()


def resolve_call_targets(
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


def _deduplicate_resolved_call_targets(
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


def _enumerate_constant_expression_branches(
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


def _evaluate_constant_expression(expr: Optional[Expression]) -> Optional[int]:
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

    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left_value = _evaluate_constant_expression(expr.operands[0])
        right_value = _evaluate_constant_expression(expr.operands[1])
        if left_value is None or right_value is None:
            return None

        if expr.operator == "INT_ADD":
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


def _apply_unary_constant_op(expr: Expression, operand_value: int) -> Optional[int]:
    target_bits = max(8, (expr.size or expr.operands[0].size or 8) * 8)
    if expr.operator in {"CAST", "COPY", "INT_ZEXT"}:
        return operand_value & ((1 << target_bits) - 1)
    if expr.operator == "INT_SEXT":
        return _sign_extend_value(operand_value, expr.operands[0].get_bit_width(), target_bits)
    return None


def _apply_binary_constant_op(expr: Expression, left_value: int, right_value: int) -> Optional[int]:
    if expr.operator == "INT_ADD":
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


def _sign_extend_value(value: int, source_bits: int, target_bits: int) -> int:
    source_bits = max(1, int(source_bits))
    target_bits = max(source_bits, int(target_bits))
    mask = (1 << source_bits) - 1
    value &= mask
    sign_bit = 1 << (source_bits - 1)
    if value & sign_bit:
        value -= 1 << source_bits
    return value & ((1 << target_bits) - 1)


def _mask_to_expr_width(expr: Expression, value: int) -> int:
    bit_width = max(1, expr.get_bit_width())
    return value & ((1 << bit_width) - 1)
def _resolve_function_ref_from_address(
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


def _resolve_function_ref_by_value(
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


def _resolve_call_argument_expression(
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


def _recover_call_argument_from_storage(
    call_op,
    tracer,
    caller_parameters: Sequence[Dict],
    callee_param: Dict,
) -> Optional[Expression]:
    target_storage = _coerce_storage_info(callee_param.get("storage"))
    if target_storage is None:
        return None

    call_order = _get_order_key(call_op)
    best_candidate = None
    best_order = None
    best_rank = -1
    best_semantic_rank = -1

    for op in tracer.get_all_pcode_ops():
        op_order = _get_order_key(op)
        if op_order >= call_order:
            continue

        output = op.getOutput()
        output_rank = _varnode_storage_match_rank(output, target_storage, tracer)
        if output is not None and output_rank > 0:
            candidate_expr = _resolve_call_argument_expression(output, tracer, caller_parameters)
            semantic_rank = _call_argument_semantic_rank(
                candidate_expr,
                caller_parameters,
                callee_param,
            )
            if (
                semantic_rank > best_semantic_rank
                or (
                    semantic_rank == best_semantic_rank
                    and (
                        output_rank > best_rank
                        or (output_rank == best_rank and (best_order is None or op_order > best_order))
                    )
                )
            ):
                best_candidate = candidate_expr
                best_order = op_order
                best_rank = output_rank
                best_semantic_rank = semantic_rank

        if not target_storage.is_register and op.getMnemonic() == "STORE" and op.getNumInputs() >= 3:
            if _stack_varnode_matches_storage(op.getInput(1), target_storage):
                candidate_expr = _resolve_call_argument_expression(op.getInput(2), tracer, caller_parameters)
                semantic_rank = _call_argument_semantic_rank(
                    candidate_expr,
                    caller_parameters,
                    callee_param,
                )
                if (
                    semantic_rank > best_semantic_rank
                    or (
                        semantic_rank == best_semantic_rank
                        and (3 > best_rank or (3 == best_rank and (best_order is None or op_order > best_order)))
                    )
                ):
                    best_candidate = candidate_expr
                    best_order = op_order
                    best_rank = 3
                    best_semantic_rank = semantic_rank

    if best_candidate is None:
        return None

    return best_candidate


def _parameter_expression_from_matching_storage(
    callee_param: Dict,
    caller_parameters: Sequence[Dict],
    size: Optional[int] = None,
) -> Optional[Expression]:
    callee_storage = _coerce_storage_info(callee_param.get("storage"))
    if callee_storage is None:
        return None

    matches: List[Dict] = []
    for caller_param in caller_parameters:
        caller_storage = _coerce_storage_info(caller_param.get("storage"))
        if caller_storage is None:
            continue
        if _storage_infos_match(caller_storage, callee_storage):
            matches.append(caller_param)

    if len(matches) != 1:
        return None
    return _parameter_expression_from_descriptor(matches[0], size=size or callee_param.get("size"))


def _varnode_matches_storage(varnode, target_storage: StorageInfo, tracer) -> bool:
    return _varnode_storage_match_rank(varnode, target_storage, tracer) > 0


def _varnode_storage_match_rank(varnode, target_storage: StorageInfo, tracer) -> int:
    varnode_storage = tracer._get_storage_info_from_varnode(varnode)
    if varnode_storage is not None:
        return _storage_match_rank(varnode_storage, target_storage)
    if target_storage.is_register:
        return 0
    return 3 if _stack_varnode_matches_storage(varnode, target_storage) else 0


def _stack_varnode_matches_storage(varnode, target_storage: StorageInfo) -> bool:
    if varnode is None:
        return False
    try:
        addr = varnode.getAddress()
        space = addr.getAddressSpace()
        if space is None:
            return False
        return (
            space.getName() == target_storage.space_name
            and int(varnode.getOffset()) == target_storage.offset
            and int(varnode.getSize()) == target_storage.size
        )
    except Exception:
        return False


def _storage_infos_match(left: StorageInfo, right: StorageInfo) -> bool:
    return _storage_match_rank(left, right) > 0


def _storage_match_rank(left: StorageInfo, right: StorageInfo) -> int:
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
            if (
                StorageInfo._normalize_reg_name(left.register_name or "")
                == StorageInfo._normalize_reg_name(right.register_name or "")
            ):
                return 2
            if left.bit_range_overlaps_with(right):
                return 1
            return 0
        return (
            2
            if StorageInfo._normalize_reg_name(left.register_name or "")
            == StorageInfo._normalize_reg_name(right.register_name or "")
            else 0
        )
    return 3 if (
        left.space_name == right.space_name
        and left.offset == right.offset
        and left.size == right.size
    ) else 0


def _normalize_call_argument_expression(
    expr: Expression,
    arg_index: int,
    parameters: Sequence[Dict],
) -> Expression:
    if expr is None:
        return expr

    if _expression_maps_to_parameter(expr, parameters):
        return expr

    if expr.expr_type not in (ExpressionType.PARAMETER, ExpressionType.VARIABLE, ExpressionType.UNKNOWN):
        return expr
    if getattr(expr, "operands", None):
        return expr
    if arg_index < 0 or arg_index >= len(parameters):
        return expr

    fallback = _parameter_expression_from_descriptor(parameters[arg_index], size=expr.size or None)
    return fallback or expr


def _choose_effect_substitution_args(
    location: CanonicalLocation,
    callee_params: Sequence[object],
    args: Sequence[Expression],
    caller_parameters: Sequence[Dict],
) -> Sequence[Expression]:
    direct_location = substitute_location(location, callee_params, args, caller_parameters)
    if direct_location is not None:
        return args

    positional_args = _build_positional_parameter_args(args, caller_parameters)
    if positional_args is None:
        return args

    positional_location = substitute_location(
        location,
        callee_params,
        positional_args,
        caller_parameters,
    )
    if positional_location is not None:
        return positional_args
    return args


def _build_positional_parameter_args(
    args: Sequence[Expression],
    parameters: Sequence[Dict],
) -> Optional[List[Expression]]:
    if not args:
        return None
    positional_args: List[Expression] = []
    changed = False
    for index, expr in enumerate(args):
        fallback = _parameter_expression_from_descriptor(
            parameters[index],
            size=(expr.size if expr is not None else None),
        ) if index < len(parameters) else None
        if fallback is None:
            positional_args.append(expr)
            continue
        positional_args.append(fallback)
        changed = changed or not _expressions_equivalent(expr, fallback)
    if not changed:
        return None
    return positional_args


def _expression_maps_to_parameter(expr: Optional[Expression], parameters: Sequence[Dict]) -> bool:
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


def _normalize_parameter_index(value: Optional[object]) -> Optional[int]:
    try:
        if value is None:
            return None
        normalized = int(value)
    except Exception:
        return None
    return normalized if normalized >= 0 else None


def _storage_identity_key(storage: Optional[StorageInfo]) -> Optional[Tuple[object, ...]]:
    storage = _coerce_storage_info(storage)
    if storage is None:
        return None
    if storage.is_register:
        base_name = StorageInfo._normalize_reg_name(storage.base_register_name or storage.register_name or "")
        if not base_name:
            return None
        return (
            "param_storage_reg",
            base_name,
            int(storage.bit_offset_in_base or 0),
            int(storage.size_bits or 0),
        )
    return (
        "param_storage_mem",
        storage.space_name or "",
        int(storage.offset or 0),
        int(storage.size or 0),
    )


def _parameter_identity_key_from_base_ref(
    base_ref: Optional[LocationBaseRef],
) -> Optional[Tuple[object, ...]]:
    if base_ref is None or not base_ref.is_parameter():
        return None
    if base_ref.parameter_index is None:
        return None
    return ("parameter", int(base_ref.parameter_index))


def _parameter_identity_keys_from_descriptor(param: Optional[Dict]) -> Set[Tuple[object, ...]]:
    if not param:
        return set()
    keys: Set[Tuple[object, ...]] = set()
    param_index = _normalize_parameter_index(param.get("index"))
    if param_index is not None:
        keys.add(("parameter", param_index))
    storage_key = _storage_identity_key(_coerce_storage_info(param.get("storage")))
    if storage_key is not None:
        keys.add(storage_key)
    return keys


def _parameter_identity_keys_from_expression(
    expr: Optional[Expression],
    parameters: Sequence[Dict],
) -> Set[Tuple[object, ...]]:
    if expr is None:
        return set()

    keys: Set[Tuple[object, ...]] = set()

    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, LocationBaseRef):
        base_key = _parameter_identity_key_from_base_ref(runtime_ref)
        if base_key is not None:
            keys.add(base_key)
    elif isinstance(runtime_ref, CanonicalLocation):
        base_key = _parameter_identity_key_from_base_ref(runtime_ref.base_ref)
        if base_key is not None and not runtime_ref.steps and int(runtime_ref.offset) == 0:
            keys.add(base_key)

    if expr.expr_type == ExpressionType.PARAMETER:
        param_index = _normalize_parameter_index(getattr(expr, "value", None))
        if param_index is not None:
            keys.add(("parameter", param_index))

    storage_key = _storage_identity_key(_coerce_storage_info(getattr(expr, "storage_info", None)))
    if storage_key is not None:
        keys.add(storage_key)

    descriptor = _resolve_parameter_descriptor(expr, parameters)
    keys.update(_parameter_identity_keys_from_descriptor(descriptor))
    return keys


def _parameter_descriptors_share_identity(left: Optional[Dict], right: Optional[Dict]) -> bool:
    if not left or not right:
        return False
    return bool(
        _parameter_identity_keys_from_descriptor(left).intersection(
            _parameter_identity_keys_from_descriptor(right)
        )
    )


def _parameter_base_ref_matches_descriptor(
    base_ref: Optional[LocationBaseRef],
    param: Optional[Dict],
) -> bool:
    base_key = _parameter_identity_key_from_base_ref(base_ref)
    if base_key is None or not param:
        return False
    return base_key in _parameter_identity_keys_from_descriptor(param)


def _coerce_callee_parameter_ref(param: object, index: int) -> LocationBaseRef:
    if isinstance(param, LocationBaseRef) and param.is_parameter():
        normalized_index = _normalize_parameter_index(param.parameter_index)
        if normalized_index is not None:
            return LocationBaseRef.parameter(param.parameter_name, index=normalized_index)
        return LocationBaseRef.parameter(param.parameter_name, index=index)
    if isinstance(param, dict):
        return _parameter_base_ref(
            name=param.get("name"),
            index=param.get("index", index),
        )
    if isinstance(param, str):
        return LocationBaseRef.parameter(param, index=index)
    return LocationBaseRef.parameter(None, index=index)


def _coerce_callee_parameter_refs(params: Sequence[object]) -> List[LocationBaseRef]:
    return [_coerce_callee_parameter_ref(param, index) for index, param in enumerate(params)]


def _build_parameter_replacements(
    callee_params: Sequence[object],
    args: Sequence[Expression],
) -> Dict[Tuple[object, ...], Expression]:
    replacements: Dict[Tuple[object, ...], Expression] = {}
    for param_ref, arg in zip(_coerce_callee_parameter_refs(callee_params), args):
        key = _parameter_identity_key_from_base_ref(param_ref)
        if key is not None:
            replacements[key] = arg
    return replacements


def _parameter_base_ref(
    *,
    name: Optional[object] = None,
    index: Optional[object] = None,
) -> LocationBaseRef:
    normalized_name = str(name) if isinstance(name, str) and name else None
    return LocationBaseRef(
        kind="parameter",
        parameter_name=normalized_name,
        parameter_index=_normalize_parameter_index(index),
        display_hint=normalized_name,
    )


def _parameter_base_ref_from_expression(expr: Optional[Expression]) -> Optional[LocationBaseRef]:
    if expr is None:
        return None

    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, LocationBaseRef) and runtime_ref.is_parameter():
        return runtime_ref
    if isinstance(runtime_ref, CanonicalLocation) and runtime_ref.base_ref.is_parameter():
        if not runtime_ref.steps and int(runtime_ref.offset) == 0:
            return runtime_ref.base_ref

    if expr.expr_type == ExpressionType.PARAMETER:
        return _parameter_base_ref(name=expr.name, index=expr.value)
    return None


def _resolve_parameter_descriptor_from_identity(
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


def _resolve_parameter_descriptor(
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


def _parameter_expression_from_descriptor(param: Dict, size: Optional[int] = None) -> Optional[Expression]:
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
        runtime_ref=_parameter_base_ref(name=name, index=param_index),
    )


def _recover_parameter_expression_from_varnode(
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


def _parameter_expression_from_varnode(varnode, tracer, parameters: Sequence[Dict]) -> Optional[Expression]:
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


def _recover_parameter_from_stack_load(
    load_op,
    tracer,
    parameters: Sequence[Dict],
    depth: int,
    seen: Set[int],
) -> Optional[Expression]:
    location = _stack_location_key(load_op.getInput(1), size=load_op.getOutput().getSize() if load_op.getOutput() else 0)
    if location is None:
        return None

    load_order = _get_order_key(load_op)
    best_candidate = None
    best_order = None
    for op in tracer.get_all_pcode_ops():
        op_order = _get_order_key(op)
        if op_order >= load_order:
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


def _stack_location_key(varnode, size: int = 0) -> Optional[Tuple[str, int, int]]:
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


def is_call_effect_summary_allowed(summary: EffectSummary) -> bool:
    if summary is None:
        return False
    if summary.has_unsupported_call:
        return False
    if not summary.effects:
        return False

    for effect in summary.effects:
        if not _expression_is_call_scope_safe(effect.value):
            return False
        for condition in effect.conditions:
            if not _expression_is_call_scope_safe(condition.expression):
                return False

    if summary.synthetic_expr is not None and not _expression_is_call_scope_safe(summary.synthetic_expr):
        return False

    return True


def _expression_is_call_scope_safe(expr: Optional[Expression]) -> bool:
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


def _summary_has_interdependent_writes(summary: EffectSummary) -> bool:
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


def canonicalize_param_location(
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


def canonicalize_location(
    addr_expr: Expression,
    parameters: Sequence[Dict],
    size: int = 4,
) -> Optional[CanonicalLocation]:
    return _canonicalize_address_expression(addr_expr, parameters, size=size)


def substitute_location(
    location: CanonicalLocation,
    callee_params: Sequence[object],
    call_args: Sequence[Expression],
    caller_params: Sequence[Dict],
) -> Optional[CanonicalLocation]:
    if not location.base_ref.is_parameter():
        return None
    callee_refs = _coerce_callee_parameter_refs(callee_params)
    param_index = _normalize_parameter_index(location.base_ref.parameter_index)
    if param_index is None or param_index >= len(callee_refs):
        return None
    if _parameter_identity_key_from_base_ref(callee_refs[param_index]) != _parameter_identity_key_from_base_ref(
        location.base_ref
    ):
        return None
    if param_index >= len(call_args):
        return None
    actual_addr = call_args[param_index]
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


def rewrite_loads_from_effects(
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
            runtime_location=_expression_location_ref(expr),
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
            preserve_symbolic_fallback=preserve_symbolic_fallback,
        )

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL):
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


def rewrite_location_read_from_effects(
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


def _rewrite_canonical_location_read(
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
    normalized_return_conditions = ConditionSimplifier.simplify_conditions(list(return_conditions))
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
        normalized_effect_conditions = ConditionSimplifier.simplify_conditions(list(effect.conditions))
        if max_order_key is not None and effect.order_key >= max_order_key:
            continue
        if effect.location.size != location.size:
            continue
        if ConditionSimplifier.is_contradiction(normalized_return_conditions + normalized_effect_conditions):
            continue
        if not locations_match(location, effect.location, normalized_return_conditions + normalized_effect_conditions):
            continue
        residual = subtract_implied_conditions(normalized_effect_conditions, normalized_return_conditions)
        matched.append((effect.order_key, residual, effect.value))

    if not matched:
        return fallback_expr

    if definite_post_state and _all_residual_guards_empty(matched):
        replayed_state = _replay_definite_active_effects_for_location(
            location,
            normalized_return_conditions,
            effects,
            parameters,
        )
        if replayed_state is not None:
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


def rewrite_observed_loads_from_effects(
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


def _matches_existing_effect_value(
    expr: Expression,
    location: CanonicalLocation,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    max_order_key: Optional[int] = None,
) -> bool:
    return (
        _find_matching_effect_value(
            expr,
            location,
            return_conditions,
            effects,
            parameters,
            max_order_key=max_order_key,
        )
        is not None
    )


def _find_matching_effect_value(
    expr: Expression,
    location: CanonicalLocation,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    max_order_key: Optional[int] = None,
) -> Optional[Tuple[int, Expression]]:
    normalized_return_conditions = ConditionSimplifier.simplify_conditions(list(return_conditions))
    for effect in effects:
        normalized_effect_conditions = ConditionSimplifier.simplify_conditions(list(effect.conditions))
        if max_order_key is not None and effect.order_key >= max_order_key:
            continue
        if ConditionSimplifier.is_contradiction(normalized_return_conditions + normalized_effect_conditions):
            continue
        if not locations_match(location, effect.location, normalized_return_conditions):
            continue
        if not _expression_reads_location(expr, location, normalized_return_conditions, parameters):
            continue
        if _expression_matches_value_under_conditions(
            expr,
            effect.value,
            normalized_return_conditions + normalized_effect_conditions,
            parameters,
        ):
            return effect.order_key, effect.value
    return None


def _expression_matches_value_under_conditions(
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
        if ConditionSimplifier.is_contradiction(combined):
            continue
        if _expression_matches_value_under_conditions(reduced_expr, branch_value, combined, parameters):
            return True
    return False


def canonicalize_expr_read_location(expr: Expression, parameters: Sequence[Dict]) -> Optional[CanonicalLocation]:
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


def _expression_reads_location(
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


def _compute_effect_cycle_components(
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
) -> Dict[CanonicalLocation, FrozenSet[CanonicalLocation]]:
    locations = sorted({effect.location for effect in effects}, key=_location_sort_key)
    if len(locations) <= 1:
        return {}

    graph: Dict[CanonicalLocation, Set[CanonicalLocation]] = {location: set() for location in locations}
    for effect in effects:
        for candidate in locations:
            if candidate == effect.location:
                continue
            if _expression_reads_location(effect.value, candidate, effect.conditions, parameters):
                graph[effect.location].add(candidate)

    components: Dict[CanonicalLocation, FrozenSet[CanonicalLocation]] = {}
    for component in _strongly_connected_components(graph):
        if len(component) <= 1:
            continue
        frozen_component = frozenset(component)
        for location in component:
            components[location] = frozen_component
    return components


def _strongly_connected_components(
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


def _expressions_equivalent(left: Optional[Expression], right: Optional[Expression]) -> bool:
    if left is right:
        return True
    if left is None or right is None:
        return False
    left_key = expression_key_safe(left, include_memory_read_order=True)
    right_key = expression_key_safe(right, include_memory_read_order=True)
    if left_key is None or right_key is None:
        return False
    return left_key == right_key


def _expression_contains_parameter_identity(
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


def _collect_parameter_replacements_from_conditions(
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


def _apply_condition_parameter_replacements(
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


def _additive_signature(expr: Optional[Expression]) -> Optional[Tuple[int, Tuple[Tuple[object, int], ...], int]]:
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


def _expressions_equivalent_under_conditions(
    left: Optional[Expression],
    right: Optional[Expression],
    conditions: Sequence[Condition],
    parameters: Sequence[Dict],
) -> bool:
    if _expressions_equivalent(left, right):
        return True

    left_rewritten = _apply_condition_parameter_replacements(left, conditions, parameters)
    right_rewritten = _apply_condition_parameter_replacements(right, conditions, parameters)
    if _expressions_equivalent(left_rewritten, right_rewritten):
        return True

    left_sig = _additive_signature(left_rewritten)
    right_sig = _additive_signature(right_rewritten)
    if left_sig is None or right_sig is None:
        return False
    return left_sig == right_sig


def build_void_effect_summary_expr(effects: Sequence[StoreEffect]) -> Optional[Expression]:
    groups: Dict[CanonicalLocation, List[StoreEffect]] = {}
    for effect in effects:
        groups.setdefault(effect.location, []).append(effect)

    if not groups:
        return None

    summary_parts: List[Expression] = []
    for location in sorted(groups.keys(), key=_location_sort_key):
        loc_effects = sorted(groups[location], key=lambda effect: effect.order_key, reverse=True)
        value_branches = []
        flag_branches = []
        for effect in loc_effects:
            cond = Condition.combine_and(effect.conditions)
            value_branches.append((cond, effect.value))
            flag_branches.append((cond, Expression.constant(1, 1)))
        value_branches.append((None, Expression.constant(0, max(1, location.size))))
        flag_branches.append((None, Expression.constant(0, 1)))
        value_expr = Expression.phi(value_branches)
        value_expr.size = max(1, location.size)
        flag_expr = Expression.phi(flag_branches)
        flag_expr.size = 1
        summary_parts.append(_concat(flag_expr, value_expr))

    result = summary_parts[0]
    for part in summary_parts[1:]:
        result = _concat(result, part)
    return result


@overload
def collapse_post_state_expr_to_canonical_memory(
    expr: Expression,
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    return_conditions: Optional[Sequence[Condition]] = None,
) -> Optional[Expression]:
    ...


@overload
def collapse_post_state_expr_to_canonical_memory(
    expr: Optional[Expression],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    return_conditions: Optional[Sequence[Condition]] = None,
) -> Optional[Expression]:
    ...


def collapse_post_state_expr_to_canonical_memory(
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


def _latest_definite_effect_value_for_location(
    location: CanonicalLocation,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
) -> Optional[Expression]:
    normalized_return_conditions = ConditionSimplifier.simplify_conditions(list(return_conditions))
    latest_effect: Optional[StoreEffect] = None
    for effect in effects:
        normalized_effect_conditions = ConditionSimplifier.simplify_conditions(list(effect.conditions))
        if effect.location.size != location.size:
            continue
        if ConditionSimplifier.is_contradiction(normalized_return_conditions + normalized_effect_conditions):
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


def collapse_post_state_expr_to_canonical_read(
    expr: Optional[Expression],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    return_conditions: Optional[Sequence[Condition]] = None,
    *,
    symbolic_post_state: bool = False,
) -> Optional[Expression]:
    if expr is None or not effects or not parameters:
        return None

    active_conditions = list(return_conditions or [])
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


@overload
def collapse_pruned_post_state_memory_leaf_to_canonical_memory(
    expr: Expression,
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    return_conditions: Optional[Sequence[Condition]] = None,
) -> Optional[Expression]:
    ...


@overload
def collapse_pruned_post_state_memory_leaf_to_canonical_memory(
    expr: Optional[Expression],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    return_conditions: Optional[Sequence[Condition]] = None,
) -> Optional[Expression]:
    ...


def collapse_pruned_post_state_memory_leaf_to_canonical_memory(
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


@overload
def canonicalize_post_state_subexpressions(
    expr: Expression,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    *,
    symbolic_post_state: bool = False,
    allow_memory_leaf_collapse: bool = False,
) -> Expression:
    ...


@overload
def canonicalize_post_state_subexpressions(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    *,
    symbolic_post_state: bool = False,
    allow_memory_leaf_collapse: bool = False,
) -> Optional[Expression]:
    ...


def canonicalize_post_state_subexpressions(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    *,
    symbolic_post_state: bool = False,
    allow_memory_leaf_collapse: bool = False,
) -> Optional[Expression]:
    if expr is None:
        return None

    if expr.expr_type != ExpressionType.MEMORY or allow_memory_leaf_collapse:
        collapsed = collapse_post_state_expr_to_canonical_read(
            expr,
            effects,
            parameters,
            return_conditions=return_conditions,
            symbolic_post_state=symbolic_post_state,
        )
        if collapsed is not None:
            return collapsed

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL, ExpressionType.MEMORY):
        rewritten_operands = [
            canonicalize_post_state_subexpressions(
                op,
                return_conditions,
                effects,
                parameters,
                symbolic_post_state=symbolic_post_state,
                allow_memory_leaf_collapse=False,
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
            )
            branches.append((cond, new_value))
            changed = changed or (new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt

    return expr


@overload
def normalize_post_state_expression(
    expr: Expression,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    *,
    prefer_canonical_post_state: bool = True,
    symbolic_post_state: bool = False,
    preserve_composite_location_wrappers: bool = False,
) -> Expression:
    ...


@overload
def normalize_post_state_expression(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    *,
    prefer_canonical_post_state: bool = True,
    symbolic_post_state: bool = False,
    preserve_composite_location_wrappers: bool = False,
) -> Optional[Expression]:
    ...


def normalize_post_state_expression(
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

    def _normalize_candidate(candidate_expr: Expression) -> Expression:
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

        post_state_promoted = (
            expression_contains_post_state_reads(normalized)
            and not expression_contains_post_state_reads(candidate_expr)
        )

        if not prefer_canonical_post_state or (
            _expressions_equivalent(normalized, candidate_expr)
            and not post_state_promoted
        ):
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
    if _expression_contains_observed_loads(expr):
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
        if observed_rank == normalized_rank and not _expressions_equivalent(observed_normalized, expr):
            return observed_normalized

    return normalized


@overload
def lower_post_state_expression_for_smt(
    expr: Expression,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
) -> Expression:
    ...


@overload
def lower_post_state_expression_for_smt(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
) -> Optional[Expression]:
    ...


def lower_post_state_expression_for_smt(
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

    lowered = rewrite_loads_from_effects(
        expr,
        return_conditions,
        effects,
        parameters,
        preserve_symbolic_fallback=False,
    )
    reduced = _reduce_expression_under_conditions(lowered, return_conditions)
    return reduced if reduced is not None else lowered


@overload
def lower_post_state_expression_for_smt_if_needed(
    expr: Expression,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
) -> Expression:
    ...


@overload
def lower_post_state_expression_for_smt_if_needed(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
) -> Optional[Expression]:
    ...


def lower_post_state_expression_for_smt_if_needed(
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


def _rewrite_definite_post_state_subexpressions(
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
        return current if _expressions_equivalent(current, resolved) else resolved

    if expr.expr_type in (
        ExpressionType.BINARY_OP,
        ExpressionType.UNARY_OP,
        ExpressionType.CALL,
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


def materialize_definite_post_state_expression(
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


def _should_preserve_composite_location_wrapper(
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


def _replay_definite_active_effects_for_location(
    location: CanonicalLocation,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
) -> Optional[Expression]:
    normalized_return_conditions = ConditionSimplifier.simplify_conditions(list(return_conditions))
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


def _collect_definite_active_effects(
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
) -> List[StoreEffect]:
    normalized_return_conditions = ConditionSimplifier.simplify_conditions(list(return_conditions))
    active_effects: List[StoreEffect] = []
    for effect in effects:
        normalized_effect_conditions = ConditionSimplifier.simplify_conditions(list(effect.conditions))
        if ConditionSimplifier.is_contradiction(normalized_return_conditions + normalized_effect_conditions):
            continue
        residual = subtract_implied_conditions(normalized_effect_conditions, normalized_return_conditions)
        if residual:
            continue
        active_effects.append(
            StoreEffect(
                location=effect.location,
                value=effect.value,
                conditions=normalized_effect_conditions,
                order_key=effect.order_key,
            )
        )
    return active_effects


def _rewrite_expression_with_replayed_state(
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


def _build_alias_representative_map(
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


def _resolve_alias_representative(
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


def _location_sort_key(location: CanonicalLocation) -> Tuple[Tuple[object, ...], Tuple[Tuple[str, int], ...], int, int]:
    normalized = _normalize_canonical_location(location)
    step_key = tuple((step.kind, int(step.value)) for step in normalized.steps)
    return (normalized.base_ref.stable_key(), step_key, normalized.offset, normalized.size)


def memory_expression_for_location(
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
            _synthetic_location_read_name(location),
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


def post_state_read_expression_for_location(
    location: CanonicalLocation,
    parameters: Sequence[Dict],
    *,
    symbolic: bool = False,
) -> Expression:
    location = _normalize_canonical_location(location)
    concrete_expr = memory_expression_for_location(location, parameters)
    if concrete_expr is not None and concrete_expr.expr_type == ExpressionType.MEMORY and concrete_expr.operands:
        if not symbolic:
            return concrete_expr
        return _memory_expr_with_runtime_location(
            concrete_expr.operands[0],
            concrete_expr.size,
            read_order_key=concrete_expr.read_order_key,
            runtime_location=location,
        )
    if not symbolic:
        return Expression.variable(
            _synthetic_location_read_name(location),
            size=max(1, location.size),
        )
    return Expression.variable(
        _synthetic_location_read_name(location),
        size=max(1, location.size),
        runtime_ref=location,
    )


def _reduce_expression_under_conditions(
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

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL, ExpressionType.MEMORY):
        new_operands = [_reduce_expression_under_conditions(op, conditions) for op in expr.operands]
        return _clone_expression_with_operands(expr, new_operands) if not all(
            new is old for new, old in zip(new_operands, expr.operands)
        ) else expr

    return expr


def locations_match(
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


def subtract_implied_conditions(
    effect_conditions: Sequence[Condition],
    return_conditions: Sequence[Condition],
) -> List[Condition]:
    implied = _collect_implied_condition_norms(return_conditions)
    residual = []
    for cond in effect_conditions:
        if not _condition_is_implied(cond, implied):
            residual.append(cond)
    return residual


def _collect_implied_condition_norms(
    conditions: Sequence[Condition],
):
    implied = set()
    stack = list(conditions or [])
    while stack:
        condition = stack.pop()
        if condition is None:
            continue
        normalized = ConditionNormalizer.normalize_for_contradiction(condition)
        implied.add(normalized)

        expr = condition.expression
        if (
            not condition.negated
            and expr is not None
            and expr.expr_type == ExpressionType.BINARY_OP
            and expr.operator == "BOOL_AND"
        ):
            stack.append(Condition(expr.operands[0], False))
            stack.append(Condition(expr.operands[1], False))

    return implied


def _condition_is_implied(
    condition: Condition,
    implied_conditions,
) -> bool:
    normalized = ConditionNormalizer.normalize_for_contradiction(condition)
    if normalized in implied_conditions:
        return True

    expr = condition.expression
    if (
        not condition.negated
        and expr is not None
        and expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "BOOL_AND"
    ):
        stack = [Condition(expr.operands[0], False), Condition(expr.operands[1], False)]
        while stack:
            current = stack.pop()
            current_expr = current.expression
            if (
                not current.negated
                and current_expr is not None
                and current_expr.expr_type == ExpressionType.BINARY_OP
                and current_expr.operator == "BOOL_AND"
            ):
                stack.append(Condition(current_expr.operands[0], False))
                stack.append(Condition(current_expr.operands[1], False))
                continue
            if ConditionNormalizer.normalize_for_contradiction(current) not in implied_conditions:
                return False
        return True

    return False


def substitute_condition(
    condition: Condition,
    replacements: Dict[Tuple[object, ...], Expression],
    parameters: Optional[Sequence[Dict]] = None,
) -> Condition:
    return Condition(
        substitute_expression(condition.expression, replacements, parameters),
        condition.negated,
    )


def substitute_expression(
    expr: Expression,
    replacements: Dict[Tuple[object, ...], Expression],
    parameters: Optional[Sequence[Dict]] = None,
) -> Expression:
    replacement = _lookup_parameter_replacement(expr, replacements, parameters)
    if replacement is not None:
        return _simplify_substituted_expression(replacement, parameters)

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL, ExpressionType.MEMORY):
        new_operands = [substitute_expression(op, replacements, parameters) for op in expr.operands]
        if all(new is old for new, old in zip(new_operands, expr.operands)):
            return _simplify_substituted_expression(expr, parameters)
        rebuilt = _clone_expression_with_operands(expr, new_operands)
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


def _lookup_parameter_replacement(
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


def _simplify_substituted_expression(
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


def _expression_truth_value(expr: Optional[Expression]) -> Optional[bool]:
    if expr is None:
        return None
    return ConditionSimplifier.evaluate_condition_truth(Condition(expr, False))


def _simplify_boolean_binary_expression(
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


def _known_nonnull_address_comparison_truth(
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


def _is_zero_constant(expr: Optional[Expression]) -> bool:
    return (
        expr is not None
        and expr.expr_type == ExpressionType.CONSTANT
        and isinstance(expr.value, int)
        and int(expr.value) == 0
    )


def _is_known_nonnull_stack_address(
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


def _collect_param_equalities(
    conditions: Sequence[Condition],
) -> Set[FrozenSet[Tuple[object, ...]]]:
    equalities: Set[FrozenSet[Tuple[object, ...]]] = set()
    for condition in conditions:
        pair = _extract_positive_param_equality_pair(condition)
        if pair is not None:
            equalities.add(pair)
    return equalities


def _extract_positive_param_equality_pair(
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


def _parameter_like_identity(expr: Optional[Expression]) -> Optional[Tuple[object, ...]]:
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
    if isinstance(runtime_ref, CanonicalLocation):
        return _parameter_identity_key_from_base_ref(runtime_ref.base_ref)
    return None


def _normalize_location_steps(steps: Sequence[LocationStep]) -> Tuple[LocationStep, ...]:
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


def _location_step_sequence(location: CanonicalLocation) -> List[LocationStep]:
    steps: List[LocationStep] = list(getattr(location, "steps", ()) or ())
    if int(getattr(location, "offset", 0) or 0) != 0:
        steps.append(LocationStep("offset", int(location.offset)))
    return list(_normalize_location_steps(steps))


def _normalize_canonical_location(location: CanonicalLocation) -> CanonicalLocation:
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


def _canonicalize_address_expression(
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


def _extract_location_root_and_steps(
    expr: Expression,
    parameters: Sequence[Dict],
) -> Optional[Tuple[LocationBaseRef, List[LocationStep]]]:
    if expr is None:
        return None

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


def _flatten_param_addition(
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


def _flatten_location_addition(
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

    if expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
        return expr.value, []

    return None, []


def _resolve_location_base_with_offset(
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
    if not expr_storage.is_register and expr_storage.space_name == "stack":
        return LocationBaseRef.stack_frame(), int(expr_storage.offset)
    base_ref = _storage_base_ref(expr_storage)
    if base_ref is None:
        return None
    return base_ref, 0


def _is_stack_frame_base_expression(expr: Optional[Expression]) -> bool:
    if expr is None:
        return False

    expr_storage = _coerce_storage_info(getattr(expr, "storage_info", None))
    register_candidates = []
    if expr_storage is not None and expr_storage.is_register:
        register_candidates.extend(
            [
                expr_storage.register_name,
                expr_storage.base_register_name,
            ]
        )

    if expr.expr_type == ExpressionType.VARIABLE and expr.name:
        register_candidates.append(expr.name)

    normalized = {
        StorageInfo._normalize_reg_name(candidate or "")
        for candidate in register_candidates
        if candidate
    }
    return bool(
        normalized.intersection(
            {
                "sp",
                "wsp",
                "rsp",
                "esp",
                "rbp",
                "ebp",
                "bp",
                "fp",
                "s8",
                "x29",
            }
        )
    )


def _resolve_parameter_name(expr: Expression, parameters: Sequence[Dict]) -> Optional[str]:
    if expr is None:
        return None

    descriptor = _resolve_parameter_descriptor(expr, parameters)
    if descriptor is None:
        return None
    name = descriptor.get("name")
    return str(name) if isinstance(name, str) and name else None


def _coerce_storage_info(storage: Optional[object]) -> Optional[StorageInfo]:
    if storage is None:
        return None
    if isinstance(storage, StorageInfo):
        return storage
    if isinstance(storage, dict):
        try:
            return StorageInfo(
                is_register=bool(storage.get("is_register", False)),
                space_name=str(storage.get("space_name", "")),
                offset=int(storage.get("offset", 0)),
                size=int(storage.get("size", 0)),
                size_bits=int(storage.get("size_bits", 0)),
                register_name=storage.get("register_name"),
                base_register_name=storage.get("base_register_name"),
                base_register_offset=int(storage.get("base_register_offset", 0)),
                base_register_size=int(storage.get("base_register_size", 0)),
                base_register_size_bits=int(storage.get("base_register_size_bits", 0)),
                bit_offset_in_base=int(storage.get("bit_offset_in_base", 0)),
            )
        except Exception:
            return None
    return None


def _storage_matches_parameter(expr_storage: StorageInfo, param_storage: StorageInfo) -> bool:
    if expr_storage.is_register and param_storage.is_register:
        if expr_storage.shares_base_register_with(param_storage):
            expr_low = expr_storage.bit_offset_in_base
            expr_high = expr_low + max(0, int(expr_storage.size_bits or 0))
            param_low = param_storage.bit_offset_in_base
            param_high = param_low + max(0, int(param_storage.size_bits or 0))
            if expr_high <= expr_low or param_high <= param_low:
                return (
                    StorageInfo._normalize_reg_name(expr_storage.register_name or "")
                    == StorageInfo._normalize_reg_name(param_storage.register_name or "")
                )
            # Only treat a register-backed value as "the same parameter" when all
            # of the value's bits are contained within the parameter fragment.
            # Mere overlap is too permissive on architectures like MIPS64 where
            # `a0` and `a0_lo` share a base register but mean different things.
            return param_low <= expr_low and expr_high <= param_high
        return (
            StorageInfo._normalize_reg_name(expr_storage.register_name or "")
            == StorageInfo._normalize_reg_name(param_storage.register_name or "")
        )

    return (
        expr_storage.space_name == param_storage.space_name
        and expr_storage.offset == param_storage.offset
        and expr_storage.size == param_storage.size
    )


def _constant_factor(expr: Expression) -> Optional[int]:
    value = _evaluate_constant_expression(expr)
    if value is None:
        return None
    return int(value)


def _concat(left: Expression, right: Expression) -> Expression:
    result = Expression.binary_op("PIECE", left, right)
    result.size = (left.size or 0) + (right.size or 0)
    return result


def _has_overlapping_guards(matched: Sequence[Tuple[int, List[Condition], Expression]]) -> bool:
    for i in range(len(matched)):
        for j in range(i + 1, len(matched)):
            residual_i = list(matched[i][1])
            residual_j = list(matched[j][1])
            if not residual_i or not residual_j:
                return True
            if not ConditionSimplifier.is_contradiction(residual_i + residual_j):
                return True
    return False


def _all_residual_guards_empty(matched: Sequence[Tuple[int, List[Condition], Expression]]) -> bool:
    return all(not list(residual) for _order, residual, _value in matched)


def _get_order_key(op) -> int:
    seq = op.getSeqnum()
    if seq is None:
        return 0
    target = seq.getTarget()
    return (target.getOffset() << 8) | seq.getOrder()
