"""Stateless effect-summary implementations."""

from __future__ import annotations

from typing import Any, Callable, Dict, FrozenSet, Iterable, List, Optional, Sequence, Set, Tuple
from scripts.function_tracer_pcode.core import (
    CallTargetRef,
    CanonicalLocation,
    Condition,
    Expression,
    PcodeBlockRef,
    PcodeOpRef,
    expression_provenance_key,
)
from scripts.function_tracer_pcode.analysis.effects._shared import (
    CallArgumentEvidence,
    CallSiteEffectSummaryEvidence,
    CallTargetResolutionEvidence,
    ConditionSimplifier,
    EffectSummary,
    StoreEffect,
    StoreEffectProvenance,
    UnsupportedCallEffectRef,
    _EFFECT_ORDER_UNAVAILABLE_REASON,
)
from scripts.function_tracer_pcode.analysis.effects._api import (
    _block_has_path_incomplete_effects,
    _build_parameter_replacements,
    _call_argument_recovery_status,
    _call_arguments_may_expose_parameter_memory,
    _call_arguments_width_safe_for_effect_summary,
    _call_op_requires_path_covered_effect_summary,
    _choose_effect_substitution_args,
    _collect_named_parameter_names,
    _concat,
    _condition_evidence_key,
    _effect_summary_incomplete_reasons,
    _enumerate_call_argument_variants,
    _expression_is_call_scope_safe,
    _expression_matches_value_under_conditions,
    _expression_reads_location,
    _find_matching_effect_value,
    _infer_call_argument_sources,
    _location_sort_key,
    _normalize_call_argument_expression,
    _parameter_refs_from_descriptors,
    _path_coverage_for_effect_block,
    _record_call_argument_evidence,
    _recover_call_argument_expressions,
    _reduce_conditions_under_context,
    _reduce_expression_under_conditions,
    _resolve_call_argument_expression,
    _resolve_call_target_expression,
    _resolve_call_target_ref,
    _resolve_call_targets_for_effect_summary,
    _resolve_direct_call_value_effects,
    _resolve_object_centric_store_value_effects,
    _resolve_store_value_effects,
    _runtime_conditions_signature,
    _runtime_expression_signature,
    _strongly_connected_components,
    _try_get_order_key,
    build_void_effect_summary_expr,
    canonicalize_param_location,
    is_call_effect_summary_allowed,
    locations_match,
    substitute_condition,
    substitute_expression,
    substitute_location,
    subtract_implied_conditions,
)

def _impl_summarize_store_effects(
    block_infos: Iterable,
    tracer,
    condition_tracker,
    parameters: Sequence[Dict],
    direct_call_summary: Optional[Callable[[CallTargetRef, Sequence[Expression]], Optional["EffectSummary"]]] = None,
    direct_call_expander: Optional[Callable[[CallTargetRef, Sequence[Expression]], Optional[Sequence[object]]]] = None,
    resolve_callee_parameters: Optional[Callable[[CallTargetRef], Sequence[Dict]]] = None,
    read_memory_value: Optional[Callable[[int, int], Optional[int]]] = None,
    image_base: Optional[int] = None,
    debug: bool = False,
) -> EffectSummary:
    parameter_names = _collect_named_parameter_names(parameters)
    effects: List[StoreEffect] = []
    has_unsupported_call = False
    incomplete_reasons: Set[str] = set()
    call_argument_evidence: Dict[Tuple[object, ...], CallArgumentEvidence] = {}
    unsupported_call_sites: List[UnsupportedCallEffectRef] = []
    call_target_resolution_evidence: List[CallTargetResolutionEvidence] = []
    call_site_effect_summary_evidence: List[CallSiteEffectSummaryEvidence] = []

    def _pcode_ref_for_op(op) -> Optional[PcodeOpRef]:
        make_pcode_op_ref = getattr(tracer, "_make_pcode_op_ref", None)
        if callable(make_pcode_op_ref):
            try:
                return make_pcode_op_ref(op)
            except Exception:
                return None
        return PcodeOpRef.from_pcode_op(op)

    def _pcode_block_ref_for_block_info(block_info) -> Optional[PcodeBlockRef]:
        block = getattr(block_info, "block", None)
        if block is None:
            return None
        try:
            block_index = int(block.getIndex())
        except Exception:
            block_index = None
        try:
            start = block.getStart()
            start_offset = int(start.getOffset()) if start is not None else None
        except Exception:
            start_offset = None
        if block_index is None and start_offset is None:
            return None
        return PcodeBlockRef(
            block_index=block_index,
            start_address_offset=start_offset,
            binary_id=getattr(tracer, "_function_binary_id", None),
            function_entry_space=getattr(tracer, "_function_entry_space", None),
            function_entry_offset=getattr(tracer, "_function_entry_offset", None),
        )

    def _record_call_effect_summary_evidence(
        op,
        *,
        target_ref: Optional[CallTargetRef],
        arguments: Sequence[Expression],
        path_conditions: Sequence[Condition],
        summary_status: str,
        callee_summary: Optional["EffectSummary"] = None,
        incomplete_reasons: Sequence[str] = (),
        return_expansions: Optional[Sequence[object]] = None,
    ) -> None:
        callee_profile = (
            callee_summary.function_control_effect_profile
            if callee_summary is not None
            else None
        )
        expansion_values: List[Tuple[object, ...]] = []
        expansion_guards: List[Tuple[object, ...]] = []
        expansion_partitions: List[Tuple[Tuple[Condition, ...], Expression]] = []
        for expansion in return_expansions or ():
            expansion_value = getattr(expansion, "value", None)
            expansion_conditions = tuple(
                condition
                for condition in getattr(expansion, "conditions", ()) or ()
                if isinstance(condition, Condition)
            )
            value_key = (
                expression_provenance_key(expansion_value)
                if isinstance(expansion_value, Expression)
                else None
            )
            if isinstance(value_key, tuple):
                expansion_values.append(value_key)
                expansion_partitions.append(
                    (expansion_conditions, expansion_value)
                )
            expansion_guards.extend(
                _condition_evidence_key(condition)
                for condition in getattr(expansion, "conditions", ()) or ()
            )
        call_site_effect_summary_evidence.append(
            CallSiteEffectSummaryEvidence(
                pcode_op_ref=_pcode_ref_for_op(op),
                target_ref=target_ref,
                argument_keys=tuple(
                    expression_provenance_key(argument)
                    for argument in arguments or ()
                ),
                path_condition_keys=tuple(
                    _condition_evidence_key(condition)
                    for condition in path_conditions or ()
                ),
                summary_status=str(summary_status),
                memory_effect_count=len(getattr(callee_summary, "effects", ()) or ()),
                has_unsupported_nested_call=bool(
                    getattr(callee_summary, "has_unsupported_call", False)
                ),
                incomplete_reasons=tuple(str(reason) for reason in incomplete_reasons or ()),
                callee_control_profile_key=(
                    callee_profile.stable_key()
                    if callee_profile is not None
                    else None
                ),
                callee_ordered_scalar_store_candidate=bool(
                    callee_profile is not None
                    and callee_profile.phase3_ordered_scalar_store_candidate
                ),
                callee_cfg_edge_keys=tuple(
                    getattr(callee_profile, "region_cfg_edge_keys", ()) or ()
                ),
                callee_recursive_scc_proven=bool(
                    callee_profile is not None
                    and callee_profile.recursive_scc_proven
                ),
                callee_recursive_scc_identity=(
                    callee_profile.recursive_scc_identity
                    if callee_profile is not None
                    else None
                ),
                callee_recursive_scc_member_keys=(
                    callee_profile.recursive_scc_member_keys
                    if callee_profile is not None
                    else ()
                ),
                return_summary_status=(
                    "complete"
                    if expansion_values
                    and bool(getattr(return_expansions, "coverage_complete", False))
                    else "candidate" if expansion_values else "unavailable"
                ),
                return_semantic_bit_width=(
                    int(getattr(return_expansions, "return_semantic_bit_width"))
                    if getattr(return_expansions, "return_semantic_bit_width", None)
                    else None
                ),
                return_signed=(
                    bool(getattr(return_expansions, "return_signed"))
                    if getattr(return_expansions, "return_signed", None) is not None
                    else None
                ),
                return_value_keys=tuple(expansion_values),
                return_guard_keys=tuple(expansion_guards),
                return_partitions=tuple(expansion_partitions),
                memory_effects=tuple(getattr(callee_summary, "effects", ()) or ()),
            )
        )

    def _unsupported_call_effect_ref(
        op,
        *,
        target_ref: Optional[CallTargetRef],
        target_expr: Optional[Expression],
        arguments: Sequence[Expression] = (),
        path_conditions: Sequence[Condition] = (),
        reason: str,
    ) -> UnsupportedCallEffectRef:
        pcode_op_ref = _pcode_ref_for_op(op)
        return UnsupportedCallEffectRef.from_call_op(
            op,
            target_ref=target_ref,
            target_expr=target_expr,
            arguments=arguments,
            path_conditions=path_conditions,
            reason=reason,
            pcode_op_ref=pcode_op_ref,
        )

    for block_info in block_infos:
        producer_block_ref = _pcode_block_ref_for_block_info(block_info)
        coverage_status, path_sets = _path_coverage_for_effect_block(condition_tracker, block_info)
        if coverage_status == "complete_unreachable":
            continue
        if coverage_status != "complete" or not path_sets:
            if _block_has_path_incomplete_effects(
                block_info,
                tracer,
                parameters,
                direct_call_summary,
                resolve_callee_parameters,
            ):
                has_unsupported_call = True
                incomplete_reasons.add("effect_summary_path_coverage_incomplete")
                if debug:
                    print(
                        "[EffectSummary] skip effect-sensitive block: "
                        "path coverage unavailable"
                    )
            continue

        for op in block_info.pcode_ops:
            mnemonic = op.getMnemonic()
            op_order_key = _try_get_order_key(op)
            if op_order_key is None and mnemonic in {"STORE", "CALL", "CALLIND"}:
                incomplete_reasons.add(_EFFECT_ORDER_UNAVAILABLE_REASON)
                if mnemonic in {"CALL", "CALLIND"}:
                    has_unsupported_call = True
                if debug:
                    print(
                        "[EffectSummary] skip order-sensitive op: "
                        f"mnemonic={mnemonic} order unavailable"
                    )
                continue

            if mnemonic == "STORE" and op.getNumInputs() >= 3:
                addr_expr = tracer.trace_varnode(op.getInput(1), use_cache=False)
                location = canonicalize_param_location(addr_expr, parameters, size=op.getInput(2).getSize())
                if location is None:
                    continue
                value_effects = _resolve_store_value_effects(
                    op,
                    tracer,
                    condition_tracker,
                    parameters,
                    direct_call_expander=direct_call_expander,
                    resolve_callee_parameters=resolve_callee_parameters,
                    read_memory_value=read_memory_value,
                    image_base=image_base,
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
                                order_key=op_order_key,
                                provenance=StoreEffectProvenance(
                                    source_kind="local_store",
                                    producer_pcode_op_ref=_pcode_ref_for_op(op),
                                    producer_block_ref=producer_block_ref,
                                ),
                            )
                        )
                continue

            if mnemonic not in {"CALL", "CALLIND"} or direct_call_summary is None or op.getNumInputs() < 1:
                continue

            explicit_args = [
                _normalize_call_argument_expression(
                    _resolve_call_argument_expression(op.getInput(i), tracer, parameters),
                    i - 1,
                    parameters,
                )
                for i in range(1, op.getNumInputs())
            ]
            target_expr = _resolve_call_target_expression(tracer, op)
            if debug:
                explicit_dump = ", ".join(arg.to_string() for arg in explicit_args)
            for path_conditions in path_sets:
                normalized_path_conditions = ConditionSimplifier.simplify_conditions(list(path_conditions))
                resolved_targets = _resolve_call_targets_for_effect_summary(
                    tracer,
                    op,
                    normalized_path_conditions,
                    parameters,
                    read_memory_value=read_memory_value,
                    image_base=image_base,
                    debug=debug,
                )
                if not resolved_targets:
                    has_unsupported_call = True
                    unsupported_call_sites.append(
                        _unsupported_call_effect_ref(
                            op,
                            target_ref=None,
                            target_expr=target_expr,
                            arguments=explicit_args,
                            path_conditions=normalized_path_conditions,
                            reason="target_identity_unavailable",
                        )
                    )
                    if debug:
                        print(
                            "[EffectSummary] skip unresolved call effect summary: "
                            "target identity is unavailable"
                        )
                    continue
                processed_target_for_path = False
                for target_ref, target_conditions, resolution_kind in resolved_targets:
                    if resolution_kind == "pathless_target_resolution":
                        call_target_resolution_evidence.append(
                            CallTargetResolutionEvidence.from_call_op(
                                op,
                                target_ref=target_ref,
                                target_expr=target_expr,
                                resolution_kind=resolution_kind,
                                path_conditions=normalized_path_conditions,
                                target_conditions=target_conditions,
                            )
                        )
                    if target_ref is None or target_ref.is_unknown():
                        has_unsupported_call = True
                        unsupported_call_sites.append(
                            _unsupported_call_effect_ref(
                                op,
                            target_ref=target_ref,
                            target_expr=target_expr,
                            arguments=explicit_args,
                            path_conditions=ConditionSimplifier.simplify_conditions(
                                list(normalized_path_conditions) + list(target_conditions or ())
                            ),
                            reason="target_identity_unavailable",
                        )
                    )
                        continue
                    normalized_target_conditions = ConditionSimplifier.simplify_conditions(
                        list(target_conditions or ())
                    )
                    call_path_conditions = ConditionSimplifier.simplify_conditions(
                        list(normalized_path_conditions) + list(normalized_target_conditions)
                    )
                    if ConditionSimplifier.is_contradiction(call_path_conditions):
                        continue
                    processed_target_for_path = True
                    target_label = target_ref.display_name()
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
                        condition_tracker=condition_tracker,
                        current_conditions=call_path_conditions,
                    )
                    argument_recovery_status = _call_argument_recovery_status(
                        callee_parameters,
                        args,
                    )
                    argument_coverage_complete = (
                        argument_recovery_status == CallArgumentEvidence.RECOVERY_COMPLETE
                    )
                    _record_call_argument_evidence(
                        call_argument_evidence,
                        tracer,
                        op,
                        target_ref,
                        callee_parameters,
                        args,
                        call_path_conditions,
                        coverage_complete=argument_coverage_complete,
                        sources=_infer_call_argument_sources(args, explicit_args),
                        reason=(
                            None
                            if argument_coverage_complete
                            else (
                                "argument_recovery_recoverable_partial"
                                if argument_recovery_status == CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL
                                else "argument_recovery_incomplete"
                            )
                        ),
                        recovery_status=argument_recovery_status,
                    )
                    if debug:
                        recovered_dump = ", ".join(arg.to_string() for arg in args)
                        print(
                            "[EffectSummary] call arguments: "
                            f"target={target_label} explicit=[{explicit_dump}] "
                            f"path=[{', '.join(cond.to_string() for cond in call_path_conditions)}] "
                            f"recovered=[{recovered_dump}]"
                        )
                    if callee_parameters and not argument_coverage_complete:
                        if argument_recovery_status != CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL:
                            has_unsupported_call = True
                            if debug:
                                print(
                                    "[EffectSummary] skip call effect summary: "
                                    f"target={target_label} recovered_args={len(args)} "
                                    f"callee_params={len(callee_parameters)}"
                                )
                            continue
                        if debug:
                            print(
                                "[EffectSummary] continue with recoverable partial call arguments: "
                                f"target={target_label} recovered_args={len(args)} "
                                f"callee_params={len(callee_parameters)}"
                            )
                    path_reduced_args = [
                        _reduce_expression_under_conditions(arg, call_path_conditions)
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
                            list(call_path_conditions) + list(variant_conditions)
                        )
                        callee_summary = direct_call_summary(target_ref, variant_args)
                        if callee_summary is None:
                            _record_call_effect_summary_evidence(
                                op,
                                target_ref=target_ref,
                                arguments=variant_args,
                                path_conditions=active_conditions,
                                summary_status="missing",
                                incomplete_reasons=("callee_effect_summary_missing",),
                            )
                            has_unsupported_call = True
                            unsupported_call_sites.append(
                                _unsupported_call_effect_ref(
                                    op,
                                    target_ref=target_ref,
                                    target_expr=target_expr,
                                    arguments=variant_args,
                                    path_conditions=active_conditions,
                                    reason="callee_effect_summary_missing",
                                )
                            )
                            if debug:
                                print(
                                    "[EffectSummary] missing callee effect summary: "
                                    f"target={target_label}"
                                )
                            continue
                        if not _call_arguments_width_safe_for_effect_summary(
                            callee_summary,
                            callee_parameters,
                            variant_args,
                        ):
                            has_unsupported_call = True
                            unsupported_call_sites.append(
                                _unsupported_call_effect_ref(
                                    op,
                                    target_ref=target_ref,
                                    target_expr=target_expr,
                                    arguments=variant_args,
                                    path_conditions=active_conditions,
                                    reason="call_argument_width_unsafe_for_effect_summary",
                                )
                            )
                            if debug:
                                print(
                                    "[EffectSummary] skip call effect summary: "
                                    f"target={target_label} partial-width argument has full-width effect use"
                                )
                            continue
                        callee_incomplete_reasons = _effect_summary_incomplete_reasons(callee_summary)
                        return_expansions = None
                        if direct_call_expander is not None:
                            try:
                                return_expansions = direct_call_expander(
                                    target_ref,
                                    variant_args,
                                )
                            except Exception:
                                return_expansions = None
                        summary_complete = not callee_incomplete_reasons and not bool(
                            callee_summary.has_unsupported_call
                        )
                        _record_call_effect_summary_evidence(
                            op,
                            target_ref=target_ref,
                            arguments=variant_args,
                            path_conditions=active_conditions,
                            summary_status="complete" if summary_complete else "incomplete",
                            callee_summary=callee_summary,
                            incomplete_reasons=callee_incomplete_reasons,
                            return_expansions=return_expansions,
                        )
                        if callee_incomplete_reasons:
                            has_unsupported_call = True
                            unsupported_call_sites.append(
                                _unsupported_call_effect_ref(
                                    op,
                                    target_ref=target_ref,
                                    target_expr=target_expr,
                                    arguments=variant_args,
                                    path_conditions=active_conditions,
                                    reason="callee_effect_summary_incomplete",
                                )
                            )
                            if debug:
                                print(
                                    "[EffectSummary] skip incomplete callee effect summary: "
                                    f"target={target_label} reasons={callee_incomplete_reasons}"
                                )
                            continue
                        if not callee_summary.effects:
                            if callee_summary.has_unsupported_call:
                                if _call_arguments_may_expose_parameter_memory(
                                    variant_args,
                                    parameters,
                                    callee_parameters,
                                ):
                                    has_unsupported_call = True
                                    unsupported_call_sites.append(
                                        _unsupported_call_effect_ref(
                                            op,
                                            target_ref=target_ref,
                                            target_expr=target_expr,
                                            arguments=variant_args,
                                            path_conditions=active_conditions,
                                            reason="callee_unsupported_call_may_expose_parameter_memory",
                                        )
                                    )
                                elif debug:
                                    print(
                                        "[EffectSummary] effect-free callee summary has only "
                                        "parameter-memory-insensitive unsupported calls: "
                                        f"target={target_label}"
                                    )
                            elif debug:
                                print(
                                    "[EffectSummary] effect-free callee summary: "
                                    f"target={target_label}"
                                )
                            continue
                        if not is_call_effect_summary_allowed(callee_summary):
                            has_unsupported_call = True
                            unsupported_call_sites.append(
                                _unsupported_call_effect_ref(
                                    op,
                                    target_ref=target_ref,
                                    target_expr=target_expr,
                                    arguments=variant_args,
                                    path_conditions=active_conditions,
                                    reason="callee_effect_summary_not_allowed",
                                )
                            )
                            continue

                        for callee_effect_index, effect in enumerate(callee_summary.effects):
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
                                has_unsupported_call = True
                                unsupported_call_sites.append(
                                    _unsupported_call_effect_ref(
                                        op,
                                        target_ref=target_ref,
                                        target_expr=target_expr,
                                        arguments=variant_args,
                                        path_conditions=active_conditions,
                                        reason="substituted_effect_location_unavailable",
                                    )
                                )
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
                                    order_key=op_order_key,
                                    provenance=StoreEffectProvenance(
                                        source_kind="call_derived",
                                        producer_pcode_op_ref=_pcode_ref_for_op(op),
                                        producer_block_ref=producer_block_ref,
                                        call_target_ref=target_ref,
                                        callee_effect_index=callee_effect_index,
                                        nested_effect_provenance=effect.provenance,
                                    ),
                                )
                            )
                if not processed_target_for_path:
                    has_unsupported_call = True
                    unsupported_call_sites.append(
                        _unsupported_call_effect_ref(
                            op,
                            target_ref=None,
                            target_expr=target_expr,
                            arguments=explicit_args,
                            path_conditions=normalized_path_conditions,
                            reason="target_identity_unavailable",
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
        incomplete_reasons=tuple(sorted(incomplete_reasons)),
        parameter_refs=_parameter_refs_from_descriptors(parameters),
        call_argument_evidence=dict(call_argument_evidence),
        unsupported_call_sites=tuple(unsupported_call_sites),
        call_target_resolution_evidence=tuple(call_target_resolution_evidence),
        call_site_effect_summary_evidence=tuple(call_site_effect_summary_evidence),
    )

def _impl__block_has_effect_sensitive_ops(block_info) -> bool:
    for op in getattr(block_info, "pcode_ops", []) or ():
        try:
            mnemonic = str(op.getMnemonic()).upper()
        except Exception:
            continue
        if mnemonic in {"STORE", "CALL", "CALLIND"}:
            return True
    return False

def _impl__path_coverage_for_effect_block(condition_tracker, block_info) -> Tuple[str, List[List[Condition]]]:
    coverage_fn = getattr(condition_tracker, "get_path_coverage_to_block", None)
    if callable(coverage_fn):
        try:
            coverage = coverage_fn(block_info)
        except Exception:
            return "inconclusive", []
        status = str(getattr(coverage, "status", "") or "")
        condition_paths = getattr(coverage, "condition_paths", None)
        if condition_paths is None:
            condition_paths = getattr(coverage, "paths", None)
        if condition_paths is None:
            condition_paths = []
        return status if status in {"complete", "complete_unreachable", "inconclusive"} else "inconclusive", list(condition_paths or [])

    try:
        path_sets = condition_tracker.get_all_valid_paths_to_block(block_info)
    except Exception:
        return "inconclusive", []
    return ("complete", list(path_sets or [])) if path_sets else ("inconclusive", [])

def _impl__block_has_path_incomplete_effects(
    block_info,
    tracer,
    parameters: Sequence[Dict],
    direct_call_summary: Optional[Callable[[CallTargetRef, Sequence[Expression]], Optional["EffectSummary"]]],
    resolve_callee_parameters: Optional[Callable[[CallTargetRef], Sequence[Dict]]],
) -> bool:
    for op in getattr(block_info, "pcode_ops", []) or ():
        try:
            mnemonic = str(op.getMnemonic()).upper()
        except Exception:
            continue
        if mnemonic == "STORE":
            return True
        if mnemonic in {"CALL", "CALLIND"} and _call_op_requires_path_covered_effect_summary(
            op,
            tracer,
            parameters,
            direct_call_summary,
            resolve_callee_parameters,
        ):
            return True
    return False

def _impl__call_op_requires_path_covered_effect_summary(
    op,
    tracer,
    parameters: Sequence[Dict],
    direct_call_summary: Optional[Callable[[CallTargetRef, Sequence[Expression]], Optional["EffectSummary"]]],
    resolve_callee_parameters: Optional[Callable[[CallTargetRef], Sequence[Dict]]],
) -> bool:
    if direct_call_summary is None:
        return True
    try:
        if op.getNumInputs() < 1:
            return True
        explicit_args = [
            _normalize_call_argument_expression(
                _resolve_call_argument_expression(op.getInput(i), tracer, parameters),
                i - 1,
                parameters,
            )
            for i in range(1, op.getNumInputs())
        ]
        target_ref = _resolve_call_target_ref(tracer, op)
        if target_ref is None:
            return True
        callee_parameters = (
            list(resolve_callee_parameters(target_ref) or [])
            if resolve_callee_parameters
            else []
        )
        if callee_parameters and len(explicit_args) < len(callee_parameters):
            return True
        callee_summary = direct_call_summary(target_ref, explicit_args)
        if callee_summary is None:
            return True
        if getattr(callee_summary, "has_unsupported_call", False):
            return _call_arguments_may_expose_parameter_memory(
                explicit_args,
                parameters,
                callee_parameters,
            )
        incomplete_reasons = getattr(callee_summary, "incomplete_reasons", ())
        if isinstance(incomplete_reasons, (list, tuple, set, frozenset)) and incomplete_reasons:
            return True
        return bool(getattr(callee_summary, "effects", None))
    except Exception:
        return True

def _impl__resolve_store_value_effects(
    store_op,
    tracer,
    condition_tracker,
    parameters: Sequence[Dict],
    *,
    direct_call_expander: Optional[Callable[[CallTargetRef, Sequence[Expression]], Optional[Sequence[object]]]] = None,
    resolve_callee_parameters: Optional[Callable[[CallTargetRef], Sequence[Dict]]] = None,
    read_memory_value: Optional[Callable[[int, int], Optional[int]]] = None,
    image_base: Optional[int] = None,
) -> List[Tuple[Expression, List[Condition]]]:
    value_varnode = store_op.getInput(2)
    object_centric = _resolve_object_centric_store_value_effects(
        value_varnode,
        tracer,
        condition_tracker,
        parameters,
        direct_call_expander=direct_call_expander,
        resolve_callee_parameters=resolve_callee_parameters,
        read_memory_value=read_memory_value,
        image_base=image_base,
    )
    if object_centric:
        return object_centric
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

def _impl__resolve_object_centric_store_value_effects(
    value_varnode,
    tracer,
    condition_tracker,
    parameters: Sequence[Dict],
    *,
    direct_call_expander: Optional[Callable[[CallTargetRef, Sequence[Expression]], Optional[Sequence[object]]]] = None,
    resolve_callee_parameters: Optional[Callable[[CallTargetRef], Sequence[Dict]]] = None,
    read_memory_value: Optional[Callable[[int, int], Optional[int]]] = None,
    image_base: Optional[int] = None,
) -> List[Tuple[Expression, List[Condition]]]:
    if value_varnode is None or condition_tracker is None:
        return []

    from scripts.function_tracer_pcode.semantics.transform.expander import ExpressionExpander

    expander = ExpressionExpander(
        tracer,
        condition_tracker,
        debug=False,
        call_resolver=direct_call_expander,
        parameters=list(parameters or []),
        resolve_callee_parameters=resolve_callee_parameters,
        read_memory_value=read_memory_value,
        image_base=image_base,
        record_deferred_call=getattr(tracer, "record_deferred_call", None),
    )

    try:
        expanded = expander.expand_from_varnode(value_varnode, [])
    except Exception:
        return []

    resolved: List[Tuple[Expression, List[Condition]]] = []
    seen = set()
    for item in expanded or []:
        value = getattr(item, "value", None)
        conditions = getattr(item, "conditions", None)
        if not isinstance(value, Expression):
            continue
        normalized_conditions = ConditionSimplifier.simplify_conditions(list(conditions or []))
        if ConditionSimplifier.is_contradiction(normalized_conditions):
            continue
        reduced_value = _reduce_expression_under_conditions(value, normalized_conditions)
        normalized_value = reduced_value if reduced_value is not None else value
        key = (
            _runtime_expression_signature(normalized_value),
            _runtime_conditions_signature(normalized_conditions),
        )
        if key in seen:
            continue
        seen.add(key)
        resolved.append((normalized_value, normalized_conditions))
    return resolved

def _impl__resolve_direct_call_value_effects(
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

def _impl__choose_effect_substitution_args(
    location: CanonicalLocation,
    callee_params: Sequence[object],
    args: Sequence[Expression],
    caller_parameters: Sequence[Dict],
) -> Sequence[Expression]:
    direct_location = substitute_location(location, callee_params, args, caller_parameters)
    if direct_location is not None:
        return args
    return args

def _impl_is_call_effect_summary_allowed(summary: EffectSummary) -> bool:
    if summary is None:
        return False
    if summary.has_unsupported_call:
        return False
    if _effect_summary_incomplete_reasons(summary):
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

def _impl__effect_summary_incomplete_reasons(summary: Optional[EffectSummary]) -> Tuple[str, ...]:
    reasons = getattr(summary, "incomplete_reasons", ()) if summary is not None else ()
    if isinstance(reasons, (list, tuple, set, frozenset)):
        return tuple(str(reason) for reason in reasons if reason)
    return (str(reasons),) if reasons else ()

def _impl__matches_existing_effect_value(
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

def _impl__find_matching_effect_value(
    expr: Expression,
    location: CanonicalLocation,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    max_order_key: Optional[int] = None,
) -> Optional[Tuple[int, Expression]]:
    normalized_return_conditions = ConditionSimplifier.simplify_conditions_object_centric(list(return_conditions))
    for effect in effects:
        normalized_effect_conditions = ConditionSimplifier.simplify_conditions_object_centric(list(effect.conditions))
        if max_order_key is not None and effect.order_key >= max_order_key:
            continue
        combined_conditions = ConditionSimplifier.simplify_conditions_object_centric(
            normalized_return_conditions + normalized_effect_conditions
        )
        if ConditionSimplifier.object_centric_is_contradiction(combined_conditions):
            continue
        if not locations_match(location, effect.location, combined_conditions):
            continue
        if not _expression_reads_location(expr, location, combined_conditions, parameters):
            continue
        if _expression_matches_value_under_conditions(
            expr,
            effect.value,
            combined_conditions,
            parameters,
        ):
            return effect.order_key, effect.value
    return None

def _impl__compute_effect_cycle_components(
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

def _impl_build_void_effect_summary_expr(effects: Sequence[StoreEffect]) -> Optional[Expression]:
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

def _impl__collect_definite_active_effects(
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
) -> List[StoreEffect]:
    normalized_return_conditions = ConditionSimplifier.simplify_conditions_object_centric(
        list(return_conditions)
    )
    active_effects: List[StoreEffect] = []
    for effect in effects:
        normalized_effect_conditions = ConditionSimplifier.simplify_conditions_object_centric(
            list(effect.conditions)
        )
        if ConditionSimplifier.object_centric_is_contradiction(
            normalized_return_conditions + normalized_effect_conditions
        ):
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
                provenance=effect.provenance,
            )
        )
    return active_effects
