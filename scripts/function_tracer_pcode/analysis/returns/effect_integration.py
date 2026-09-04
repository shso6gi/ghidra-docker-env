"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.returns.analyzer``."""

from __future__ import annotations

from dataclasses import replace
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple
from scripts.function_tracer_pcode.analysis.returns._shared import (
    ComparisonSurface,
    CallTargetRef,
    Condition,
    ConditionSimplifier,
    EffectSummary,
    Expression,
    ExpressionType,
    FunctionControlEffectProfile,
    PcodeBlockRef,
    PcodeOpRef,
    PcodeTracer,
    PostStateValueRef,
    ReturnInfo,
    StructuralKey,
    _EffectRewritePrecision,
    _FUNCTION_PROFILE_RECOGNIZED_PCODE_MNEMONICS,
    _PHASE2_MEMORY_FREE_SCALAR_PCODE_MNEMONICS,
    _TrackedReturnValue,
    _expression_contains_observed_loads,
    _expression_reads_location,
    _expressions_equivalent,
    _expressions_equivalent_under_conditions,
    _find_matching_effect_value,
    _find_unique_effect_location_for_value,
    _iter_expression_nodes,
    _materialize_existing_effect_value_carrier,
    _replay_definite_active_effects_for_location,
    _strip_materialized_post_state_value_refs,
    canonicalize_expr_read_location,
    concretize_readonly_loads,
    expression_contains_post_state_reads,
    expression_matches_stale_post_state_replay,
    lower_post_state_expression_for_smt,
    materialize_definite_post_state_expression,
    normalize_post_state_expression,
    promote_effect_value_carrier_to_post_state_read,
    promote_effect_value_match_to_post_state_read,
    promote_observed_loads_to_post_state_reads,
    resolve_definite_post_state_read_for_location,
    rewrite_loads_from_effects,
    rewrite_observed_loads_from_effects,
    summarize_store_effects,
)
from scripts.function_tracer_pcode.analysis.returns._api import ConditionTracker

def _impl__effect_summary_allows_pre_return_structural_summary(
    self,
    effect_summary: Optional[EffectSummary],
    *,
    function=None,
    high_function=None,
    return_type: Optional[str] = None,
    return_type_obj=None,
) -> bool:
    if effect_summary is None:
        return False
    if self._phase1_return_type_is_float(return_type, return_type_obj):
        self._debug_print("Declined pre-return counted loop summary: Phase 1 excludes FP return types")
        return False
    if self._function_body_has_phase1_pure_return_forbidden_ops(function):
        self._debug_print(
            "Declined pre-return counted loop summary: function body is not Phase 1 pure/no-memory"
        )
        return False
    if self._high_function_has_phase1_pure_return_forbidden_ops(high_function):
        self._debug_print(
            "Declined pre-return counted loop summary: HighFunction-visible body is not Phase 1 pure/no-memory"
        )
        return False
    if getattr(effect_summary, "effects", None):
        self._debug_print("Declined pre-return counted loop summary: effect summary contains memory writes")
        return False
    if getattr(effect_summary, "has_unsupported_call", False):
        self._debug_print("Declined pre-return counted loop summary: effect summary contains unsupported call")
        return False
    return True

def _impl__build_function_control_effect_profile(
    self,
    high_function,
    function=None,
    parameters: Optional[Sequence[Dict[str, Any]]] = None,
) -> FunctionControlEffectProfile:
    """Conservatively census CFG/P-code for direct-call eligibility."""

    function_identity_key = None
    if function is not None:
        try:
            function_identity_key = CallTargetRef.from_function(function).stable_key()
        except Exception:
            function_identity_key = None

    blocks, blocks_complete = self._collect_java_or_python_iterable(
        getattr(high_function, "getBasicBlocks", lambda: None)()
        if high_function is not None
        and callable(getattr(high_function, "getBasicBlocks", None))
        else None
    )
    adjacency: Dict[int, Tuple[int, ...]] = {}
    block_keys_by_index: Dict[int, Tuple[object, ...]] = {}
    block_refs_by_index: Dict[int, PcodeBlockRef] = {}
    terminal_return_indices: Set[int] = set()
    pcode_complete = bool(blocks_complete)
    edges_complete = bool(blocks_complete)
    terminal_coverage_complete = bool(blocks_complete and blocks)
    pcode_op_count = 0
    return_block_count = 0
    counts = {
        "LOAD": 0,
        "STORE": 0,
        "CALL": 0,
        "CALLIND": 0,
        "CALLOTHER": 0,
        "BRANCHIND": 0,
    }
    float_op_count = 0
    pcode_after_return_count = 0
    abnormal_terminal_block_count = 0
    call_like_pcode_op_keys: List[Tuple[object, ...]] = []
    call_like_identity_complete = bool(blocks_complete)
    direct_call_target_keys: List[Tuple[object, ...]] = []
    call_graph_edges_complete = bool(blocks_complete and function_identity_key is not None)
    phase2_unsafe: Set[str] = set()
    region_pcode_op_keys: List[Tuple[object, ...]] = []
    region_live_in_keys: Set[Tuple[object, ...]] = set()
    region_live_out_keys: Set[Tuple[object, ...]] = set()
    region_identity_complete = bool(blocks_complete and function_identity_key is not None)
    unsupported: Set[str] = set()
    function_entry_address = None
    if function is not None:
        try:
            function_entry_address = function.getEntryPoint()
        except Exception:
            function_entry_address = None
    if function_entry_address is None:
        function_entry_address = self._current_function_entry_address()
    try:
        function_entry_space = function_entry_address.getAddressSpace().getName()
        function_entry_offset = int(function_entry_address.getOffset())
    except Exception:
        function_entry_space = None
        function_entry_offset = None

    for ordinal, block in enumerate(blocks):
        try:
            block_index = int(block.getIndex())
        except Exception:
            block_index = ordinal
            edges_complete = False
        try:
            start = block.getStart()
            start_space = start.getAddressSpace().getName()
            start_offset = int(start.getOffset())
        except Exception:
            start_space = None
            start_offset = None
            region_identity_complete = False
        block_keys_by_index[block_index] = (
            "pcode_block",
            self._binary_id,
            function_identity_key,
            block_index,
            start_space,
            start_offset,
        )
        block_refs_by_index[block_index] = PcodeBlockRef(
            block_index=block_index,
            start_address_offset=start_offset,
            binary_id=self._binary_id,
            function_entry_space=function_entry_space,
            function_entry_offset=function_entry_offset,
        )
        successors: List[int] = []
        try:
            out_size = int(block.getOutSize())
        except Exception:
            out_size = 0
            edges_complete = False
        for out_index in range(max(0, out_size)):
            try:
                successors.append(int(block.getOut(out_index).getIndex()))
            except Exception:
                edges_complete = False
        adjacency[block_index] = tuple(successors)

        ops, complete = self._collect_java_or_python_iterable(
            getattr(block, "getIterator", lambda: None)()
        )
        pcode_complete = pcode_complete and complete
        saw_return = False
        if not complete:
            terminal_coverage_complete = False
        for local_ordinal, op in enumerate(ops):
            pcode_op_count += 1
            try:
                mnemonic = str(op.getMnemonic() or "").strip().upper()
            except Exception:
                mnemonic = ""
            region_ref = PcodeOpRef.from_pcode_op(
                op,
                binary_id=self._binary_id,
                program_uid=self._program_identity(),
                function_entry=self._current_function_entry_address(),
                local_op_ordinal=local_ordinal,
            )
            if region_ref is None:
                region_identity_complete = False
            else:
                region_pcode_op_keys.append(region_ref.stable_key())
            try:
                num_inputs = int(op.getNumInputs())
            except Exception:
                num_inputs = 0
                region_identity_complete = False
            for input_index in range(max(0, num_inputs)):
                try:
                    input_varnode = op.getInput(input_index)
                except Exception:
                    region_identity_complete = False
                    continue
                input_key, input_status = self._region_live_in_key(
                    input_varnode,
                    mnemonic=mnemonic,
                    input_index=input_index,
                    parameters=parameters or (),
                )
                if input_status == "incomplete":
                    region_identity_complete = False
                elif input_key is not None:
                    region_live_in_keys.add(tuple(input_key))
            if not mnemonic:
                unsupported.add("<missing_mnemonic>")
                continue
            if mnemonic not in _FUNCTION_PROFILE_RECOGNIZED_PCODE_MNEMONICS:
                unsupported.add(mnemonic)
            elif mnemonic not in _PHASE2_MEMORY_FREE_SCALAR_PCODE_MNEMONICS:
                phase2_unsafe.add(mnemonic)
            if mnemonic in counts:
                counts[mnemonic] += 1
            if saw_return:
                pcode_after_return_count += 1
                unsupported.add(f"<op_after_return:{mnemonic}>")
            if mnemonic in {"CALL", "CALLIND", "CALLOTHER"}:
                ref = PcodeOpRef.from_pcode_op(
                    op,
                    binary_id=self._binary_id,
                    program_uid=self._program_identity(),
                    function_entry=self._current_function_entry_address(),
                    local_op_ordinal=local_ordinal,
                )
                if ref is None:
                    call_like_identity_complete = False
                else:
                    call_like_pcode_op_keys.append(ref.stable_key())
            if mnemonic == "CALL":
                target_key = self._direct_call_target_function_key(op)
                if target_key is None:
                    call_graph_edges_complete = False
                else:
                    direct_call_target_keys.append(target_key)
            elif mnemonic in {"CALLIND", "CALLOTHER"}:
                call_graph_edges_complete = False
            if "FLOAT" in mnemonic or mnemonic in {"INT2FLOAT", "FLOAT2INT"}:
                float_op_count += 1
            if mnemonic == "RETURN":
                saw_return = True
                for input_index in range(max(0, num_inputs)):
                    if self._region_input_is_nondata_operand(mnemonic, input_index):
                        continue
                    try:
                        return_input = op.getInput(input_index)
                        if bool(return_input.isConstant()):
                            continue
                        output_key = self._varnode_location_key(return_input)
                    except Exception:
                        output_key = None
                    if output_key is not None:
                        region_live_out_keys.add(
                            ("return_value", input_index - 1, tuple(output_key))
                        )
        if not successors:
            if saw_return:
                return_block_count += 1
                terminal_return_indices.add(block_index)
            else:
                terminal_coverage_complete = False
                abnormal_terminal_block_count += 1

    visiting: Set[int] = set()
    visited: Set[int] = set()

    def has_cycle(node: int) -> bool:
        if node in visiting:
            return True
        if node in visited:
            return False
        visiting.add(node)
        for successor in adjacency.get(node, ()):
            if successor not in adjacency:
                nonlocal_edges_complete[0] = False
                continue
            if has_cycle(successor):
                return True
        visiting.remove(node)
        visited.add(node)
        return False

    nonlocal_edges_complete = [edges_complete]
    cfg_acyclic = bool(blocks_complete)
    for node in adjacency:
        if has_cycle(node):
            cfg_acyclic = False
            break
    edges_complete = nonlocal_edges_complete[0]
    predecessor_counts = {index: 0 for index in adjacency}
    for successors in adjacency.values():
        for successor in successors:
            if successor in predecessor_counts:
                predecessor_counts[successor] += 1
    entry_indices = tuple(
        index for index, count in predecessor_counts.items() if count == 0
    )
    region_single_entry = len(entry_indices) == 1
    region_entry_block_key = (
        block_keys_by_index.get(entry_indices[0]) if region_single_entry else None
    )
    region_exit_block_keys = tuple(
        block_keys_by_index[index]
        for index in sorted(terminal_return_indices)
        if index in block_keys_by_index
    )
    region_identity_complete = bool(
        region_identity_complete
        and pcode_complete
        and edges_complete
        and len(block_keys_by_index) == len(blocks)
        and len(region_pcode_op_keys) == pcode_op_count
    )

    if function_identity_key is not None:
        self._direct_call_graph[function_identity_key] = set(direct_call_target_keys)
        if call_graph_edges_complete and pcode_complete:
            self._direct_call_graph_complete_nodes.add(function_identity_key)
        else:
            self._direct_call_graph_complete_nodes.discard(function_identity_key)
    recursive_scc_proven, recursive_scc_identity, recursive_scc_members = (
        self._recursive_scc_certificate(function_identity_key)
    )
    region_cfg_edge_keys = tuple(
        (
            block_refs_by_index[source].stable_key(),
            block_refs_by_index[target].stable_key(),
        )
        for source in sorted(adjacency)
        for target in sorted(adjacency[source])
        if source in block_refs_by_index and target in block_refs_by_index
    )

    return FunctionControlEffectProfile(
        block_count=len(blocks),
        pcode_op_count=pcode_op_count,
        return_block_count=return_block_count,
        pcode_enumeration_complete=pcode_complete,
        cfg_edges_complete=edges_complete,
        cfg_acyclic=cfg_acyclic,
        terminal_return_coverage_complete=terminal_coverage_complete,
        load_count=counts["LOAD"],
        store_count=counts["STORE"],
        call_count=counts["CALL"],
        callind_count=counts["CALLIND"],
        callother_count=counts["CALLOTHER"],
        branchind_count=counts["BRANCHIND"],
        float_op_count=float_op_count,
        pcode_after_return_count=pcode_after_return_count,
        abnormal_terminal_block_count=abnormal_terminal_block_count,
        call_like_pcode_op_keys=tuple(call_like_pcode_op_keys),
        call_like_identity_complete=(
            call_like_identity_complete and pcode_complete
        ),
        function_identity_key=function_identity_key,
        direct_call_target_keys=tuple(direct_call_target_keys),
        call_graph_edges_complete=(call_graph_edges_complete and pcode_complete),
        recursive_scc_proven=recursive_scc_proven,
        recursive_scc_identity=recursive_scc_identity,
        recursive_scc_member_keys=recursive_scc_members,
        phase2_unsafe_mnemonics=tuple(sorted(phase2_unsafe)),
        region_entry_block_key=region_entry_block_key,
        region_exit_block_keys=region_exit_block_keys,
        region_block_keys=tuple(
            block_keys_by_index[index] for index in sorted(block_keys_by_index)
        ),
        region_cfg_edge_keys=region_cfg_edge_keys,
        region_pcode_op_keys=tuple(region_pcode_op_keys),
        region_live_in_keys=tuple(sorted(region_live_in_keys, key=repr)),
        region_live_out_keys=tuple(sorted(region_live_out_keys, key=repr)),
        region_identity_complete=region_identity_complete,
        region_single_entry=region_single_entry,
        region_all_exits_enumerated=bool(
            edges_complete and terminal_coverage_complete
        ),
        region_cross_edges_enumerated=bool(edges_complete),
        unsupported_mnemonics=tuple(sorted(unsupported)),
    )

def _impl__extract_stack_protector_memory_probe(
    self,
    expr: Optional[Expression],
) -> Optional[Tuple[StructuralKey, int, int, int]]:
    if expr is None:
        return None

    current = expr
    while (
        current.expr_type == ExpressionType.UNARY_OP
        and current.operator in {"INT_ZEXT", "INT_SEXT"}
        and current.operands
    ):
        current = current.operands[0]

    if current.expr_type == ExpressionType.MEMORY and current.operands:
        probe = self._extract_indirect_probe(current.operands[0])
        if probe is None:
            return None
        base_key, displacement, deref_depth = probe
        return (base_key, displacement, deref_depth, int(current.size or 0))

    # Some architectures materialize the stack-protector spill as a direct
    # INDIRECT expression over an already-dereferenced guard pointer instead
    # of wrapping it in a MEMORY node. Preserve the same structured probe.
    probe = self._extract_indirect_probe(current)
    if probe is None:
        return None
    base_key, displacement, deref_depth = probe
    return (base_key, displacement, deref_depth, int(current.size or 0))

def _impl__make_empty_effect_summary(
    self,
    parameters: List[Dict],
) -> EffectSummary:
    parameter_names = [
        str(name)
        for param in (parameters or [])
        for name in [param.get("name")]
        if isinstance(name, str) and name
    ]
    return EffectSummary(parameter_names=parameter_names, effects=[])

def _impl__propagate_indirect_return_effect(
    self,
    tracked: _TrackedReturnValue,
    pcode_op,
    tracer: Optional[PcodeTracer],
) -> List[_TrackedReturnValue]:
    try:
        base_input = pcode_op.getInput(0)
    except Exception:
        return []

    # Ghidra の INDIRECT は input0 が 0 の場合、
    # 出力が「副作用 op によってのみ生成された値」であることを表す。
    # この場合は return storage 自体を追跡し続ける。
    if self._is_zero_constant_varnode(base_input):
        return [tracked]

    if base_input is None:
        return []
    return [self._make_tracked_return_value(base_input, tracer)]

def _impl__invoke_build_effect_summary(
    self,
    function,
    high_function,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    parameters: List[Dict],
    active_functions: Set[Tuple[Any, ...]],
    *,
    bound_parameter_values: Optional[Dict[int, Expression]] = None,
    bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]] = None,
):
    try:
        return self._build_effect_summary(
            function,
            high_function,
            tracer,
            condition_tracker,
            parameters,
            active_functions=active_functions,
            bound_parameter_values=bound_parameter_values,
            bound_parameter_storage_values=bound_parameter_storage_values,
        )
    except TypeError:
        return self._build_effect_summary(
            function,
            high_function,
            tracer,
            condition_tracker,
            parameters,
            active_functions=active_functions,
        )

def _impl__build_effect_summary(
    self,
    function,
    high_function,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    parameters: List[Dict],
    active_functions: Set[Tuple[Any, ...]],
    bound_parameter_values: Optional[Dict[int, Expression]] = None,
    bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]] = None,
):
    function_cache_key = self._function_cache_key(function)
    if function_cache_key is None:
        return None
    self._effect_summary_parameter_cache[function_cache_key] = list(parameters)
    summary_cache_key = self._analysis_scope_key(
        function,
        bound_parameter_values,
        bound_parameter_storage_values,
    )
    cached = self._effect_summary_cache.get(summary_cache_key)
    if cached is not None:
        return cached

    def summarize_call(target, args):
        target_ref = self._coerce_runtime_target_ref(target)
        if target_ref is None:
            return None
        active_key = self._target_active_key(target_ref)
        if active_key is not None and active_key in active_functions:
            return None
        callee = self._resolve_target_function(target_ref)
        if callee is None:
            return None
        callee_parameters_for_binding = self._get_freshest_callee_parameters(target_ref)
        callee_bound_parameter_values = self._bound_parameter_values_from_call_args(
            args,
            callee_parameters_for_binding,
        )
        callee_bound_parameter_storage_values = self._bound_parameter_storage_values_from_call_args(
            args,
            callee_parameters_for_binding,
        )
        callee_scope_key = self._analysis_scope_key(
            callee,
            callee_bound_parameter_values,
            callee_bound_parameter_storage_values,
        )
        if callee_scope_key is None:
            return None
        cached_callee = self._effect_summary_cache.get(callee_scope_key)
        if cached_callee is not None:
            return cached_callee

        from scripts.function_tracer_pcode.ghidra.decompilation_broker import (
            EFFECT_SUMMARY_SOURCE_CONTRACT,
            decompile_function,
        )
        results = decompile_function(
            self, callee, 60, None,
            source_contract_id=EFFECT_SUMMARY_SOURCE_CONTRACT,
            semantic_owner="subordinate",
        )
        if not results.decompileCompleted():
            return None
        callee_high = results.getHighFunction()
        if callee_high is None:
            return None

        fresh_callee_parameters = self._collect_parameters(callee_high)
        callee_parameters = self._choose_richer_parameter_descriptors(
            callee_parameters_for_binding,
            fresh_callee_parameters,
        )
        callee_bound_parameter_values = self._bound_parameter_values_from_call_args(
            args,
            callee_parameters,
        )
        callee_bound_parameter_storage_values = self._bound_parameter_storage_values_from_call_args(
            args,
            callee_parameters,
        )
        callee_tracer = self._make_tracer(
            callee_high,
            bound_parameter_values=callee_bound_parameter_values,
            bound_parameter_storage_values=callee_bound_parameter_storage_values,
        )
        callee_tracer.record_deferred_call = self._make_deferred_call_recorder(callee)
        callee_tracker = ConditionTracker(callee_tracer)
        callee_tracer.condition_tracker = callee_tracker
        from scripts.function_tracer_pcode.analysis.phi_resolver import PhiHandler

        callee_phi_handler = PhiHandler(callee_tracer, callee_tracker)
        callee_tracer.phi_handler = callee_phi_handler
        callee_tracker.build()
        callee_function_cache_key = self._function_cache_key(callee)
        if callee_function_cache_key is not None:
            self._effect_summary_parameter_cache[callee_function_cache_key] = list(callee_parameters)
        image_base = None
        try:
            image_base = self.program.getImageBase().getOffset()
        except Exception:
            image_base = None
        callee_tracker.refine_branch_conditions(
            call_resolver=self._make_call_resolver(
                self._extend_active_functions(active_functions, target_ref),
                callee,
            ),
            parameters=callee_parameters,
            resolve_callee_parameters=self._get_freshest_callee_parameters,
            read_memory_value=self._read_memory_value,
            image_base=image_base,
        )
        summary = self._invoke_build_effect_summary(
            callee,
            callee_high,
            callee_tracer,
            callee_tracker,
            callee_parameters,
            self._extend_active_functions(active_functions, target_ref),
            bound_parameter_values=callee_bound_parameter_values,
            bound_parameter_storage_values=callee_bound_parameter_storage_values,
        )
        return summary

    def resolve_callee_parameters(target):
        return self._get_freshest_callee_parameters(target)

    current_target = CallTargetRef.from_function(function)
    # Register outgoing direct-call edges before recursive summary descent;
    # recompute the certificate after descent when more graph nodes exist.
    self._build_function_control_effect_profile(high_function, function, parameters)
    image_base = None
    try:
        image_base = self.program.getImageBase().getOffset()
    except Exception:
        image_base = None
    summary = summarize_store_effects(
        condition_tracker.block_by_index.values(),
        tracer,
        condition_tracker,
        parameters,
        direct_call_summary=summarize_call,
        direct_call_expander=self._make_call_resolver(
            self._extend_active_functions(active_functions, current_target),
            function,
        ),
        resolve_callee_parameters=resolve_callee_parameters,
        read_memory_value=self._read_memory_value,
        image_base=image_base,
        debug=self.debug,
    )
    summary.function_control_effect_profile = self._build_function_control_effect_profile(
        high_function,
        function,
        parameters,
    )
    self._effect_summary_cache[summary_cache_key] = summary
    return summary

def _impl__local_memory_key(self, addr_expr: Expression, size: int) -> Tuple[StructuralKey, int]:
    key_expr = (
        addr_expr.operands[0]
        if getattr(addr_expr, "expr_type", None) == ExpressionType.MEMORY
        and getattr(addr_expr, "operands", None)
        else addr_expr
    )
    return (
        key_expr.structural_key(
            normalize_commutative=True,
            strip_width_adapters=True,
            collapse_full_masks=True,
        ),
        int(size),
    )

def _impl__apply_local_store_effect(
    self,
    pcode_op,
    tracer,
    local_values: Dict[Tuple[str, int, int], Expression],
    local_storages: Dict[Tuple[str, int, int], Any],
    local_memory: Dict[Tuple[StructuralKey, int], Expression],
) -> None:
    if pcode_op.getNumInputs() < 3:
        return
    addr_expr = self._evaluate_local_varnode_expression(
        pcode_op.getInput(1),
        tracer,
        local_values,
        local_storages,
        local_memory,
    )
    value_expr = self._evaluate_local_varnode_expression(
        pcode_op.getInput(2),
        tracer,
        local_values,
        local_storages,
        local_memory,
    )
    size = pcode_op.getInput(2).getSize()
    local_memory[self._local_memory_key(addr_expr, size)] = value_expr

def _impl__split_effect_sensitive_return_case(
    self,
    value: Expression,
    conditions: List[Condition],
) -> List[Tuple[Expression, List[Condition]]]:
    effect_summary = self._current_effect_summary
    if effect_summary is None or not effect_summary.effects:
        return [(value, conditions)]

    rewritten = self._rewrite_effect_sensitive_return_value(
        value,
        conditions,
        effect_summary,
    )
    if self.debug and rewritten is not None and not _expressions_equivalent(rewritten, value):
        self._debug_print(
            "Effect-sensitive rewrite candidate: "
            f"{self._debug_expr_identity_summary(value)} -> "
            f"{self._debug_expr_identity_summary(rewritten)}"
        )
    if rewritten is None or _expressions_equivalent(rewritten, value):
        return [(value, conditions)]

    expanded = self._expand_object_centric_expression_cases(
        rewritten,
        conditions,
    )
    if not expanded:
        return [(value, conditions)]
    expanded = [
        (
            self._collapse_effect_sensitive_case_wrapper(
                value,
                case_value,
                case_conditions,
                effect_summary,
            ),
            case_conditions,
        )
        for case_value, case_conditions in expanded
    ]

    deduplicated = self._deduplicate_expression_cases(expanded)
    if self.debug and deduplicated:
        for case_index, (case_value, case_conditions) in enumerate(deduplicated):
            cond_dump = [
                ConditionSimplifier.get_simplified_condition_string(cond)
                for cond in case_conditions
            ]
            self._debug_print(
                "  effect-sensitive case "
                f"[{case_index}]: {self._debug_expr_identity_summary(case_value)}"
            )
            self._debug_print(f"    conditions={cond_dump}")
    if (
        len(deduplicated) == 1
        and _expressions_equivalent(deduplicated[0][0], value)
        and self._condition_lists_equivalent(deduplicated[0][1], conditions)
    ):
        return [(value, conditions)]

    if self.debug and len(deduplicated) > 1:
        self._debug_print(
            "Split effect-sensitive expanded return into "
            f"{len(deduplicated)} object-centric cases: "
            f"{self._debug_expr_summary(value)} -> {self._debug_expr_summary(rewritten)}"
        )
    return deduplicated

def _impl__rewrite_effect_sensitive_return_value(
    self,
    value: Expression,
    conditions: List[Condition],
    effect_summary: EffectSummary,
) -> Optional[Expression]:
    precise_object_state_value = self._resolve_precise_object_state_value(
        value,
        conditions,
        effect_summary,
    )
    if precise_object_state_value is not None and precise_object_state_value is not value:
        if self.debug:
            self._debug_print(
                "Resolved return to precise object-state carrier before generic rewrite: "
                f"{self._debug_expr_identity_summary(value)} -> "
                f"{self._debug_expr_identity_summary(precise_object_state_value)}"
            )
        return precise_object_state_value

    for rewrite_kind, rewritten in self._iter_effect_sensitive_rewrite_candidates(
        value,
        conditions,
        effect_summary,
    ):
        accepted = self._accept_effect_sensitive_rewrite(
            value,
            rewritten,
            conditions,
            effect_summary,
            rewrite_kind=rewrite_kind,
        )
        if (
            not accepted
            and self._accept_effect_rewrite_without_rank_gain(
                value,
                rewritten,
                conditions,
                effect_summary,
            )
        ):
            accepted = True
        if accepted:
            return rewritten
    return value

def _impl__accept_effect_rewrite_without_rank_gain(
    self,
    original: Optional[Expression],
    rewritten: Optional[Expression],
    conditions: List[Condition],
    effect_summary: EffectSummary,
) -> bool:
    if original is None or rewritten is None:
        return False
    if _expressions_equivalent(original, rewritten):
        return False
    if _expression_contains_observed_loads(original):
        return False
    if self._rewrite_drops_composite_location_wrapper(original, rewritten, conditions):
        return False
    if expression_contains_post_state_reads(rewritten):
        return True
    original_effect_locations = self._matched_effect_locations(
        original,
        conditions,
        effect_summary,
    )
    rewritten_effect_locations = self._matched_effect_locations(
        rewritten,
        conditions,
        effect_summary,
    )
    if rewritten_effect_locations > original_effect_locations:
        return True

    location = canonicalize_expr_read_location(
        original,
        self._current_parameters,
    )
    if location is None:
        return False

    original_match = _find_matching_effect_value(
        original,
        location,
        conditions,
        effect_summary.effects,
        self._current_parameters,
    )
    rewritten_match = _find_matching_effect_value(
        rewritten,
        location,
        conditions,
        effect_summary.effects,
        self._current_parameters,
    )
    return original_match is None and rewritten_match is not None

def _impl__matched_effect_locations(
    self,
    expr: Optional[Expression],
    conditions: List[Condition],
    effect_summary: EffectSummary,
) -> set[tuple]:
    matched_locations: set[tuple] = set()
    if expr is None:
        return matched_locations

    for current in _iter_expression_nodes(expr, include_phi_conditions=False):
        location = canonicalize_expr_read_location(current, self._current_parameters)
        if location is None:
            continue
        if _find_matching_effect_value(
            current,
            location,
            conditions,
            effect_summary.effects,
            self._current_parameters,
        ) is None:
            continue
        matched_locations.add(location.stable_key())
    return matched_locations

def _impl__iter_effect_sensitive_rewrite_candidates(
    self,
    value: Expression,
    conditions: List[Condition],
    effect_summary: EffectSummary,
) -> Iterable[Tuple[str, Optional[Expression]]]:
    expr_location = canonicalize_expr_read_location(
        value,
        self._current_parameters,
    )
    nontrivial_location_wrapper = False
    effect_value_matches_wrapper = False
    if expr_location is not None:
        nontrivial_location_wrapper = self._expression_has_nontrivial_location_wrapper(
            value,
            expr_location,
        )
        if nontrivial_location_wrapper:
            effect_value_matches_wrapper = _find_matching_effect_value(
                value,
                expr_location,
                conditions,
                effect_summary.effects,
                self._current_parameters,
            ) is not None
    if expr_location is not None:
        post_state_read = resolve_definite_post_state_read_for_location(
            expr_location,
            conditions,
            effect_summary.effects,
            self._current_parameters,
            symbolic_post_state=True,
        )
        if post_state_read is not None:
            yield ("final object-state concrete", lower_post_state_expression_for_smt(
                post_state_read,
                conditions,
                effect_summary.effects,
                self._current_parameters,
            ))
            if not nontrivial_location_wrapper or effect_value_matches_wrapper:
                yield ("final object-state symbolic", post_state_read)
    if _expression_contains_observed_loads(value):
        yield (
            "observed-load",
            rewrite_observed_loads_from_effects(
                value,
                conditions,
                effect_summary.effects,
                self._current_parameters,
            ),
        )
    yield (
        "wrapper-preserving effect-sensitive",
        normalize_post_state_expression(
            value,
            conditions,
            effect_summary.effects,
            self._current_parameters,
            prefer_canonical_post_state=False,
            preserve_composite_location_wrappers=True,
        ),
    )
    yield (
        "generic effect-sensitive",
        rewrite_loads_from_effects(
            value,
            conditions,
            effect_summary.effects,
            self._current_parameters,
        ),
    )

def _impl__collapse_effect_sensitive_case_wrapper(
    self,
    original: Optional[Expression],
    rewritten: Optional[Expression],
    conditions: List[Condition],
    effect_summary: EffectSummary,
) -> Optional[Expression]:
    if original is None or rewritten is None:
        return rewritten
    rebuilt_wrapper = self._rebuild_effect_sensitive_case_wrapper(
        original,
        rewritten,
        conditions,
        effect_summary,
    )
    if rebuilt_wrapper is not None:
        return rebuilt_wrapper
    if (
        original.expr_type != ExpressionType.BINARY_OP
        or rewritten.expr_type != ExpressionType.BINARY_OP
        or original.operator != rewritten.operator
        or len(original.operands) != 2
        or len(rewritten.operands) != 2
    ):
        return rewritten

    original_operands = list(original.operands)
    rewritten_operands = list(rewritten.operands)
    for original_index, original_operand in enumerate(original_operands):
        location = canonicalize_expr_read_location(
            original_operand,
            self._current_parameters,
        )
        if location is None:
            continue
        shared_original = original_operands[1 - original_index]
        for rewritten_index, rewritten_operand in enumerate(rewritten_operands):
            shared_rewritten = rewritten_operands[1 - rewritten_index]
            if not _expressions_equivalent(shared_rewritten, shared_original):
                continue
            if not self._wrapper_preserves_collapsed_operand(
                original.operator,
                shared_original,
                kept_operand_index=rewritten_index,
            ):
                continue
            if (
                _find_matching_effect_value(
                    rewritten_operand,
                    location,
                    conditions,
                    effect_summary.effects,
                    self._current_parameters,
                )
                is None
            ):
                continue
            post_state_read = promote_effect_value_carrier_to_post_state_read(
                rewritten_operand,
                conditions,
                effect_summary.effects,
                self._current_parameters,
                symbolic_post_state=True,
            )
            if post_state_read is not None:
                final_replayed = _replay_definite_active_effects_for_location(
                    location,
                    conditions,
                    effect_summary.effects,
                    self._current_parameters,
                )
                if final_replayed is not None and _expressions_equivalent_under_conditions(
                    final_replayed,
                    rewritten_operand,
                    conditions,
                    self._current_parameters,
                ):
                    post_state_read = None
            if self.debug:
                self._debug_print(
                    "Collapsed duplicate effect-sensitive binary wrapper: "
                    f"{self._debug_expr_identity_summary(rewritten)} -> "
                    f"{self._debug_expr_identity_summary(post_state_read or rewritten_operand)}"
                )
            return post_state_read or rewritten_operand

    return rewritten

def _impl__rebuild_effect_sensitive_case_wrapper(
    self,
    original: Optional[Expression],
    rewritten: Optional[Expression],
    conditions: List[Condition],
    effect_summary: EffectSummary,
) -> Optional[Expression]:
    if (
        original is None
        or rewritten is None
        or original.expr_type != ExpressionType.BINARY_OP
        or len(original.operands) != 2
    ):
        return None
    if (
        rewritten.expr_type == ExpressionType.BINARY_OP
        and rewritten.operator == original.operator
        and len(rewritten.operands) == 2
    ):
        return None

    rewritten_runtime_ref = getattr(rewritten, "runtime_ref", None)
    if not isinstance(rewritten_runtime_ref, PostStateValueRef):
        return None

    original_operands = list(original.operands)
    for original_index, original_operand in enumerate(original_operands):
        location = canonicalize_expr_read_location(
            original_operand,
            self._current_parameters,
        )
        if location is None:
            continue
        rewritten_without_carrier_ref = _strip_materialized_post_state_value_refs(rewritten)
        if _expression_reads_location(
            rewritten_without_carrier_ref,
            location,
            conditions,
            self._current_parameters,
        ):
            continue
        shared_original = original_operands[1 - original_index]
        if self._wrapper_preserves_collapsed_operand(
            original.operator,
            shared_original,
            kept_operand_index=original_index,
        ):
            continue
        if (
            _find_matching_effect_value(
                rewritten,
                location,
                conditions,
                effect_summary.effects,
                self._current_parameters,
            )
            is None
        ):
            continue
        rebuilt_operands = [shared_original, shared_original]
        rebuilt_operands[original_index] = rewritten
        rebuilt_operands[1 - original_index] = shared_original
        rebuilt = original.clone_with(operands=rebuilt_operands)
        rebuilt = ConditionSimplifier.reduce_expression_under_conditions(
            rebuilt,
            conditions,
        )
        rebuilt = self._fold_constant_expression(rebuilt, fallback_expr=original)
        if self.debug:
            self._debug_print(
                "Rebuilt effect-sensitive wrapper around branch-local effect value: "
                f"{self._debug_expr_identity_summary(rewritten)} -> "
                f"{self._debug_expr_identity_summary(rebuilt)}"
            )
        return rebuilt

    return None

def _impl__accept_effect_sensitive_rewrite(
    self,
    original: Optional[Expression],
    rewritten: Optional[Expression],
    conditions: List[Condition],
    effect_summary: EffectSummary,
    *,
    rewrite_kind: str,
) -> bool:
    if rewritten is None or original is None:
        return False
    if _expressions_equivalent(rewritten, original):
        return False

    if self._is_semantically_lossless_effect_sensitive_rewrite(
        original,
        rewritten,
        conditions,
        effect_summary,
    ):
        original_precision = self._effect_sensitive_rewrite_precision(
            original,
            conditions,
            effect_summary,
        )
        rewritten_precision = self._effect_sensitive_rewrite_precision(
            rewritten,
            conditions,
            effect_summary,
        )
        accepted = (
            rewritten_precision.post_state_reads > original_precision.post_state_reads
            or rewritten_precision.observed_loads < original_precision.observed_loads
            or rewritten_precision.matched_effect_locations >= original_precision.matched_effect_locations
            or rewritten_precision.downstream_unresolved_values
            <= original_precision.downstream_unresolved_values
        )
        if accepted:
            return True

    original_precision = self._effect_sensitive_rewrite_precision(
        original,
        conditions,
        effect_summary,
    )
    rewritten_precision = self._effect_sensitive_rewrite_precision(
        rewritten,
        conditions,
        effect_summary,
    )
    accepted = (
        rewritten_precision.opaque_unknowns < original_precision.opaque_unknowns
        or rewritten_precision.downstream_unresolved_values < original_precision.downstream_unresolved_values
        or rewritten_precision.matched_effect_locations > original_precision.matched_effect_locations
        or rewritten_precision.post_state_reads > original_precision.post_state_reads
        or (
            rewritten_precision.object_centric_unknowns > original_precision.object_centric_unknowns
            and rewritten_precision.downstream_unresolved_values
            <= original_precision.downstream_unresolved_values
        )
    )
    if not accepted:
        original_rank = self._effect_sensitive_rewrite_rank(original)
        rewritten_rank = self._effect_sensitive_rewrite_rank(rewritten)
        accepted = rewritten_rank > original_rank
    else:
        original_rank = self._effect_sensitive_rewrite_rank(original)
        rewritten_rank = self._effect_sensitive_rewrite_rank(rewritten)

    if self.debug and not accepted:
        self._debug_print(
            f"Rejected {rewrite_kind} rewrite without object-centric precision gain: "
            f"{self._debug_expr_identity_summary(original)} -> "
            f"{self._debug_expr_identity_summary(rewritten)} "
            f"rank {original_rank} -> {rewritten_rank} "
            f"precision {original_precision} -> {rewritten_precision}"
        )

    return accepted

def _impl__effect_sensitive_rewrite_precision(
    self,
    expr: Optional[Expression],
    conditions: List[Condition],
    effect_summary: EffectSummary,
) -> _EffectRewritePrecision:
    matched_locations = len(
        self._matched_effect_locations(expr, conditions, effect_summary)
    )
    post_state_reads = 1 if expression_contains_post_state_reads(expr) else 0
    lowered = expr
    if expr is not None and effect_summary is not None and getattr(effect_summary, "effects", None):
        lowered_candidate = lower_post_state_expression_for_smt(
            expr,
            conditions,
            effect_summary.effects,
            self._current_parameters,
        )
        if lowered_candidate is not None:
            lowered = lowered_candidate

    return _EffectRewritePrecision(
        matched_effect_locations=matched_locations,
        post_state_reads=post_state_reads,
        object_centric_unknowns=self._count_object_centric_unknowns(expr),
        opaque_unknowns=self._count_opaque_unknowns(expr),
        downstream_unresolved_values=self._count_unresolved_value_nodes(lowered),
        observed_loads=self._count_observed_loads(expr),
        phi_nodes=self._count_phi_nodes(expr),
    )

def _impl__effect_sensitive_rewrite_rank(
    self,
    expr: Optional[Expression],
) -> Tuple[int, int, int, int]:
    if expr is None:
        return (0, 0, 0, 0)
    return (
        1 if expression_contains_post_state_reads(expr) else 0,
        1 if self._expression_contains_phi(expr) else 0,
        1 if _expression_contains_observed_loads(expr) else 0,
        self._count_memory_reads(expr),
    )

def _impl__count_observed_loads(self, expr: Optional[Expression]) -> int:
    count = 0
    for current in _iter_expression_nodes(expr, include_phi_conditions=False):
        if _expression_contains_observed_loads(current):
            count += 1
    return count

def _impl__return_info_effective_region_conditions(
    self,
    info: ReturnInfo,
) -> List[Condition]:
    """ReturnInfo conditions plus proof/runtime guards carried by its value."""

    conditions = list(getattr(info, "conditions", None) or [])
    conditions.extend(self._expression_runtime_guard_conditions(getattr(info, "value", None)))
    return ConditionSimplifier.simplify_conditions_object_centric(conditions)

def _impl__normalize_return_value_with_effect_summary(
    self,
    value: Expression,
    conditions: List[Condition],
    effect_summary: EffectSummary,
) -> Optional[Expression]:
    carrier_post_state_read = promote_effect_value_carrier_to_post_state_read(
        value,
        conditions,
        effect_summary.effects,
        self._current_parameters,
        symbolic_post_state=True,
    )
    atomic_object_state_value = _materialize_existing_effect_value_carrier(
        value,
        conditions,
        effect_summary.effects,
        self._current_parameters,
    )
    if (
        atomic_object_state_value is not None
        and atomic_object_state_value is not value
        and isinstance(getattr(atomic_object_state_value, "runtime_ref", None), PostStateValueRef)
        and self._count_memory_reads(value) > 1
    ):
        return atomic_object_state_value

    canonicalized = normalize_post_state_expression(
        value,
        conditions,
        effect_summary.effects,
        self._current_parameters,
        prefer_canonical_post_state=True,
        symbolic_post_state=True,
    )
    canonicalized = self._collapse_effect_sensitive_case_wrapper(
        value,
        canonicalized,
        conditions,
        effect_summary,
    )
    if carrier_post_state_read is not None and expression_contains_post_state_reads(canonicalized):
        return canonicalized
    materialized_canonicalized = _materialize_existing_effect_value_carrier(
        canonicalized,
        conditions,
        effect_summary.effects,
        self._current_parameters,
    )
    original_location = canonicalize_expr_read_location(
        value,
        self._current_parameters,
    )
    if original_location is None:
        original_location = _find_unique_effect_location_for_value(
            value,
            conditions,
            effect_summary.effects,
            self._current_parameters,
        )
    carrier_matches_wrapped_object = (
        carrier_post_state_read is not None
        and original_location is not None
        and (
            self._expression_has_nontrivial_location_wrapper(value, original_location)
            or value.expr_type != ExpressionType.MEMORY
        )
    )
    if carrier_matches_wrapped_object:
        materialized_canonicalized = carrier_post_state_read
        drops_composite_wrapper = False
    else:
        drops_composite_wrapper = self._rewrite_drops_composite_location_wrapper(
            value,
            materialized_canonicalized,
            conditions,
        )
    if (
        not drops_composite_wrapper
        and original_location is not None
        and self._expression_has_nontrivial_location_wrapper(value, original_location)
        and isinstance(getattr(materialized_canonicalized, "runtime_ref", None), PostStateValueRef)
    ):
        distinct_read_locations = {
            location.stable_key()
            for node in _iter_expression_nodes(value, include_phi_conditions=False)
            for location in (
                canonicalize_expr_read_location(
                    node,
                    self._current_parameters,
                ),
            )
            if location is not None
        }
        if len(distinct_read_locations) == 1:
            lowered_materialized = lower_post_state_expression_for_smt(
                materialized_canonicalized,
                conditions,
                effect_summary.effects,
                self._current_parameters,
            )
            if lowered_materialized is None or not _expressions_equivalent_under_conditions(
                lowered_materialized,
                value,
                conditions,
                self._current_parameters,
            ):
                drops_composite_wrapper = True
    if drops_composite_wrapper:
        wrapper_preserving = normalize_post_state_expression(
            value,
            conditions,
            effect_summary.effects,
            self._current_parameters,
            prefer_canonical_post_state=False,
            preserve_composite_location_wrappers=True,
        )
        canonicalized = wrapper_preserving if wrapper_preserving is not None else canonicalized
    else:
        if carrier_post_state_read is not None:
            canonicalized = carrier_post_state_read
        else:
            canonicalized = materialized_canonicalized
    canonicalized = self._prefer_lossless_materialized_post_state_roundtrip(
        canonicalized,
        value,
        conditions,
        effect_summary,
    )
    if expression_matches_stale_post_state_replay(
        value,
        canonicalized,
        conditions,
        effect_summary.effects,
        self._current_parameters,
    ):
        return canonicalized
    if self._should_replay_canonicalized_return(canonicalized, value):
        replayed = normalize_post_state_expression(
            canonicalized,
            conditions,
            effect_summary.effects,
            self._current_parameters,
            prefer_canonical_post_state=False,
        )
        if replayed is not None:
            canonicalized = replayed

    if self._symbolic_post_state_roundtrip_rejected(canonicalized, value, conditions, effect_summary):
        if self.debug:
            self._debug_print(
                "Rejected symbolic post-state canonicalization due to non-equivalent round trip: "
                f"{self._debug_expr_summary(value)} -> "
                f"{self._debug_expr_summary(canonicalized)}"
            )
        fallback_replayed = None
        if carrier_post_state_read is not None:
            fallback_replayed = carrier_post_state_read
        if fallback_replayed is None and value.expr_type == ExpressionType.MEMORY:
            fallback_replayed = materialize_definite_post_state_expression(
                value,
                conditions,
                effect_summary.effects,
                self._current_parameters,
                preserve_composite_location_wrappers=True,
            )
        if fallback_replayed is None or _expressions_equivalent(fallback_replayed, value):
            fallback_replayed = normalize_post_state_expression(
                value,
                conditions,
                effect_summary.effects,
                self._current_parameters,
                prefer_canonical_post_state=False,
                preserve_composite_location_wrappers=True,
            )
        return fallback_replayed if fallback_replayed is not None else value

    return canonicalized

def _impl__prefer_lossless_materialized_post_state_roundtrip(
    self,
    canonicalized: Optional[Expression],
    original: Expression,
    conditions: List[Condition],
    effect_summary: EffectSummary,
) -> Optional[Expression]:
    if canonicalized is None:
        return None
    if original.expr_type == ExpressionType.MEMORY:
        return canonicalized
    if _expression_contains_observed_loads(original):
        return canonicalized
    if canonicalized.expr_type == ExpressionType.MEMORY:
        return canonicalized
    if not expression_contains_post_state_reads(canonicalized):
        return canonicalized

    carrier_post_state_read = promote_effect_value_carrier_to_post_state_read(
        original,
        conditions,
        effect_summary.effects,
        self._current_parameters,
        symbolic_post_state=True,
    )
    if (
        carrier_post_state_read is not None
        and _expressions_equivalent(canonicalized, carrier_post_state_read)
    ):
        return canonicalized

    lowered_roundtrip = lower_post_state_expression_for_smt(
        canonicalized,
        conditions,
        effect_summary.effects,
        self._current_parameters,
    )
    if lowered_roundtrip is None:
        return canonicalized
    if expression_contains_post_state_reads(lowered_roundtrip):
        return canonicalized
    if not _expressions_equivalent_under_conditions(
        lowered_roundtrip,
        original,
        conditions,
        self._current_parameters,
    ):
        return canonicalized
    return lowered_roundtrip

def _impl__symbolic_post_state_roundtrip_rejected(
    self,
    canonicalized: Optional[Expression],
    original: Expression,
    conditions: List[Condition],
    effect_summary: EffectSummary,
) -> bool:
    if canonicalized is None or _expressions_equivalent(canonicalized, original):
        return False
    if not expression_contains_post_state_reads(canonicalized):
        return False
    lowered_roundtrip = lower_post_state_expression_for_smt(
        canonicalized,
        conditions,
        effect_summary.effects,
        self._current_parameters,
    )
    if lowered_roundtrip is None:
        return True

    comparison_targets = [original]
    if original.expr_type == ExpressionType.MEMORY:
        expected_roundtrip = materialize_definite_post_state_expression(
            original,
            conditions,
            effect_summary.effects,
            self._current_parameters,
            preserve_composite_location_wrappers=True,
        )
        if expected_roundtrip is not None:
            comparison_targets.insert(0, expected_roundtrip)
    if _expression_contains_observed_loads(original):
        observed_post_state = promote_observed_loads_to_post_state_reads(
            original,
            conditions,
            effect_summary.effects,
            self._current_parameters,
            symbolic_post_state=True,
        )
        if observed_post_state is not None:
            comparison_targets.append(observed_post_state)
            lowered_observed_post_state = lower_post_state_expression_for_smt(
                observed_post_state,
                conditions,
                effect_summary.effects,
                self._current_parameters,
            )
            if lowered_observed_post_state is not None:
                comparison_targets.append(lowered_observed_post_state)
        observed_rewritten = rewrite_observed_loads_from_effects(
            original,
            conditions,
            effect_summary.effects,
            self._current_parameters,
        )
        if observed_rewritten is not None:
            comparison_targets.append(observed_rewritten)
        observed_roundtrip = normalize_post_state_expression(
            original,
            conditions,
            effect_summary.effects,
            self._current_parameters,
            prefer_canonical_post_state=False,
            preserve_composite_location_wrappers=True,
        )
        if observed_roundtrip is not None:
            comparison_targets.append(observed_roundtrip)

    for comparison_target in comparison_targets:
        if _expressions_equivalent_under_conditions(
            lowered_roundtrip,
            comparison_target,
            conditions,
            self._current_parameters,
        ):
            return False
    if self._expression_contains_stale_effect_value_for_post_state(
        original,
        canonicalized,
        conditions,
        effect_summary,
    ):
        return False
    return True

def _impl__expression_contains_stale_effect_value_for_post_state(
    self,
    expr: Optional[Expression],
    target_post_state: Optional[Expression],
    conditions: List[Condition],
    effect_summary: EffectSummary,
) -> bool:
    if expr is None or target_post_state is None:
        return False

    candidates = [expr]
    if expr.expr_type == ExpressionType.PHI and expr.value:
        candidates.extend(
            value
            for _cond, value in expr.value
            if value is not None
        )

    for current in candidates:
        location = canonicalize_expr_read_location(current, self._current_parameters)
        if location is not None:
            promoted = promote_effect_value_match_to_post_state_read(
                current,
                location,
                conditions,
                effect_summary.effects,
                self._current_parameters,
                symbolic_post_state=True,
            )
            if promoted is not None and _expressions_equivalent(promoted, target_post_state):
                return True
        if expression_matches_stale_post_state_replay(
            current,
            target_post_state,
            conditions,
            effect_summary.effects,
            self._current_parameters,
        ):
            return True
    return False

def _impl__count_memory_reads(self, expr: Optional[Expression]) -> int:
    if expr is None:
        return 0
    count = 1 if expr.expr_type == ExpressionType.MEMORY else 0
    if expr.expr_type == ExpressionType.PHI and expr.value:
        return count + sum(self._count_memory_reads(value) for _cond, value in expr.value)
    for operand in getattr(expr, "operands", []) or []:
        count += self._count_memory_reads(operand)
    return count

def _impl__concretize_readonly_loads(
    self,
    value: Expression,
    conditions: List[Condition],
    parameters: List[Dict],
) -> Expression:
    """Resolve simple read-only indexed loads into finite PHI chains when possible."""
    try:
        return concretize_readonly_loads(
            value,
            conditions,
            parameters,
            self._read_memory_value,
            image_base=self.program.getImageBase().getOffset(),
            debug=self.debug,
        )
    except Exception as exc:
        self._debug_print(f"Readonly load concretization failed: {exc}")
        return value

def _impl__read_memory_value(self, address_value: int, size_bytes: int) -> Optional[int]:
    """Read an unsigned integer from program memory."""
    if address_value < 0 or size_bytes <= 0:
        return None

    try:
        memory = self.program.getMemory()
        default_space = self.program.getAddressFactory().getDefaultAddressSpace()
        addr = default_space.getAddress(address_value)
        if addr is None:
            return None

        raw_bytes = []
        for offset in range(size_bytes):
            byte_val = memory.getByte(addr.add(offset))
            raw_bytes.append(int(byte_val) & 0xFF)

        is_big_endian = self.program.getLanguage().isBigEndian()
        ordered = raw_bytes if is_big_endian else list(reversed(raw_bytes))

        result = 0
        for byte_val in ordered:
            result = (result << 8) | byte_val
        return result
    except Exception:
        return None


OBSERVABLE_EFFECT_SURFACE_SOURCE = "observable_effects_and_return_value"


def observable_store_effects(effect_summary: Any) -> List[Any]:
    """Stores a caller can observe: through parameter pointers or globals.

    Stack-frame stores die with the frame and are not part of the observable
    behaviour; everything else (parameter-based, storage/global) is.
    """
    observable: List[Any] = []
    for effect in getattr(effect_summary, "effects", None) or ():
        location = getattr(effect, "location", None)
        base_ref = getattr(location, "base_ref", None)
        if getattr(base_ref, "kind", None) == "stack_frame":
            continue
        observable.append(effect)
    return observable


def _impl__apply_observable_effect_surface(
    self,
    result: FunctionReturnAnalysis,
    return_type_obj: Any,
    return_type: Optional[str],
) -> bool:
    """Compare non-void functions on ``stores ⊕ return value`` (Issue #13).

    A function that writes through a parameter pointer (or to a global) and
    returns something is observable through both; comparing the return value
    alone let two functions that only differ in what they store come out
    EQUIVALENT (raytrace constructors returning the sret pointer).  This is
    the void ``memory_effect`` surface generalised: the packed store summary
    (per-location presence flag and value, conditional on the store's path
    conditions) is concatenated with each return case's value, and the
    comparison surface becomes ``memory_effect`` with the combined width.

    When the effect summary is not trustworthy (unsupported call, incomplete
    coverage) the surface is not built; the existing equivalence-blocking
    reasons already keep such functions away from EQUIVALENT.
    """
    if result is None or not result.returns:
        return False
    if return_type_obj is not None and self._is_void_type(return_type_obj):
        return False
    if getattr(result, "comparison_surface", None) is not None:
        return False
    effect_summary = getattr(result, "effect_summary", None)
    if effect_summary is None:
        return False
    if getattr(effect_summary, "has_unsupported_call", False):
        return False
    effects = observable_store_effects(effect_summary)
    if not effects:
        return False
    from scripts.function_tracer_pcode.analysis.effects.summary import (
        _concat as concat_expressions,
        build_void_effect_summary_expr,
    )

    effects_expr = build_void_effect_summary_expr(effects)
    if effects_expr is None:
        return False
    effect_bits = int(effects_expr.get_bit_width() or 0)
    return_bits = max(
        (int(ret.value.get_bit_width() or 0) for ret in result.returns if ret.value is not None),
        default=0,
    )
    if effect_bits <= 0 or return_bits <= 0:
        return False
    rewritten = []
    for ret in result.returns:
        if ret.value is None:
            return False
        combined = concat_expressions(effects_expr, ret.value)
        rewritten.append(replace(ret, value=combined))
    result.returns = rewritten
    result.comparison_surface = ComparisonSurface(
        kind="memory_effect",
        explicit_bit_width=effect_bits + return_bits,
        use_sign_extension=False,
        evidence={
            "source": OBSERVABLE_EFFECT_SURFACE_SOURCE,
            "effect_count": len(effects),
            "effect_bits": effect_bits,
            "return_bits": return_bits,
            "declared_return_type": return_type,
        },
    )
    if "observable_effect_surface" not in result.analysis_notes:
        result.analysis_notes.append("observable_effect_surface")
    self._debug_print(
        f"Observable effect surface: {len(effects)} store effect(s) ({effect_bits} bits) "
        f"combined with the {return_bits}-bit return value"
    )
    return True
