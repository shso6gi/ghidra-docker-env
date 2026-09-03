"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.recurrence.summarizer``."""

from __future__ import annotations

from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    Condition,
    CountedLoopGuard,
    Counter,
    Expression,
    ExpressionType,
    LoopBodyEffectRef,
    LoopSideEffectProfileRef,
    ParameterInfo,
    PcodeBlockRef,
    PcodeOpRef,
    ReturnInfo,
    StorageInfo,
    _runtime_expression_signature,
    canonicalize_location,
    get_declared_type_signedness,
    parameter_identity_key_from_descriptor,
    parameter_identity_key_from_expression,
    re,
)

def _impl_try_summarize_function(self, function, high_function, analysis) -> Optional[Tuple[List[ReturnInfo], str]]:
    if function is None or high_function is None or analysis is None:
        return None

    if len(getattr(analysis, "parameters", []) or []) == 1:
        summary = self._try_summarize_linear_self_recursion(function, high_function, analysis)
        if summary is not None:
            return summary

    summary = self._try_summarize_readonly_pointer_reduction(function, high_function, analysis)
    if summary is not None:
        return summary

    summary = self._try_summarize_vectorized_affine_progression_sum(function, high_function, analysis)
    if summary is not None:
        return summary

    summary = self._try_summarize_multiplicative_phi_return_region(
        function,
        high_function,
        analysis,
    )
    if summary is not None:
        return summary

    summary = self._try_summarize_counted_scalar_loop(function, high_function, analysis)
    if summary is not None:
        return summary

    summary = self._try_summarize_proved_return_region_state_transition_composition(
        function,
        high_function,
        analysis,
    )
    if summary is not None:
        return summary

    summary = self._try_summarize_state_transition_loop(function, high_function, analysis)
    if summary is not None:
        return summary

    summary = self._try_summarize_branch_accumulator_loop(analysis)
    if summary is not None:
        return summary
    return None

def _impl__counter_parameter_candidate_matches_descriptor(
    self,
    candidate: Optional[Expression],
    counter_param: dict,
) -> bool:
    if candidate is None or getattr(candidate, "expr_type", None) != ExpressionType.PARAMETER:
        return False
    expected_storage = self._summary_storage_info_from_parameter(counter_param)
    candidate_storage = getattr(candidate, "storage_info", None)
    if expected_storage is not None:
        return (
            candidate_storage is not None
            and self._storage_infos_refer_to_same_parameter_slot(candidate_storage, expected_storage)
        )
    try:
        expected_index = int(counter_param.get("index"))
    except (TypeError, ValueError):
        expected_index = -1
    try:
        candidate_index = int(getattr(candidate, "value", -1))
    except (TypeError, ValueError):
        candidate_index = -1
    if expected_index >= 0 or candidate_index >= 0:
        return expected_index >= 0 and expected_index == candidate_index
    expected_identity = None
    try:
        expected_identity = parameter_identity_key_from_descriptor(counter_param)
    except Exception:
        expected_identity = None
    candidate_identity = None
    try:
        candidate_identity = parameter_identity_key_from_expression(candidate)
    except Exception:
        candidate_identity = None
    if expected_identity is not None or candidate_identity is not None:
        return expected_identity is not None and expected_identity == candidate_identity
    return False

def _impl__complete_counter_constant_cover(
    self,
    conditions: Sequence[Condition],
    counter_expr: Expression,
    *,
    search_limit: int = 64,
) -> Optional[Tuple[int, ...]]:
    size = max(1, int(getattr(counter_expr, "size", 0) or 4))
    possible_values: List[int] = []
    for value in range(0, int(search_limit) + 1):
        equality = Condition(
            Expression.binary_op(
                "INT_EQUAL",
                counter_expr,
                Expression.constant(value, size=size),
            ),
            False,
        )
        is_unsat = self._condition_conjunction_unsat_with_solver(list(conditions) + [equality])
        if is_unsat is None:
            return None
        if is_unsat is False:
            possible_values.append(value)
        elif is_unsat is not True:
            return None
    if not possible_values:
        return None
    disjunction = None
    for value in possible_values:
        equality_expr = Expression.binary_op(
            "INT_EQUAL",
            counter_expr,
            Expression.constant(value, size=size),
        )
        equality_expr.size = 1
        if disjunction is None:
            disjunction = equality_expr
        else:
            disjunction = Expression.binary_op("BOOL_OR", disjunction, equality_expr)
            disjunction.size = 1
    outside_cover = Condition(disjunction, True)
    cover_complete = self._condition_conjunction_unsat_with_solver(list(conditions) + [outside_cover])
    if cover_complete is None:
        return None
    if cover_complete is not True:
        return None
    return tuple(possible_values)

def _impl__counter_parameter_candidate_can_normalize(
    self,
    candidate: Optional[Expression],
    counter_param: dict,
    counter_expr: Expression,
) -> bool:
    if candidate is None or getattr(candidate, "expr_type", None) != ExpressionType.PARAMETER:
        return False
    if counter_expr is None or getattr(counter_expr, "expr_type", None) != ExpressionType.PARAMETER:
        return False
    candidate_storage = getattr(candidate, "storage_info", None)
    counter_storage = getattr(counter_expr, "storage_info", None)
    if candidate_storage is not None or counter_storage is not None:
        return (
            candidate_storage is not None
            and counter_storage is not None
            and self._storage_infos_refer_to_same_parameter_slot(candidate_storage, counter_storage)
        )
    candidate_identity = self._parameter_expression_semantic_identity(candidate)
    counter_identity = self._parameter_expression_semantic_identity(counter_expr)
    if candidate_identity is not None or counter_identity is not None:
        return candidate_identity is not None and candidate_identity == counter_identity
    expected_index = None
    try:
        if counter_param.get("index") is not None:
            expected_index = int(counter_param.get("index"))
    except (TypeError, ValueError):
        expected_index = None
    try:
        candidate_index = int(getattr(candidate, "value", -1))
        counter_index = int(getattr(counter_expr, "value", -1))
    except (TypeError, ValueError):
        candidate_index = counter_index = -1
    if candidate_index < 0:
        return False
    if counter_index >= 0:
        return candidate_index == counter_index
    return expected_index is not None and candidate_index == expected_index

def _impl__loop_effect_profile_name(
    self,
    *,
    memory_reads: bool,
    memory_writes: bool,
    calls: bool,
    escapes: bool,
    conditional_guards: bool,
) -> str:
    if calls or escapes:
        return "effect_unknown"
    if memory_writes:
        return "effect_aware"
    if conditional_guards:
        return "pure_conditional"
    if memory_reads:
        return "pure_memory_read"
    return "pure"

def _impl__build_loop_side_effect_profile(
    self,
    *,
    analysis=None,
    high_function=None,
    loop_blocks: Optional[Sequence[object]] = None,
    ignored_branch_ops: Optional[Sequence[object]] = None,
    block_guard_conditions: Optional[Dict[object, Sequence[Condition]]] = None,
    block_guard_info: Optional[Dict[object, Dict[str, Any]]] = None,
    memory_reads: bool = False,
) -> LoopSideEffectProfileRef:
    descriptors: List[LoopBodyEffectRef] = []
    context_descriptors: List[LoopBodyEffectRef] = []
    has_memory_reads = bool(memory_reads)
    has_memory_writes = False
    has_calls = False
    has_escapes = False
    has_conditional_guards = False
    has_context_memory_writes = False
    has_context_calls = False
    has_context_escapes = False
    has_context_conditional_guards = False

    effect_summary = getattr(analysis, "effect_summary", None) if analysis is not None else None
    for effect in getattr(effect_summary, "effects", None) or []:
        has_context_memory_writes = True
        effect_conditions = tuple(getattr(effect, "conditions", None) or ())
        if effect_conditions:
            has_context_conditional_guards = True
        context_descriptors.append(
            LoopBodyEffectRef(
                kind="memory_write",
                source="function_effect_summary",
                scope="function",
                location=getattr(effect, "location", None),
                value_expr=getattr(effect, "value", None),
                guard_constraints=effect_conditions,
                order_key=getattr(effect, "order_key", None),
            )
        )
    if getattr(effect_summary, "has_unsupported_call", False):
        has_context_calls = True
        has_context_escapes = True
        context_descriptors.append(
            LoopBodyEffectRef(
                kind="unsupported_call",
                source="function_effect_summary",
                scope="function",
            )
        )
    if getattr(analysis, "incomplete_control_flow", False):
        has_context_escapes = True
        context_descriptors.append(
            LoopBodyEffectRef(
                kind="incomplete_control_flow",
                source="function_analysis",
                scope="function",
            )
        )

    ignored_ids = {id(op) for op in (ignored_branch_ops or ()) if op is not None}
    pcode_scope = "loop" if loop_blocks is not None else "function"
    if loop_blocks is None and high_function is not None:
        loop_blocks = list(self._iter_basic_blocks(high_function))
    for block in loop_blocks or ():
        for op in self._iter_block_ops(block):
            mnemonic = getattr(op, "getMnemonic", lambda: None)()
            if mnemonic == "LOAD":
                if pcode_scope == "loop":
                    has_memory_reads = True
                continue
            if mnemonic == "STORE":
                block_key = self._block_key(block)
                guard_info = (block_guard_info or {}).get(block_key, {})
                guard_conditions = tuple(
                    guard_info.get(
                        "common",
                        (block_guard_conditions or {}).get(block_key, ()),
                    )
                )
                path_condition_sets = tuple(
                    tuple(path_conditions or ())
                    for path_conditions in guard_info.get("paths", ())
                )
                store_effect = self._store_effect_ref_for_op(
                    op,
                    scope=pcode_scope,
                    guard_constraints=guard_conditions,
                    path_condition_sets=path_condition_sets,
                    guard_paths_incomplete=bool(guard_info.get("incomplete", False)),
                )
                if pcode_scope == "loop":
                    has_memory_writes = True
                    descriptors.append(store_effect)
                else:
                    has_context_memory_writes = True
                    context_descriptors.append(store_effect)
                continue
            if mnemonic in {"CALL", "CALLIND"}:
                call_effect = LoopBodyEffectRef(
                    kind="call",
                    source="pcode_scan",
                    scope=pcode_scope,
                    target_ref=self._call_target_ref_for_op(op),
                    order_key=self._pcode_op_order_key(op),
                )
                if pcode_scope == "loop":
                    has_calls = True
                    has_escapes = True
                    descriptors.append(call_effect)
                else:
                    has_context_calls = True
                    has_context_escapes = True
                    context_descriptors.append(call_effect)
                continue
            if mnemonic == "BRANCHIND":
                escape_effect = LoopBodyEffectRef(
                    kind="escape",
                    source="pcode_scan",
                    scope=pcode_scope,
                    order_key=self._pcode_op_order_key(op),
                )
                if pcode_scope == "loop":
                    has_escapes = True
                    descriptors.append(escape_effect)
                else:
                    has_context_escapes = True
                    context_descriptors.append(escape_effect)
                continue
            if mnemonic == "CBRANCH" and id(op) not in ignored_ids:
                condition = self._condition_for_cbranch_op(op)
                guard_effect = LoopBodyEffectRef(
                    kind="conditional_guard",
                    source="pcode_scan",
                    scope=pcode_scope,
                    guard_constraints=(condition,) if condition is not None else (),
                    order_key=self._pcode_op_order_key(op),
                )
                if pcode_scope == "loop":
                    has_conditional_guards = True
                    descriptors.append(guard_effect)
                else:
                    has_context_conditional_guards = True
                    context_descriptors.append(guard_effect)

    guard_count = sum(1 for effect in descriptors if effect.kind == "conditional_guard")
    profile = self._loop_effect_profile_name(
        memory_reads=has_memory_reads,
        memory_writes=has_memory_writes,
        calls=has_calls,
        escapes=has_escapes,
        conditional_guards=has_conditional_guards,
    )
    return LoopSideEffectProfileRef(
        profile=profile,
        memory_reads=has_memory_reads,
        memory_writes=has_memory_writes,
        calls=has_calls,
        escapes=has_escapes,
        conditional_guards=has_conditional_guards,
        context_memory_writes=has_context_memory_writes,
        context_calls=has_context_calls,
        context_escapes=has_context_escapes,
        context_conditional_guards=has_context_conditional_guards,
        effect_count=len(descriptors),
        guard_count=guard_count,
        effect_descriptors=tuple(descriptors),
        context_descriptors=tuple(context_descriptors),
    )

def _impl__store_effect_ref_for_op(
    self,
    op,
    *,
    scope: str,
    guard_constraints: Sequence[Condition] = (),
    path_condition_sets: Sequence[Sequence[Condition]] = (),
    guard_paths_incomplete: bool = False,
) -> LoopBodyEffectRef:
    address_space = None
    address_expr = None
    value_expr = None
    unkeyable_reasons: List[str] = []
    input_count = self._safe_pcode_input_count(op)
    if input_count >= 3:
        address_space = self._store_address_space_ref_for_op(op)
        try:
            address_expr = self._build_pcode_expression(op.getInput(1), placeholders={})
        except RecursionError:
            address_expr = None
        try:
            value_expr = self._build_pcode_expression(op.getInput(2), placeholders={})
        except RecursionError:
            value_expr = None
    if address_space is None:
        unkeyable_reasons.append("store_address_space_unresolved")
    if address_expr is None or self._expression_is_unresolved(address_expr):
        address_expr = None
        unkeyable_reasons.append("store_address_unresolved")
    if value_expr is None or self._expression_is_unresolved(value_expr):
        value_expr = None
        unkeyable_reasons.append("store_value_unresolved")
    if guard_paths_incomplete:
        unkeyable_reasons.append("store_guard_paths_incomplete")
    return LoopBodyEffectRef(
        kind="memory_write",
        source="pcode_scan",
        scope=scope,
        address_space=address_space,
        location=address_expr,
        value_expr=value_expr,
        guard_constraints=tuple(guard_constraints or ()),
        path_condition_sets=tuple(
            tuple(path_conditions or ())
            for path_conditions in (path_condition_sets or ())
        ),
        guard_paths_incomplete=bool(guard_paths_incomplete),
        order_key=self._pcode_op_order_key(op),
        keyable=not unkeyable_reasons,
        unkeyable_reason=";".join(unkeyable_reasons) if unkeyable_reasons else None,
    )

def _impl__safe_call(self, obj, method_name: str):
    method = getattr(obj, method_name, None)
    if not callable(method):
        return None
    try:
        return method()
    except (AttributeError, TypeError, ValueError, RuntimeError):
        return None

def _impl__safe_bool_call(self, obj, method_name: str) -> Optional[bool]:
    value = self._safe_call(obj, method_name)
    if value is None:
        return None
    return bool(value)

def _impl__safe_int(self, value) -> Optional[int]:
    if value is None:
        return None
    try:
        return int(value)
    except (TypeError, ValueError, OverflowError):
        return None

def _impl__call_target_ref_for_op(self, op):
    if op is None or self._safe_pcode_input_count(op) < 1:
        return None
    resolver = getattr(self.tracer, "resolve_call_target_ref", None)
    if not callable(resolver):
        return None
    try:
        return resolver(op.getInput(0))
    except (AttributeError, TypeError, ValueError, RecursionError):
        return None

def _impl__safe_pcode_input_count(self, op) -> int:
    try:
        value = getattr(op, "getNumInputs", lambda: 0)()
        if not isinstance(value, (int, float, str, bytes)):
            return 0
        return int(value or 0)
    except Exception:
        return 0

def _impl__varnode_def_is_multiequal(self, varnode) -> bool:
    if varnode is None:
        return False
    definition = getattr(varnode, "getDef", lambda: None)()
    return getattr(definition, "getMnemonic", lambda: None)() == "MULTIEQUAL"

def _impl__safe_pcode_input_varnode(self, op, index: int):
    try:
        return op.getInput(int(index))
    except Exception:
        return None

def _impl__unique_parameters_by_name(parameters: Optional[Sequence[dict]]) -> Dict[str, dict]:
    by_name: Dict[str, dict] = {}
    name_counts: Dict[str, int] = {}
    for param in parameters or ():
        if not isinstance(param, dict):
            continue
        name = str(param.get("name") or "")
        if not name:
            continue
        name_counts[name] = name_counts.get(name, 0) + 1
        by_name.setdefault(name, param)
    return {
        name: param
        for name, param in by_name.items()
        if name_counts.get(name, 0) == 1
    }

def _impl__small_integer_power_roots(
    self,
    value: int,
    *,
    max_root: int = 256,
) -> Tuple[int, ...]:
    try:
        value = int(value)
    except (TypeError, ValueError):
        return ()
    if value <= 1:
        return ()
    roots: List[int] = []
    for root in range(2, int(max_root) + 1):
        product = root * root
        while product < value:
            product *= root
        if product == value:
            roots.append(root)
    return tuple(roots)

def _impl__build_auxiliary_parameter_infos(
    self,
    symbol_specs: Sequence[dict],
) -> List[ParameterInfo]:
    infos: List[ParameterInfo] = []
    for spec in sorted(
        symbol_specs or [],
        key=lambda item: (
            self._summary_symbol_identity_sort_key(item.get("identity")),
            int(item.get("size", 0) or 0),
        ),
    ):
        aux_name = str(spec.get("aux_name") or "")
        if not aux_name:
            continue
        width_bits = max(1, int(spec.get("size", 0) or 4)) * 8
        infos.append(
            ParameterInfo(
                original_name=aux_name,
                smt_name=aux_name,
                bit_width=width_bits,
                index=int(spec.get("aux_index", -1) or -1),
                is_signed=bool(spec.get("is_signed", True)),
            )
        )
    return infos

def _impl__value_preserving_varnode_path(
    self,
    start_varnode,
    target_varnode,
    *,
    budget: int = 128,
) -> Optional[Tuple[Tuple[Any, ...], ...]]:
    if start_varnode is None or target_varnode is None:
        return None
    if self._same_varnode_object_identity(start_varnode, target_varnode):
        edge = self._value_preserving_edge_key("identity", start_varnode, target_varnode)
        return (edge,) if edge is not None else None
    stack = [(start_varnode, ())]
    seen = set()
    exhausted = False
    while stack:
        if len(seen) >= budget:
            exhausted = True
            break
        current, path = stack.pop()
        if current is None:
            continue
        current_id = id(current)
        if current_id in seen:
            continue
        seen.add(current_id)
        descendants = getattr(current, "getDescendants", lambda: None)()
        if descendants is None:
            continue
        for op in self._iter_descendant_ops(descendants):
            edge_kind = self._value_preserving_edge_kind(op, current)
            if edge_kind is None:
                continue
            output = getattr(op, "getOutput", lambda: None)()
            if output is not None:
                edge = self._value_preserving_edge_key(edge_kind, current, output, op=op)
                if edge is None:
                    continue
                next_path = path + (edge,)
                if self._same_varnode_object_identity(output, target_varnode):
                    return next_path
                stack.append((output, next_path))
    return None if exhausted else None

def _impl__iter_descendant_ops(self, descendants) -> Iterable[Any]:
    try:
        iterator = iter(descendants)
    except TypeError:
        iterator = None
    if iterator is not None:
        yield from iterator
        return
    while descendants.hasNext():
        yield descendants.next()

def _impl__value_preserving_edge_kind(self, op, input_varnode) -> Optional[str]:
    mnemonic = getattr(op, "getMnemonic", lambda: None)()
    output = getattr(op, "getOutput", lambda: None)()
    if output is None:
        return None
    if self._safe_pcode_input_count(op) < 1:
        return None
    try:
        first_input = op.getInput(0)
    except Exception:
        return None
    if not self._same_varnode_object_identity(first_input, input_varnode):
        return None
    if mnemonic == "COPY":
        return "COPY"
    if mnemonic == "SUBPIECE":
        if self._safe_pcode_input_count(op) < 2:
            return None
        offset = self._varnode_constant_value(op.getInput(1))
        if int(offset or 0) == 0 and self._varnode_size_bits(input_varnode) == self._varnode_size_bits(output):
            return "SUBPIECE_ZERO_SAME_WIDTH"
        return None
    if mnemonic in {"INT_ZEXT", "INT_SEXT"}:
        in_bits = self._varnode_size_bits(input_varnode)
        out_bits = self._varnode_size_bits(output)
        if in_bits > 0 and out_bits >= in_bits:
            return mnemonic
    return None

def _impl__varnode_size_bits(self, varnode) -> int:
    try:
        return max(1, int(getattr(varnode, "getSize", lambda: 0)() or 0)) * 8
    except Exception:
        return 0

def _impl__phi_input_predecessor_block(self, phi_op, input_index: int):
    if phi_op is None:
        return None
    parent = getattr(phi_op, "getParent", lambda: None)()
    if parent is None:
        return None
    try:
        index = int(input_index)
        in_size = int(getattr(parent, "getInSize", lambda: 0)() or 0)
        if index < 0 or index >= in_size:
            return None
        return parent.getIn(index)
    except Exception:
        return None

def _impl__iter_basic_blocks(self, high_function) -> Iterable:
    try:
        for block in high_function.getBasicBlocks():
            yield block
    except Exception:
        return

def _impl__iter_block_ops(self, block) -> Iterable:
    iterator = getattr(block, "getIterator", lambda: None)()
    if iterator is None:
        return
    while iterator.hasNext():
        yield iterator.next()

def _impl__find_cbranch_op(self, block):
    for op in self._iter_block_ops(block):
        if getattr(op, "getMnemonic", lambda: None)() == "CBRANCH":
            return op
    return None

def _impl__make_pcode_op_ref(self, pcode_op) -> Optional[PcodeOpRef]:
    return PcodeOpRef.from_pcode_op(
        pcode_op,
        binary_id=getattr(self.tracer, "_function_binary_id", None),
        program_uid=getattr(self.tracer, "_function_program_id", None),
        function_entry_space=getattr(self.tracer, "_function_entry_space", None),
        function_entry_offset=getattr(self.tracer, "_function_entry_offset", None),
    )

def _impl__make_pcode_block_ref(self, block) -> Optional[PcodeBlockRef]:
    if block is None:
        return None
    block_index = None
    start_address_offset = None
    try:
        block_index = int(block.getIndex())
    except Exception:
        block_index = None
    try:
        start = block.getStart()
        start_address_offset = int(start.getOffset()) if start is not None else None
    except Exception:
        start_address_offset = None
    if block_index is None and start_address_offset is None:
        return None
    return PcodeBlockRef(
        block_index=block_index,
        start_address_offset=start_address_offset,
        binary_id=(
            getattr(self.tracer, "_function_binary_id", None)
            or getattr(self.tracer, "_function_program_id", None)
        ),
        function_entry_space=getattr(self.tracer, "_function_entry_space", None),
        function_entry_offset=getattr(self.tracer, "_function_entry_offset", None),
    )

def _impl__collect_block_successors(self, block) -> List[object]:
    successors = []
    out_size = int(getattr(block, "getOutSize", lambda: 0)() or 0)
    for index in range(out_size):
        successor = getattr(block, "getOut", lambda _idx: None)(index)
        if successor is not None:
            successors.append(successor)
    return successors

def _impl__collect_block_predecessors(self, block) -> List[object]:
    predecessors = []
    in_size = int(getattr(block, "getInSize", lambda: 0)() or 0)
    for index in range(in_size):
        predecessor = getattr(block, "getIn", lambda _idx: None)(index)
        if predecessor is not None:
            predecessors.append(predecessor)
    return predecessors

def _impl__collect_loop_body_blocks(
    self,
    *,
    header_block,
    guard: CountedLoopGuard,
) -> Tuple[object, ...]:
    if guard is None or guard.body_block is None:
        return ()
    natural_loop_blocks = self._collect_natural_loop_blocks(
        header_block=header_block,
        guard=guard,
    )
    if natural_loop_blocks:
        return natural_loop_blocks
    self._debug("Falling back to reachability-based loop body collection")
    return self._collect_reachable_loop_body_blocks(
        header_block=header_block,
        guard=guard,
    )

def _impl__collect_natural_loop_blocks(
    self,
    *,
    header_block,
    guard: CountedLoopGuard,
) -> Tuple[object, ...]:
    if header_block is None or guard is None or guard.body_block is None or guard.latch_block is None:
        return ()
    header_key = self._block_key(header_block)
    latch_key = self._block_key(guard.latch_block)
    body_key = self._block_key(guard.body_block)
    exit_key = self._block_key(guard.exit_block)
    if header_key is None or latch_key is None or body_key is None:
        return ()
    if not any(self._block_key(successor) == header_key for successor in self._collect_block_successors(guard.latch_block)):
        return ()

    blocks_by_key: Dict[object, object] = {
        header_key: header_block,
        latch_key: guard.latch_block,
    }
    stack = [guard.latch_block]
    while stack:
        current = stack.pop()
        for predecessor in self._collect_block_predecessors(current):
            predecessor_key = self._block_key(predecessor)
            if predecessor_key is None or predecessor_key == exit_key:
                continue
            if predecessor_key in blocks_by_key:
                continue
            blocks_by_key[predecessor_key] = predecessor
            if predecessor_key != header_key:
                stack.append(predecessor)

    if body_key not in blocks_by_key:
        return ()
    return tuple(blocks_by_key.values())

def _impl__collect_reachable_loop_body_blocks(
    self,
    *,
    header_block,
    guard: CountedLoopGuard,
) -> Tuple[object, ...]:
    if guard is None or guard.body_block is None:
        return ()
    header_key = self._block_key(header_block)
    exit_key = self._block_key(guard.exit_block)
    blocks_by_key: Dict[object, object] = {}

    def add_block(block) -> None:
        key = self._block_key(block)
        if key is not None and key != exit_key and key not in blocks_by_key:
            blocks_by_key[key] = block

    add_block(header_block)
    add_block(guard.body_block)
    add_block(guard.latch_block)
    stack = [guard.body_block]
    visited = set()
    while stack:
        current = stack.pop()
        current_key = self._block_key(current)
        if current_key in visited or current_key == exit_key:
            continue
        visited.add(current_key)
        add_block(current)
        for successor in self._collect_block_successors(current):
            successor_key = self._block_key(successor)
            if successor_key == exit_key:
                continue
            if successor_key == header_key:
                add_block(successor)
                continue
            if successor_key not in visited:
                stack.append(successor)
    return tuple(blocks_by_key.values())

def _impl__can_reach_block(self, start_block, target_block) -> bool:
    if start_block is None or target_block is None:
        return False
    target_key = self._block_key(target_block)
    stack = [start_block]
    visited = set()
    while stack:
        current = stack.pop()
        current_key = self._block_key(current)
        if current_key in visited:
            continue
        visited.add(current_key)
        if current_key == target_key:
            return True
        for successor in self._collect_block_successors(current):
            stack.append(successor)
    return False

def _impl__pick_body_and_exit_blocks(self, header_block) -> Optional[Tuple[object, object, bool]]:
    successors = self._collect_block_successors(header_block)
    if len(successors) != 2:
        return None

    reaches = [
        successor for successor in successors
        if self._can_reach_block(successor, header_block)
    ]
    if len(reaches) != 1:
        return None

    body_block = reaches[0]
    exit_block = successors[0] if successors[1] is body_block else successors[1]
    true_out = getattr(header_block, "getTrueOut", lambda: None)()
    body_on_true = true_out is not None and self._block_key(true_out) == self._block_key(body_block)
    return body_block, exit_block, body_on_true

def _impl__adjust_loop_bound_for_strict_relation(
    self,
    bound_expr: Expression,
    delta: int,
) -> Expression:
    if delta == 0:
        return bound_expr
    adjusted = Expression.binary_op(
        "INT_ADD" if delta > 0 else "INT_SUB",
        bound_expr,
        Expression.constant(abs(delta), size=bound_expr.size or 4),
    )
    adjusted.size = bound_expr.size
    return adjusted

def _impl__parse_counter_comparison(
    self,
    expr: Optional[Expression],
    counter_name: str,
) -> Optional[Tuple[str, Expression, bool]]:
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return None
    operator = expr.operator
    if operator not in {"INT_SLESS", "INT_SLESSEQUAL", "INT_LESS", "INT_LESSEQUAL"}:
        return None
    signed = operator.startswith("INT_S")
    left, right = expr.operands
    left_is_counter = self._expr_matches_counter_placeholder(left, counter_name)
    right_is_counter = self._expr_matches_counter_placeholder(right, counter_name)
    if left_is_counter == right_is_counter:
        return None
    if left_is_counter:
        relation = "<" if operator in {"INT_SLESS", "INT_LESS"} else "<="
        return relation, right, signed
    relation = ">" if operator in {"INT_SLESS", "INT_LESS"} else ">="
    return relation, left, signed

def _impl__expr_matches_counter_placeholder(
    self,
    expr: Optional[Expression],
    counter_name: str,
) -> bool:
    normalized = self._normalize_counter_view(expr, counter_name)
    return bool(normalized is not None and getattr(normalized[0], "name", None) == counter_name)

def _impl__safe_expr_text(self, expr: Optional[Expression]) -> str:
    signature = _runtime_expression_signature(expr)
    return repr(signature)

def _impl__substitute_generated_loop_variable_aliases(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
    replacement: Expression,
) -> Optional[Expression]:
    if expr is None:
        return None
    placeholder_name = str(getattr(placeholder, "name", "") or "")
    if not placeholder_name.startswith("__loop_"):
        return expr
    if (
        getattr(expr, "expr_type", None) == ExpressionType.VARIABLE
        and str(getattr(expr, "name", "") or "") == placeholder_name
    ):
        return self._coerce_summary_expression_to_size(
            replacement,
            max(1, int(getattr(expr, "size", 0) or getattr(replacement, "size", 0) or 4)),
            signed=self._expression_prefers_signed_extension(replacement),
        )
    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left = self._substitute_generated_loop_variable_aliases(
            expr.operands[0],
            placeholder,
            replacement,
        )
        right = self._substitute_generated_loop_variable_aliases(
            expr.operands[1],
            placeholder,
            replacement,
        )
        if left is expr.operands[0] and right is expr.operands[1]:
            return expr
        rebuilt = Expression.binary_op(expr.operator, left, right)
        rebuilt.size = expr.size
        return rebuilt
    if expr.expr_type == ExpressionType.UNARY_OP and len(expr.operands) == 1:
        operand = self._substitute_generated_loop_variable_aliases(
            expr.operands[0],
            placeholder,
            replacement,
        )
        if operand is expr.operands[0]:
            return expr
        rebuilt = Expression.unary_op(expr.operator, operand)
        rebuilt.size = expr.size
        return rebuilt
    if expr.expr_type == ExpressionType.PHI and expr.value:
        branches = []
        changed = False
        for condition, value in expr.value:
            new_condition = condition
            if condition is not None:
                condition_expr = self._substitute_generated_loop_variable_aliases(
                    condition.expression,
                    placeholder,
                    replacement,
                )
                if condition_expr is not condition.expression:
                    new_condition = Condition(condition_expr, condition.negated)
                    changed = True
            new_value = self._substitute_generated_loop_variable_aliases(
                value,
                placeholder,
                replacement,
            )
            if new_value is not value:
                changed = True
            branches.append((new_condition, new_value))
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt
    if expr.expr_type in {ExpressionType.CALL, ExpressionType.INTRINSIC, ExpressionType.MEMORY} and expr.operands:
        new_operands = [
            self._substitute_generated_loop_variable_aliases(operand, placeholder, replacement)
            for operand in expr.operands
        ]
        if all(new is old for new, old in zip(new_operands, expr.operands)):
            return expr
        if expr.expr_type == ExpressionType.CALL:
            rebuilt = Expression.call(expr.name or "call", new_operands)
        elif expr.expr_type == ExpressionType.INTRINSIC:
            rebuilt = Expression.intrinsic(
                expr.name or "intrinsic",
                new_operands,
                size=expr.size,
                runtime_ref=expr.runtime_ref,
                opcode=expr.opcode,
            )
        else:
            rebuilt = Expression.memory(
                new_operands[0],
                size=expr.size,
                read_order_key=expr.read_order_key,
                runtime_ref=expr.runtime_ref,
            )
        rebuilt.size = expr.size
        return rebuilt
    return expr

def _impl__expr_matches_placeholder(self, expr: Optional[Expression], placeholder: Expression) -> bool:
    expr = self._canonicalize_expression(expr)
    if expr is None:
        return False
    try:
        return expr.structural_key() == placeholder.structural_key()
    except (AttributeError, TypeError, ValueError, RecursionError):
        return False

def _impl__state_loop_phi_indices(self, header_block, phi_op) -> Optional[Tuple[int, Tuple[int, ...]]]:
    input_count = self._safe_pcode_input_count(phi_op)
    if input_count < 2:
        return None
    init_indices: List[int] = []
    backedge_indices: List[int] = []
    in_size = int(getattr(header_block, "getInSize", lambda: 0)() or 0)
    for index in range(input_count):
        predecessor = header_block.getIn(index) if index < in_size else None
        if predecessor is not None and self._can_reach_block(header_block, predecessor):
            backedge_indices.append(index)
        else:
            init_indices.append(index)
    if len(init_indices) != 1 or not backedge_indices:
        return None
    return init_indices[0], tuple(backedge_indices)

def _impl__extract_delta_from_possible_phi(
    self,
    expr: Expression,
    accumulator_placeholder: Expression,
    parameters: Sequence[dict],
) -> Tuple[Expression, ...]:
    if expr.expr_type == ExpressionType.PHI and expr.value:
        deltas = []
        for _condition, branch_value in expr.value:
            if branch_value is None:
                return ()
            branch_deltas = self._extract_delta_from_possible_phi(
                branch_value,
                accumulator_placeholder,
                parameters,
            )
            if not branch_deltas:
                return ()
            deltas.extend(branch_deltas)
        return tuple(deltas)
    delta = self._extract_additive_delta(expr, accumulator_placeholder, parameters)
    if delta is not None:
        return (delta,)
    multiplicative = self._extract_multiplicative_accumulator_transition(
        expr,
        accumulator_placeholder,
    )
    if multiplicative is not None:
        return (multiplicative,)
    return ()

def _impl__debug(self, message: str) -> None:
    if self.debug:
        print(f"[RecurrenceSummary] {message}")

def _impl__parameter_bases_memory_reads(
    self,
    analysis,
    param: dict,
) -> bool:
    for ret in analysis.returns or []:
        for node in self._iter_expression_nodes(ret.value):
            if node.expr_type == ExpressionType.MEMORY and node.operands:
                location = canonicalize_location(
                    node.operands[0],
                    analysis.parameters or [],
                    size=max(1, int(getattr(node, "size", 0) or 0) or 1),
                )
                if location is not None and location.base_ref.matches_parameter(param):
                    return True
            if node.expr_type == ExpressionType.INTRINSIC and getattr(node, "name", None) == "PTRADD":
                base_name = self._parameter_name_from_expr(node.operands[0] if node.operands else None)
                if base_name and base_name == param.get("name"):
                    return True
    return False

def _impl__parse_pcode_site_text(
    self,
    text: str,
) -> Tuple[Optional[int], Optional[int], Optional[int]]:
    remainder = str(text or "").strip()
    seq_time: Optional[int] = None
    seq_order: Optional[int] = None
    while remainder:
        suffix = re.search(r":([to])([+-]?(?:0[xX][0-9a-fA-F]+|[0-9]+))$", remainder)
        if suffix is None:
            break
        value = self._coerce_pcode_site_int(suffix.group(2))
        if suffix.group(1) == "t" and seq_time is None:
            seq_time = value
        elif suffix.group(1) == "o" and seq_order is None:
            seq_order = value
        remainder = remainder[: suffix.start()]
    return self._parse_pcode_address_offset(remainder), seq_time, seq_order

def _impl__coerce_pcode_site_int(self, value: object) -> Optional[int]:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return int(value)
    if not isinstance(value, str):
        try:
            return int(value)
        except Exception:
            return None
    text = value.strip()
    if not text:
        return None
    try:
        return int(text, 0)
    except Exception:
        try:
            return int(text, 10)
        except Exception:
            return None

def _impl__fp_denominator_is_count_parameter(
    self,
    expr: Optional[Expression],
    count_name: str,
) -> bool:
    if expr is None:
        return False
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands and expr.operator in {"INT2FLOAT", "CAST", "COPY"}:
        return self._fp_denominator_is_count_parameter(expr.operands[0], count_name)
    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2 and expr.operator == "SUBPIECE":
        return self._fp_denominator_is_count_parameter(expr.operands[0], count_name)
    return (
        expr.expr_type == ExpressionType.PARAMETER
        and str(getattr(expr, "name", "") or "") == str(count_name)
    )

def _impl__counter_value_satisfies_relation(self, value: int, relation: str, constant: int) -> bool:
    if relation == ">":
        return int(value) > int(constant)
    if relation == ">=":
        return int(value) >= int(constant)
    if relation == "<":
        return int(value) < int(constant)
    if relation == "<=":
        return int(value) <= int(constant)
    return False

def _impl__analysis_parameter_declared_signedness(
    self,
    analysis,
    count_param: Optional[Dict[str, Any]],
) -> Optional[bool]:
    declared = None if count_param is None else count_param.get("is_signed")
    index = None if count_param is None else count_param.get("index")
    if index is None:
        return declared
    try:
        index_value = int(index)
    except (TypeError, ValueError):
        return declared
    for hypothesis_payload in list(getattr(analysis, "signature_hypotheses", []) or []):
        if not isinstance(hypothesis_payload, dict):
            continue
        resolved_overrides = dict(hypothesis_payload.get("resolved_parameter_overrides") or {})
        resolved_payload = resolved_overrides.get(index_value)
        if resolved_payload is None:
            resolved_payload = resolved_overrides.get(str(index_value))
        if isinstance(resolved_payload, dict) and "is_signed" in resolved_payload:
            raw_signed = resolved_payload.get("is_signed")
            declared = None if raw_signed is None else bool(raw_signed)
        parameter_overrides = dict(hypothesis_payload.get("parameter_type_overrides") or {})
        override_name = parameter_overrides.get(index_value)
        if override_name is None:
            override_name = parameter_overrides.get(str(index_value))
        if override_name:
            declared = get_declared_type_signedness(
                None,
                str(override_name),
                fallback_signed=bool(declared if declared is not None else True),
            )
    return declared

def _impl__round_down_quotient_source(
    self,
    quotient_vn,
    count_param: dict,
    lane_count: int,
) -> Optional[Tuple[object, int, int]]:
    quotient_vn = self._follow_passthrough_varnode(quotient_vn)
    def_op = getattr(quotient_vn, "getDef", lambda: None)()
    if def_op is None or int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return None
    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    dividend = self._follow_passthrough_varnode(def_op.getInput(0))
    divisor_or_shift = self._varnode_unsigned_constant_value(def_op.getInput(1))
    if mnemonic == "INT_SUB" and divisor_or_shift == 1:
        source = self._round_down_quotient_source(dividend, count_param, lane_count)
        if source is None:
            return None
        source_vn, start_index, tail_start_index_delta = source
        return source_vn, start_index, tail_start_index_delta + int(lane_count)
    if mnemonic in {"INT_DIV", "INT_SDIV"}:
        if divisor_or_shift is None or int(divisor_or_shift) != int(lane_count):
            return None
        source = self._rounded_count_source(dividend, count_param)
        if source is None:
            return None
        _count_source_vn, start_index = source
        return dividend, start_index, 0
    if mnemonic in {"INT_RIGHT", "INT_SRIGHT"}:
        if divisor_or_shift is None or int(lane_count) != (1 << int(divisor_or_shift)):
            return None
        source = self._rounded_count_source(dividend, count_param)
        if source is None:
            return None
        _count_source_vn, start_index = source
        return dividend, start_index, 0
    return None

def _impl__rounded_count_source(
    self,
    value,
    count_param: dict,
) -> Optional[Tuple[object, int]]:
    value = self._follow_passthrough_varnode(value)
    if self._varnode_matches_parameter(value, count_param):
        return value, 0

    def_op = getattr(value, "getDef", lambda: None)()
    if def_op is None:
        return None
    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return None

    left = self._follow_passthrough_varnode(def_op.getInput(0))
    right = self._follow_passthrough_varnode(def_op.getInput(1))
    if mnemonic == "INT_SUB" and self._varnode_matches_parameter(left, count_param):
        peeled = self._varnode_unsigned_constant_value(right)
        if peeled is not None and int(peeled) >= 0:
            return left, int(peeled)
        return None
    if mnemonic == "INT_ADD":
        if self._varnode_matches_parameter(left, count_param):
            delta = self._signed_varnode_constant_value(right)
            if delta is not None and int(delta) <= 0:
                return left, -int(delta)
        if self._varnode_matches_parameter(right, count_param):
            delta = self._signed_varnode_constant_value(left)
            if delta is not None and int(delta) <= 0:
                return right, -int(delta)
    return None

def _impl__power_of_two_rounding_from_mask(self, mask: int, *, count_width_bits: int) -> Optional[int]:
    width_bits = int(count_width_bits or 0)
    if width_bits <= 0:
        return None
    full_mask = (1 << width_bits) - 1
    current = int(mask) & full_mask
    low_clear = 0
    while low_clear < width_bits and (current & (1 << low_clear)) == 0:
        low_clear += 1
    if low_clear <= 0:
        return None
    lane_count = 1 << low_clear
    expected = full_mask ^ (lane_count - 1)
    if current != expected:
        return None
    return lane_count

def _impl__varnode_bit_width(self, varnode) -> Optional[int]:
    try:
        size = int(getattr(varnode, "getSize", lambda: 0)() or 0)
    except Exception:
        size = 0
    if size > 0:
        return size * 8
    expr = self._trace_varnode_expression(varnode)
    size = int(getattr(expr, "size", 0) or 0)
    if size > 0:
        return size * 8
    return None

def _impl__dedupe_pcode_refs(
    self,
    refs: Sequence[PcodeOpRef],
) -> Tuple[PcodeOpRef, ...]:
    unique: Dict[Tuple[Any, ...], PcodeOpRef] = {}
    for ref in refs or ():
        if ref is None:
            continue
        unique[ref.stable_key()] = ref
    return tuple(sorted(unique.values(), key=lambda ref: repr(ref.stable_key())))

def _impl__varnode_depends_on_varnode(self, start_varnode, target_varnode, *, budget: int = 64) -> bool:
    stack = [start_varnode]
    seen = set()
    steps = 0
    while stack and steps < budget:
        current = stack.pop()
        steps += 1
        key = self._varnode_cache_key(current)
        if key in seen:
            continue
        seen.add(key)
        if self._same_varnode_identity(current, target_varnode):
            return True
        def_op = getattr(current, "getDef", lambda: None)()
        if def_op is None:
            continue
        input_count = int(getattr(def_op, "getNumInputs", lambda: 0)() or 0)
        for index in range(input_count):
            try:
                stack.append(def_op.getInput(index))
            except Exception:
                continue
    return False

def _impl__phi_input_is_cfg_entry_seed(
    self,
    phi_op,
    input_index: int,
    update_indices: Sequence[int],
) -> bool:
    parent_block = getattr(phi_op, "getParent", lambda: None)()
    if parent_block is None:
        return False
    in_size = int(getattr(parent_block, "getInSize", lambda: 0)() or 0)
    if input_index < 0 or input_index >= in_size:
        return False
    try:
        seed_predecessor = parent_block.getIn(input_index)
    except Exception:
        return False
    if seed_predecessor is None:
        return False
    for update_index in update_indices:
        if update_index < 0 or update_index >= in_size:
            return False
        try:
            update_predecessor = parent_block.getIn(update_index)
        except Exception:
            return False
        if seed_predecessor is update_predecessor:
            return False
    return not self._cfg_block_reachable_without_reentering_header(
        parent_block,
        seed_predecessor,
        budget=128,
    )

def _impl__cfg_block_reachable_without_reentering_header(
    self,
    header_block,
    target_block,
    *,
    budget: int = 128,
) -> bool:
    if header_block is None or target_block is None:
        return False
    stack = [header_block]
    seen = set()
    steps = 0
    while stack and steps < budget:
        current = stack.pop()
        steps += 1
        current_key = self._block_identity_key(current)
        if current_key in seen:
            continue
        seen.add(current_key)
        out_size = int(getattr(current, "getOutSize", lambda: 0)() or 0)
        for index in range(out_size):
            try:
                successor = current.getOut(index)
            except Exception:
                continue
            if successor is target_block:
                return True
            if successor is None or successor is header_block:
                continue
            stack.append(successor)
    return False

def _impl__varnode_input_multiplicity(self, op, varnode) -> int:
    count = 0
    input_count = int(getattr(op, "getNumInputs", lambda: 0)() or 0)
    for index in range(input_count):
        try:
            candidate = op.getInput(index)
        except Exception:
            continue
        if self._same_varnode_value(candidate, varnode):
            count += 1
    return count

def _impl__iter_varnode_descendant_ops(self, varnode):
    descendants = getattr(varnode, "getDescendants", lambda: None)()
    if descendants is None:
        return ()
    try:
        return tuple(iter(descendants))
    except TypeError:
        pass
    ops = []
    try:
        while descendants.hasNext():
            ops.append(descendants.next())
    except Exception:
        return ()
    return tuple(ops)

def _impl__varnode_is_count_minus_rounded(
    self,
    candidate_vn,
    count_param: dict,
    rounded_vn,
    *,
    start_index: int = 0,
) -> bool:
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    if int(start_index) > 0:
        def_op = getattr(candidate_vn, "getDef", lambda: None)()
        if def_op is not None and getattr(def_op, "getMnemonic", lambda: None)() == "INT_SUB":
            if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
                left = self._follow_passthrough_varnode(def_op.getInput(0))
                right = self._follow_passthrough_varnode(def_op.getInput(1))
                if self._signed_varnode_constant_value(right) == int(start_index):
                    return self._varnode_is_count_minus_rounded(
                        left,
                        count_param,
                        rounded_vn,
                        start_index=0,
                    )
        if self._varnode_is_count_minus_rounded_plus_start(
            candidate_vn,
            count_param,
            rounded_vn,
            start_index=int(start_index),
        ):
            return True
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "INT_SUB":
        return False
    if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return False
    left = self._follow_passthrough_varnode(def_op.getInput(0))
    right = self._follow_passthrough_varnode(def_op.getInput(1))
    return (
        self._varnode_matches_parameter(left, count_param)
        and self._same_varnode_value(right, rounded_vn)
    )

def _impl__varnode_is_count_minus_rounded_plus_start(
    self,
    candidate_vn,
    count_param: dict,
    rounded_vn,
    *,
    start_index: int,
) -> bool:
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "INT_SUB":
        return False
    if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return False
    left = self._follow_passthrough_varnode(def_op.getInput(0))
    right = self._follow_passthrough_varnode(def_op.getInput(1))
    if not self._varnode_matches_parameter(left, count_param):
        return False
    return self._rounded_tail_index_varnode_matches(
        right,
        rounded_vn,
        start_index=int(start_index),
    )

def _impl__varnode_is_base_plus_scaled_parameter(
    self,
    candidate_vn,
    pointer_param: dict,
    count_param: dict,
    *,
    element_size: int,
    byte_offset: int,
) -> bool:
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None:
        return False
    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    if mnemonic == "PTRADD" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 3:
        base = self._follow_passthrough_varnode(def_op.getInput(0))
        index = self._follow_passthrough_varnode(def_op.getInput(1))
        elem = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(2)))
        if (
            elem == int(element_size)
            and self._varnode_matches_parameter(base, pointer_param)
            and self._varnode_matches_parameter(index, count_param)
            and int(byte_offset) == 0
        ):
            return True
    scaled_count = self._scaled_parameter_varnode(candidate_vn, count_param, element_size=element_size)
    if scaled_count is not None and self._varnode_matches_parameter(scaled_count, pointer_param):
        return int(byte_offset) == 0
    if mnemonic in {"INT_ADD", "PTRSUB"} and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
        left = self._follow_passthrough_varnode(def_op.getInput(0))
        right = self._follow_passthrough_varnode(def_op.getInput(1))
        left_const = self._signed_varnode_constant_value(left)
        right_const = self._signed_varnode_constant_value(right)
        if right_const == int(byte_offset):
            return self._varnode_is_base_plus_scaled_parameter(
                left,
                pointer_param,
                count_param,
                element_size=element_size,
                byte_offset=0,
            )
        if mnemonic == "INT_ADD" and left_const == int(byte_offset):
            return self._varnode_is_base_plus_scaled_parameter(
                right,
                pointer_param,
                count_param,
                element_size=element_size,
                byte_offset=0,
            )
        if self._varnode_matches_parameter(left, pointer_param):
            return self._varnode_is_scaled_parameter_plus_constant(
                right,
                count_param,
                element_size=element_size,
                byte_offset=byte_offset,
            )
        if mnemonic == "INT_ADD" and self._varnode_matches_parameter(right, pointer_param):
            return self._varnode_is_scaled_parameter_plus_constant(
                left,
                count_param,
                element_size=element_size,
                byte_offset=byte_offset,
            )
    return False

def _impl__varnode_is_base_plus_scaled_counter(
    self,
    candidate_vn,
    pointer_param: dict,
    counter_vn,
    *,
    element_size: int,
    byte_offset: int,
) -> bool:
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None:
        return False
    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    if mnemonic == "PTRADD" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 3:
        base = self._follow_passthrough_varnode(def_op.getInput(0))
        index = self._follow_passthrough_varnode(def_op.getInput(1))
        elem = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(2)))
        if elem == int(element_size):
            base_offset = self._byte_offset_from_parameter_pointer(base, pointer_param)
            if base_offset is not None and self._same_varnode_value(index, counter_vn):
                return int(base_offset) == int(byte_offset)
            index_delta = self._counter_plus_constant_delta(index, counter_vn)
            if (
                index_delta is not None
                and self._varnode_matches_parameter(base, pointer_param)
                and int(index_delta) * int(element_size) == int(byte_offset)
            ):
                return True
            if (
                int(byte_offset) % int(element_size) == 0
                and self._varnode_matches_parameter(base, pointer_param)
                and self._rounded_tail_index_varnode_matches(
                    index,
                    counter_vn,
                    start_index=int(byte_offset) // int(element_size),
                )
            ):
                return True
    if mnemonic in {"INT_ADD", "PTRSUB"} and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
        left = self._follow_passthrough_varnode(def_op.getInput(0))
        right = self._follow_passthrough_varnode(def_op.getInput(1))
        left_const = self._signed_varnode_constant_value(left)
        right_const = self._signed_varnode_constant_value(right)
        if right_const == int(byte_offset):
            return self._varnode_is_base_plus_scaled_counter(
                left,
                pointer_param,
                counter_vn,
                element_size=element_size,
                byte_offset=0,
            )
        if mnemonic == "INT_ADD" and left_const == int(byte_offset):
            return self._varnode_is_base_plus_scaled_counter(
                right,
                pointer_param,
                counter_vn,
                element_size=element_size,
                byte_offset=0,
            )
        if self._varnode_matches_parameter(left, pointer_param):
            return self._varnode_is_scaled_counter_plus_constant(
                right,
                counter_vn,
                element_size=element_size,
                byte_offset=byte_offset,
            )
        if mnemonic == "INT_ADD" and self._varnode_matches_parameter(right, pointer_param):
            return self._varnode_is_scaled_counter_plus_constant(
                left,
                counter_vn,
                element_size=element_size,
                byte_offset=byte_offset,
            )
    return False

def _impl__varnode_low_bits_clear(self, candidate_vn, bit_count: int) -> bool:
    if int(bit_count) <= 0:
        return True
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    mask = (1 << int(bit_count)) - 1
    constant = self._varnode_unsigned_constant_value(candidate_vn)
    if constant is not None:
        return (int(constant) & mask) == 0
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None or int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return False
    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    if mnemonic == "INT_AND":
        left = self._follow_passthrough_varnode(def_op.getInput(0))
        right = self._follow_passthrough_varnode(def_op.getInput(1))
        left_const = self._varnode_unsigned_constant_value(left)
        right_const = self._varnode_unsigned_constant_value(right)
        if left_const is not None and (int(left_const) & mask) == 0:
            return True
        if right_const is not None and (int(right_const) & mask) == 0:
            return True
    return False

def _impl__counter_plus_constant_delta(
    self,
    candidate_vn,
    counter_vn,
) -> Optional[int]:
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    if self._same_varnode_value(candidate_vn, counter_vn):
        return 0
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None:
        return None
    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    if mnemonic not in {"INT_ADD", "INT_SUB", "INT_OR"}:
        return None
    if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return None
    left = self._follow_passthrough_varnode(def_op.getInput(0))
    right = self._follow_passthrough_varnode(def_op.getInput(1))
    if mnemonic == "INT_OR":
        right_const = self._signed_varnode_constant_value(right)
        if self._same_varnode_value(left, counter_vn) and right_const is not None:
            if self._counter_low_bits_clear_for_or_delta(counter_vn, int(right_const)):
                return int(right_const)
        left_const = self._signed_varnode_constant_value(left)
        if self._same_varnode_value(right, counter_vn) and left_const is not None:
            if self._counter_low_bits_clear_for_or_delta(counter_vn, int(left_const)):
                return int(left_const)
        return None
    right_const = self._signed_varnode_constant_value(right)
    if self._same_varnode_value(left, counter_vn) and right_const is not None:
        return int(right_const) if mnemonic == "INT_ADD" else -int(right_const)
    if mnemonic == "INT_ADD":
        left_const = self._signed_varnode_constant_value(left)
        if self._same_varnode_value(right, counter_vn) and left_const is not None:
            return int(left_const)
    return None

def _impl__counter_low_bits_clear_for_or_delta(
    self,
    counter_vn,
    delta: int,
) -> bool:
    if int(delta) < 0:
        return False
    if int(delta) == 0:
        return True
    counter_bits = None
    try:
        counter_expr = self._build_pcode_expression(counter_vn, placeholders={})
    except Exception:
        counter_expr = None
    if counter_expr is not None:
        candidate_names = []
        counter_name = self._parameter_name_from_expr(counter_expr)
        if counter_name is not None:
            candidate_names.append(counter_name)
        else:
            candidate_names.extend(self._parameter_names_from_expr(counter_expr))
        candidate_bits: List[int] = []
        for name in candidate_names:
            if not name:
                continue
            inferred_bits = self._infer_counter_bit_width(counter_expr, str(name))
            if inferred_bits is not None and int(inferred_bits) > 0:
                candidate_bits.append(int(inferred_bits))
        if candidate_bits:
            counter_bits = min(candidate_bits)
    if counter_bits is None:
        counter_bits = self._varnode_bit_width(counter_vn)
    if counter_bits is not None and int(delta) >= (1 << int(counter_bits)):
        return False
    counter_vn = self._follow_passthrough_varnode(counter_vn)
    def_op = getattr(counter_vn, "getDef", lambda: None)()
    if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "INT_AND":
        return False
    if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return False
    left = self._follow_passthrough_varnode(def_op.getInput(0))
    right = self._follow_passthrough_varnode(def_op.getInput(1))
    mask = self._varnode_unsigned_constant_value(left)
    if mask is None:
        mask = self._varnode_unsigned_constant_value(right)
    if mask is None:
        return False
    return (int(mask) & int(delta)) == 0

def _impl__parameter_names_from_expr(self, expr) -> Tuple[str, ...]:
    names = []
    queue = [expr]
    while queue:
        current = queue.pop()
        if current is None:
            continue
        if getattr(current, "expr_type", None) == ExpressionType.PARAMETER and current.name:
            names.append(current.name)
        for operand in getattr(current, "operands", ()):
            queue.append(operand)
    return tuple(dict.fromkeys(names))

def _impl__varnode_is_scaled_parameter_plus_constant(
    self,
    candidate_vn,
    count_param: dict,
    *,
    element_size: int,
    byte_offset: int,
) -> bool:
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    if int(byte_offset) == 0 and self._scaled_parameter_varnode(candidate_vn, count_param, element_size=element_size) is not None:
        return True
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "INT_ADD":
        return False
    if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return False
    left = self._follow_passthrough_varnode(def_op.getInput(0))
    right = self._follow_passthrough_varnode(def_op.getInput(1))
    left_const = self._signed_varnode_constant_value(left)
    right_const = self._signed_varnode_constant_value(right)
    if left_const == int(byte_offset):
        return self._scaled_parameter_varnode(right, count_param, element_size=element_size) is not None
    if right_const == int(byte_offset):
        return self._scaled_parameter_varnode(left, count_param, element_size=element_size) is not None
    return False

def _impl__varnode_is_scaled_counter_plus_constant(
    self,
    candidate_vn,
    counter_vn,
    *,
    element_size: int,
    byte_offset: int,
) -> bool:
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    scaled_delta = self._scaled_counter_delta_bytes(
        candidate_vn,
        counter_vn,
        element_size=element_size,
    )
    if scaled_delta is not None:
        return int(scaled_delta) == int(byte_offset)
    if int(byte_offset) == 0 and self._varnode_is_scaled_counter(candidate_vn, counter_vn, element_size=element_size):
        return True
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "INT_ADD":
        return False
    if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return False
    left = self._follow_passthrough_varnode(def_op.getInput(0))
    right = self._follow_passthrough_varnode(def_op.getInput(1))
    left_const = self._signed_varnode_constant_value(left)
    right_const = self._signed_varnode_constant_value(right)
    if left_const == int(byte_offset):
        return self._varnode_is_scaled_counter(right, counter_vn, element_size=element_size)
    if right_const == int(byte_offset):
        return self._varnode_is_scaled_counter(left, counter_vn, element_size=element_size)
    return False

def _impl__scaled_counter_delta_bytes(
    self,
    candidate_vn,
    counter_vn,
    *,
    element_size: int,
) -> Optional[int]:
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None:
        return None
    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    if mnemonic == "INT_MULT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
        left = self._follow_passthrough_varnode(def_op.getInput(0))
        right = self._follow_passthrough_varnode(def_op.getInput(1))
        right_elem = self._varnode_unsigned_constant_value(right)
        if right_elem == int(element_size):
            delta = self._counter_plus_constant_delta(left, counter_vn)
            if delta is not None:
                return int(delta) * int(element_size)
        left_elem = self._varnode_unsigned_constant_value(left)
        if left_elem == int(element_size):
            delta = self._counter_plus_constant_delta(right, counter_vn)
            if delta is not None:
                return int(delta) * int(element_size)
        return None
    if mnemonic == "INT_LEFT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
        shifted = self._follow_passthrough_varnode(def_op.getInput(0))
        shift_bits = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(1)))
        if shift_bits is None or (1 << int(shift_bits)) != int(element_size):
            return None
        delta = self._counter_plus_constant_delta(shifted, counter_vn)
        if delta is not None:
            return int(delta) * int(element_size)
    return None

def _impl__scaled_parameter_varnode(
    self,
    candidate_vn,
    count_param: dict,
    *,
    element_size: int,
):
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None:
        return None
    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    if mnemonic == "INT_MULT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
        left = self._follow_passthrough_varnode(def_op.getInput(0))
        right = self._follow_passthrough_varnode(def_op.getInput(1))
        if self._varnode_matches_parameter(left, count_param) and self._varnode_unsigned_constant_value(right) == int(element_size):
            return left
        if self._varnode_matches_parameter(right, count_param) and self._varnode_unsigned_constant_value(left) == int(element_size):
            return right
    if mnemonic == "INT_LEFT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
        shifted = self._follow_passthrough_varnode(def_op.getInput(0))
        shift_bits = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(1)))
        if (
            shift_bits is not None
            and (1 << int(shift_bits)) == int(element_size)
            and self._varnode_matches_parameter(shifted, count_param)
        ):
            return shifted
    return None

def _impl__varnode_is_scaled_counter(
    self,
    candidate_vn,
    counter_vn,
    *,
    element_size: int,
) -> bool:
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None:
        return False
    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    if mnemonic == "INT_MULT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
        left = self._follow_passthrough_varnode(def_op.getInput(0))
        right = self._follow_passthrough_varnode(def_op.getInput(1))
        return (
            self._same_varnode_value(left, counter_vn)
            and self._varnode_unsigned_constant_value(right) == int(element_size)
        ) or (
            self._same_varnode_value(right, counter_vn)
            and self._varnode_unsigned_constant_value(left) == int(element_size)
        )
    if mnemonic == "INT_LEFT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
        shifted = self._follow_passthrough_varnode(def_op.getInput(0))
        shift_bits = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(1)))
        return (
            shift_bits is not None
            and (1 << int(shift_bits)) == int(element_size)
            and self._same_varnode_value(shifted, counter_vn)
        )
    return False

def _impl__low_mask_width_bytes(
    self,
    value_expr: Optional[Expression],
    mask_expr: Optional[Expression],
) -> Optional[int]:
    if value_expr is None or mask_expr is None:
        return None
    mask_value = self._raw_constant_value(mask_expr)
    value_size = max(1, int(getattr(value_expr, "size", 0) or 0))
    if mask_value is None or mask_value < 0:
        return None
    full_mask = (1 << (value_size * 8)) - 1
    mask_value = int(mask_value) & full_mask
    for width in range(1, value_size + 1):
        if mask_value == ((1 << (width * 8)) - 1):
            return width
    return None

def _impl__program_is_big_endian(self) -> bool:
    program = getattr(self.tracer, "program", None)
    if program is None:
        return False
    language_getter = getattr(program, "getLanguage", None)
    if not callable(language_getter):
        return False
    language = language_getter()
    is_big_endian = getattr(language, "isBigEndian", None)
    if not callable(is_big_endian):
        return False
    try:
        return bool(is_big_endian())
    except Exception:
        return False

def _impl__phi_input_value_varnode(self, phi_op, input_index: int):
    """Resolve the concrete value feeding a MULTIEQUAL input edge.

    Ghidra can represent a PHI input with the same register/storage varnode
    as the PHI output.  For object-level loop reasoning, the relevant value
    is the definition that reaches the PHI along that specific incoming
    edge.  Use the PHI parent's incoming block and pick the last p-code op
    in that predecessor that defines the same storage object.
    """

    try:
        raw_input = phi_op.getInput(int(input_index))
    except Exception:
        return None
    parent = getattr(phi_op, "getParent", lambda: None)()
    if parent is None:
        return raw_input
    incoming_block = self._phi_incoming_block(parent, int(input_index))
    if incoming_block is None:
        return raw_input

    fallback_output = None
    phi_output = getattr(phi_op, "getOutput", lambda: None)()
    block_ops = list(self._iter_block_ops(incoming_block))
    for candidate_op in reversed(block_ops):
        output = getattr(candidate_op, "getOutput", lambda: None)()
        if output is None:
            continue
        if self._same_storage_varnode(output, raw_input):
            if self._same_high_variable(output, raw_input) or self._same_high_variable(output, phi_output):
                return output
            if fallback_output is None:
                fallback_output = output
    if fallback_output is not None:
        if (
            self._same_high_variable(raw_input, phi_output)
            and not self._same_storage_varnode(raw_input, phi_output)
            and not self._same_high_variable(fallback_output, raw_input)
            and not self._same_high_variable(fallback_output, phi_output)
        ):
            return raw_input
        return fallback_output
    return raw_input

def _impl__phi_incoming_block(self, phi_parent, input_index: int):
    try:
        input_index = int(input_index)
        if input_index < 0 or input_index >= int(phi_parent.getInSize()):
            return None
        incoming_block = phi_parent.getIn(input_index)
    except Exception:
        return None
    if incoming_block is None:
        return None
    try:
        reverse_index = int(phi_parent.getInRevIndex(input_index))
        if reverse_index < 0 or reverse_index >= int(incoming_block.getOutSize()):
            return None
        if not self._same_pcode_block(incoming_block.getOut(reverse_index), phi_parent):
            return None
    except Exception:
        return None
    return incoming_block

def _impl__varnode_is_int_to_float_parameter(self, varnode, parameter: Optional[dict]) -> bool:
    if not isinstance(parameter, dict):
        return False
    varnode = self._follow_readonly_load_addend_passthrough(varnode)
    def_op = getattr(varnode, "getDef", lambda: None)()
    if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "INT2FLOAT":
        return False
    if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 1:
        return False
    return self._varnode_matches_parameter(def_op.getInput(0), parameter)

def _impl__low_mask_width_bytes_from_value(self, mask: int) -> Optional[int]:
    if mask < 0:
        return None
    width = 0
    current = int(mask)
    while current & 0xFF == 0xFF:
        width += 1
        current >>= 8
    if current != 0 or width <= 0:
        return None
    return width

def _impl__follow_passthrough_varnode(self, varnode):
    current = varnode
    seen = set()
    passthrough = {"COPY", "CAST", "INT_ZEXT", "INT_SEXT", "SUBPIECE"}
    while current is not None:
        current_key = self._varnode_cache_key(current)
        if current_key in seen:
            break
        seen.add(current_key)
        def_op = getattr(current, "getDef", lambda: None)()
        if def_op is None:
            break
        if getattr(def_op, "getMnemonic", lambda: None)() not in passthrough:
            break
        input_count = int(getattr(def_op, "getNumInputs", lambda: 0)() or 0)
        if input_count <= 0:
            break
        current = def_op.getInput(0)
    return current

def _impl__new_loop_variable_binder_scope(self) -> Dict[Tuple[str, Tuple[Any, ...]], int]:
    return {}

def _impl__loop_variable_binder_ordinal(
    self,
    scope: Optional[Dict[Tuple[str, Tuple[Any, ...]], int]],
    role: str,
    varnode,
) -> int:
    if scope is None:
        return 0
    key = self._varnode_cache_key(varnode)
    if key is None:
        return 0
    role_key = str(role or "loop_variable")
    scoped_key = (role_key, key)
    if scoped_key not in scope:
        scope[scoped_key] = sum(
            1 for existing_role, _existing_key in scope
            if existing_role == role_key
        )
    return int(scope[scoped_key])

def _impl__varnode_matches_parameter(
    self,
    varnode,
    parameter: dict,
) -> bool:
    if not isinstance(parameter, dict):
        return False
    varnode = self._follow_passthrough_varnode(varnode)
    parameter_identities = self._parameter_identity_keys_from_descriptor(parameter)
    if not parameter_identities:
        return False

    varnode_storage = self._storage_info_from_varnode(varnode)
    storage_key = self._summary_storage_identity_key(varnode_storage)
    if storage_key is not None and ("parameter_storage", storage_key) in parameter_identities:
        return True

    high = getattr(varnode, "getHigh", lambda: None)()
    symbol_getter = getattr(high, "getSymbol", lambda: None)
    if callable(symbol_getter):
        try:
            symbol = symbol_getter()
            symbol_index = self._parameter_index_from_symbol(symbol)
            if symbol_index is not None and ("parameter_index", symbol_index) in parameter_identities:
                return True
        except Exception:
            pass
    expr = self._trace_varnode_expression(varnode)
    expr_identity = (
        parameter_identity_key_from_expression(expr)
        if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER
        else None
    )
    return bool(expr_identity is not None and expr_identity in parameter_identities)

def _impl__storage_info_from_varnode(self, varnode) -> Optional[StorageInfo]:
    getter = getattr(self.tracer, "_get_storage_info_from_varnode", None)
    if callable(getter):
        try:
            storage = getter(varnode)
            if isinstance(storage, StorageInfo):
                return storage
            if isinstance(storage, dict):
                return StorageInfo(**storage)
        except Exception:
            return None
    return None

def _impl__varnode_constant_value(
    self,
    varnode,
) -> Optional[int]:
    try:
        address = varnode.getAddress()
        if address is not None and address.getAddressSpace().getName() == "const":
            return int(varnode.getOffset())
    except Exception:
        pass
    expr = self._trace_varnode_expression(varnode)
    return self._raw_constant_value(expr)

def _impl__varnode_unsigned_constant_value(self, varnode) -> Optional[int]:
    value = self._varnode_constant_value(varnode)
    if value is None:
        return None
    return int(value)

def _impl__signed_varnode_constant_value(self, varnode) -> Optional[int]:
    value = self._varnode_constant_value(varnode)
    if value is None:
        return None
    try:
        bit_width = max(1, int(getattr(varnode, "getSize", lambda: 0)() or 0)) * 8
    except Exception:
        bit_width = 0
    if bit_width <= 0:
        return int(value)
    modulus = 1 << bit_width
    signed = int(value) % modulus
    if signed >= (1 << (bit_width - 1)):
        signed -= modulus
    return signed

def _impl__float_add_has_zero_other_operand(self, op, current_varnode) -> bool:
    if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
        return False
    left = self._follow_passthrough_varnode(op.getInput(0))
    right = self._follow_passthrough_varnode(op.getInput(1))
    if self._same_varnode_value(left, current_varnode):
        return self._varnode_constant_value(right) == 0
    if self._same_varnode_value(right, current_varnode):
        return self._varnode_constant_value(left) == 0
    return False

def _impl__float_div_is_average_projection(self, op, current_varnode, count_param: dict) -> bool:
    if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
        return False
    numerator = self._follow_passthrough_varnode(op.getInput(0))
    if not self._same_varnode_value(numerator, current_varnode):
        return False
    denominator = self._follow_passthrough_varnode(op.getInput(1))
    denominator_def = getattr(denominator, "getDef", lambda: None)()
    if denominator_def is None or getattr(denominator_def, "getMnemonic", lambda: None)() != "INT2FLOAT":
        return False
    if int(getattr(denominator_def, "getNumInputs", lambda: 0)() or 0) < 1:
        return False
    return self._varnode_matches_parameter(denominator_def.getInput(0), count_param)

def _impl__high_varnode_instances(self, varnode) -> Tuple[object, ...]:
    instances = [varnode]
    high = getattr(varnode, "getHigh", lambda: None)()
    if high is None:
        return tuple(instances)
    representative = getattr(high, "getRepresentative", lambda: None)()
    if representative is not None:
        instances.append(representative)
    high_instances = getattr(high, "getInstances", lambda: None)()
    if high_instances is not None:
        try:
            iterator = iter(high_instances)
        except TypeError:
            iterator = None
        if iterator is not None:
            instances.extend(instance for instance in iterator if instance is not None)
        else:
            try:
                count = int(getattr(high_instances, "length", 0) or 0)
            except Exception:
                count = 0
            for index in range(count):
                try:
                    instance = high_instances[index]
                except Exception:
                    continue
                if instance is not None:
                    instances.append(instance)
    deduped: List[object] = []
    seen = set()
    for instance in instances:
        instance_id = id(instance)
        if instance_id in seen:
            continue
        seen.add(instance_id)
        deduped.append(instance)
    return tuple(deduped)

def _impl__infer_loop_parameter_pair(self, analysis) -> Optional[Tuple[str, str]]:
    candidates: Counter[Tuple[str, str]] = Counter()
    all_conditions: List[Condition] = []
    for ret in analysis.returns or []:
        all_conditions.extend(ret.conditions or [])
    effect_summary = getattr(analysis, "effect_summary", None)
    if effect_summary is not None:
        for effect in effect_summary.effects or []:
            all_conditions.extend(effect.conditions or [])

    for cond in all_conditions:
        pair = self._match_less_parameter_pair(cond)
        if pair is not None:
            candidates[pair] += 1
    if not candidates:
        return None
    return candidates.most_common(1)[0][0]

def _impl__match_less_parameter_pair(self, condition: Condition) -> Optional[Tuple[str, str]]:
    relation = self._parameter_comparison_relation(condition)
    if relation is None:
        return None
    left_name, relation_name, right_name = relation
    if relation_name == "<":
        return left_name, right_name
    if relation_name == ">":
        return right_name, left_name
    return None

def _impl__parameter_name_from_expr(self, expr: Optional[Expression]) -> Optional[str]:
    if expr is None:
        return None
    if expr.expr_type == ExpressionType.PARAMETER and expr.name:
        return expr.name
    normalized = self._normalize_counter_view(expr, getattr(expr, "name", None) or "")
    if normalized is not None and normalized[0].name:
        return normalized[0].name
    return None

def _impl__param_expr(self, analysis, name: str) -> Expression:
    for param in analysis.parameters or []:
        if param.get("name") != name:
            continue
        return Expression.parameter(
            name,
            index=int(param.get("index", 0)),
            data_type=param.get("data_type"),
            data_type_obj=param.get("data_type_obj"),
            size=int(param.get("size", 4) or 4),
        )
    return Expression.parameter(name, size=4)

def _impl__find_no_loop_base_case(
    self,
    returns: Sequence[ReturnInfo],
    pointer_name: str,
    start_name: str,
    limit_name: str,
    *,
    require_pointer_nonnull: bool,
) -> Optional[ReturnInfo]:
    for ret in returns:
        if self._return_is_constant(ret):
            continue
        has_nonnull = any(self._condition_is_pointer_nonnull(cond, pointer_name) for cond in ret.conditions or [])
        has_not_less = any(self._condition_is_not_less(cond, start_name, limit_name) for cond in ret.conditions or [])
        if has_not_less and (has_nonnull or not require_pointer_nonnull):
            return ret
    return None

def _impl__find_one_step_cases(
    self,
    returns: Sequence[ReturnInfo],
    pointer_name: str,
    start_name: str,
    limit_name: str,
    *,
    require_pointer_nonnull: bool,
) -> Optional[Tuple[ReturnInfo, ReturnInfo]]:
    even_case = None
    odd_case = None
    for ret in returns:
        conditions = ret.conditions or []
        has_nonnull = any(self._condition_is_pointer_nonnull(cond, pointer_name) for cond in conditions)
        has_loop = any(self._condition_is_less(cond, start_name, limit_name) for cond in conditions)
        has_one_step = any(self._condition_is_step_equality(cond, start_name, limit_name) for cond in conditions)
        if not (has_loop and has_one_step and (has_nonnull or not require_pointer_nonnull)):
            continue
        parity = self._extract_counter_parity(conditions, start_name)
        if parity is True:
            even_case = ret
        elif parity is False:
            odd_case = ret
    if even_case is None or odd_case is None:
        return None
    return even_case, odd_case
