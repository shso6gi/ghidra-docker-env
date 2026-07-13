"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.analyzer``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    Condition,
    ConditionSimplifier,
    Expression,
)
from ...model import CallTargetRef

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl__filter_noreturn_return_path_entries(
    self,
    path_entries,
    tracer: PcodeTracer,
    return_op,
):
    if not path_entries:
        return path_entries, []

    filtered = []
    blocked_conditions: List[List[Condition]] = []
    for block_path, conditions in path_entries:
        noreturn_op = None
        for block_info in block_path:
            for candidate_op in getattr(block_info, "pcode_ops", []) or []:
                if self._pcode_ops_match(candidate_op, return_op):
                    break
                if self._is_noreturn_control_transfer_op(candidate_op, tracer):
                    noreturn_op = candidate_op
                    break
            if noreturn_op is not None:
                break
        if noreturn_op is not None:
            blocked_conditions.append(list(conditions))
            targets = tuple(self._resolve_object_centric_transfer_targets(noreturn_op, tracer) or ())
            noreturn_contract_keys = []
            for target_ref in targets:
                target_function = self._resolve_function_from_call_target_ref(target_ref)
                if target_function is None or not self._function_has_no_return(target_function):
                    noreturn_contract_keys = []
                    break
                noreturn_contract_keys.append((
                    "resolved_noreturn_function_v1",
                    target_ref.stable_key(),
                    CallTargetRef.from_function(target_function).stable_key(),
                ))
            argument_keys = []
            try:
                for input_index in range(1, int(noreturn_op.getNumInputs())):
                    expression = tracer.trace_varnode(noreturn_op.getInput(input_index), use_cache=False)
                    argument_keys.append(expression.structural_key())
            except Exception:
                argument_keys = []
            site = self._describe_pcode_site(noreturn_op, "unknown")
            self._current_noreturn_terminal_observations.append({
                "pcode_op_ref": site.get("pcode_op_ref"),
                "target_refs": targets,
                "noreturn_contract_keys": tuple(noreturn_contract_keys),
                "argument_keys": tuple(argument_keys),
                "conditions": tuple(conditions or ()),
            })
            if self.debug:
                cond_strs = [
                    ConditionSimplifier.get_simplified_condition_string(c)
                    for c in conditions
                ]
                block_indexes = [getattr(block, "index", "?") for block in block_path]
                self._debug_print(
                    "Pruned RETURN path that contains a noreturn call: "
                    f"blocks={block_indexes}, conditions={cond_strs}"
                )
            continue
        filtered.append((block_path, conditions))

    return filtered, blocked_conditions

def _impl__is_noreturn_control_transfer_op(self, pcode_op, tracer: PcodeTracer) -> bool:
    if pcode_op is None or pcode_op.getMnemonic() not in {"CALL", "CALLIND", "BRANCHIND"}:
        return False

    resolved_targets = self._resolve_object_centric_transfer_targets(pcode_op, tracer)
    if self.debug and not resolved_targets:
        try:
            traced_target = tracer.trace_varnode(pcode_op.getInput(0), use_cache=False)
            traced_summary = traced_target.to_string()
        except Exception:
            traced_summary = "<unavailable>"
        self._debug_print(
            f"CALL noreturn resolution failed to resolve targets for {pcode_op.getMnemonic()} "
            f"target={traced_summary}"
        )

    if not resolved_targets:
        return False

    resolved_functions = []
    for target_ref in resolved_targets:
        target_function = self._resolve_function_from_call_target_ref(target_ref)
        if target_function is None:
            if self.debug:
                self._debug_print(
                    "Control-transfer target stayed unresolved for noreturn pruning: "
                    f"{target_ref.display_name()}"
                )
            return False
        resolved_functions.append((target_ref, target_function))

    if resolved_functions and all(self._function_has_no_return(function) for _target_ref, function in resolved_functions):
        if self.debug:
            names = ", ".join(target_ref.display_name() for target_ref, _function in resolved_functions)
            self._debug_print(
                "Detected noreturn control transfer via object-centric resolution: "
                f"{names}"
            )
        return True
    return False

def _impl__recover_implicit_return_from_block_paths(
    self,
    return_op,
    address: str,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    return_index: int,
    path_entries,
    active_functions: Optional[Set[Tuple[Any, ...]]] = None,
    current_function=None,
    site_metadata: Optional[Dict[str, Optional[object]]] = None,
) -> Optional[List[ReturnInfo]]:
    """RETURN block 以前の path 上にある返り値レジスタ更新から暗黙 return を復元する。"""
    normalized_entries = self._coerce_block_path_entries(path_entries)
    if not normalized_entries:
        return None

    recovered_results: List[ReturnInfo] = []
    unresolved_paths: List[int] = []

    for path_idx, (block_path, conditions) in enumerate(normalized_entries):
        tracked_sources = self._resolve_implicit_return_tracked_values(
            return_op,
            tracer,
            condition_tracker,
            current_function,
            block_path=block_path,
        )
        if not tracked_sources:
            unresolved_paths.append(path_idx)
            continue

        path_results = self._recover_return_infos_from_tracked_sources(
            tracked_sources,
            address,
            tracer,
            condition_tracker,
            list(conditions),
            return_index * 1000 + path_idx * 100,
            all_path_conditions=[list(conditions)],
            active_functions=active_functions,
            current_function=current_function,
            site_metadata=site_metadata,
        )
        if not path_results:
            unresolved_paths.append(path_idx)
            continue

        recovered_results.extend(path_results)

    if recovered_results and not unresolved_paths:
        if self.debug:
            self._debug_print(
                "Implicit return path recovery succeeded for all RETURN path variants"
            )
        return self._merge_equivalent_return_infos(recovered_results)

    if self.debug and unresolved_paths:
        self._debug_print(
            "Implicit return path recovery could not resolve terminal producer on "
            f"path(s) {unresolved_paths}"
        )
    return None

def _impl__select_path_specific_return_source(
    self,
    candidate,
    block_path,
    condition_tracker: Optional[ConditionTracker] = None,
    path_conditions: Optional[List[Condition]] = None,
):
    """PHI 出力をそのまま返す代わりに、実際の predecessor に対応する入力へ絞る。"""
    if candidate is None or not block_path or len(block_path) < 2:
        return candidate

    normalized_path = [getattr(entry, "block", entry) for entry in block_path]
    selected = candidate
    max_refinements = max(1, len(normalized_path))

    for _ in range(max_refinements):
        def_op = getattr(selected, "getDef", lambda: None)()
        if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
            break

        phi_parent = getattr(def_op, "getParent", lambda: None)()
        phi_index = self._find_block_index_on_path(normalized_path, phi_parent)
        if phi_index is None or phi_index <= 0:
            break

        predecessor = normalized_path[phi_index - 1]
        refined = self._select_multiequal_input_for_return_path(
            multiequal_op=def_op,
            predecessor=predecessor,
            condition_tracker=condition_tracker,
            path_conditions=path_conditions,
        )
        if refined is None or refined is selected:
            break

        if self.debug:
            self._debug_print(
                "Refined implicit return PHI source to predecessor-specific input "
                f"{refined}"
            )
        selected = refined

    return selected

def _impl__find_block_index_on_path(self, block_path, target_block) -> Optional[int]:
    if target_block is None:
        return None

    for index in range(len(block_path) - 1, -1, -1):
        if self._blocks_match(block_path[index], target_block):
            return index
    return None

def _impl__select_multiequal_input_for_return_path(
    self,
    multiequal_op,
    predecessor,
    condition_tracker: Optional[ConditionTracker] = None,
    path_conditions: Optional[List[Condition]] = None,
):
    phi_parent = getattr(multiequal_op, "getParent", lambda: None)()
    get_in_size = getattr(phi_parent, "getInSize", None)
    get_in = getattr(phi_parent, "getIn", None)
    if not callable(get_in_size) or not callable(get_in):
        return None

    current_condition_keys = self._build_condition_signature_set(path_conditions or [])
    exact_matches = []
    best_input = None
    best_score: Optional[Tuple[int, int, int]] = None
    exact_best_input = None
    exact_best_score: Optional[Tuple[int, int, int]] = None

    try:
        for index in range(int(get_in_size())):
            incoming = get_in(index)
            candidate_input = multiequal_op.getInput(index)
            if candidate_input is None:
                continue
            is_exact_match = self._blocks_match(incoming, predecessor)
            if is_exact_match:
                exact_matches.append(candidate_input)
            score = self._score_multiequal_incoming_for_return_path(
                incoming,
                predecessor,
                condition_tracker,
                current_condition_keys,
            )
            if is_exact_match and (exact_best_score is None or score > exact_best_score):
                exact_best_score = score
                exact_best_input = candidate_input
            if best_score is None or score > best_score:
                best_score = score
                best_input = candidate_input
    except Exception:
        return None

    if exact_best_input is not None:
        if (
            best_input is not None
            and best_input is not exact_best_input
            and best_score is not None
            and exact_best_score is not None
            and bool(current_condition_keys)
            and best_score[0] == len(current_condition_keys)
            and best_score[0] > exact_best_score[0]
        ):
            return best_input
        return exact_best_input
    if len(exact_matches) == 1:
        return exact_matches[0]
    if exact_matches:
        return exact_matches[0]

    return best_input

def _impl__score_multiequal_incoming_for_return_path(
    self,
    incoming_block,
    predecessor,
    condition_tracker: Optional[ConditionTracker],
    current_condition_keys: Set[object],
) -> Tuple[int, int, int]:
    predecessor_match = 1 if self._blocks_match(incoming_block, predecessor) else 0
    if condition_tracker is None or not current_condition_keys:
        return (0, predecessor_match, 0)

    block_info = condition_tracker.get_block_by_hash(incoming_block)
    if block_info is None:
        return (0, predecessor_match, 0)

    incoming_conditions = condition_tracker.get_path_conditions_to_block(block_info)
    incoming_keys = self._build_condition_signature_set(incoming_conditions)
    if not incoming_keys:
        return (0, predecessor_match, 0)

    matched = len(incoming_keys & current_condition_keys)
    specificity = len(incoming_keys)
    return (matched, predecessor_match, specificity)

def _impl__blocks_match(self, lhs, rhs) -> bool:
    if lhs is rhs:
        return True
    try:
        if lhs == rhs:
            return True
    except Exception:
        pass

    lhs_start = self._get_block_start_address(lhs)
    rhs_start = self._get_block_start_address(rhs)
    if lhs_start is not None and rhs_start is not None:
        return lhs_start == rhs_start

    return False

def _impl__get_block_start_address(self, block) -> Optional[str]:
    get_start = getattr(block, "getStart", None)
    if not callable(get_start):
        return None
    try:
        start = get_start()
    except Exception:
        return None
    if start is None:
        return None
    return str(start)

def _impl__path_condition_sets_union_condition(
    self,
    path_condition_sets: Sequence[Sequence[Condition]],
) -> Optional[Condition]:
    disjuncts: List[Expression] = []
    for conditions in path_condition_sets or ():
        conjunct = self._condition_set_conjunction_expression(conditions)
        if conjunct is None:
            return None
        disjuncts.append(conjunct)
    if len(disjuncts) <= 1:
        return None
    union_expr = disjuncts[0]
    for disjunct in disjuncts[1:]:
        union_expr = Expression.binary_op("BOOL_OR", union_expr, disjunct)
        union_expr.size = 1
    return Condition(union_expr)

def _impl__matches_blocked_return_path_conditions(
    self,
    conditions: List[Condition],
) -> bool:
    blocked_sets = getattr(self, "_current_blocked_return_path_conditions", None) or []
    if not blocked_sets:
        return False

    condition_keys = self._build_condition_signature_set(conditions)
    if not condition_keys:
        return False

    for blocked_conditions in blocked_sets:
        blocked_keys = self._build_condition_signature_set(blocked_conditions)
        if blocked_keys and blocked_keys.issubset(condition_keys):
            return True
    return False

def _impl__split_branch_index(
    self,
    branch_index: Optional[int],
    original_index: int,
    split_index: int,
) -> Optional[int]:
    seed = branch_index if branch_index is not None else (original_index + 1) * 1000
    return seed * 10 + split_index

def _impl__min_branch_index(
    self,
    left: Optional[int],
    right: Optional[int],
) -> Optional[int]:
    if left is None:
        return right
    if right is None:
        return left
    return min(left, right)
