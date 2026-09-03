"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.returns.analyzer``."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Sequence, Set, Tuple
from scripts.function_tracer_pcode.analysis.returns._shared import (
    CallTargetRef,
    Condition,
    ConditionSimplifier,
    ConditionTracker,
    DivergenceOutcome,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    PcodeTracer,
    ReturnInfo,
    ReturnOutcome,
    UnknownOutcome,
    _TrackedReturnValue,
    _expression_contains_observed_loads,
    _expressions_equivalent,
    build_switch_dispatch_summaries,
    cast,
    expression_contains_post_state_reads,
)
from scripts.function_tracer_pcode.analysis.returns._api import StructuralRecurrenceSummarizer

def _impl__check_condition_coverage(self, analysis: FunctionReturnAnalysis):
    """
    条件カバレッジの簡易チェック

    各パラメータについて、正・負・ゼロのケースが存在するかをヒューリスティックに確認
    """
    if not self.debug or not analysis.returns:
        return

    self._debug_print("Condition coverage check:")

    # パラメータ名を収集
    param_names = [p.get('name', f'param_{i}') for i, p in enumerate(analysis.parameters)]

    if not param_names:
        return

    # 各パラメータについて、どのような条件が存在するか確認
    for param_name in param_names:
        has_zero_check = False
        has_positive_check = False
        has_negative_check = False
        param_referenced = False

        for ret_info in analysis.returns:
            for cond in ret_info.conditions:
                if not self._condition_mentions_param(cond, param_name):
                    continue
                param_referenced = True
                is_zero, is_pos, is_neg = self._classify_param_condition(cond, param_name)
                has_zero_check = has_zero_check or is_zero
                has_positive_check = has_positive_check or is_pos
                has_negative_check = has_negative_check or is_neg

        if not param_referenced:
            self._debug_print(f"  {param_name}: not referenced in conditions")
            continue

        coverage_info = []
        if has_zero_check:
            coverage_info.append("zero")
        if has_positive_check:
            coverage_info.append("positive")
        if has_negative_check:
            coverage_info.append("negative")

        if coverage_info:
            self._debug_print(f"  {param_name}: {', '.join(coverage_info)} checks found", 1)
        else:
            self._debug_print(f"  {param_name}: no explicit checks", 1)

def _impl__phase1_direct_branch_escapes_function_body(self, instruction, body) -> bool:
    target = self._resolve_local_branch_target(instruction)
    if target is None:
        return True
    return not self._phase1_body_contains_address(body, target)

def _impl__block_successors(self, block) -> Tuple[Any, ...]:
    successors = []
    out_size = int(getattr(block, "getOutSize", lambda: 0)() or 0)
    for index in range(out_size):
        successor = getattr(block, "getOut", lambda _idx: None)(index)
        if successor is not None:
            successors.append(successor)
    return tuple(successors)

def _impl__block_predecessor_count(self, block) -> int:
    return int(getattr(block, "getInSize", lambda: 0)() or 0)

def _impl__block_has_return_op(self, block) -> bool:
    return any(getattr(op, "getMnemonic", lambda: None)() == "RETURN" for op in self._iter_high_block_ops(block))

def _impl__block_writes_outcome_guard_state(self, block) -> bool:
    for op in self._iter_high_block_ops(block):
        if bool(getattr(op, "writes_guard_state", False)):
            return True
    return False

def _impl__direct_cbranch_successor_relation(self, cbranch, block, successor) -> Optional[str]:
    target_keys = self._cbranch_direct_target_keys(cbranch, block)
    if not target_keys:
        return None
    successor_keys = self._block_start_address_keys(successor)
    if successor_keys & target_keys:
        return "true"

    successors = self._block_successors(block)
    if len(successors) != 2:
        return None
    target_successors = [
        candidate
        for candidate in successors
        if self._block_start_address_keys(candidate) & target_keys
    ]
    if len(target_successors) != 1:
        return None
    if self._same_high_block(target_successors[0], successor):
        return "true"
    return "false"

def _impl__block_start_address_keys(self, block) -> Set[Tuple[str, int]]:
    keys: Set[Tuple[str, int]] = set()
    for getter_name in ("getStart", "getMinAddress"):
        try:
            value = getattr(block, getter_name, lambda: None)()
        except Exception:
            value = None
        keys.update(self._address_like_keys(value))
    return keys

def _impl__block_start_address_spaces(self, block) -> Set[str]:
    return {
        space
        for space, _offset in self._block_start_address_keys(block)
        if space
    }

def _impl__first_high_block_cbranch(self, block):
    for op in self._iter_high_block_ops(block):
        if getattr(op, "getMnemonic", lambda: None)() == "CBRANCH":
            return op
    return None

def _impl__same_high_block(self, left, right) -> bool:
    if left is right:
        return True
    try:
        if left == right:
            return True
    except Exception:
        pass
    return self._block_debug_key(left) == self._block_debug_key(right)

def _impl__block_debug_key(self, block) -> Any:
    try:
        index = getattr(block, "getIndex", lambda: None)()
        if index is not None:
            return int(index)
    except Exception:
        pass
    try:
        start = getattr(block, "getStart", lambda: None)()
        if start is not None:
            return str(start)
    except Exception:
        pass
    return f"block@{id(block):x}"


def _current_cfg_applicability_surface(self, high_function) -> Tuple[Tuple[Any, ...], Tuple[Tuple[Any, Any], ...]]:
    blocks = tuple(self._iter_high_basic_blocks(high_function))
    block_keys = tuple(sorted((self._block_debug_key(block) for block in blocks), key=repr))
    edge_keys = tuple(sorted((
        (self._block_debug_key(block), self._block_debug_key(successor))
        for block in blocks
        for successor in self._block_successors(block)
    ), key=repr))
    return block_keys, edge_keys

def _impl__try_apply_branch_guarded_while_outcomes(
    self,
    high_function,
    analysis: FunctionReturnAnalysis,
) -> bool:
    if len(getattr(analysis, "parameters", []) or []) != 2:
        self._debug_print("Outcome branch-guarded while summary declined: expected two parameters")
        return False
    if getattr(analysis, "deferred_calls", None):
        self._debug_print("Outcome branch-guarded while summary declined: deferred calls present")
        return False
    if self._high_function_has_forbidden_control_outcome_ops(high_function, allow_call=False):
        self._debug_print("Outcome branch-guarded while summary declined: forbidden control/effect op present")
        return False
    if self._high_function_cbranch_count(high_function) < 2:
        self._debug_print("Outcome branch-guarded while summary declined: expected two control guards")
        return False
    if not any(
        self._expression_contains_phi_circular(ret.value)
        or self._return_info_candidate_phi_origin_keys(ret)
        for ret in analysis.returns or ()
    ):
        self._debug_print("Outcome branch-guarded while summary declined: no phi_circular return or candidate provenance")
        return False

    role_params = self._infer_branch_guarded_while_role_parameters(analysis)
    if role_params is None:
        self._debug_print("Outcome branch-guarded while summary declined: role parameters unavailable")
        return False
    t_param, c_param = role_params
    if t_param is None or c_param is None:
        self._debug_print("Outcome branch-guarded while summary declined: parameter expression unavailable")
        return False
    t_positive = self._signed_positive_condition(t_param)
    c_positive = self._signed_positive_condition(c_param)
    c_nonpositive = c_positive.negate()
    t_nonpositive = t_positive.negate()

    zero_ret, initial_c_ret = self._find_branch_guarded_while_return_partition(
        analysis,
        high_function=high_function,
        c_param=c_param,
        c_nonpositive=c_nonpositive,
        c_positive=c_positive,
        t_positive=t_positive,
    )
    if zero_ret is None or initial_c_ret is None:
        self._debug_print("Outcome branch-guarded while summary declined: return partition/value proof unavailable")
        return False
    divergence_proof = self._prove_branch_guarded_while_nonprogress_must_diverge(
        high_function,
        invariant_conditions=(c_positive, t_nonpositive),
    )
    if divergence_proof is None:
        divergence_proof = self._prove_branch_guarded_structural_nonprogress_must_diverge(
            high_function,
            analysis=analysis,
            initial_c_ret=initial_c_ret,
            invariant_conditions=(c_positive, t_nonpositive),
        )
    analysis.returns = [zero_ret, initial_c_ret]
    analysis.return_outcomes = (
        ReturnOutcome(guard=tuple(zero_ret.conditions), value=zero_ret.value, provenance={"source": "branch_guarded_affine_recurrence"}, return_info=zero_ret),
        ReturnOutcome(guard=tuple(initial_c_ret.conditions), value=initial_c_ret.value, provenance={"source": "branch_guarded_affine_recurrence"}, return_info=initial_c_ret),
    )
    if divergence_proof is not None:
        analysis.divergence_outcomes = (
            DivergenceOutcome(
                guard=(c_positive, t_nonpositive),
                proof=divergence_proof,
            ),
        )
        analysis.unknown_outcomes = ()
        if "outcome_partition_proved_branch_guarded_while_divergence" not in analysis.analysis_notes:
            analysis.analysis_notes.append("outcome_partition_proved_branch_guarded_while_divergence")
    else:
        analysis.divergence_outcomes = ()
        analysis.unknown_outcomes = (
            UnknownOutcome(
                guard=(c_positive, t_nonpositive),
                reason="branch_guarded_recurrence_proof_missing",
                evidence={
                    "candidate_rule": "branch_guarded_loop_invariant_nonprogress",
                    "state_reference": "inferred_state_count_parameter",
                    "state_parameter": getattr(c_param, "name", None) or getattr(c_param, "value", None),
                    "forbidden_ops_absent": True,
                    "loop_has_cfg_cycle": self._high_function_has_cfg_cycle(high_function),
                    "has_control_guards": True,
                    "missing_proof": "scc_exit_impossibility_guard_preservation_and_affine_transition",
                },
            ),
        )
        if "outcome_partition_unknown_branch_guarded_while" not in analysis.analysis_notes:
            analysis.analysis_notes.append("outcome_partition_unknown_branch_guarded_while")
    return True

def _impl__infer_branch_guarded_while_role_parameters(
    self,
    analysis: FunctionReturnAnalysis,
) -> Optional[Tuple[Expression, Expression]]:
    params = tuple(getattr(analysis, "parameters", ()) or ())
    candidate_params = []
    for index in range(len(params)):
        param = self._parameter_expression(analysis, index)
        if param is not None:
            candidate_params.append(param)
    if len(candidate_params) < 2:
        return None

    returns = tuple(getattr(analysis, "returns", ()) or ())
    for c_param in candidate_params:
        c_positive = self._signed_positive_condition(c_param)
        c_nonpositive = c_positive.negate()
        zero_seed = None
        for ret in returns:
            if self._constant_int_value(getattr(ret, "value", None)) != 0:
                continue
            conditions = tuple(getattr(ret, "conditions", ()) or ())
            if self._conditions_equivalent(conditions, [c_nonpositive]) or (
                len(conditions) == 1
                and self._condition_is_signed_nonpositive_of_param(conditions[0], c_param)
            ):
                zero_seed = ret
                break
        if zero_seed is None:
            continue
        for t_param in candidate_params:
            if self._expressions_same_key(t_param, c_param):
                continue
            t_positive = self._signed_positive_condition(t_param)
            target_conditions = (c_positive, t_positive)
            if any(
                self._conditions_overlap(tuple(getattr(ret, "conditions", ()) or ()), target_conditions)
                and (
                    self._expression_is_same_parameter_ignoring_subpiece(getattr(ret, "value", None), c_param)
                    or self._expressions_equal_under_conditions_smt(
                        getattr(ret, "value", None),
                        c_param,
                        tuple(target_conditions) + tuple(getattr(ret, "conditions", ()) or ()),
                        getattr(analysis, "parameters", ()) or (),
                    )
                    or self._branch_guarded_affine_singleton_base_anchor_matches(
                        getattr(ret, "value", None),
                        tuple(getattr(ret, "conditions", ()) or ()),
                        c_param,
                        target_conditions,
                    )
                    or self._branch_guarded_affine_phi_step(getattr(ret, "value", None)) is not None
                    or self._return_info_candidate_phi_origin_keys(ret)
                )
                for ret in returns
            ):
                return t_param, c_param
    return None

def _impl__prove_branch_guarded_structural_nonprogress_must_diverge(
    self,
    high_function,
    *,
    analysis: Optional[FunctionReturnAnalysis] = None,
    initial_c_ret: ReturnInfo,
    invariant_conditions: Sequence[Condition],
) -> Optional[Dict[str, Any]]:
    if high_function is None:
        return None
    structural_proof = self._branch_guarded_structural_proof_from_return(initial_c_ret)
    if structural_proof is None:
        return None
    if not self._validate_branch_guarded_structural_proof(
        high_function,
        structural_proof=structural_proof,
        analysis=analysis,
        initial_c_ret=initial_c_ret,
        invariant_conditions=invariant_conditions,
    ):
        return None
    nonprogress_backedges = self._tuple_field_from_structural_proof(
        structural_proof,
        "nonprogress_backedges",
    )
    conditional_progress_backedges = self._tuple_field_from_structural_proof(
        structural_proof,
        "conditional_progress_backedges",
    )
    conditional_progress_guard_keys = self._conditional_progress_guard_keys_from_structural_proof(
        structural_proof,
    )
    conditional_progress_guards_blocked = self._conditional_progress_guards_contradict_invariant(
        conditional_progress_guard_keys,
        target_conditions=tuple(getattr(initial_c_ret, "conditions", ()) or ()),
        invariant_conditions=tuple(invariant_conditions or ()),
    )
    if not nonprogress_backedges and not (conditional_progress_backedges and conditional_progress_guards_blocked):
        return None
    if not self._high_function_has_cfg_cycle(high_function):
        return None
    if self._high_function_has_forbidden_control_outcome_ops(high_function, allow_call=False):
        return None
    return {
        "proof_kind": "branch_guarded_structural_nonprogress_must_diverge",
        "candidate_rule": "branch_guarded_loop_invariant_nonprogress",
        "invariant": [condition.to_string() for condition in invariant_conditions or ()],
        "structural_recurrence_proof": structural_proof,
        "nonprogress_backedges": tuple(nonprogress_backedges),
        "conditional_progress_backedges": tuple(conditional_progress_backedges),
        "conditional_progress_guard_keys": tuple(sorted(conditional_progress_guard_keys.items(), key=repr)),
        "conditional_progress_guard_negated_by_invariant": bool(conditional_progress_guards_blocked),
        "state_preservation": "state_phi_nonprogress_backedge_identity",
        "accumulator_preservation": "accumulator_phi_nonprogress_backedge_identity",
        "loop_has_cfg_cycle": True,
        "forbidden_control_effect_ops_absent": True,
        "cfg_applicability_surface": _current_cfg_applicability_surface(self, high_function),
    }

def _impl__branch_guarded_structural_proof_from_return(
    self,
    ret: ReturnInfo,
) -> Optional[Tuple[Any, ...]]:
    source_key = getattr(ret, "summary_candidate_source_key", None)
    return self._find_branch_guarded_structural_proof_tuple(source_key)

def _impl__find_branch_guarded_structural_proof_tuple(
    self,
    value,
) -> Optional[Tuple[Any, ...]]:
    if not isinstance(value, tuple):
        return None
    if value and value[0] == "branch_guarded_affine_unit_count_structural_proof":
        return value
    for item in value:
        found = self._find_branch_guarded_structural_proof_tuple(item)
        if found is not None:
            return found
    return None

def _impl__validate_branch_guarded_structural_proof(
    self,
    high_function,
    *,
    structural_proof: Tuple[Any, ...],
    analysis: Optional[FunctionReturnAnalysis],
    initial_c_ret: ReturnInfo,
    invariant_conditions: Sequence[Condition],
) -> bool:
    if high_function is None:
        return False
    if self._field_value_from_structural_proof(structural_proof, "schema_version") != 1:
        return False
    if analysis is not None and self._field_value_from_structural_proof(
        structural_proof,
        "function",
    ) != getattr(analysis, "function_name", None):
        return False
    proof_target_keys = self._tuple_field_from_structural_proof(
        structural_proof,
        "target_guard_keys",
    )
    current_target_keys = tuple(
        sorted(
            (self._condition_identity_key(condition) for condition in tuple(getattr(initial_c_ret, "conditions", ()) or ())),
            key=repr,
        )
    )
    if proof_target_keys != current_target_keys:
        return False
    acc_phi_key = self._field_value_from_structural_proof(structural_proof, "acc_phi")
    state_phi_key = self._field_value_from_structural_proof(structural_proof, "state_phi")
    if not isinstance(acc_phi_key, tuple) or not isinstance(state_phi_key, tuple):
        return False
    try:
        tracer = self._make_tracer(high_function)
    except Exception:
        return False
    summarizer = StructuralRecurrenceSummarizer(
        tracer,
        debug=False,
        enable_completed_recovery_proofs=self.enable_completed_recovery_proofs,
    )
    acc_phi = None
    state_phi = None
    header_block = None
    for block in summarizer._iter_basic_blocks(high_function):
        for op in summarizer._iter_block_ops(block):
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            op_key = self._pcode_op_stable_key(op)
            if op_key == acc_phi_key:
                acc_phi = op
                header_block = block
            if op_key == state_phi_key:
                state_phi = op
                header_block = block if header_block is None else header_block
    if acc_phi is None or state_phi is None or header_block is None:
        return False
    acc_parent = getattr(acc_phi, "getParent", lambda: None)()
    state_parent = getattr(state_phi, "getParent", lambda: None)()
    if acc_parent is None or state_parent is None:
        return False
    if self._block_debug_key(acc_parent) != self._block_debug_key(state_parent):
        return False
    header_block = acc_parent
    acc_indices = summarizer._state_loop_phi_indices(header_block, acc_phi)
    state_indices = summarizer._state_loop_phi_indices(header_block, state_phi)
    if acc_indices is None or state_indices is None:
        return False
    _acc_init_index, acc_backedge_indices = acc_indices
    _state_init_index, state_backedge_indices = state_indices
    if tuple(int(index) for index in acc_backedge_indices) != tuple(int(index) for index in state_backedge_indices):
        return False
    progress_backedges = set(int(index) for index in self._tuple_field_from_structural_proof(structural_proof, "progress_backedges"))
    nonprogress_backedges = set(int(index) for index in self._tuple_field_from_structural_proof(structural_proof, "nonprogress_backedges"))
    conditional_progress_backedges = set(int(index) for index in self._tuple_field_from_structural_proof(structural_proof, "conditional_progress_backedges"))
    expected_conditional_guard_keys = self._conditional_progress_guard_keys_from_structural_proof(
        structural_proof,
    )
    proof_backedges = progress_backedges | nonprogress_backedges
    if not progress_backedges:
        return False
    if conditional_progress_backedges:
        proof_backedges |= conditional_progress_backedges
    if proof_backedges != set(int(index) for index in acc_backedge_indices):
        return False
    target_conditions = tuple(getattr(initial_c_ret, "conditions", ()) or ())
    if conditional_progress_backedges and not expected_conditional_guard_keys:
        return False
    if conditional_progress_backedges and set(expected_conditional_guard_keys) != conditional_progress_backedges:
        return False
    if conditional_progress_backedges and not self._conditional_progress_guards_contradict_invariant(
        expected_conditional_guard_keys,
        target_conditions=target_conditions,
        invariant_conditions=tuple(invariant_conditions or ()),
    ):
        return False
    acc_output = getattr(acc_phi, "getOutput", lambda: None)()
    state_output = getattr(state_phi, "getOutput", lambda: None)()
    if acc_output is None or state_output is None:
        return False
    acc_placeholder = Expression.variable("__branch_guarded_acc", size=max(1, int(getattr(acc_output, "getSize", lambda: 4)() or 4)))
    state_placeholder = Expression.variable("__branch_guarded_state", size=max(1, int(getattr(state_output, "getSize", lambda: 4)() or 4)))
    for backedge_index in acc_backedge_indices:
        index = int(backedge_index)
        acc_expr = summarizer._build_pcode_expression(
            acc_phi.getInput(index),
            placeholders={acc_output: acc_placeholder},
        )
        state_expr = summarizer._build_pcode_expression(
            state_phi.getInput(index),
            placeholders={state_output: state_placeholder},
        )
        if index in conditional_progress_backedges:
            acc_guard_key = self._placeholder_plus_unit_condition_guard_key(
                acc_expr,
                acc_placeholder,
                target_conditions,
            )
            state_guard_key = self._placeholder_minus_one_unit_condition_guard_key(
                state_expr,
                state_placeholder,
                target_conditions,
            )
            if acc_guard_key is None or state_guard_key is None:
                return False
            if acc_guard_key != state_guard_key:
                return False
            if expected_conditional_guard_keys.get(index) != acc_guard_key:
                return False
            if index in nonprogress_backedges:
                if not (
                    self._expression_is_placeholder_plus_zero_under_conditions(
                        acc_expr,
                        acc_placeholder,
                        invariant_conditions,
                    )
                    or self._expressions_equal_under_conditions_smt(
                        acc_expr,
                        acc_placeholder,
                        tuple(invariant_conditions or ()),
                        getattr(analysis, "parameters", ()) or (),
                    )
                ):
                    return False
                if not (
                    self._expression_is_placeholder_plus_zero_under_conditions(
                        state_expr,
                        state_placeholder,
                        invariant_conditions,
                    )
                    or self._expressions_equal_under_conditions_smt(
                        state_expr,
                        state_placeholder,
                        tuple(invariant_conditions or ()),
                        getattr(analysis, "parameters", ()) or (),
                    )
                ):
                    return False
            continue
        if index in nonprogress_backedges:
            if not (
                self._expressions_same_key(acc_expr, acc_placeholder)
                or self._expression_is_placeholder_plus_zero_under_conditions(
                    acc_expr,
                    acc_placeholder,
                    invariant_conditions,
                )
                or self._expressions_equal_under_conditions_smt(
                    acc_expr,
                    acc_placeholder,
                    tuple(invariant_conditions or ()),
                    getattr(analysis, "parameters", ()) or (),
                )
            ):
                return False
            if not (
                self._expressions_same_key(state_expr, state_placeholder)
                or self._expression_is_placeholder_plus_zero_under_conditions(
                    state_expr,
                    state_placeholder,
                    invariant_conditions,
                )
                or self._expressions_equal_under_conditions_smt(
                    state_expr,
                    state_placeholder,
                    tuple(invariant_conditions or ()),
                    getattr(analysis, "parameters", ()) or (),
                )
            ):
                return False
            continue
        if index in progress_backedges:
            if not self._expression_is_placeholder_plus_one_under_conditions(
                acc_expr,
                acc_placeholder,
                target_conditions,
            ):
                return False
            if not self._expression_is_placeholder_minus_one_under_conditions(
                state_expr,
                state_placeholder,
                target_conditions,
            ):
                return False
            continue
        return False
    return self._state_phi_feeds_positive_loop_guard(
        high_function,
        summarizer=summarizer,
        header_block=header_block,
        backedge_indices=tuple(int(index) for index in state_backedge_indices),
        state_phi=state_phi,
        state_placeholder=state_placeholder,
        target_conditions=target_conditions,
        allow_latch_progress_guard=bool(conditional_progress_backedges),
    )

def _impl__find_branch_guarded_while_return_partition(
    self,
    analysis: FunctionReturnAnalysis,
    *,
    high_function,
    c_param: Expression,
    c_nonpositive: Condition,
    c_positive: Condition,
    t_positive: Condition,
) -> Tuple[Optional[ReturnInfo], Optional[ReturnInfo]]:
    zero_ret = None
    initial_c_ret = None
    for ret in getattr(analysis, "returns", []) or ():
        conditions = tuple(getattr(ret, "conditions", ()) or ())
        if zero_ret is None and self._constant_int_value(getattr(ret, "value", None)) == 0:
            if self._conditions_equivalent(conditions, [c_nonpositive]) or (
                len(conditions) == 1
                and self._condition_is_signed_nonpositive_of_param(conditions[0], c_param)
            ):
                zero_ret = ret
                continue
        if initial_c_ret is None and self._expression_is_same_parameter_ignoring_subpiece(
            getattr(ret, "value", None),
            c_param,
        ):
            if self._conditions_equivalent(conditions, [c_positive, t_positive]):
                initial_c_ret = ret
    if zero_ret is not None and initial_c_ret is None:
        initial_c_ret = self._synthesize_branch_guarded_affine_initial_count_return(
            high_function,
            analysis,
            c_param=c_param,
            c_positive=c_positive,
            t_positive=t_positive,
            zero_ret=zero_ret,
        )
    return zero_ret, initial_c_ret

def _impl__synthesize_branch_guarded_affine_initial_count_return(
    self,
    high_function,
    analysis: FunctionReturnAnalysis,
    *,
    c_param: Expression,
    c_positive: Condition,
    t_positive: Condition,
    zero_ret: ReturnInfo,
) -> Optional[ReturnInfo]:
    target_conditions = (c_positive, t_positive)
    candidate_returns = [
        ret
        for ret in tuple(getattr(analysis, "returns", ()) or ())
        if self._conditions_overlap(tuple(getattr(ret, "conditions", ()) or ()), target_conditions)
    ]
    if not candidate_returns:
        self._debug_print("Outcome branch-guarded affine proof declined: no target-overlapping returns")
        return None
    exact_base_returns: List[ReturnInfo] = []
    recursive_returns: List[Tuple[ReturnInfo, int]] = []
    ignored_artifacts: List[ReturnInfo] = []
    for ret in candidate_returns:
        conditions = tuple(getattr(ret, "conditions", ()) or ())
        value = getattr(ret, "value", None)
        if (
            self._expressions_equal_under_conditions_smt(
                value,
                c_param,
                tuple(target_conditions) + conditions,
                getattr(analysis, "parameters", ()) or (),
            )
            or self._branch_guarded_affine_singleton_base_anchor_matches(
                value,
                conditions,
                c_param,
                target_conditions,
            )
        ):
            exact_base_returns.append(ret)
            continue
        step = self._branch_guarded_affine_phi_step(value)
        implies_target = self._conditions_imply(conditions, target_conditions)
        if step is not None and implies_target:
            recursive_returns.append((ret, int(step)))
            continue
        if self.debug and (step is not None or self._expression_contains_phi_circular(value)):
            self._debug_print(
                "Outcome branch-guarded affine candidate skipped: "
                f"step={step}, implies_target={implies_target}, "
                f"value={getattr(value, 'to_string', lambda: value)()}, "
                f"conditions={[condition.to_string() for condition in conditions]}"
            )
        ignored_artifacts.append(ret)

    candidate_phi_origin_keys = tuple(
        sorted(
            {
                key
                for ret in candidate_returns
                for key in self._return_info_candidate_phi_origin_keys(ret)
            },
            key=repr,
        )
    )
    return_phi_origin_keys = tuple(
        sorted(
            {
                key
                for ret in candidate_returns
                for key in self._return_info_return_phi_origin_keys(ret)
            },
            key=repr,
        )
    )
    if not recursive_returns and not candidate_phi_origin_keys:
        self._debug_print("Outcome branch-guarded affine proof declined: recursive phi step missing")
        return None
    if recursive_returns:
        steps = {step for _ret, step in recursive_returns}
        if len(steps) != 1:
            self._debug_print(f"Outcome branch-guarded affine proof declined: mixed recursive steps {sorted(steps)}")
            return None
        step = next(iter(steps))
        if step <= 0 or step > 4:
            self._debug_print(f"Outcome branch-guarded affine proof declined: unsupported recursive step {step}")
            return None
    else:
        step = 1
    structural_proof = None
    exact_base_covers_target = bool(exact_base_returns) and self._return_conditions_cover_region(
        target_conditions,
        exact_base_returns,
    )
    if not exact_base_covers_target:
        structural_proof = self._prove_branch_guarded_affine_unit_count_recurrence(
            high_function,
            analysis=analysis,
            c_param=c_param,
            target_conditions=target_conditions,
            recursive_returns=tuple(ret for ret, _step in recursive_returns),
            candidate_phi_origin_keys=candidate_phi_origin_keys,
            return_phi_origin_keys=return_phi_origin_keys,
            nonprogress_conditions=(c_positive, t_positive.negate()),
            allow_latch_progress_guard=bool(exact_base_returns),
        )
        if structural_proof is None:
            if exact_base_returns:
                self._debug_print("Outcome branch-guarded affine proof declined: exact base returns do not cover target")
            else:
                self._debug_print("Outcome branch-guarded affine proof declined: exact base return missing")
            return None
        ignored_artifacts = [
            artifact for artifact in ignored_artifacts
            if not self._branch_guarded_artifact_is_imprecise_zero_seed(
                artifact,
                zero_ret=zero_ret,
                parameters=getattr(analysis, "parameters", ()) or (),
            )
            and not self._branch_guarded_artifact_is_structural_accumulator_seed_projection(
                artifact,
                recursive_returns=tuple(ret for ret, _step in recursive_returns),
                parameters=getattr(analysis, "parameters", ()) or (),
            )
        ]
        if ignored_artifacts and self.debug:
            for artifact in ignored_artifacts:
                self._debug_print(
                    "Outcome branch-guarded affine artifact retained: "
                    f"value={getattr(getattr(artifact, 'value', None), 'to_string', lambda: getattr(artifact, 'value', None))()}, "
                    f"conditions={[condition.to_string() for condition in tuple(getattr(artifact, 'conditions', ()) or ())]}, "
                    f"site={self._return_site_key(artifact)}"
                )
    proof_returns = list(exact_base_returns) + [ret for ret, _step in recursive_returns]
    if not self._branch_guarded_affine_ignored_artifacts_are_shadowed(
        ignored_artifacts,
        recursive_returns,
        getattr(analysis, "parameters", ()) or (),
    ):
        self._debug_print("Outcome branch-guarded affine proof declined: unshadowed target artifact return")
        return None

    anchor = recursive_returns[0][0] if recursive_returns else exact_base_returns[0]
    source_keys = tuple(
        self._return_info_summary_identity_key(ret)
        for ret in proof_returns
    )
    return ReturnInfo(
        address=str(getattr(anchor, "address", None) or getattr(analysis, "entry_point", None) or "outcome-summary"),
        value=c_param,
        conditions=list(target_conditions),
        branch_index=31_200,
        pcode_identity=getattr(anchor, "pcode_identity", None),
        pcode_order=getattr(anchor, "pcode_order", None),
        pcode_time=getattr(anchor, "pcode_time", None),
        pcode_op_ref=getattr(anchor, "pcode_op_ref", None),
        return_value_pcode_op_refs=tuple(getattr(anchor, "return_value_pcode_op_refs", ()) or ()),
        return_kind="outcome_summary",
        summary_candidate_id=("branch_guarded_affine_initial_count", getattr(analysis, "function_name", None)),
        summary_candidate_source_key=(
            "branch_guarded_affine_initial_count",
            ("step", step),
            ("candidate_phi_origin_keys", candidate_phi_origin_keys),
            ("return_phi_origin_keys", return_phi_origin_keys),
            ("structural_proof", structural_proof),
            ("sources", source_keys),
        ),
    )

def _impl__branch_guarded_artifact_is_imprecise_zero_seed(
    self,
    artifact: ReturnInfo,
    *,
    zero_ret: ReturnInfo,
    parameters: Sequence[Dict],
) -> bool:
    artifact_conditions = tuple(getattr(artifact, "conditions", ()) or ())
    zero_conditions = tuple(getattr(zero_ret, "conditions", ()) or ())
    if not self._expressions_equal_under_conditions_smt(
        getattr(artifact, "value", None),
        getattr(zero_ret, "value", None),
        artifact_conditions + zero_conditions,
        parameters,
    ):
        return False
    if not self._conditions_imply(zero_conditions, artifact_conditions):
        return False
    if self._conditions_imply(artifact_conditions, zero_conditions):
        return False
    return True

def _impl__branch_guarded_artifact_is_structural_accumulator_seed_projection(
    self,
    artifact: ReturnInfo,
    *,
    recursive_returns: Sequence[ReturnInfo],
    parameters: Sequence[Dict],
) -> bool:
    if self._constant_int_value(getattr(artifact, "value", None)) != 0:
        return False
    artifact_conditions = tuple(getattr(artifact, "conditions", ()) or ())
    artifact_site = self._return_site_key(artifact)
    for recursive in recursive_returns or ():
        recursive_conditions = tuple(getattr(recursive, "conditions", ()) or ())
        if artifact_site != self._return_site_key(recursive):
            continue
        if not (
            self._condition_lists_equivalent(list(artifact_conditions), list(recursive_conditions))
            or (
                self._conditions_imply(artifact_conditions, recursive_conditions)
                and self._conditions_imply(recursive_conditions, artifact_conditions)
            )
        ):
            continue
        if self._branch_guarded_affine_phi_step(getattr(recursive, "value", None)) == 1:
            return True
    return False

def _impl__prove_branch_guarded_affine_unit_count_recurrence(
    self,
    high_function,
    *,
    analysis: FunctionReturnAnalysis,
    c_param: Expression,
    target_conditions: Sequence[Condition],
    recursive_returns: Sequence[ReturnInfo],
    candidate_phi_origin_keys: Sequence[Tuple[Any, ...]] = (),
    return_phi_origin_keys: Sequence[Tuple[Any, ...]] = (),
    nonprogress_conditions: Sequence[Condition] = (),
    allow_latch_progress_guard: bool = False,
) -> Optional[Tuple[Any, ...]]:
    if high_function is None or self.program is None:
        return None
    recursive_origin_keys = set(candidate_phi_origin_keys or ())
    return_origin_keys = set(return_phi_origin_keys or ())
    for ret in recursive_returns or ():
        recursive_origin_keys.update(self._phi_circular_origin_stable_keys(getattr(ret, "value", None)))
        recursive_origin_keys.update(self._return_info_candidate_phi_origin_keys(ret))
        return_origin_keys.update(self._phi_circular_origin_stable_keys(getattr(ret, "value", None)))
        return_origin_keys.update(self._return_info_return_phi_origin_keys(ret))
    if not recursive_origin_keys:
        self._debug_print("Outcome branch-guarded structural proof declined: recursive phi origin unavailable")
        return None
    if not return_origin_keys:
        self._debug_print("Outcome branch-guarded structural proof declined: return phi origin unavailable")
        return None
    try:
        tracer = self._make_tracer(high_function)
    except Exception:
        self._debug_print("Outcome branch-guarded structural proof declined: tracer unavailable")
        return None
    summarizer = StructuralRecurrenceSummarizer(
        tracer,
        debug=False,
        enable_completed_recovery_proofs=self.enable_completed_recovery_proofs,
    )
    saw_acc_candidate = False
    saw_acc_transition = False
    saw_state_transition = False
    saw_state_guard = False
    for header_block in summarizer._iter_basic_blocks(high_function):
        phi_ops = [
            op for op in summarizer._iter_block_ops(header_block)
            if getattr(op, "getMnemonic", lambda: None)() == "MULTIEQUAL"
            and getattr(op, "getOutput", lambda: None)() is not None
        ]
        if len(phi_ops) < 2:
            continue
        if any(self._pcode_op_stable_key(phi_op) in recursive_origin_keys for phi_op in phi_ops):
            saw_acc_candidate = True
        for acc_phi in phi_ops:
            acc_phi_key = self._pcode_op_stable_key(acc_phi)
            acc_flows_to_return = self._acc_phi_flows_to_return_origin_phi(
                acc_phi,
                return_origin_keys,
                summarizer=summarizer,
                high_function=high_function,
            )
            if acc_phi_key not in return_origin_keys and not acc_flows_to_return:
                if self.debug:
                    self._debug_print(
                        "Outcome branch-guarded structural proof acc candidate skipped: "
                        f"return provenance missing acc_phi={acc_phi_key}, "
                        f"return_origins={sorted(return_origin_keys, key=repr)}"
                    )
                continue
            acc_indices = summarizer._state_loop_phi_indices(header_block, acc_phi)
            if acc_indices is None:
                if self.debug:
                    self._debug_print("Outcome branch-guarded structural proof acc candidate skipped: loop phi indices unavailable")
                continue
            acc_init_index, acc_backedge_indices = acc_indices
            acc_output = getattr(acc_phi, "getOutput", lambda: None)()
            if acc_output is None:
                continue
            acc_placeholder = Expression.variable(
                "__branch_guarded_acc",
                size=max(1, int(getattr(acc_output, "getSize", lambda: 4)() or 4)),
            )
            acc_init = summarizer._build_pcode_expression(
                acc_phi.getInput(acc_init_index),
                placeholders={acc_output: acc_placeholder},
            )
            if self._constant_int_value(acc_init) != 0:
                if self.debug:
                    self._debug_print(
                        "Outcome branch-guarded structural proof acc candidate skipped: "
                        f"init={self._debug_expr_summary(acc_init)}"
                    )
                continue
            acc_progress_indices: Set[int] = set()
            acc_nonprogress_indices: Set[int] = set()
            acc_conditional_progress_keys: Dict[int, Tuple[Any, ...]] = {}
            acc_unknown_transition = False
            for backedge_index in acc_backedge_indices:
                backedge_index_int = int(backedge_index)
                acc_backedge_expr = summarizer._build_pcode_expression(
                    acc_phi.getInput(backedge_index),
                    placeholders={acc_output: acc_placeholder},
                )
                if self._expression_is_placeholder_plus_one(acc_backedge_expr, acc_placeholder):
                    acc_progress_indices.add(backedge_index_int)
                    continue
                acc_guard_key = self._placeholder_plus_unit_condition_guard_key(
                    acc_backedge_expr,
                    acc_placeholder,
                    target_conditions,
                )
                if acc_guard_key is not None:
                    acc_progress_indices.add(backedge_index_int)
                    acc_conditional_progress_keys[backedge_index_int] = acc_guard_key
                    if (
                        self._expression_is_placeholder_plus_zero_under_conditions(
                            acc_backedge_expr,
                            acc_placeholder,
                            nonprogress_conditions,
                        )
                        or self._expressions_equal_under_conditions_smt(
                            acc_backedge_expr,
                            acc_placeholder,
                            tuple(nonprogress_conditions or ()),
                            getattr(analysis, "parameters", ()) or (),
                        )
                    ):
                        acc_nonprogress_indices.add(backedge_index_int)
                    continue
                if (
                    self._expressions_same_key(acc_backedge_expr, acc_placeholder)
                    or self._expression_is_placeholder_plus_zero_under_conditions(
                        acc_backedge_expr,
                        acc_placeholder,
                        nonprogress_conditions,
                    )
                    or self._expressions_equal_under_conditions_smt(
                        acc_backedge_expr,
                        acc_placeholder,
                        tuple(nonprogress_conditions or ()),
                        getattr(analysis, "parameters", ()) or (),
                    )
                ):
                    acc_nonprogress_indices.add(backedge_index_int)
                    continue
                if self._expression_is_placeholder_plus_one_under_conditions(
                    acc_backedge_expr,
                    acc_placeholder,
                    target_conditions,
                ):
                    acc_progress_indices.add(backedge_index_int)
                    continue
                if self.debug:
                    self._debug_print(
                        "Outcome branch-guarded structural proof acc transition unrecognized: "
                        f"index={backedge_index_int}, expr={self._debug_expr_summary(acc_backedge_expr)}"
                    )
                acc_unknown_transition = True
                break
            if acc_unknown_transition or not acc_progress_indices:
                continue
            saw_acc_transition = True
            for state_phi in phi_ops:
                if state_phi is acc_phi:
                    continue
                state_phi_key = self._pcode_op_stable_key(state_phi)
                if acc_phi_key not in recursive_origin_keys and state_phi_key not in recursive_origin_keys:
                    continue
                state_indices = summarizer._state_loop_phi_indices(header_block, state_phi)
                if state_indices is None:
                    continue
                state_init_index, state_backedge_indices = state_indices
                if tuple(int(index) for index in state_backedge_indices) != tuple(int(index) for index in acc_backedge_indices):
                    continue
                state_output = getattr(state_phi, "getOutput", lambda: None)()
                if state_output is None:
                    continue
                state_placeholder = Expression.variable(
                    "__branch_guarded_state",
                    size=max(1, int(getattr(state_output, "getSize", lambda: 4)() or 4)),
                )
                state_init = summarizer._build_pcode_expression(
                    state_phi.getInput(state_init_index),
                    placeholders={state_output: state_placeholder},
                )
                if not self._expression_is_same_parameter_ignoring_subpiece(state_init, c_param):
                    continue
                state_progress_indices: Set[int] = set()
                state_nonprogress_indices: Set[int] = set()
                state_conditional_progress_keys: Dict[int, Tuple[Any, ...]] = {}
                state_unknown_transition = False
                for backedge_index in state_backedge_indices:
                    backedge_index_int = int(backedge_index)
                    state_backedge_expr = summarizer._build_pcode_expression(
                        state_phi.getInput(backedge_index),
                        placeholders={state_output: state_placeholder},
                    )
                    if self._expression_is_placeholder_minus_one(state_backedge_expr, state_placeholder):
                        state_progress_indices.add(backedge_index_int)
                        continue
                    state_guard_key = self._placeholder_minus_one_unit_condition_guard_key(
                        state_backedge_expr,
                        state_placeholder,
                        target_conditions,
                    )
                    if state_guard_key is not None:
                        state_progress_indices.add(backedge_index_int)
                        state_conditional_progress_keys[backedge_index_int] = state_guard_key
                        if (
                            self._expression_is_placeholder_plus_zero_under_conditions(
                                state_backedge_expr,
                                state_placeholder,
                                nonprogress_conditions,
                            )
                            or self._expressions_equal_under_conditions_smt(
                                state_backedge_expr,
                                state_placeholder,
                                tuple(nonprogress_conditions or ()),
                                getattr(analysis, "parameters", ()) or (),
                            )
                        ):
                            state_nonprogress_indices.add(backedge_index_int)
                        continue
                    if (
                        self._expressions_same_key(state_backedge_expr, state_placeholder)
                        or self._expression_is_placeholder_plus_zero_under_conditions(
                            state_backedge_expr,
                            state_placeholder,
                            nonprogress_conditions,
                        )
                        or self._expressions_equal_under_conditions_smt(
                            state_backedge_expr,
                            state_placeholder,
                            tuple(nonprogress_conditions or ()),
                            getattr(analysis, "parameters", ()) or (),
                        )
                    ):
                        state_nonprogress_indices.add(backedge_index_int)
                        continue
                    if self._expression_is_placeholder_minus_one_under_conditions(
                        state_backedge_expr,
                        state_placeholder,
                        target_conditions,
                    ):
                        state_progress_indices.add(backedge_index_int)
                        continue
                    if self.debug:
                        self._debug_print(
                            "Outcome branch-guarded structural proof state transition unrecognized: "
                            f"index={backedge_index_int}, expr={self._debug_expr_summary(state_backedge_expr)}"
                        )
                    state_unknown_transition = True
                    break
                if (
                    state_unknown_transition
                    or not state_progress_indices
                    or state_progress_indices != acc_progress_indices
                    or state_nonprogress_indices != acc_nonprogress_indices
                    or state_conditional_progress_keys != acc_conditional_progress_keys
                ):
                    if self.debug:
                        self._debug_print(
                            "Outcome branch-guarded structural proof state transition set mismatch: "
                            f"state_unknown={state_unknown_transition}, "
                            f"acc_progress={sorted(acc_progress_indices)}, "
                            f"state_progress={sorted(state_progress_indices)}, "
                            f"acc_nonprogress={sorted(acc_nonprogress_indices)}, "
                            f"state_nonprogress={sorted(state_nonprogress_indices)}, "
                            f"acc_conditional={sorted(acc_conditional_progress_keys)}, "
                            f"state_conditional={sorted(state_conditional_progress_keys)}"
                        )
                    continue
                saw_state_transition = True
                if not self._state_phi_feeds_positive_loop_guard(
                    high_function,
                    summarizer=summarizer,
                    header_block=header_block,
                    backedge_indices=tuple(int(index) for index in state_backedge_indices),
                    state_phi=state_phi,
                    state_placeholder=state_placeholder,
                    target_conditions=target_conditions,
                    allow_latch_progress_guard=allow_latch_progress_guard,
                ):
                    continue
                saw_state_guard = True
                return (
                    "branch_guarded_affine_unit_count_structural_proof",
                    ("schema_version", 1),
                    ("function", getattr(analysis, "function_name", None)),
                    ("acc_phi", self._pcode_op_stable_key(acc_phi)),
                    ("state_phi", self._pcode_op_stable_key(state_phi)),
                    ("progress_backedges", tuple(sorted(acc_progress_indices))),
                    ("nonprogress_backedges", tuple(sorted(acc_nonprogress_indices))),
                    ("conditional_progress_backedges", tuple(sorted(acc_conditional_progress_keys))),
                    ("conditional_progress_guard_keys", tuple(sorted(acc_conditional_progress_keys.items(), key=repr))),
                    ("target", tuple(condition.to_string() for condition in target_conditions or ())),
                    ("target_guard_keys", tuple(sorted((self._condition_identity_key(condition) for condition in target_conditions or ()), key=repr))),
                )
    self._debug_print(
        "Outcome branch-guarded structural proof declined: "
        f"saw_acc_candidate={saw_acc_candidate}, "
        f"saw_acc_transition={saw_acc_transition}, "
        f"saw_state_transition={saw_state_transition}, "
        f"saw_state_guard={saw_state_guard}"
    )
    return None

def _impl__branch_guarded_affine_ignored_artifacts_are_shadowed(
    self,
    ignored_artifacts: Sequence[ReturnInfo],
    recursive_returns: Sequence[Tuple[ReturnInfo, int]],
    parameters: Sequence[Dict],
) -> bool:
    if not ignored_artifacts:
        return True
    for artifact in ignored_artifacts:
        artifact_conditions = tuple(getattr(artifact, "conditions", ()) or ())
        artifact_site = self._return_site_key(artifact)
        if not any(
            artifact_site == self._return_site_key(recursive)
            and (
                self._condition_lists_equivalent(
                    list(artifact_conditions),
                    list(getattr(recursive, "conditions", ()) or ()),
                )
                or (
                    self._conditions_imply(
                        artifact_conditions,
                        tuple(getattr(recursive, "conditions", ()) or ()),
                    )
                    and self._conditions_imply(
                        tuple(getattr(recursive, "conditions", ()) or ()),
                        artifact_conditions,
                    )
                )
            )
            and self._expressions_equal_under_conditions_smt(
                getattr(artifact, "value", None),
                getattr(recursive, "value", None),
                tuple(artifact_conditions) + tuple(getattr(recursive, "conditions", ()) or ()),
                parameters,
            )
            for recursive, _step in recursive_returns
        ):
            return False
    return True

def _impl__branch_guarded_affine_phi_step(self, value: Optional[Expression]) -> Optional[int]:
    signature = self._phi_circular_additive_signature(value)
    if signature is None:
        return None
    phi_coeff, constant = signature
    if phi_coeff != 1:
        return None
    try:
        return int(constant)
    except (TypeError, ValueError):
        return None

def _impl__branch_guarded_affine_singleton_base_anchor_matches(
    self,
    value: Optional[Expression],
    conditions: Sequence[Condition],
    c_param: Expression,
    target_conditions: Sequence[Condition],
) -> bool:
    if self._constant_int_value(value) != 1:
        return False
    if not self._conditions_overlap(tuple(conditions or ()), target_conditions):
        return False
    return any(
        self._condition_is_param_minus_one_nonpositive(condition, c_param, target_conditions)
        for condition in conditions or ()
    )

def _impl__branch_guarded_expression_is_param_minus_one(
    self,
    expr: Optional[Expression],
    param: Expression,
    target_conditions: Sequence[Condition],
) -> bool:
    if expr is None or getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return False
    if self._expressions_equal_under_conditions_smt(
        expr,
        Expression.binary_op(
            "INT_SUB",
            param,
            Expression.constant(1, size=max(1, int(getattr(param, "size", 0) or 4))),
        ),
        tuple(target_conditions or ()),
        getattr(self, "_current_parameters", ()) or (),
    ):
        return True
    if getattr(expr, "operator", None) == "INT_ADD":
        operands = tuple(getattr(expr, "operands", ()) or ())
        if len(operands) != 2:
            return False
        left, right = operands
        if self._expression_is_same_parameter_ignoring_subpiece(left, param):
            return self._expression_is_placeholder_minus_one_under_conditions(expr, left, target_conditions)
        if self._expression_is_same_parameter_ignoring_subpiece(right, param):
            return self._expression_is_placeholder_minus_one_under_conditions(expr, right, target_conditions)
        return False
    if getattr(expr, "operator", None) != "INT_SUB":
        return False
    operands = tuple(getattr(expr, "operands", ()) or ())
    if len(operands) != 2:
        return False
    return self._expression_is_same_parameter_ignoring_subpiece(
        operands[0],
        param,
    ) and self._expression_is_one_under_conditions(operands[1], target_conditions)

def _impl__prove_branch_guarded_while_nonprogress_must_diverge(
    self,
    high_function,
    *,
    invariant_conditions: Sequence[Condition],
) -> Optional[Dict[str, Any]]:
    if high_function is None:
        return None
    blocks = tuple(self._iter_high_basic_blocks(high_function))
    if not blocks:
        return None
    tracer = None
    if self.program is not None:
        try:
            tracer = self._make_tracer(high_function)
        except Exception:
            tracer = None

    adjacency: Dict[Any, List[Any]] = {}
    excluded_edges: List[Dict[str, Any]] = []
    for block in blocks:
        block_key = self._block_debug_key(block)
        adjacency[block_key] = []
        for successor in self._block_successors(block):
            successor_key = self._block_debug_key(successor)
            edge_condition = self._edge_condition_for_successor(block, successor, tracer)
            if edge_condition is not None and self._condition_contradicts_any(
                edge_condition,
                tuple(invariant_conditions or ()),
            ):
                excluded_edges.append(
                    {
                        "source": block_key,
                        "target": successor_key,
                        "edge_condition": edge_condition.to_string(),
                        "relation": "invariant_contradicts_edge",
                    }
                )
                continue
            adjacency[block_key].append(successor_key)

    key_to_block = {self._block_debug_key(block): block for block in blocks}
    entry_keys = [
        self._block_debug_key(block)
        for block in blocks
        if self._block_predecessor_count(block) == 0
    ]
    if not entry_keys:
        entry_keys = [self._block_debug_key(blocks[0])]

    reachable: Set[Any] = set()
    stack = list(entry_keys)
    while stack:
        key = stack.pop()
        if key in reachable or key not in key_to_block:
            continue
        reachable.add(key)
        stack.extend(adjacency.get(key, ()))
    if not reachable:
        return None
    if not excluded_edges:
        self._debug_print("Outcome branch-guarded divergence proof declined: no invariant-excluding guard edges")
        return None
    for key in reachable:
        block = key_to_block.get(key)
        if block is None:
            return None
        if self._block_has_return_op(block):
            self._debug_print("Outcome branch-guarded divergence proof declined: reachable RETURN under invariant")
            return None
        if self._block_writes_outcome_guard_state(block):
            self._debug_print("Outcome branch-guarded divergence proof declined: reachable guard-state write under invariant")
            return None
        if not adjacency.get(key):
            self._debug_print("Outcome branch-guarded divergence proof declined: reachable terminal block under invariant")
            return None
    cycle_keys = self._reachable_cycle_keys(reachable, adjacency)
    if not cycle_keys:
        self._debug_print("Outcome branch-guarded divergence proof declined: no feasible invariant cycle")
        return None
    reachable_blocks = {
        key_to_block[key]
        for key in reachable
        if key in key_to_block
    }
    if not reachable_blocks or not self._scc_preserves_guard_dependencies(reachable_blocks):
        self._debug_print("Outcome branch-guarded divergence proof declined: reachable graph redefines guard dependency")
        return None
    cycle_blocks = {
        key_to_block[key]
        for key in cycle_keys
        if key in key_to_block
    }
    if not cycle_blocks or not self._scc_preserves_guard_dependencies(cycle_blocks):
        self._debug_print("Outcome branch-guarded divergence proof declined: cycle redefines guard dependency")
        return None
    return {
        "proof_kind": "branch_guarded_while_nonprogress_must_diverge",
        "candidate_rule": "branch_guarded_loop_invariant_nonprogress",
        "invariant": [condition.to_string() for condition in invariant_conditions or ()],
        "reachable_blocks": sorted(str(key) for key in reachable),
        "cycle_blocks": sorted(str(key) for key in cycle_keys),
        "excluded_edges": excluded_edges,
        "side_effect_control_safety": {
            "forbidden_ops_absent": True,
            "return_ops_absent_under_invariant": True,
            "guard_state_writes_absent_under_invariant": True,
            "guard_dependency_writes_absent_under_invariant": True,
        },
        "cfg_applicability_surface": _current_cfg_applicability_surface(self, high_function),
    }

def _impl__high_function_has_forbidden_control_outcome_ops(self, high_function, *, allow_call: bool) -> bool:
    forbidden = {"CALLIND", "BRANCHIND", "LOAD", "STORE", "CALLOTHER"}
    if not allow_call:
        forbidden.add("CALL")
    for block in self._iter_high_basic_blocks(high_function):
        for op in self._iter_high_block_ops(block):
            mnemonic = getattr(op, "getMnemonic", lambda: None)()
            if mnemonic in forbidden or self._is_control_outcome_forbidden_fp_mnemonic(mnemonic):
                return True
    return False

def _impl__is_control_outcome_forbidden_fp_mnemonic(self, mnemonic: Optional[str]) -> bool:
    if not mnemonic:
        return False
    return (
        mnemonic.startswith("FLOAT_")
        or mnemonic in {"INT2FLOAT", "FLOAT2FLOAT", "TRUNC", "CEIL", "FLOOR", "ROUND", "NAN"}
    )

def _impl__block_reaches(self, start, target, allowed: Set[Any]) -> bool:
    stack = [start]
    seen = set()
    while stack:
        current = stack.pop()
        if current in seen:
            continue
        seen.add(current)
        if current is target:
            return True
        out_size = int(getattr(current, "getOutSize", lambda: 0)() or 0)
        for index in range(out_size):
            succ = getattr(current, "getOut", lambda _idx: None)(index)
            if succ in allowed and succ not in seen:
                stack.append(succ)
    return False

def _impl__high_function_cbranch_count(self, high_function) -> int:
    return sum(
        1
        for block in self._iter_high_basic_blocks(high_function)
        for op in self._iter_high_block_ops(block)
        if getattr(op, "getMnemonic", lambda: None)() == "CBRANCH"
    )

def _impl__iter_high_basic_blocks(self, high_function):
    if high_function is None or not callable(getattr(high_function, "getBasicBlocks", None)):
        return
    try:
        for block in high_function.getBasicBlocks():
            yield block
    except Exception:
        return

def _impl__iter_high_block_ops(self, block):
    iterator = getattr(block, "getIterator", lambda: None)()
    if iterator is None:
        return
    while iterator.hasNext():
        yield iterator.next()

def _impl__mark_incomplete_control_flow(self, analysis: FunctionReturnAnalysis) -> None:
    """後段で保守的に扱うべき不完全な制御フロー要約を記録する。"""
    auto_notes = {
        "unknown_return",
        "overlapping_unconditional_returns",
        "indirect_control_flow_unresolved",
        "deferred_call_return_unresolved",
    }
    analysis.analysis_notes = [
        note for note in analysis.analysis_notes
        if note not in auto_notes
    ]
    reasons = []

    if analysis.has_unknown_return():
        reasons.append("unknown_return")
    if analysis.has_overlapping_unconditional_returns():
        reasons.append("overlapping_unconditional_returns")
    if (
        analysis.has_unresolved_return_value()
        and any(
            reason in {"call_out_of_scope", "callind_out_of_scope"}
            for reason in analysis.unknown_event_reasons
        )
    ):
        reasons.append("indirect_control_flow_unresolved")
    if analysis.has_unresolved_return_value() and getattr(analysis, "deferred_calls", None):
        reasons.append("deferred_call_return_unresolved")

    if analysis.recovered_from_decompiler:
        reasons = [reason for reason in reasons if reason == "unknown_return"]

    seen = set(analysis.analysis_notes)
    for reason in reasons:
        if reason not in seen:
            analysis.analysis_notes.append(reason)
            seen.add(reason)
    analysis.incomplete_control_flow = bool(reasons)

def _impl__recover_control_region_returns_early(
    self,
    current_function,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    return_ops: List[Any],
    *,
    active_functions,
) -> Tuple[Optional[List[ReturnInfo]], List[str]]:
    if not return_ops:
        return None, []

    recovered_switch = self._recover_switch_like_returns_from_placeholder_analysis(
        current_function,
        tracer,
        condition_tracker,
        return_ops,
        active_functions=active_functions,
    )
    if recovered_switch is not None and self._control_region_returns_are_safe(recovered_switch):
        return recovered_switch, ["switch_return_recovery", "control_region_return_recovery"]

    recovered_paths = self._recover_control_flow_returns_from_block_paths(
        current_function,
        tracer,
        condition_tracker,
        return_ops,
        active_functions=active_functions,
    )
    if recovered_paths is not None and self._control_region_returns_are_safe(recovered_paths):
        return recovered_paths, ["control_region_return_recovery"]

    return None, []

def _impl__recover_switch_like_returns_from_placeholder_analysis(
    self,
    current_function,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    return_ops: List[Any],
    *,
    active_functions,
) -> Optional[List[ReturnInfo]]:
    placeholders: List[ReturnInfo] = []
    fallback_address = (
        str(current_function.getEntryPoint())
        if current_function is not None and hasattr(current_function, "getEntryPoint")
        else "unknown"
    )
    for return_index, return_op in enumerate(return_ops or []):
        site_metadata = self._describe_pcode_site(return_op, fallback_address)
        placeholders.append(
            self._make_return_info(
                address=cast(str, site_metadata.get("address") or fallback_address),
                value=Expression.unknown("control_region_placeholder"),
                conditions=[],
                branch_index=return_index,
                site_metadata=site_metadata,
            )
        )

    placeholder_analysis = FunctionReturnAnalysis(
        function_name=current_function.getName() if current_function is not None else "unknown",
        entry_point=fallback_address,
        parameters=list(self._current_parameters or []),
        returns=placeholders,
        function_ref=(
            CallTargetRef.from_function(current_function)
            if current_function is not None
            else None
        ),
        return_type="unknown",
        return_type_obj=None,
        unknown_event_count=1,
        unknown_event_reasons=["indirect_control_flow_unresolved"],
        program_is_big_endian=self._program_is_big_endian(),
        binary_id=self._binary_id,
    )
    recovered = self._recover_switch_like_returns_from_pcode(
        placeholder_analysis,
        tracer,
        condition_tracker,
        return_ops=return_ops,
        current_function=current_function,
        active_functions=active_functions,
    )
    if recovered is None:
        return None
    return self._merge_equivalent_return_infos(
        self._prune_less_precise_return_infos(recovered)
    )

def _impl__recover_control_flow_returns_from_block_paths(
    self,
    current_function,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    return_ops: List[Any],
    *,
    active_functions,
) -> Optional[List[ReturnInfo]]:
    recovered_results: List[ReturnInfo] = []
    fallback_address = (
        str(current_function.getEntryPoint())
        if current_function is not None and hasattr(current_function, "getEntryPoint")
        else "unknown"
    )

    for return_index, return_op in enumerate(return_ops or []):
        path_entries = self._get_cached_return_path_entries(
            condition_tracker,
            return_op,
            tracer=tracer,
        )
        if not path_entries:
            return None

        site_metadata = self._describe_pcode_site(return_op, fallback_address)
        address = cast(str, site_metadata.get("address") or fallback_address)
        num_inputs = self._coerce_optional_int(getattr(return_op, "getNumInputs", lambda: 0)())
        num_inputs = num_inputs if num_inputs is not None else 0

        if num_inputs >= 2:
            path_recovered = self._recover_explicit_return_from_block_paths(
                return_op,
                address,
                tracer,
                condition_tracker,
                return_index,
                path_entries,
                active_functions=active_functions,
                current_function=current_function,
                site_metadata=site_metadata,
            )
        else:
            path_recovered = self._recover_implicit_return_from_block_paths(
                return_op,
                address,
                tracer,
                condition_tracker,
                return_index,
                path_entries,
                active_functions=active_functions,
                current_function=current_function,
                site_metadata=site_metadata,
            )

        if not path_recovered:
            return None
        recovered_results.extend(path_recovered)

    if not recovered_results:
        return None

    recovered_results = self._merge_equivalent_return_infos(
        self._prune_less_precise_return_infos(recovered_results)
    )
    return recovered_results

def _impl__recover_explicit_return_from_block_paths(
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
    normalized_entries = self._coerce_block_path_entries(path_entries)
    if not normalized_entries:
        return None

    try:
        candidate_source = return_op.getInput(1)
    except Exception:
        return None

    recovered_results: List[ReturnInfo] = []
    unresolved_paths: List[int] = []

    for path_idx, (block_path, conditions) in enumerate(normalized_entries):
        selected_source = self._select_path_specific_return_source(
            candidate_source,
            block_path,
            condition_tracker=condition_tracker,
            path_conditions=conditions,
        )
        if selected_source is None:
            unresolved_paths.append(path_idx)
            continue

        path_results = self._recover_explicit_return_from_path_source(
            selected_source,
            address,
            tracer,
            condition_tracker,
            list(conditions),
            return_index * 1000 + path_idx * 100,
            active_functions=active_functions,
            current_function=current_function,
            site_metadata=site_metadata,
        )
        if not path_results:
            unresolved_paths.append(path_idx)
            continue
        recovered_results.extend(path_results)

    if recovered_results and not unresolved_paths:
        return self._merge_equivalent_return_infos(recovered_results)

    if self.debug and unresolved_paths:
        self._debug_print(
            "Explicit return path recovery could not resolve source on "
            f"path(s) {unresolved_paths}"
        )
    return None

def _impl__recover_explicit_return_from_path_source(
    self,
    return_source,
    address: str,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    path_conditions: List[Condition],
    return_index_base: int,
    active_functions: Optional[Set[Tuple[Any, ...]]] = None,
    current_function=None,
    site_metadata: Optional[Dict[str, Optional[object]]] = None,
) -> Optional[List[ReturnInfo]]:
    direct_results = self._materialize_direct_path_specific_return_source(
        return_source,
        address,
        tracer,
        path_conditions,
        return_index_base,
        site_metadata=site_metadata,
    )
    if direct_results is not None:
        return direct_results

    tracked_sources = [self._make_tracked_return_value(return_source, tracer)]
    return self._recover_return_infos_from_tracked_sources(
        tracked_sources,
        address,
        tracer,
        condition_tracker,
        list(path_conditions),
        return_index_base,
        all_path_conditions=[list(path_conditions)],
        active_functions=active_functions,
        current_function=current_function,
        site_metadata=site_metadata,
    )

def _impl__materialize_direct_path_specific_return_source(
    self,
    return_source,
    address: str,
    tracer: PcodeTracer,
    path_conditions: List[Condition],
    return_index_base: int,
    site_metadata: Optional[Dict[str, Optional[object]]] = None,
) -> Optional[List[ReturnInfo]]:
    if return_source is None or self._contains_multiequal(return_source):
        return None

    # get_all_valid_block_paths_to_return() already provides exact feasible path
    # partitions, so re-simplifying the same guard set here only burns solver time.
    normalized_conditions = list(path_conditions or [])

    try:
        tracer.clear_cache()
    except Exception:
        pass

    value = tracer.trace_varnode(return_source, use_cache=False)
    if value is None:
        return None

    candidate_value = self._fold_constant_expression(
        value,
        fallback_expr=value,
    ) or value
    candidate_value = self._concretize_readonly_loads(
        candidate_value,
        normalized_conditions,
        self._current_parameters,
    )
    if candidate_value is None:
        return None
    if (
        self._expression_contains_unresolved_value(candidate_value)
        or expression_contains_post_state_reads(candidate_value)
        or _expression_contains_observed_loads(candidate_value)
    ):
        return None

    if not self._expression_contains_phi(candidate_value):
        value_site_metadata = self._site_metadata_with_return_value_pcode_op_refs(
            site_metadata,
            return_varnode=return_source,
        )
        return [
            self._make_return_info(
                address=address,
                value=candidate_value,
                conditions=normalized_conditions,
                branch_index=return_index_base,
                site_metadata=value_site_metadata,
            )
        ]

    reduced_value = ConditionSimplifier.reduce_expression_under_conditions(
        candidate_value,
        normalized_conditions,
    )
    candidate_value = self._fold_constant_expression(
        reduced_value,
        fallback_expr=candidate_value,
    ) or reduced_value
    if (
        self._expression_contains_unresolved_value(candidate_value)
        or expression_contains_post_state_reads(candidate_value)
        or _expression_contains_observed_loads(candidate_value)
    ):
        return None
    if not self._expression_contains_phi(candidate_value):
        value_site_metadata = self._site_metadata_with_return_value_pcode_op_refs(
            site_metadata,
            return_varnode=return_source,
        )
        return [
            self._make_return_info(
                address=address,
                value=candidate_value,
                conditions=normalized_conditions,
                branch_index=return_index_base,
                site_metadata=value_site_metadata,
            )
        ]

    split_cases = self._split_object_centric_return_case(
        candidate_value,
        normalized_conditions,
    )
    results: List[ReturnInfo] = []
    value_site_metadata = self._site_metadata_with_return_value_pcode_op_refs(
        site_metadata,
        return_varnode=return_source,
    )
    for split_index, (split_value, split_conditions) in enumerate(split_cases or []):
        normalized_value = self._fold_constant_expression(
            split_value,
            fallback_expr=candidate_value,
        ) or split_value
        if (
            self._expression_contains_unresolved_value(normalized_value)
            or expression_contains_post_state_reads(normalized_value)
            or _expression_contains_observed_loads(normalized_value)
        ):
            return None
        results.append(
            self._make_return_info(
                address=address,
                value=normalized_value,
                conditions=list(split_conditions or []),
                branch_index=(
                    return_index_base
                    if len(split_cases) == 1
                    else return_index_base * 10 + split_index
                ),
                site_metadata=value_site_metadata,
            )
        )

    if not results:
        return None
    return self._merge_equivalent_return_infos(results)

def _impl__get_cached_return_path_entries(
    self,
    condition_tracker: ConditionTracker,
    return_op,
    *,
    tracer: Optional[PcodeTracer] = None,
) -> Optional[List[Tuple[List[Any], List[Condition]]]]:
    key = self._pcode_op_identity_key(return_op) or ("id", id(return_op))
    cached = self._return_path_entry_cache.get(key, None)
    if key in self._return_path_entry_cache:
        return cached

    get_paths_to_return = getattr(condition_tracker, "get_all_valid_block_paths_to_return", None)
    if not callable(get_paths_to_return):
        self._return_path_entry_cache[key] = None
        return None

    raw_path_entries = get_paths_to_return(return_op)
    path_entries = self._coerce_block_path_entries(raw_path_entries)
    if path_entries and tracer is not None:
        path_entries = self._filter_noreturn_return_path_entries(path_entries, tracer, return_op)

    self._return_path_entry_cache[key] = path_entries
    return path_entries

def _impl__control_region_returns_are_safe(
    self,
    return_infos: List[ReturnInfo],
) -> bool:
    if not return_infos:
        return False
    for info in return_infos:
        if self._expression_contains_unresolved_value(info.value):
            return False
        if expression_contains_post_state_reads(info.value):
            return False
        if _expression_contains_observed_loads(info.value):
            return False
    return True

def _impl__return_path_is_covered_by_existing_return(
    self,
    analysis: FunctionReturnAnalysis,
    path_conditions: Sequence[Condition],
) -> bool:
    path_conditions = ConditionSimplifier.simplify_conditions_object_centric(
        list(path_conditions or [])
    )
    if ConditionSimplifier.object_centric_is_contradiction(path_conditions):
        return True
    path_constraint_set = ConditionSimplifier.build_constraint_set(path_conditions)
    if path_constraint_set.is_contradictory:
        return True
    for ret in analysis.returns or []:
        ret_conditions = self._return_info_effective_region_conditions(ret)
        if path_constraint_set.implies_all(ret_conditions):
            return True
    return False

def _impl__should_attempt_switch_recovery(
    self,
    analysis: Optional[FunctionReturnAnalysis],
) -> bool:
    if analysis is None or not analysis.returns:
        return False
    if analysis.recovered_from_decompiler:
        return False
    if analysis.has_unknown_return():
        return True
    if analysis.has_overlapping_unconditional_returns():
        return True
    if self._analysis_has_ambiguous_condition_region_returns(analysis):
        return True
    if analysis.has_unresolved_return_value():
        return True
    return any(
        reason in {"callind_out_of_scope", "indirect_control_flow_unresolved"}
        for reason in getattr(analysis, "unknown_event_reasons", [])
    )

def _impl__recover_switch_like_returns_from_pcode(
    self,
    analysis: FunctionReturnAnalysis,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    return_ops: Optional[List[Any]] = None,
    current_function=None,
    active_functions: Optional[Set[Tuple[Any, ...]]] = None,
) -> Optional[List[ReturnInfo]]:
    from scripts.function_tracer_pcode.semantics.transform.expander import ExpandedValue

    if not self._should_attempt_switch_recovery(analysis):
        return None

    switch_dispatch_summaries = build_switch_dispatch_summaries(
        tracer=tracer,
        condition_tracker=condition_tracker,
        parameters=self._current_parameters,
        concretize_readonly_loads=self._concretize_readonly_loads,
        read_memory_value=self._read_memory_value,
        max_cases=self._bounded_call_max_cases,
        debug=self.debug,
        debug_print=self._debug_print if self.debug else None,
    )
    attach_summaries = getattr(condition_tracker, "attach_switch_dispatch_summaries", None)
    if callable(attach_summaries):
        attach_summaries(switch_dispatch_summaries)

    for dispatch_summary in switch_dispatch_summaries:
        switch_block = dispatch_summary.block_info
        dispatch_op = dispatch_summary.dispatch_op

        impacted_site_keys = self._collect_switch_impacted_return_sites(
            switch_block,
            return_ops or [],
            condition_tracker,
            analysis.entry_point,
        )
        if impacted_site_keys is None or not impacted_site_keys:
            continue

        affected_returns = [
            ret for ret in (analysis.returns or []) if self._return_site_key(ret) in impacted_site_keys
        ]
        unaffected_returns = [
            ret for ret in (analysis.returns or []) if self._return_site_key(ret) not in impacted_site_keys
        ]
        if not affected_returns:
            continue
        if not self._switch_recovery_targets_problematic_region(analysis, affected_returns):
            continue

        candidate_entries = self._enumerate_switch_dispatch_targets(dispatch_summary)
        if not candidate_entries or len(candidate_entries) < 2:
            continue

        dispatch_args = self._recover_dispatch_call_arguments(dispatch_op, tracer)
        expanded_values: List[ExpandedValue] = []
        candidate_failed = False
        for address_value, branch_conditions in candidate_entries:
            resolved = self._resolve_local_code_target_expansions(
                address_value,
                active_functions or set(),
                current_function=current_function,
                args=dispatch_args,
            )
            if not resolved:
                resolved = self._resolve_switch_case_target_expansions(
                    address_value,
                    branch_conditions,
                    tracer,
                    condition_tracker,
                    return_ops or [],
                    active_functions=active_functions or set(),
                    current_function=current_function,
                )
            if not resolved:
                if self.debug:
                    cond_dump = [
                        ConditionSimplifier.get_simplified_condition_string(cond)
                        for cond in branch_conditions
                    ]
                    self._debug_print(
                        "Switch recovery aborted: local target expansion failed for "
                        f"0x{address_value:x} under {cond_dump}"
                    )
                candidate_failed = True
                break

            for ev in resolved:
                merged_conditions = ConditionSimplifier.simplify_conditions(
                    list(branch_conditions) + list(getattr(ev, "conditions", []) or [])
                )
                if ConditionSimplifier.is_contradiction(merged_conditions):
                    continue
                expanded_values.append(
                    ExpandedValue(
                        value=self._clone_expression(ev.value),
                        conditions=merged_conditions,
                    )
                )

        if candidate_failed or not expanded_values:
            continue

        site_metadata = self._describe_pcode_site(
            dispatch_op,
            analysis.entry_point,
            identity_prefix="switch_dispatch",
        )
        recovered = self._build_return_infos_from_expansions(
            cast(str, site_metadata.get("address") or analysis.entry_point),
            expanded_values,
            0,
            site_metadata=site_metadata,
        )
        recovered = self._merge_equivalent_return_infos(
            self._prune_less_precise_return_infos(recovered)
        )
        if not recovered:
            continue
        if not self._switch_recovery_improves_returns(analysis, affected_returns, recovered):
            continue
        if self._switch_recovery_conflicts_with_unaffected_returns(unaffected_returns, recovered):
            continue
        combined = self._merge_equivalent_return_infos(
            self._prune_less_precise_return_infos(list(unaffected_returns) + recovered)
        )
        if not combined:
            continue
        if self.debug:
            self._debug_print(
                "Recovered switch-like return cases from JumpTable/CFG structure "
                f"(dispatch={dispatch_summary.dispatch_mnemonic}, "
                f"affected_sites={sorted(impacted_site_keys)}, recovered={len(recovered)})"
            )
        return combined

    block_by_index = getattr(condition_tracker, "block_by_index", None) or {}
    switch_blocks = [
        block_info
        for block_info in block_by_index.values()
        if self._find_indirect_dispatch_op_on_block(block_info) is not None
    ]
    if not switch_blocks:
        return None

    for switch_block in sorted(switch_blocks, key=lambda info: info.index):
        indirect_op = self._find_indirect_dispatch_op_on_block(switch_block)
        if indirect_op is None:
            continue

        impacted_site_keys = self._collect_switch_impacted_return_sites(
            switch_block,
            return_ops or [],
            condition_tracker,
            analysis.entry_point,
        )
        if impacted_site_keys is None or not impacted_site_keys:
            continue

        affected_returns = [
            ret for ret in (analysis.returns or []) if self._return_site_key(ret) in impacted_site_keys
        ]
        unaffected_returns = [
            ret for ret in (analysis.returns or []) if self._return_site_key(ret) not in impacted_site_keys
        ]
        if not affected_returns:
            continue
        if not self._switch_recovery_targets_problematic_region(analysis, affected_returns):
            continue

        candidate_entries = self._enumerate_switch_branch_targets(
            switch_block,
            indirect_op,
            tracer,
            condition_tracker,
        )
        if not candidate_entries or len(candidate_entries) < 2:
            continue

        dispatch_args = self._recover_dispatch_call_arguments(indirect_op, tracer)
        expanded_values: List[ExpandedValue] = []
        candidate_failed = False
        for address_value, branch_conditions in candidate_entries:
            resolved = self._resolve_local_code_target_expansions(
                address_value,
                active_functions or set(),
                current_function=current_function,
                args=dispatch_args,
            )
            if not resolved:
                resolved = self._resolve_switch_case_target_expansions(
                    address_value,
                    branch_conditions,
                    tracer,
                    condition_tracker,
                    return_ops or [],
                    active_functions=active_functions or set(),
                    current_function=current_function,
                )
            if not resolved:
                if self.debug:
                    cond_dump = [
                        ConditionSimplifier.get_simplified_condition_string(cond)
                        for cond in branch_conditions
                    ]
                    self._debug_print(
                        "Switch recovery aborted: local target expansion failed for "
                        f"0x{address_value:x} under {cond_dump}"
                    )
                candidate_failed = True
                break

            for ev in resolved:
                merged_conditions = ConditionSimplifier.simplify_conditions(
                    list(branch_conditions) + list(getattr(ev, "conditions", []) or [])
                )
                if ConditionSimplifier.is_contradiction(merged_conditions):
                    continue
                expanded_values.append(
                    ExpandedValue(
                        value=self._clone_expression(ev.value),
                        conditions=merged_conditions,
                    )
                )

        if candidate_failed or not expanded_values:
            continue

        site_metadata = self._describe_pcode_site(
            indirect_op,
            analysis.entry_point,
            identity_prefix="indirect_dispatch",
        )
        recovered = self._build_return_infos_from_expansions(
            cast(str, site_metadata.get("address") or analysis.entry_point),
            expanded_values,
            0,
            site_metadata=site_metadata,
        )
        recovered = self._merge_equivalent_return_infos(
            self._prune_less_precise_return_infos(recovered)
        )
        if not recovered:
            continue
        if not self._switch_recovery_improves_returns(analysis, affected_returns, recovered):
            continue
        if self._switch_recovery_conflicts_with_unaffected_returns(unaffected_returns, recovered):
            continue
        combined = self._merge_equivalent_return_infos(
            self._prune_less_precise_return_infos(list(unaffected_returns) + recovered)
        )
        if not combined:
            continue
        if self.debug:
            self._debug_print(
                "Recovered switch-like return cases from indirect-dispatch/CFG structure "
                f"(affected_sites={sorted(impacted_site_keys)}, recovered={len(recovered)})"
            )
        return combined

    return None

def _impl__address_offset_for_block_endpoint(self, address) -> Optional[int]:
    if address is None:
        return None
    try:
        return int(address.getOffset())
    except Exception:
        return None

def _impl__collect_switch_impacted_return_sites(
    self,
    switch_block,
    return_ops: List[Any],
    condition_tracker: ConditionTracker,
    fallback_address: str,
) -> Optional[Set[str]]:
    impacted: Set[str] = set()
    switch_index = getattr(switch_block, "index", None)

    for return_index, return_op in enumerate(return_ops or []):
        raw_entries = condition_tracker.get_all_valid_block_paths_to_return(return_op)
        path_entries = self._coerce_block_path_entries(raw_entries)
        if not path_entries:
            continue

        path_hits = [
            any(getattr(block_info, "index", None) == switch_index for block_info in (block_path or []))
            for block_path, _conditions in path_entries
        ]
        if not any(path_hits):
            continue
        if not all(path_hits):
            if self.debug:
                self._debug_print(
                    "Switch recovery skipped: candidate BRANCHIND only influences a subset of "
                    f"paths to RETURN #{return_index}"
                )
            return None

        site_metadata = self._describe_pcode_site(return_op, fallback_address)
        impacted.add(cast(str, site_metadata.get("pcode_identity") or site_metadata.get("address")))

    return impacted

def _impl__switch_recovery_improves_returns(
    self,
    analysis: FunctionReturnAnalysis,
    affected_returns: List[ReturnInfo],
    recovered: List[ReturnInfo],
) -> bool:
    if not recovered:
        return False
    if any(self._expression_contains_unresolved_value(ret.value) for ret in recovered):
        return False

    original_unresolved = sum(
        1 for ret in affected_returns if self._expression_contains_unresolved_value(ret.value)
    )
    recovered_unresolved = sum(
        1 for ret in recovered if self._expression_contains_unresolved_value(ret.value)
    )
    if recovered_unresolved < original_unresolved:
        return True

    affected_analysis = analysis.semantic_successor(
        returns=list(affected_returns),
    )
    if affected_analysis.has_overlapping_unconditional_returns():
        return True
    if self._analysis_has_ambiguous_condition_region_returns(affected_analysis):
        return True
    return False

def _impl__switch_recovery_conflicts_with_unaffected_returns(
    self,
    unaffected_returns: List[ReturnInfo],
    recovered: List[ReturnInfo],
) -> bool:
    for existing in unaffected_returns:
        for candidate in recovered:
            overlap_conditions = ConditionSimplifier.simplify_conditions(
                list(existing.conditions) + list(candidate.conditions)
            )
            if ConditionSimplifier.is_contradiction(overlap_conditions):
                continue
            if _expressions_equivalent(existing.value, candidate.value):
                continue
            if self.debug:
                cond_dump = [
                    ConditionSimplifier.get_simplified_condition_string(cond)
                    for cond in overlap_conditions
                ]
                self._debug_print(
                    "Switch recovery rejected due to overlap with unaffected return case: "
                    f"existing={self._debug_expr_summary(existing.value)} "
                    f"candidate={self._debug_expr_summary(candidate.value)} "
                    f"conditions={cond_dump}"
                )
            return True
    return False

def _impl__propagate_multiequal_input_for_return_path(
    self,
    pcode_op,
    *,
    tracer: Optional[PcodeTracer],
    condition_tracker: Optional[ConditionTracker],
    path_conditions: Optional[List[Condition]] = None,
) -> List[_TrackedReturnValue]:
    if condition_tracker is None:
        return []
    parent = getattr(pcode_op, "getParent", lambda: None)()
    predecessor = None
    normalized_conditions = list(path_conditions or [])
    if parent is not None:
        get_in_size = getattr(parent, "getInSize", None)
        get_in = getattr(parent, "getIn", None)
        if callable(get_in_size) and callable(get_in):
            current_keys = self._build_condition_signature_set(normalized_conditions)
            best_score = None
            try:
                for index in range(int(get_in_size())):
                    incoming = get_in(index)
                    score = self._score_multiequal_incoming_for_return_path(
                        incoming,
                        None,
                        condition_tracker,
                        current_keys,
                    )
                    if best_score is None or score > best_score[0]:
                        best_score = (score, incoming)
            except Exception:
                best_score = None
            if best_score is not None:
                predecessor = best_score[1]

    selected = self._select_multiequal_input_for_return_path(
        multiequal_op=pcode_op,
        predecessor=predecessor,
        condition_tracker=condition_tracker,
        path_conditions=normalized_conditions,
    )
    if selected is None:
        try:
            selected = pcode_op.getInput(0)
        except Exception:
            selected = None
    if selected is None:
        return []
    return [self._make_tracked_return_value(selected, tracer)]

def _impl__coerce_block_path_entries(self, path_entries) -> Optional[List[Tuple[List[Any], List[Condition]]]]:
    if not isinstance(path_entries, (list, tuple)):
        return None

    normalized: List[Tuple[List[Any], List[Condition]]] = []
    for entry in path_entries:
        if not isinstance(entry, (list, tuple)) or len(entry) != 2:
            return None
        block_path, conditions = entry
        if not isinstance(block_path, (list, tuple)):
            return None
        if not isinstance(conditions, (list, tuple)):
            return None
        normalized.append((list(block_path), list(conditions)))
    return normalized
