"""State-transition loop models (multiplicative / counted / prior-state)."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.core import (
    COUNTED_STATE_TRANSITION_VALUE_OPCODE,
    Condition,
    CountedStateTransitionLoopSummaryRef,
    Expression,
    ExpressionType,
    LoopCaseRef,
    LoopSideEffectProfileRef,
    ReturnInfo,
    STATE_TRANSITION_LOOP_COUNT_OPCODE,
    StateTransitionLoopSummaryRef,
)
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    ConditionSMTOracle,
    ConditionSimplifier,
    CountedLoopAccumulator,
    CountedLoopGuard,
    CountedLoopInduction,
    CountedLoopUpdateCase,
    CountedStateTransitionLoopModel,
    ResidueLoopCase,
    StateTransitionLoopModel,
    _UNSUPPORTED_STATE_TRANSITION_CONDITION,
    _reduce_expression_under_conditions,
    _runtime_conditions_signature,
    _runtime_expression_signature,
)
from scripts.function_tracer_pcode.analysis.debug import summarize_expression


def _impl__counted_loop_transition_evidence_key_from_parts(
    self,
    *,
    header_block,
    latch_block,
    exit_block,
    induction_phi_op,
    accumulator_phi_op,
    guard: CountedLoopGuard,
    accumulator_init_expr: Optional[Expression],
    loop_base_expr: Optional[Expression],
    update_cases: Sequence[CountedLoopUpdateCase],
    loop_cases: Sequence[LoopCaseRef],
) -> Optional[Tuple[Any, ...]]:
    try:
        header_ref = self._make_pcode_block_ref(header_block)
        effective_latch_block = latch_block or getattr(guard, "latch_block", None) or getattr(guard, "body_block", None)
        latch_ref = self._make_pcode_block_ref(effective_latch_block)
        exit_ref = self._make_pcode_block_ref(exit_block)
        induction_phi_ref = self._make_pcode_op_ref(induction_phi_op)
        accumulator_phi_ref = self._make_pcode_op_ref(accumulator_phi_op)
        guard_op = getattr(guard, "guard_op", None)
        if guard_op is None:
            guard_op = self._find_cbranch_op(latch_block)
        if guard_op is None:
            guard_op = self._find_cbranch_op(header_block)
        exit_guard_ref = self._make_pcode_op_ref(guard_op)
        refs = (
            header_ref,
            latch_ref,
            exit_ref,
            induction_phi_ref,
            accumulator_phi_ref,
            exit_guard_ref,
        )
        if any(ref is None for ref in refs):
            return None
        case_keys = tuple(
            self._sanitize_summary_evidence_key(case.stable_key())
            for case in loop_cases or ()
        )
        if not case_keys or any(key is None for key in case_keys):
            return None
        update_keys = tuple(
            (
                _runtime_conditions_signature(tuple(case.conditions or ())),
                _runtime_expression_signature(case.update_expr),
                _runtime_expression_signature(case.delta_expr),
            )
            for case in update_cases or ()
        )
        if not update_keys:
            return None
        accumulator_init_key = _runtime_expression_signature(accumulator_init_expr)
        loop_base_key = _runtime_expression_signature(loop_base_expr)
        prior_dependency_key = self._summary_value_source_key(loop_base_expr)
        if prior_dependency_key is None:
            if accumulator_init_key != loop_base_key:
                return None
            prior_dependency_key = ("prior_summary_dependency", "none")
        return (
            "counted_loop_transition_evidence",
            ("header_block", header_ref.stable_key()),
            ("latch_block", latch_ref.stable_key()),
            ("exit_block", exit_ref.stable_key()),
            ("induction_phi", induction_phi_ref.stable_key()),
            ("accumulator_phi", accumulator_phi_ref.stable_key()),
            ("exit_guard", exit_guard_ref.stable_key()),
            ("exit_guard_binding", _runtime_expression_signature(guard.condition_expr)),
            ("bound_binding", _runtime_expression_signature(guard.bound_expr)),
            (
                "accumulator_base",
                accumulator_init_key,
                loop_base_key,
                prior_dependency_key,
            ),
            ("updates", update_keys),
            ("loop_cases", case_keys),
            ("replacement_obligation", "not_required_without_phi_circular"),
        )
    except Exception:
        return None


def _impl__build_counted_state_transition_value(
    self,
    *,
    initial_state: Expression,
    start_expr: Expression,
    limit_expr: Expression,
    induction_step: int,
    transition_cases: Sequence[Tuple[Tuple[Condition, ...], Expression]],
    state_placeholder: Expression,
    side_effect_profile: LoopSideEffectProfileRef,
    guard_constraints: Sequence[Condition],
    result_size: int,
    signed_loop: bool,
    handoff_proof_key: Optional[Tuple[Any, ...]] = None,
) -> Optional[Expression]:
    if induction_step == 0 or not transition_cases:
        return None
    if any(self._expression_is_unresolved(expr) for expr in (initial_state, start_expr, limit_expr)):
        return None
    case_key = tuple(
        (
            _runtime_conditions_signature(tuple(conditions or ())),
            _runtime_expression_signature(transition_expr),
        )
        for conditions, transition_expr in transition_cases
    )
    step_expr = Expression.constant(
        int(induction_step),
        size=max(1, int(getattr(start_expr, "size", 0) or getattr(limit_expr, "size", 0) or 4)),
    )
    runtime_ref = CountedStateTransitionLoopSummaryRef(
        initial_state=initial_state,
        start_expr=start_expr,
        limit_expr=limit_expr,
        step_expr=step_expr,
        transition_expr=transition_cases[0][1],
        state_placeholder=state_placeholder,
        transition_cases=case_key,
        side_effect_profile=side_effect_profile,
        guard_constraints=tuple(guard_constraints or ()),
        state_size=max(1, int(getattr(state_placeholder, "size", 0) or getattr(initial_state, "size", 0) or 4)),
        result_size=max(1, int(result_size or getattr(initial_state, "size", 0) or 4)),
        signed_loop=bool(signed_loop),
        handoff_proof_key=handoff_proof_key,
    )
    intrinsic = Expression.intrinsic(
        "COUNTED_STATE_TRANSITION_VALUE",
        [initial_state, start_expr, limit_expr],
        size=max(1, int(result_size or getattr(initial_state, "size", 0) or 4)),
        runtime_ref=runtime_ref,
        opcode=COUNTED_STATE_TRANSITION_VALUE_OPCODE,
    )
    intrinsic.size = max(1, int(result_size or getattr(initial_state, "size", 0) or 4))
    return intrinsic


def _impl__recover_proved_multiplicative_state_transition_base(
    self,
    *,
    loop_base_expr: Expression,
    continue_conditions: Sequence[Condition],
    start_expr: Expression,
    limit_expr: Expression,
    result_size: int,
    signed_loop: bool,
    multiplier: Optional[int] = None,
) -> Optional[Expression]:
    """Recover a pure multiplicative state-transition summary for an optimized base.

    This is deliberately proof-backed.  It does not infer a handoff proof or
    claim side-effect coverage for an earlier loop; it only replaces the
    current loop base value when the existing expression and the canonical
    counted state-transition value are SMT-equivalent under the active
    continue partition.
    """
    if loop_base_expr is None:
        return None
    result_size = max(1, int(result_size or getattr(loop_base_expr, "size", 0) or 4))
    if result_size <= 0:
        return None
    if self._expression_is_unresolved(loop_base_expr):
        return None
    if any(getattr(node, "expr_type", None) == ExpressionType.UNKNOWN for node in self._iter_expression_nodes(loop_base_expr)):
        return None
    if any(
        self._expression_is_unresolved(getattr(condition, "expression", None))
        for condition in continue_conditions or ()
        if condition is not None
    ):
        return None
    start_constant = self._raw_constant_value(start_expr)
    if start_constant != 1:
        return None

    for candidate_multiplier in self._multiplicative_state_transition_multiplier_candidates(
        loop_base_expr,
        preferred=multiplier,
    ):
        state_placeholder = Expression.variable("__loop_state", size=result_size)
        transition_expr = Expression.binary_op(
            "INT_MULT",
            state_placeholder,
            Expression.constant(int(candidate_multiplier), size=result_size),
        )
        transition_expr.size = result_size
        candidate = self._build_counted_state_transition_value(
            initial_state=Expression.constant(1, size=result_size),
            start_expr=start_expr,
            limit_expr=limit_expr,
            induction_step=1,
            transition_cases=(((), transition_expr),),
            state_placeholder=state_placeholder,
            side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
            guard_constraints=tuple(continue_conditions or ()),
            result_size=result_size,
            signed_loop=bool(signed_loop),
        )
        if candidate is None:
            continue
        if self._expression_contains_executable_address_constant(candidate):
            continue
        parameters = self._collect_summary_parameter_specs(
            loop_base_expr,
            candidate,
            *(condition.expression for condition in continue_conditions or () if condition is not None),
        )
        if parameters is None:
            continue
        if not self._prove_expression_equivalence_under_conditions(
            loop_base_expr,
            candidate,
            continue_conditions,
            parameters,
        ):
            continue
        self._debug(
            "Recovered multiplicative state-transition base by SMT proof: "
            f"multiplier={int(candidate_multiplier)}, start=1, size={result_size}"
        )
        return candidate
    return None


def _impl__multiplicative_phi_transition_multiplier_candidates(
    self,
    expr: Optional[Expression],
    *,
    max_candidates: int = 8,
) -> Tuple[int, ...]:
    candidates: List[int] = []
    for node in self._iter_expression_nodes(expr):
        if getattr(node, "expr_type", None) != ExpressionType.BINARY_OP:
            continue
        operands = list(getattr(node, "operands", ()) or ())
        if len(operands) != 2:
            continue
        operator = getattr(node, "operator", None)
        if operator == "INT_MULT":
            pairs = ((operands[0], operands[1]), (operands[1], operands[0]))
            for maybe_phi, maybe_const in pairs:
                if not self._return_value_contains_phi_circular(maybe_phi):
                    continue
                multiplier = self._raw_constant_value(maybe_const)
                if multiplier is None:
                    continue
                multiplier = int(multiplier)
                if multiplier in {0, 1}:
                    continue
                if multiplier not in candidates:
                    candidates.append(multiplier)
                break
        elif operator == "INT_LEFT":
            maybe_phi, maybe_shift = operands
            if not self._return_value_contains_phi_circular(maybe_phi):
                continue
            shift = self._raw_constant_value(maybe_shift)
            if shift is None:
                continue
            try:
                multiplier = 1 << int(shift)
            except (OverflowError, ValueError):
                continue
            if multiplier in {0, 1}:
                continue
            if multiplier not in candidates:
                candidates.append(multiplier)
        if len(candidates) >= int(max_candidates):
            break
    if candidates:
        return tuple(candidates[: max(1, int(max_candidates))])
    return self._multiplicative_state_transition_multiplier_candidates(
        expr,
        max_candidates=max_candidates,
    )


def _impl__single_multiplicative_phi_transition_multiplier(
    self,
    recursive_returns: Sequence[ReturnInfo],
) -> Optional[int]:
    """Return the shared multiplier only when every witness proves it.

    The PHI return-region summary emits one transition over one guard.  A
    mix such as ``phi * 2`` and ``phi * 3`` needs partitioned transition
    cases plus coverage proof, so Phase 1.5 rejects it conservatively.
    """

    expected: Optional[int] = None
    for ret in recursive_returns or ():
        candidates: List[int] = []
        for candidate in self._multiplicative_phi_transition_multiplier_candidates(
            getattr(ret, "value", None)
        ):
            candidate = int(candidate)
            if candidate in {0, 1}:
                continue
            if candidate not in candidates:
                candidates.append(candidate)
        if len(candidates) != 1:
            return None
        candidate = int(candidates[0])
        if expected is None:
            expected = candidate
        elif candidate != expected:
            return None
    return expected


def _impl__has_proved_return_region_state_transition_candidate(self, analysis) -> bool:
    parameters = list(getattr(analysis, "parameters", []) or [])
    returns = tuple(getattr(analysis, "returns", ()) or ())
    if len(parameters) != 1 or len(returns) < 2:
        return False
    return any(
        self._raw_constant_value(getattr(ret, "value", None)) == 1
        for ret in returns
    )


def _impl__try_summarize_proved_return_region_state_transition_composition(
    self,
    function,
    high_function,
    analysis,
) -> Optional[Tuple[List[ReturnInfo], str]]:
    parameters = list(getattr(analysis, "parameters", []) or [])
    returns = tuple(getattr(analysis, "returns", ()) or ())
    if len(parameters) != 1 or not returns:
        return None
    count_param = parameters[0]
    count_expr = self._parameter_expression(count_param)
    result_size = max(
        1,
        max(int(getattr(getattr(ret, "value", None), "size", 0) or 0) for ret in returns),
        int(getattr(count_expr, "size", 0) or 4),
    )
    count_expr = self._coerce_summary_expression_to_size(
        count_expr,
        max(1, int(getattr(count_expr, "size", 0) or result_size or 4)),
        signed=True,
    )
    positive_conditions = self._build_recursive_conditions(count_expr, 0)
    if not positive_conditions:
        return None
    if any(
        self._expression_is_unresolved(getattr(condition, "expression", None))
        for condition in positive_conditions
    ):
        return None
    for multiplier in self._return_region_state_transition_multiplier_candidates(returns):
        summary_value = self._build_multiplicative_state_then_triangular_sum_value(
            count_expr=count_expr,
            multiplier=int(multiplier),
            result_size=result_size,
            guard_constraints=positive_conditions,
        )
        if summary_value is None:
            continue
        proof_ref = self._record_return_region_summary_proof(
            analysis=analysis,
            summary_value=summary_value,
            summary_conditions=positive_conditions,
            exact_returns=returns,
            source="return_region_state_transition_composition",
            allow_summary_region_coverage=True,
        )
        if proof_ref is None:
            continue
        preserved_returns = [
            ret for ret in returns
            if not self._return_overlaps_conditions(ret, positive_conditions)
        ]
        anchor = self._first_return_overlapping_conditions(returns, positive_conditions) or returns[0]
        source_key = self._summary_value_source_key(summary_value)
        if source_key is None:
            source_key = (
                "return_region_state_transition_composition",
                _runtime_expression_signature(summary_value),
                int(multiplier),
            )
        summary_return = ReturnInfo(
            address=str(getattr(anchor, "address", None) or getattr(function, "getEntryPoint", lambda: "0x0")()),
            value=summary_value,
            conditions=list(positive_conditions),
            branch_index=30_100,
            pcode_identity=getattr(anchor, "pcode_identity", None),
            pcode_order=getattr(anchor, "pcode_order", None),
            pcode_time=getattr(anchor, "pcode_time", None),
            pcode_op_ref=getattr(anchor, "pcode_op_ref", None),
            return_value_pcode_op_refs=tuple(getattr(anchor, "return_value_pcode_op_refs", ()) or ()),
            return_kind="summary_derived",
            summary_candidate_source_key=source_key,
            summary_transition_evidence_key=proof_ref,
        )
        self._debug(
            "Recovered return-region state-transition composition summary "
            f"(multiplier={int(multiplier)})"
        )
        return preserved_returns + [summary_return], "return_region_state_transition_composition"
    self._debug("Declined return-region state-transition composition summary: proof unavailable")
    return None


def _impl__return_region_state_transition_multiplier_candidates(
    self,
    returns: Sequence[ReturnInfo],
    *,
    max_candidates: int = 8,
) -> Tuple[int, ...]:
    candidates: List[int] = []
    for ret in returns or ():
        value = getattr(ret, "value", None)
        for candidate in self._multiplicative_state_transition_multiplier_candidates(
            value,
            max_candidates=max_candidates,
        ):
            candidate = int(candidate)
            if candidate in {0, 1}:
                continue
            if candidate not in candidates:
                candidates.append(candidate)
            if len(candidates) >= int(max_candidates):
                return tuple(candidates)
    return tuple(candidates)


def _impl__multiplicative_state_transition_multiplier_candidates(
    self,
    expr: Expression,
    *,
    preferred: Optional[int] = None,
    max_candidates: int = 8,
) -> Tuple[int, ...]:
    candidates: List[int] = []
    if preferred is not None:
        try:
            preferred_int = int(preferred)
        except (TypeError, ValueError):
            preferred_int = 0
        if preferred_int not in {0, 1}:
            candidates.append(preferred_int)
    for value in self._expression_integer_constants(expr):
        value = int(value)
        if value in {0, 1}:
            continue
        if value < 0:
            continue
        if value > 0x10000:
            continue
        if value not in candidates:
            candidates.append(value)
        for root in self._small_integer_power_roots(value):
            if root not in candidates:
                candidates.append(root)
            if len(candidates) >= int(max_candidates):
                break
        if len(candidates) >= int(max_candidates):
            break
    return tuple(candidates[: max(1, int(max_candidates))])


def _impl__extract_counted_state_transition_loop_models(
    self,
    high_function,
    analysis,
) -> Tuple[CountedStateTransitionLoopModel, ...]:
    blocks = list(self._iter_basic_blocks(high_function))
    if not blocks:
        return ()
    models: List[CountedStateTransitionLoopModel] = []
    function_body_ranges = self._function_body_address_ranges(high_function, analysis)
    for header in blocks:
        cbranch = self._find_cbranch_op(header)
        if cbranch is None:
            continue
        phi_ops = [
            op for op in self._iter_block_ops(header)
            if getattr(op, "getMnemonic", lambda: None)() == "MULTIEQUAL"
        ]
        if len(phi_ops) < 2:
            continue
        header_key = self._block_key(header)
        induction_candidates = [
            info for info in (self._match_counted_loop_induction(phi_op) for phi_op in phi_ops)
            if info is not None
        ]
        if not induction_candidates:
            self._debug(f"Declined counted state-transition loop at {header_key}: no counted induction")
            continue
        for induction in induction_candidates:
            guards = list(self._candidate_counted_loop_guards(header, cbranch, induction))
            if not guards:
                self._debug(
                    f"Declined counted state-transition loop at {header_key}: no compatible guard"
                )
            for guard in guards:
                loop_body_blocks = self._collect_loop_body_blocks(header_block=header, guard=guard)
                loop_block_guard_info = self._loop_block_guard_effect_info(
                    header_block=header,
                    guard=guard,
                    loop_blocks=loop_body_blocks,
                )
                ignored_branch_ops = [
                    self._find_cbranch_op(block)
                    for block in (header, guard.latch_block)
                    if block is not None
                ]
                side_effect_profile = self._build_loop_side_effect_profile(
                    analysis=analysis,
                    loop_blocks=loop_body_blocks,
                    ignored_branch_ops=ignored_branch_ops,
                    block_guard_info=loop_block_guard_info,
                )
                if side_effect_profile.memory_writes or side_effect_profile.calls or side_effect_profile.escapes:
                    self._debug(
                        f"Declined counted state-transition loop at {header_key}: side effects require proof"
                    )
                    continue
                accumulators = self._match_counted_loop_accumulators(
                    phi_ops,
                    induction,
                    guard.body_block,
                    function_body_ranges=function_body_ranges,
                )
                if not accumulators:
                    self._debug(
                        f"Declined counted state-transition loop at {header_key}: no accumulator"
                    )
                for accumulator in accumulators:
                    transition_cases = self._extract_counted_state_transition_cases(
                        accumulator,
                        induction,
                        guard,
                    )
                    if not transition_cases:
                        self._debug(
                            f"Declined counted state-transition loop at {header_key}: "
                            "no state transition cases"
                        )
                        continue
                    models.append(
                        CountedStateTransitionLoopModel(
                            induction=induction,
                            accumulator=accumulator,
                            guard=guard,
                            transition_cases=transition_cases,
                            side_effect_profile=side_effect_profile,
                        )
                    )
    models.sort(key=lambda model: self._counted_loop_accumulator_priority(model.accumulator), reverse=True)
    return tuple(models)


def _impl__extract_counted_state_transition_cases(
    self,
    accumulator: CountedLoopAccumulator,
    induction: CountedLoopInduction,
    guard: CountedLoopGuard,
) -> Tuple[Tuple[Tuple[Condition, ...], Expression], ...]:
    header_block = getattr(induction.phi_op, "getParent", lambda: None)()
    placeholders = {induction.phi_output: induction.placeholder}
    for output, replacement in zip(accumulator.member_outputs, accumulator.member_placeholders):
        placeholders[output] = replacement
    if not accumulator.member_outputs and accumulator.phi_output is not None:
        placeholders[accumulator.phi_output] = accumulator.placeholder

    raw_cases: List[Tuple[List[Condition], Expression]] = []
    if accumulator.phi_op is None:
        return ()
    parent_block = getattr(accumulator.phi_op, "getParent", lambda: None)()
    in_size = int(getattr(parent_block, "getInSize", lambda: 0)() or 0) if parent_block is not None else 0
    for backedge_index in self._accumulator_backedge_indices(accumulator):
        backedge_varnode = accumulator.phi_op.getInput(backedge_index)
        target_block = None
        def_op = getattr(backedge_varnode, "getDef", lambda: None)()
        if def_op is not None and getattr(def_op, "getMnemonic", lambda: None)() == "MULTIEQUAL":
            def_parent = getattr(def_op, "getParent", lambda: None)()
            def_in_size = int(getattr(def_parent, "getInSize", lambda: 0)() or 0) if def_parent is not None else 0
            input_count = int(getattr(def_op, "getNumInputs", lambda: 0)() or 0)
            for index in range(input_count):
                expr = self._build_pcode_expression(def_op.getInput(index), placeholders=placeholders)
                if expr is None or self._expression_is_unresolved(expr):
                    continue
                branch_target = None
                if def_parent is not None and index < def_in_size:
                    branch_target = def_parent.getIn(index)
                if branch_target is None:
                    branch_target = def_parent or guard.body_block
                for conditions in self._enumerate_paths_with_conditions(
                    start_block=guard.body_block,
                    target_block=branch_target,
                    header_block=header_block,
                    placeholders=placeholders,
                    stop_block=guard.exit_block,
                ):
                    raw_cases.append((conditions, expr))
            continue
        expr = self._build_pcode_expression(backedge_varnode, placeholders=placeholders)
        if expr is None or self._expression_is_unresolved(expr):
            continue
        if parent_block is not None and backedge_index < in_size:
            target_block = parent_block.getIn(backedge_index)
        if target_block is None:
            target_block = getattr(def_op, "getParent", lambda: None)() if def_op is not None else guard.body_block
        for conditions in self._enumerate_paths_with_conditions(
            start_block=guard.body_block,
            target_block=target_block,
            header_block=header_block,
            placeholders=placeholders,
            stop_block=guard.exit_block,
        ):
            raw_cases.append((conditions, expr))
    cases: List[Tuple[Tuple[Condition, ...], Expression]] = []
    seen = set()
    for conditions, update_expr in raw_cases:
        simplified = ConditionSimplifier.simplify_conditions_object_centric(list(conditions or []))
        if ConditionSimplifier.object_centric_is_contradiction(simplified):
            continue
        reduced_update = _reduce_expression_under_conditions(update_expr, simplified) or update_expr
        if not self._expression_mentions_placeholder(reduced_update, accumulator.placeholder):
            continue
        key = (
            _runtime_conditions_signature(simplified),
            _runtime_expression_signature(reduced_update),
        )
        if key in seen:
            continue
        seen.add(key)
        cases.append((tuple(simplified), self._canonicalize_expression(reduced_update)))
    return tuple(cases)


def _impl__prior_counted_state_transition_base_value(
    self,
    *,
    high_function,
    analysis,
    current_induction: CountedLoopInduction,
    current_accumulator: CountedLoopAccumulator,
    current_guard: CountedLoopGuard,
    continue_conditions: Sequence[Condition],
    result_size: int,
) -> Optional[Expression]:
    current_header = getattr(current_induction.phi_op, "getParent", lambda: None)()
    if current_header is None or current_accumulator.phi_op is None:
        return None
    current_init_index = self._accumulator_init_index(current_accumulator, current_induction)
    try:
        current_init_varnode = current_accumulator.phi_op.getInput(current_init_index)
    except Exception:
        return None
    current_init_predecessor = self._phi_input_predecessor_block(
        current_accumulator.phi_op,
        current_init_index,
    )
    if current_init_predecessor is None:
        return None

    candidates = self._extract_counted_state_transition_loop_models(high_function, analysis)
    if self.debug:
        self._debug(
            "Prior state-transition handoff candidates: "
            f"{len(candidates)} for current header {self._block_key(current_header)}"
        )
    current_header_key = self._block_key(current_header)
    for model in candidates:
        prior_induction = model.induction
        prior_accumulator = model.accumulator
        prior_guard = model.guard
        prior_header = getattr(prior_induction.phi_op, "getParent", lambda: None)()
        if self.debug:
            self._debug(
                "Considering prior state-transition handoff candidate: "
                f"prior_header={self._block_key(prior_header)}, "
                f"current_header={current_header_key}, "
                f"start={summarize_expression(prior_induction.init_expr)}, "
                f"limit={summarize_expression(prior_guard.bound_expr)}, "
                f"step={prior_induction.step}, "
                f"cases={len(model.transition_cases)}"
            )
        if prior_header is None or self._block_key(prior_header) == current_header_key:
            if self.debug:
                self._debug("Declined prior state-transition handoff: same or missing prior header")
            continue
        if not self._can_reach_block(prior_guard.exit_block, current_header):
            if self.debug:
                self._debug("Declined prior state-transition handoff: prior exit cannot reach current header")
            continue
        loop_identity_key = self._counted_loop_identity_match_key(
            prior_induction,
            prior_guard,
            current_induction,
            current_guard,
            result_size=result_size,
        )
        if loop_identity_key is None:
            if self.debug:
                self._debug("Declined prior state-transition handoff: loop identity mismatch")
            continue
        value_flow_key = self._prior_state_transition_value_flow_key(
            prior_accumulator,
            current_init_varnode,
        )
        if value_flow_key is None:
            if self.debug:
                self._debug("Declined prior state-transition handoff: value flow not proved")
            continue
        handoff_blocks_key = self._clean_edge_specific_handoff_blocks_key(
            prior_guard.exit_block,
            current_init_predecessor,
            current_header,
        )
        if handoff_blocks_key is None:
            if self.debug:
                self._debug("Declined prior state-transition handoff: clean edge-specific handoff not proved")
            continue
        summary_value = self._build_counted_state_transition_value(
            initial_state=prior_accumulator.init_expr,
            start_expr=prior_induction.init_expr,
            limit_expr=prior_guard.bound_expr,
            induction_step=prior_induction.step,
            transition_cases=model.transition_cases,
            state_placeholder=prior_accumulator.placeholder,
            side_effect_profile=model.side_effect_profile,
            guard_constraints=continue_conditions,
            result_size=max(1, int(result_size or getattr(prior_accumulator.placeholder, "size", 0) or 4)),
            signed_loop=prior_induction.signed_guard or prior_guard.signed_comparison,
        )
        summary_key = self._runtime_ref_stable_key(summary_value)
        if summary_key is None:
            if self.debug:
                self._debug("Declined prior state-transition handoff: summary key unavailable")
            continue
        guard_handoff_key = self._guard_handoff_key(
            prior_guard=prior_guard,
            current_guard=current_guard,
            continue_conditions=continue_conditions,
        )
        if guard_handoff_key is None:
            if self.debug:
                self._debug("Declined prior state-transition handoff: guard handoff not proved")
            continue
        side_effect_key = model.side_effect_profile.stable_key()
        if side_effect_key is None:
            if self.debug:
                self._debug("Declined prior state-transition handoff: side-effect key unavailable")
            continue
        widths_key = self._handoff_widths_key(
            prior_accumulator=prior_accumulator,
            current_init_varnode=current_init_varnode,
            result_size=result_size,
            value_flow_key=value_flow_key,
        )
        if widths_key is None:
            if self.debug:
                self._debug("Declined prior state-transition handoff: width preservation not proved")
            continue
        proof_target_key = (
            "prior_state_transition_handoff_target",
            summary_key,
            handoff_blocks_key,
            value_flow_key,
            guard_handoff_key,
            loop_identity_key,
            side_effect_key,
            widths_key,
        )
        proof_obligation_id = (
            "proof_obligation_id",
            "prior_state_transition_handoff",
            proof_target_key,
        )
        if not self._record_completed_prior_state_transition_handoff_proof(
            analysis,
            proof_obligation_id=proof_obligation_id,
            object_target_key=proof_target_key,
        ):
            continue
        proof_ref_key = (
            "prior_state_transition_handoff_proof_ref",
            proof_obligation_id,
            proof_target_key,
        )
        return self._build_counted_state_transition_value(
            initial_state=prior_accumulator.init_expr,
            start_expr=prior_induction.init_expr,
            limit_expr=prior_guard.bound_expr,
            induction_step=prior_induction.step,
            transition_cases=model.transition_cases,
            state_placeholder=prior_accumulator.placeholder,
            side_effect_profile=model.side_effect_profile,
            guard_constraints=continue_conditions,
            result_size=max(1, int(result_size or getattr(prior_accumulator.placeholder, "size", 0) or 4)),
            signed_loop=prior_induction.signed_guard or prior_guard.signed_comparison,
            handoff_proof_key=proof_ref_key,
        )
    return None


def _impl__record_completed_prior_state_transition_handoff_proof(
    self,
    analysis,
    *,
    proof_obligation_id: Tuple[Any, ...],
    object_target_key: Tuple[Any, ...],
) -> bool:
    if not self.enable_completed_recovery_proofs:
        return False
    if analysis is None:
        return False
    records: List[Dict[str, Any]] = [
        dict(item)
        for item in getattr(analysis, "completed_recovery_proof_evidence", ()) or ()
        if isinstance(item, dict)
    ]
    existing_ids = {
        item.get("proof_obligation_id")
        for item in records
        if isinstance(item.get("proof_obligation_id"), tuple)
    }
    if proof_obligation_id in existing_ids:
        return True
    proof_content = self._prior_state_transition_handoff_proof_content(object_target_key)
    if proof_content is None:
        return False
    records.append(
        {
            "object_derived": True,
            "status": "complete",
            "reason_id": "prior_state_transition_handoff",
            "recovery_proof_kind": "loop_recurrence_proof",
            "proof_stage": "prior_state_transition_handoff",
            "evidence_kind": "value_preserving_handoff",
            "object_target_key": object_target_key,
            "proof_obligation_id": proof_obligation_id,
            "proof_source": "object_level_edge_specific_handoff",
            "proof_content": proof_content,
        }
    )
    analysis.completed_recovery_proof_evidence = tuple(records)
    return True


def _impl__prior_state_transition_handoff_proof_content(
    self,
    object_target_key: Tuple[Any, ...],
) -> Optional[Dict[str, Any]]:
    if not isinstance(object_target_key, tuple) or len(object_target_key) != 8:
        return None
    (
        tag,
        target_summary_key,
        handoff_blocks,
        value_flow,
        guard_handoff,
        loop_identity,
        side_effect_key,
        widths,
    ) = object_target_key
    if tag != "prior_state_transition_handoff_target":
        return None
    return {
        "object_derived": True,
        "object_target_key": object_target_key,
        "handoff_status": "proved",
        "target_summary_key": target_summary_key,
        "handoff_blocks": handoff_blocks,
        "value_flow": value_flow,
        "guard_handoff": guard_handoff,
        "loop_identity": loop_identity,
        "side_effect_profile": side_effect_key,
        "widths": widths,
        "checks": (
            ("phi_predecessor_edge", "proved"),
            ("clean_handoff_paths", "proved"),
            ("value_preserving_flow", "proved"),
            ("guard_handoff", "proved"),
            ("loop_identity", "proved"),
            ("widths", "proved"),
            ("side_effects", "proved"),
        ),
    }


def _impl__prior_state_transition_value_flow_key(
    self,
    prior_accumulator: CountedLoopAccumulator,
    current_init_varnode,
) -> Optional[Tuple[Any, ...]]:
    if current_init_varnode is None:
        return None
    starts = [
        varnode
        for varnode in (prior_accumulator.update_varnode, prior_accumulator.phi_output)
        if varnode is not None
    ]
    for start in starts:
        edges = self._value_preserving_varnode_path(start, current_init_varnode)
        if edges is None:
            continue
        source_key = self._value_flow_varnode_key(start)
        target_key = self._value_flow_varnode_key(current_init_varnode)
        if source_key is None or target_key is None:
            continue
        return (
            "value_preserving_flow",
            source_key,
            target_key,
            tuple(edges),
        )
    return None


def _impl__has_state_transition_loop_candidate(self, high_function) -> bool:
    return self._find_state_transition_loop_model(high_function, analysis=None) is not None


def _impl__try_summarize_state_transition_loop(
    self,
    function,
    high_function,
    analysis,
) -> Optional[Tuple[List[ReturnInfo], str]]:
    model = self._find_state_transition_loop_model(high_function, analysis=analysis)
    if model is None:
        self._debug("Declined state-transition loop summary: no validated transition model")
        return None

    side_effect_profile = self._build_state_transition_loop_side_effect_profile(
        loop_blocks=model.loop_blocks,
    )
    if (
        side_effect_profile.memory_reads
        or side_effect_profile.memory_writes
        or side_effect_profile.calls
        or side_effect_profile.escapes
    ):
        self._debug("Declined state-transition loop summary: loop has side effects outside scalar state")
        return None

    result_size = max(1, int(getattr(model.accumulator_phi_output, "getSize", lambda: 4)() or 4))
    state_size = max(1, int(getattr(model.state_phi_output, "getSize", lambda: 4)() or 4))
    accumulator_init = self._coerce_summary_expression_to_size(
        self._canonicalize_expression(model.accumulator_init_expr),
        result_size,
        signed=self._expression_prefers_signed_extension(model.accumulator_init_expr),
    )
    if self._expression_is_unresolved(accumulator_init):
        self._debug("Declined state-transition loop summary: accumulator seed is unresolved")
        return None
    transition_cases = self._state_transition_summary_cases(
        transition_expr=model.state_transition_expr,
        state_guard=model.state_guard_expr,
        state_placeholder=model.state_placeholder,
    )
    if transition_cases is None:
        self._debug("Declined state-transition loop summary: transition relation has unsupported conditions")
        return None
    summary_ref = StateTransitionLoopSummaryRef(
        state_guard=model.state_guard_expr,
        transition_expr=model.state_transition_expr,
        accumulator_init=model.accumulator_init_expr,
        accumulator_delta=model.accumulator_delta_expr,
        transition_cases=transition_cases,
        side_effect_profile=side_effect_profile,
        state_size=state_size,
        result_size=result_size,
    )
    transition_evidence_key = self._state_transition_loop_transition_evidence_key(summary_ref)
    if transition_evidence_key is None:
        self._debug("Declined state-transition evidence: stable evidence key unavailable")
    loop_count = Expression.intrinsic(
        "STATE_TRANSITION_LOOP_COUNT",
        [model.state_init_expr],
        size=result_size,
        runtime_ref=summary_ref,
        opcode=STATE_TRANSITION_LOOP_COUNT_OPCODE,
    )
    entry_guard_expr = self._substitute_exact_expression(
        model.state_guard_expr,
        model.state_placeholder,
        model.state_init_expr,
    )
    entry_guard_expr = self._substitute_generated_loop_variable_aliases(
        entry_guard_expr,
        model.state_placeholder,
        model.state_init_expr,
    )
    entry_guard_expr = self._substitute_generated_loop_variable_aliases(
        entry_guard_expr,
        Expression.variable(
            "__loop_state",
            size=max(1, int(getattr(model.state_init_expr, "size", 0) or 4)),
        ),
        model.state_init_expr,
    )
    if entry_guard_expr is None or self._expression_is_unresolved(entry_guard_expr):
        self._debug("Declined state-transition loop summary: entry guard is unresolved")
        return None
    entry_guard_expr = self._canonicalize_expression(entry_guard_expr)

    address = str(getattr(function, "getEntryPoint", lambda: "state_transition_loop")())
    pcode_ref = self._make_pcode_op_ref(self._find_cbranch_op(model.header_block))
    site_metadata = {}
    if pcode_ref is not None:
        site_metadata = {
            "pcode_identity": repr(pcode_ref.stable_key()),
            "pcode_time": pcode_ref.seq_time,
            "pcode_order": pcode_ref.seq_order,
        }
    progress_guard_expr = None
    progress_entry_guard_expr = None
    loop_value = _build_small_residue_state_transition_value(
        self,
        model=model,
        side_effect_profile=side_effect_profile,
        result_size=result_size,
    )
    residue_loop_value = loop_value is not None
    if residue_loop_value:
        self._debug("Recovered parity/small-modulus affine state-transition loop value")
    if not residue_loop_value:
        loop_value = self._build_progress_guarded_unit_state_transition_value(
        model=model,
        analysis=analysis,
        result_size=result_size,
        )
    progress_guarded_loop_value = loop_value is not None and not residue_loop_value
    if progress_guarded_loop_value:
        progress_guard_expr = self._progress_guarded_unit_step_expression(model)
        if progress_guard_expr is None:
            return None
        progress_entry_guard_expr = self._progress_guarded_unit_entry_guard_expression(
            model=model,
            progress_guard_expr=progress_guard_expr,
            analysis=analysis,
        )
        if progress_entry_guard_expr is None:
            return None
        self._debug("Recovered progress-guarded unit state-transition loop value")
    multiplicative_loop_value = False
    if not progress_guarded_loop_value and not residue_loop_value:
        loop_value = self._build_multiplicative_state_transition_loop_value(
            model=model,
            analysis=analysis,
            side_effect_profile=side_effect_profile,
            result_size=result_size,
        )
        multiplicative_loop_value = loop_value is not None
        if loop_value is not None:
            self._debug("Recovered multiplicative state-transition loop value")
            zero_iteration_anchor_key = self._state_transition_object_zero_iteration_anchor_key(
                model=model,
                result_size=result_size,
            )
            if zero_iteration_anchor_key is not None and transition_evidence_key is not None:
                transition_evidence_key = (
                    "state_transition_loop_evidence_with_zero_iteration_anchor",
                    transition_evidence_key,
                    ("zero_iteration_anchor_proof", zero_iteration_anchor_key),
                )
        elif self._raw_constant_value(model.accumulator_delta_expr) == 1:
            loop_value = loop_count
        else:
            loop_value = self._build_state_decrement_accumulator_sum_value(
                model=model,
                result_size=result_size,
            )
            if loop_value is None:
                latch_exit_returns = self._try_build_latch_exit_decrement_accumulator_sum_returns(
                    function=function,
                    model=model,
                    analysis=analysis,
                    result_size=result_size,
                    accumulator_init=accumulator_init,
                )
                if latch_exit_returns is not None:
                    self._debug("Recovered latch-exit decrement accumulator sum summary")
                    return latch_exit_returns, "state_transition_loop_summary"
                self._debug(
                    "Declined state-transition loop summary: accumulator delta is not one "
                    "or supported state affine "
                    f"(state_init={self._safe_expr_text(model.state_init_expr)}, "
                    f"state_guard={self._safe_expr_text(model.state_guard_expr)}, "
                    f"state_transition={self._safe_expr_text(model.state_transition_expr)}, "
                    f"accumulator_init={self._safe_expr_text(model.accumulator_init_expr)}, "
                    f"accumulator_delta={self._safe_expr_text(model.accumulator_delta_expr)})"
                )
                return None
    if not multiplicative_loop_value and not residue_loop_value:
        loop_value = self._add_state_transition_accumulator_seed(
            accumulator_init,
            loop_value,
            result_size,
        )
        if loop_value is None:
            self._debug("Declined state-transition loop summary: accumulator seed could not be combined")
            return None
    loop_conditions = [Condition(progress_entry_guard_expr or entry_guard_expr, False)]
    if progress_guard_expr is not None:
        loop_conditions.append(Condition(progress_guard_expr, False))
    exact_exclusion_conditions = self._state_transition_exact_return_exclusion_conditions(
        analysis,
        loop_conditions,
        loop_value,
    )
    # Normalize peeled/latch exact members into the same partition without
    # claiming value equality on their region.  Acceptance retains the exact
    # members and independently proves that their union with this narrowed
    # summary still covers the active precondition.
    loop_conditions.extend(exact_exclusion_conditions)
    # The zero-iteration region is an explicit member of the proposal even
    # when exact-return exclusions narrow the positive-iteration member.
    # Omitting it delegated coverage to a raw PHI return that may itself be
    # unresolved.  The acceptance gate still checks overlap with exact returns.
    returns = [
        ReturnInfo(
            address=address,
            value=accumulator_init,
            conditions=[Condition(entry_guard_expr, True)],
            branch_index=0,
            summary_candidate_source_key=summary_ref.stable_key(),
            summary_transition_evidence_key=transition_evidence_key,
            **site_metadata,
        )
    ]
    returns.append(
        ReturnInfo(
            address=address,
            value=loop_value,
            conditions=loop_conditions,
            branch_index=10_200,
            summary_candidate_source_key=summary_ref.stable_key(),
            summary_transition_evidence_key=transition_evidence_key,
            **site_metadata,
        )
    )
    self._debug("Recovered state-transition loop summary")
    return returns, "state_transition_loop_summary"


def _build_small_residue_state_transition_value(
    self,
    *,
    model: StateTransitionLoopModel,
    side_effect_profile: LoopSideEffectProfileRef,
    result_size: int,
) -> Optional[Expression]:
    """Lower the frequent `(iv & mask)` affine delta for modulus 2/4 only."""

    if side_effect_profile.requires_effect_proof():
        return None
    if not _is_unit_increment(self, model.state_transition_expr, model.state_placeholder):
        return None
    modulus = _small_residue_modulus(
        self, model.accumulator_delta_expr, model.state_placeholder
    )
    if modulus not in {2, 4}:
        return None
    limit_expr, signed_loop = _state_transition_limit(
        self, model.state_guard_expr, model.state_placeholder
    )
    if limit_expr is None:
        return None
    residue_cases = []
    for residue in range(modulus):
        affine = _affine_under_residue(
            self,
            model.accumulator_delta_expr,
            model.state_placeholder,
            modulus,
            residue,
        )
        if affine is None:
            return None
        residue_cases.append(ResidueLoopCase(modulus, residue, affine))
    return self._build_counted_loop_summary_intrinsic(
        base_expr=model.accumulator_init_expr,
        start_expr=model.state_init_expr,
        limit_expr=limit_expr,
        induction_step=1,
        residue_cases=tuple(residue_cases),
        result_size=result_size,
        signed_loop=signed_loop,
        side_effect_profile=side_effect_profile,
    )


def _is_unit_increment(self, expr: Expression, placeholder: Expression) -> bool:
    if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP or expr.operator != "INT_ADD":
        return False
    if len(expr.operands) != 2:
        return False
    left, right = expr.operands
    return (
        self._expr_matches_placeholder(left, placeholder)
        and self._raw_constant_value(right) == 1
    ) or (
        self._expr_matches_placeholder(right, placeholder)
        and self._raw_constant_value(left) == 1
    )


def _small_residue_modulus(
    self, expr: Expression, placeholder: Expression
) -> Optional[int]:
    found = set()
    stack = [expr]
    while stack:
        node = stack.pop()
        if (
            getattr(node, "expr_type", None) == ExpressionType.BINARY_OP
            and getattr(node, "operator", None) == "INT_AND"
            and len(getattr(node, "operands", ()) or ()) == 2
        ):
            left, right = node.operands
            if self._expr_matches_placeholder(left, placeholder):
                mask = self._raw_constant_value(right)
            elif self._expr_matches_placeholder(right, placeholder):
                mask = self._raw_constant_value(left)
            else:
                mask = None
            if mask in {1, 3}:
                found.add(int(mask) + 1)
            elif mask is not None:
                return None
        stack.extend(tuple(getattr(node, "operands", ()) or ()))
    return next(iter(found)) if len(found) == 1 else None


def _state_transition_limit(
    self, guard: Expression, placeholder: Expression
) -> Tuple[Optional[Expression], bool]:
    if getattr(guard, "expr_type", None) != ExpressionType.BINARY_OP or len(guard.operands) != 2:
        return None, False
    left, right = guard.operands
    if guard.operator in {"INT_SLESS", "INT_LESS"} and self._expr_matches_placeholder(left, placeholder):
        return right, guard.operator == "INT_SLESS"
    if guard.operator in {"INT_NOTEQUAL", "INT_EQUAL"}:
        if _is_unit_increment(self, left, placeholder):
            return right, False
        if _is_unit_increment(self, right, placeholder):
            return left, False
    return None, False


def _affine_under_residue(
    self,
    expr: Expression,
    placeholder: Expression,
    modulus: int,
    residue: int,
) -> Optional[Tuple[int, int]]:
    constant = self._raw_constant_value(expr)
    if constant is not None:
        return 0, int(constant)
    if self._expr_matches_placeholder(expr, placeholder):
        return 1, 0
    if getattr(expr, "expr_type", None) == ExpressionType.UNARY_OP and len(expr.operands) == 1:
        if expr.operator in {"INT_ZEXT", "INT_SEXT"}:
            return _affine_under_residue(
                self, expr.operands[0], placeholder, modulus, residue
            )
        return None
    if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return None
    left, right = expr.operands
    if expr.operator == "INT_AND":
        mask = None
        if self._expr_matches_placeholder(left, placeholder):
            mask = self._raw_constant_value(right)
        elif self._expr_matches_placeholder(right, placeholder):
            mask = self._raw_constant_value(left)
        if mask == modulus - 1:
            return 0, residue
        return None
    left_affine = _affine_under_residue(self, left, placeholder, modulus, residue)
    right_affine = _affine_under_residue(self, right, placeholder, modulus, residue)
    if left_affine is None or right_affine is None:
        return None
    if expr.operator == "INT_ADD":
        return left_affine[0] + right_affine[0], left_affine[1] + right_affine[1]
    if expr.operator == "INT_SUB":
        return left_affine[0] - right_affine[0], left_affine[1] - right_affine[1]
    if expr.operator == "INT_MULT":
        if left_affine[0] == 0:
            return right_affine[0] * left_affine[1], right_affine[1] * left_affine[1]
        if right_affine[0] == 0:
            return left_affine[0] * right_affine[1], left_affine[1] * right_affine[1]
    return None


def _impl__build_progress_guarded_unit_state_transition_value(
    self,
    *,
    model: StateTransitionLoopModel,
    analysis,
    result_size: int,
) -> Optional[Expression]:
    progress_guard = self._progress_guarded_unit_step_expression(model)
    if progress_guard is None:
        return None
    if self._progress_guarded_unit_entry_guard_expression(
        model=model,
        progress_guard_expr=progress_guard,
        analysis=analysis,
    ) is None:
        return None
    state_value = self._coerce_summary_expression_to_size(
        model.state_init_expr,
        max(1, int(result_size or getattr(model.state_init_expr, "size", 0) or 4)),
        signed=self._expression_prefers_signed_extension(model.state_init_expr),
    )
    if state_value is None or self._expression_is_unresolved(state_value):
        return None
    return self._canonicalize_expression(state_value)


def _impl__state_transition_exact_return_exclusion_conditions(
    self,
    analysis,
    loop_conditions: Sequence[Condition],
    loop_value: Optional[Expression] = None,
) -> Tuple[Condition, ...]:
    exclusions: List[Condition] = []
    for ret in tuple(getattr(analysis, "returns", ()) or ()):
        if str(getattr(ret, "return_kind", "exact") or "exact") == "summary_derived":
            continue
        if not tuple(getattr(ret, "conditions", None) or ()):
            continue
        if self._expression_is_unresolved(getattr(ret, "value", None)):
            continue
        if not self._conditions_overlap_conditions(
            tuple(getattr(ret, "conditions", None) or ()),
            tuple(loop_conditions or ()),
        ):
            continue
        if loop_value is not None and self._return_value_equals_under_conditions(
            getattr(ret, "value", None),
            loop_value,
            tuple(getattr(ret, "conditions", None) or ()) + tuple(loop_conditions or ()),
        ):
            continue
        exclusion = self._negated_return_region_condition(ret.conditions)
        if exclusion is not None:
            try:
                loop_implies_exact_region = ConditionSMTOracle.conjunction_is_unsat(
                    list(loop_conditions or ()) + [exclusion]
                ) is True
            except Exception:
                loop_implies_exact_region = False
            if loop_implies_exact_region:
                continue
            exclusions.append(exclusion)
    return tuple(exclusions)


def _impl__build_multiplicative_state_transition_loop_value(
    self,
    *,
    model: StateTransitionLoopModel,
    analysis,
    side_effect_profile: LoopSideEffectProfileRef,
    result_size: int,
) -> Optional[Expression]:
    """Lower ``acc = acc * C`` state-transition loops to an exact counted value."""

    multiplier = self._multiplicative_accumulator_delta_multiplier(
        model.accumulator_delta_expr,
        model.accumulator_placeholder,
    )
    if multiplier is None or multiplier in {0, 1}:
        return None
    if side_effect_profile is None:
        return None
    requires_effect_proof = getattr(side_effect_profile, "requires_effect_proof", None)
    if callable(requires_effect_proof):
        try:
            if requires_effect_proof():
                return None
        except Exception:
            return None
    if (
        side_effect_profile.memory_reads
        or side_effect_profile.memory_writes
        or side_effect_profile.calls
        or side_effect_profile.escapes
        or side_effect_profile.context_memory_writes
        or side_effect_profile.context_calls
        or side_effect_profile.context_escapes
    ):
        return None
    result_size = max(
        1,
        int(result_size or 0),
        int(getattr(model.accumulator_placeholder, "size", 0) or 0),
        int(getattr(model.accumulator_init_expr, "size", 0) or 0),
    )
    transition_expr = Expression.binary_op(
        "INT_MULT",
        model.accumulator_placeholder,
        Expression.constant(int(multiplier), size=result_size),
    )
    transition_expr.size = result_size
    start_expr = self._multiplicative_state_transition_iteration_start_expr(
        model=model,
        analysis=analysis,
        result_size=result_size,
        size=max(1, int(getattr(model.state_init_expr, "size", 0) or 4)),
    )
    if start_expr is None:
        return None
    transition_value = self._build_counted_state_transition_value(
        initial_state=self._coerce_summary_expression_to_size(
            model.accumulator_init_expr,
            result_size,
            signed=self._expression_prefers_signed_extension(model.accumulator_init_expr),
        ),
        start_expr=start_expr,
        limit_expr=self._coerce_summary_expression_to_size(
            model.state_init_expr,
            max(1, int(getattr(model.state_init_expr, "size", 0) or 4)),
            signed=self._expression_prefers_signed_extension(model.state_init_expr),
        ),
        induction_step=1,
        transition_cases=(((), transition_expr),),
        state_placeholder=model.accumulator_placeholder,
        side_effect_profile=side_effect_profile,
        guard_constraints=(),
        result_size=result_size,
        signed_loop=True,
    )
    if transition_value is None:
        return None
    if self._expression_contains_executable_address_constant(transition_value):
        return None
    return transition_value


def _impl__state_transition_iteration_start_expr(
    self,
    state_guard: Optional[Expression],
    state_placeholder: Expression,
    *,
    size: int,
) -> Optional[Expression]:
    stop_value = self._state_transition_guard_stop_constant(
        state_guard,
        state_placeholder,
    )
    if stop_value is None:
        return None
    return Expression.constant(int(stop_value), size=max(1, int(size or 4)))


def _impl__multiplicative_state_transition_iteration_start_expr(
    self,
    *,
    model: StateTransitionLoopModel,
    analysis,
    result_size: int,
    size: int,
) -> Optional[Expression]:
    stop_value = self._state_transition_guard_stop_constant(
        model.state_guard_expr,
        model.state_placeholder,
        allow_nonzero=True,
    )
    if stop_value is None:
        return None
    stop_value = int(stop_value)
    if stop_value == 0:
        return Expression.constant(0, size=max(1, int(size or 4)))
    if stop_value == 1 and (
        self._has_exact_accumulator_init_return_at_state_one(
            analysis=analysis,
            state_expr=model.state_init_expr,
            accumulator_init=model.accumulator_init_expr,
            result_size=result_size,
        )
        or self._state_transition_object_zero_iteration_anchor_key(
            model=model,
            result_size=result_size,
        )
        is not None
    ):
        return Expression.constant(1, size=max(1, int(size or 4)))
    if stop_value == 1:
        self._debug("Declined multiplicative state-transition start=1: anchor proof unavailable")
    return None


def _impl__state_transition_object_zero_iteration_anchor_key(
    self,
    *,
    model: StateTransitionLoopModel,
    result_size: int,
) -> Optional[Tuple[Any, ...]]:
    cbranch_op = self._find_cbranch_op(getattr(model, "header_block", None))
    if cbranch_op is None:
        self._debug("Declined zero-iteration anchor proof: header CBRANCH missing")
        return None
    if not self._state_transition_guard_false_at_stop_value(
        model.state_guard_expr,
        model.state_placeholder,
        stop_value=1,
    ):
        self._debug("Declined zero-iteration anchor proof: guard false at stop=1 not proved")
        return None
    expected_exit = self._state_transition_guard_false_successor(model)
    if expected_exit is None or self._block_key(expected_exit) != self._block_key(model.exit_block):
        self._debug("Declined zero-iteration anchor proof: false successor is not model exit block")
        return None
    accumulator_phi = getattr(model, "accumulator_phi_op", None)
    init_index = int(getattr(model, "accumulator_phi_init_index", 0) or 0)
    if accumulator_phi is None or self._safe_pcode_input_count(accumulator_phi) <= init_index:
        self._debug("Declined zero-iteration anchor proof: accumulator PHI init input missing")
        return None
    init_varnode = accumulator_phi.getInput(init_index)
    init_expr = self._build_pcode_expression(
        init_varnode,
        placeholders={
            getattr(model, "state_phi_output", None): model.state_placeholder,
            getattr(model, "accumulator_phi_output", None): model.accumulator_placeholder,
        },
    )
    init_expr = self._canonicalize_expression(init_expr)
    expected_init = self._coerce_summary_expression_to_size(
        self._canonicalize_expression(model.accumulator_init_expr),
        max(1, int(result_size or getattr(model.accumulator_init_expr, "size", 0) or 4)),
        signed=self._expression_prefers_signed_extension(model.accumulator_init_expr),
    )
    if init_expr is None or expected_init is None or self._expression_is_unresolved(init_expr):
        self._debug("Declined zero-iteration anchor proof: init expression unresolved")
        return None
    if not self._return_value_equals_under_conditions(init_expr, expected_init, ()):
        self._debug("Declined zero-iteration anchor proof: init expression does not match accumulator init")
        return None
    exit_region_proof = self._exit_region_return_refs_using_value(
        model.exit_block,
        init_varnode,
        phi_output_varnode=getattr(model, "accumulator_phi_output", None),
        forbidden_blocks=tuple(getattr(model, "loop_blocks", ()) or ()),
    )
    if exit_region_proof is None:
        self._debug("Declined zero-iteration anchor proof: exit region does not purely return init value")
        return None
    return_refs, exit_region_scan_refs = exit_region_proof
    if not return_refs:
        self._debug("Declined zero-iteration anchor proof: return refs missing")
        return None
    cbranch_ref = self._make_pcode_op_ref(cbranch_op)
    exit_ref = self._make_pcode_block_ref(model.exit_block)
    accumulator_phi_ref = self._make_pcode_op_ref(accumulator_phi)
    return (
        "state_transition_zero_iteration_anchor_proof",
        ("stop_value", 1),
        ("guard_false_edge", self._block_key(model.header_block), self._block_key(model.exit_block)),
        ("guard_key", self._summary_expression_evidence_key(model.state_guard_expr)),
        ("state_placeholder_key", self._summary_expression_evidence_key(model.state_placeholder)),
        ("accumulator_init_key", self._summary_expression_evidence_key(expected_init)),
        ("init_varnode_key", self._varnode_cache_key(init_varnode)),
        ("accumulator_phi_output_key", self._varnode_cache_key(getattr(model, "accumulator_phi_output", None))),
        ("cbranch_ref", cbranch_ref.stable_key() if cbranch_ref is not None else None),
        ("exit_block_ref", exit_ref.stable_key() if exit_ref is not None else self._block_key(model.exit_block)),
        ("accumulator_phi_ref", accumulator_phi_ref.stable_key() if accumulator_phi_ref is not None else None),
        (
            "exit_region_purity_policy",
            (
                "state_transition_zero_iteration_exit_region_purity",
                1,
                "reject_effect_memory_call_indirect_control_fp_unknown",
            ),
        ),
        ("exit_region_scan_refs", exit_region_scan_refs),
        ("return_refs", tuple(ref.stable_key() for ref in return_refs)),
    )


def _impl__state_transition_guard_false_at_stop_value(
    self,
    state_guard: Optional[Expression],
    state_placeholder: Expression,
    *,
    stop_value: int,
) -> bool:
    proven_stop = self._state_transition_guard_stop_constant(
        state_guard,
        state_placeholder,
        allow_nonzero=True,
    )
    if proven_stop is not None and int(proven_stop) == int(stop_value):
        return True
    state_size = max(1, int(getattr(state_placeholder, "size", 0) or 4))
    state_equals_stop = Expression.binary_op(
        "INT_EQUAL",
        self._canonicalize_expression(state_placeholder),
        Expression.constant(int(stop_value), size=state_size),
    )
    state_equals_stop.size = 1
    try:
        return ConditionSMTOracle.conjunction_is_unsat(
            [
                Condition(self._canonicalize_expression(state_equals_stop), False),
                Condition(self._canonicalize_expression(state_guard), False),
            ]
        ) is True
    except Exception:
        return False


def _impl__state_transition_guard_false_successor(
    self,
    model: StateTransitionLoopModel,
):
    header = getattr(model, "header_block", None)
    true_out = getattr(header, "getTrueOut", lambda: None)()
    false_out = getattr(header, "getFalseOut", lambda: None)()
    return false_out if bool(getattr(model, "continue_on_true", False)) else true_out


def _impl__state_transition_guard_stop_constant(
    self,
    state_guard: Optional[Expression],
    state_placeholder: Expression,
    *,
    allow_nonzero: bool = False,
) -> Optional[int]:
    guard = self._canonicalize_expression(state_guard)
    if guard is None:
        return None
    if (
        guard.expr_type == ExpressionType.BINARY_OP
        and guard.operator == "BOOL_AND"
        and len(guard.operands) == 2
    ):
        state_dependent_stops: List[int] = []
        for operand in self._flatten_bool_and_expression(guard):
            if not self._expression_mentions_placeholder(operand, state_placeholder):
                continue
            stop = self._state_transition_guard_stop_constant(
                operand,
                state_placeholder,
                allow_nonzero=allow_nonzero,
            )
            if stop is None:
                return None
            state_dependent_stops.append(int(stop))
        if not state_dependent_stops:
            return None
        unique_stops = set(state_dependent_stops)
        if len(unique_stops) == 1:
            return state_dependent_stops[0]
        return None
    if (
        guard.expr_type == ExpressionType.BINARY_OP
        and guard.operator == "INT_NOTEQUAL"
        and len(guard.operands) == 2
    ):
        left, right = guard.operands
        right_const = self._raw_constant_value(right)
        if right_const is not None and self._expr_matches_placeholder(left, state_placeholder):
            stop = int(right_const)
            if stop == 0 or allow_nonzero:
                return stop
        if right_const == 0:
            affine = self._extract_affine_placeholder_term(left, state_placeholder)
            if affine is not None:
                coeff, bias = affine
                if int(coeff) == 1:
                    stop = -int(bias)
                    if stop == 0 or allow_nonzero:
                        return stop
        left_const = self._raw_constant_value(left)
        if left_const is not None and self._expr_matches_placeholder(right, state_placeholder):
            stop = int(left_const)
            if stop == 0 or allow_nonzero:
                return stop
        if left_const == 0:
            affine = self._extract_affine_placeholder_term(right, state_placeholder)
            if affine is not None:
                coeff, bias = affine
                if int(coeff) == 1:
                    stop = -int(bias)
                    if stop == 0 or allow_nonzero:
                        return stop
    if (
        guard.expr_type == ExpressionType.BINARY_OP
        and guard.operator == "INT_SLESS"
        and len(guard.operands) == 2
    ):
        left, right = guard.operands
        if (
            self._raw_constant_value(left) == 0
            and self._expr_matches_placeholder(right, state_placeholder)
        ):
            return 0
    return None


def _impl__state_transition_loop_transition_evidence_key(
    self,
    summary_ref: StateTransitionLoopSummaryRef,
) -> Optional[Tuple[Any, ...]]:
    if summary_ref is None:
        return None
    side_effect_profile = getattr(summary_ref, "side_effect_profile", None)
    if side_effect_profile is None:
        self._debug("State-transition evidence unavailable: side-effect profile missing")
        return None
    if getattr(side_effect_profile, "requires_effect_proof", lambda: True)():
        self._debug("State-transition evidence unavailable: side-effect profile requires proof")
        return None
    side_effect_key = side_effect_profile.stable_key()
    guard_key = self._summary_expression_evidence_key(getattr(summary_ref, "state_guard", None))
    transition_key = self._summary_expression_evidence_key(getattr(summary_ref, "transition_expr", None))
    accumulator_init_key = self._summary_expression_evidence_key(
        getattr(summary_ref, "accumulator_init", None)
    )
    accumulator_delta_key = self._summary_expression_evidence_key(
        getattr(summary_ref, "accumulator_delta", None)
    )
    transition_cases_key = self._state_transition_cases_evidence_key(
        getattr(summary_ref, "transition_cases", None)
    )
    if transition_cases_key is None and transition_key is not None:
        transition_cases_key = ("transition_cases", "uniform_transition_expr", transition_key)
    if any(
        key is None
        for key in (
            side_effect_key,
            guard_key,
            transition_key,
            accumulator_init_key,
            accumulator_delta_key,
            transition_cases_key,
        )
    ):
        missing = [
            name
            for name, key in (
                ("side_effect_key", side_effect_key),
                ("guard_key", guard_key),
                ("transition_key", transition_key),
                ("accumulator_init_key", accumulator_init_key),
                ("accumulator_delta_key", accumulator_delta_key),
                ("transition_cases_key", transition_cases_key),
            )
            if key is None
        ]
        self._debug(
            "State-transition evidence unavailable: missing " + ",".join(missing)
        )
        return None
    summary_key = (
        "state_transition_loop_summary",
        guard_key,
        transition_cases_key,
        accumulator_init_key,
        accumulator_delta_key,
        side_effect_key,
        int(getattr(summary_ref, "state_size", 0) or 0),
        int(getattr(summary_ref, "result_size", 0) or 0),
        str(getattr(summary_ref, "source", "") or "state_transition_loop_summary"),
    )
    return (
        "state_transition_loop_evidence",
        ("summary_key", summary_key),
        ("guard_key", guard_key),
        ("transition_key", transition_key),
        ("accumulator_init_key", accumulator_init_key),
        ("accumulator_delta_key", accumulator_delta_key),
        ("transition_cases_key", transition_cases_key),
        ("side_effect_profile_key", side_effect_key),
        ("replacement_obligation", "not_required_without_phi_circular"),
    )


def _impl__state_transition_cases_evidence_key(self, cases: Any) -> Optional[Tuple[Any, ...]]:
    if not isinstance(cases, (tuple, list)) or not cases:
        return None
    entries: List[Tuple[Any, ...]] = []
    for case in cases:
        if not isinstance(case, (tuple, list)) or len(case) != 2:
            return None
        conditions, expr = case
        try:
            condition_key = _runtime_conditions_signature(tuple(conditions or ()))
            expr_key = _runtime_expression_signature(expr)
        except Exception as exc:
            self._debug(
                "State-transition evidence unavailable: transition case signature failed "
                f"({type(exc).__name__}: {exc})"
            )
            return None
        if condition_key is None or expr_key is None:
            self._debug(
                "State-transition evidence unavailable: transition case key missing "
                f"(conditions={condition_key is not None}, expr={expr_key is not None}, "
                f"expr_type={getattr(expr, 'expr_type', None)}, operator={getattr(expr, 'operator', None)}, "
                f"name={getattr(expr, 'name', None)})"
            )
            return None
        entries.append(("transition_case", condition_key, expr_key))
    entries.sort(key=repr)
    return ("transition_cases", tuple(entries))


def _impl__add_state_transition_accumulator_seed(
    self,
    accumulator_init: Expression,
    loop_value: Optional[Expression],
    result_size: int,
) -> Optional[Expression]:
    if loop_value is None or accumulator_init is None:
        return None
    result_size = max(1, int(result_size or getattr(loop_value, "size", 0) or 4))
    loop_value = self._coerce_summary_expression_to_size(
        loop_value,
        result_size,
        signed=self._expression_prefers_signed_extension(loop_value),
    )
    accumulator_init = self._coerce_summary_expression_to_size(
        accumulator_init,
        result_size,
        signed=self._expression_prefers_signed_extension(accumulator_init),
    )
    if self._raw_constant_value(accumulator_init) == 0:
        loop_value.size = result_size
        return loop_value
    combined = self._sum_expression_terms([accumulator_init, loop_value])
    if combined is None:
        return None
    combined.size = result_size
    return self._canonicalize_expression(combined)


def _impl__find_state_transition_loop_model(
    self,
    high_function,
    *,
    analysis=None,
) -> Optional[StateTransitionLoopModel]:
    if high_function is None:
        return None
    candidates: List[StateTransitionLoopModel] = []
    for header_block in self._iter_basic_blocks(high_function):
        cbranch_op = self._find_cbranch_op(header_block)
        phi_ops = [
            op for op in self._iter_block_ops(header_block)
            if getattr(op, "getMnemonic", lambda: None)() == "MULTIEQUAL"
            and getattr(op, "getOutput", lambda: None)() is not None
        ]
        if not phi_ops:
            continue
        if cbranch_op is not None and self._safe_pcode_input_count(cbranch_op) >= 2:
            block_info = self._pick_body_and_exit_blocks(header_block)
            if block_info is not None:
                body_block, exit_block, body_on_true = block_info
                for state_phi in phi_ops:
                    state_model = self._try_build_state_transition_model_for_phi(
                        header_block=header_block,
                        body_block=body_block,
                        exit_block=exit_block,
                        continue_on_true=body_on_true,
                        cbranch_op=cbranch_op,
                        phi_ops=phi_ops,
                        state_phi=state_phi,
                        analysis=analysis,
                    )
                    if state_model is not None:
                        candidates.append(state_model)
        for state_phi in phi_ops:
            state_model = self._try_build_latch_guarded_state_transition_model_for_phi(
                header_block=header_block,
                phi_ops=phi_ops,
                state_phi=state_phi,
                analysis=analysis,
            )
            if state_model is not None:
                candidates.append(state_model)
    if not candidates:
        return None
    candidates.sort(key=self._state_transition_model_priority, reverse=True)
    return candidates[0]


def _impl__try_build_latch_guarded_state_transition_model_for_phi(
    self,
    *,
    header_block,
    phi_ops: Sequence[object],
    state_phi,
    analysis=None,
) -> Optional[StateTransitionLoopModel]:
    state_output = getattr(state_phi, "getOutput", lambda: None)()
    if state_output is None:
        return None
    phi_indices = self._state_loop_phi_indices(header_block, state_phi)
    if phi_indices is None:
        return None
    init_index, backedge_indices = phi_indices
    if not backedge_indices:
        return None
    in_size = int(getattr(header_block, "getInSize", lambda: 0)() or 0)
    header_key = self._block_key(header_block)
    loop_variable_binder_scope = self._new_loop_variable_binder_scope()
    state_placeholder = self._loop_variable_expression(
        loop_variable_binder_scope,
        "state",
        "__loop_state",
        state_output,
        max(1, int(getattr(state_output, "getSize", lambda: 4)() or 4)),
    )
    latch_infos = []
    state_guard_exprs = []
    exit_blocks = []
    for backedge_index in backedge_indices:
        backedge_index = int(backedge_index)
        if backedge_index >= in_size:
            return None
        latch_block = header_block.getIn(backedge_index)
        latch_cbranch = self._find_cbranch_op(latch_block)
        if latch_cbranch is None or self._safe_pcode_input_count(latch_cbranch) < 2:
            return None
        successors = self._collect_block_successors(latch_block)
        if len(successors) != 2:
            return None
        header_successors = [successor for successor in successors if self._block_key(successor) == header_key]
        exit_successors = [successor for successor in successors if self._block_key(successor) != header_key]
        if len(header_successors) != 1 or len(exit_successors) != 1:
            return None
        exit_block = exit_successors[0]
        true_out = getattr(latch_block, "getTrueOut", lambda: None)()
        false_out = getattr(latch_block, "getFalseOut", lambda: None)()
        if true_out is not None and self._block_key(true_out) == header_key:
            continue_on_true = True
        elif false_out is not None and self._block_key(false_out) == header_key:
            continue_on_true = False
        else:
            return None

        backedge_state = state_phi.getInput(backedge_index)
        state_guard = self._build_pcode_expression(
            latch_cbranch.getInput(1),
            placeholders={
                state_output: state_placeholder,
                backedge_state: state_placeholder,
            },
        )
        if state_guard is None or self._expression_is_unresolved(state_guard):
            return None
        if not continue_on_true:
            state_guard = Expression.unary_op("BOOL_NEGATE", state_guard)
            state_guard.size = 1
        state_guard = self._normalize_state_transition_state_guard(
            state_guard,
            state_placeholder,
        )
        if not self._expression_mentions_placeholder(state_guard, state_placeholder):
            return None
        latch_infos.append((latch_block, continue_on_true))
        state_guard_exprs.append(state_guard)
        exit_blocks.append(exit_block)

    if not state_guard_exprs:
        return None
    state_guard = state_guard_exprs[0]
    guard_signature = _runtime_expression_signature(state_guard)
    if any(_runtime_expression_signature(candidate) != guard_signature for candidate in state_guard_exprs[1:]):
        if not all(self._state_guard_proves_signed_positive_placeholder(candidate, state_placeholder) for candidate in state_guard_exprs):
            return None
        state_guard = self._positive_state_guard_expression(state_placeholder)
    continue_on_true = bool(latch_infos[0][1])
    exit_block = exit_blocks[0]

    state_init = self._build_pcode_expression(
        state_phi.getInput(init_index),
        placeholders={state_output: state_placeholder},
    )
    if state_init is None or self._expression_is_unresolved(state_init):
        return None
    state_init = self._canonicalize_expression(state_init)

    state_transition = self._build_state_transition_expression(
        header_block=header_block,
        body_block=header_block,
        exit_block=exit_block,
        phi_op=state_phi,
        placeholder=state_placeholder,
        backedge_indices=backedge_indices,
    )
    if state_transition is None or self._expression_is_unresolved(state_transition):
        return None
    state_transition = self._canonicalize_expression(state_transition)
    if not self._expression_mentions_placeholder(state_transition, state_placeholder):
        return None

    loop_blocks = self._collect_state_transition_loop_blocks(
        header_block=header_block,
        body_block=header_block,
        exit_block=exit_block,
        backedge_indices=backedge_indices,
    )
    if not loop_blocks:
        return None
    accumulator_model = self._find_state_loop_accumulator(
        phi_ops=self._collect_state_transition_loop_phi_ops(loop_blocks, phi_ops),
        state_phi=state_phi,
        state_output=state_output,
        state_placeholder=state_placeholder,
        init_index=init_index,
        backedge_indices=backedge_indices,
        analysis=analysis,
        loop_variable_binder_scope=loop_variable_binder_scope,
    )
    if accumulator_model is None:
        return None
    (
        accumulator_phi,
        accumulator_output,
        accumulator_init,
        accumulator_delta,
        accumulator_placeholder,
        accumulator_init_index,
        accumulator_backedge_indices,
    ) = accumulator_model

    return StateTransitionLoopModel(
        header_block=header_block,
        body_block=header_block,
        exit_block=exit_block,
        state_phi_op=state_phi,
        state_phi_output=state_output,
        state_init_expr=state_init,
        state_placeholder=state_placeholder,
        state_guard_expr=state_guard,
        state_transition_expr=state_transition,
        accumulator_phi_op=accumulator_phi,
        accumulator_phi_output=accumulator_output,
        accumulator_init_expr=accumulator_init,
        accumulator_delta_expr=accumulator_delta,
        accumulator_placeholder=accumulator_placeholder,
        continue_on_true=continue_on_true,
        loop_blocks=loop_blocks,
        state_phi_init_index=int(init_index),
        accumulator_phi_init_index=int(accumulator_init_index),
        state_phi_backedge_indices=tuple(int(index) for index in backedge_indices),
        accumulator_phi_backedge_indices=tuple(int(index) for index in accumulator_backedge_indices),
    )


def _impl__try_build_state_transition_model_for_phi(
    self,
    *,
    header_block,
    body_block,
    exit_block,
    continue_on_true: bool,
    cbranch_op,
    phi_ops: Sequence[object],
    state_phi,
    analysis=None,
) -> Optional[StateTransitionLoopModel]:
    state_output = getattr(state_phi, "getOutput", lambda: None)()
    if state_output is None:
        return None
    input_count = self._safe_pcode_input_count(state_phi)
    if input_count < 2:
        return None
    phi_indices = self._state_loop_phi_indices(header_block, state_phi)
    if phi_indices is None:
        return None
    init_index, backedge_indices = phi_indices
    loop_variable_binder_scope = self._new_loop_variable_binder_scope()
    state_placeholder = self._loop_variable_expression(
        loop_variable_binder_scope,
        "state",
        "__loop_state",
        state_output,
        max(1, int(getattr(state_output, "getSize", lambda: 4)() or 4)),
    )
    state_guard = self._build_pcode_expression(
        cbranch_op.getInput(1),
        placeholders={state_output: state_placeholder},
    )
    if state_guard is None or self._expression_is_unresolved(state_guard):
        return None
    if not continue_on_true:
        state_guard = Expression.unary_op("BOOL_NEGATE", state_guard)
        state_guard.size = 1
    state_guard = self._canonicalize_expression(state_guard)
    if not self._expression_mentions_placeholder(state_guard, state_placeholder):
        return None

    state_init = self._build_pcode_expression(
        state_phi.getInput(init_index),
        placeholders={state_output: state_placeholder},
    )
    if state_init is None or self._expression_is_unresolved(state_init):
        return None
    state_init = self._canonicalize_expression(state_init)

    state_transition = self._build_state_transition_expression(
        header_block=header_block,
        body_block=body_block,
        exit_block=exit_block,
        phi_op=state_phi,
        placeholder=state_placeholder,
        backedge_indices=backedge_indices,
    )
    if state_transition is None or self._expression_is_unresolved(state_transition):
        return None
    state_transition = self._canonicalize_expression(state_transition)
    if not self._expression_mentions_placeholder(state_transition, state_placeholder):
        return None

    loop_blocks = self._collect_state_transition_loop_blocks(
        header_block=header_block,
        body_block=body_block,
        exit_block=exit_block,
        backedge_indices=backedge_indices,
    )
    if not loop_blocks:
        return None
    accumulator_model = self._find_state_loop_accumulator(
        phi_ops=self._collect_state_transition_loop_phi_ops(loop_blocks, phi_ops),
        state_phi=state_phi,
        state_output=state_output,
        state_placeholder=state_placeholder,
        init_index=init_index,
        backedge_indices=backedge_indices,
        analysis=analysis,
        loop_variable_binder_scope=loop_variable_binder_scope,
    )
    if accumulator_model is None:
        return None
    (
        accumulator_phi,
        accumulator_output,
        accumulator_init,
        accumulator_delta,
        accumulator_placeholder,
        accumulator_init_index,
        accumulator_backedge_indices,
    ) = accumulator_model

    return StateTransitionLoopModel(
        header_block=header_block,
        body_block=body_block,
        exit_block=exit_block,
        state_phi_op=state_phi,
        state_phi_output=state_output,
        state_init_expr=state_init,
        state_placeholder=state_placeholder,
        state_guard_expr=state_guard,
        state_transition_expr=state_transition,
        accumulator_phi_op=accumulator_phi,
        accumulator_phi_output=accumulator_output,
        accumulator_init_expr=accumulator_init,
        accumulator_delta_expr=accumulator_delta,
        accumulator_placeholder=accumulator_placeholder,
        continue_on_true=continue_on_true,
        loop_blocks=loop_blocks,
        state_phi_init_index=int(init_index),
        accumulator_phi_init_index=int(accumulator_init_index),
        state_phi_backedge_indices=tuple(int(index) for index in backedge_indices),
        accumulator_phi_backedge_indices=tuple(int(index) for index in accumulator_backedge_indices),
    )


def _impl__build_state_transition_expression(
    self,
    *,
    header_block,
    body_block,
    exit_block,
    phi_op,
    placeholder: Expression,
    backedge_indices: Sequence[int],
) -> Optional[Expression]:
    phi_output = getattr(phi_op, "getOutput", lambda: None)()
    branches = []
    parent_block = getattr(phi_op, "getParent", lambda: None)()
    for backedge_index in backedge_indices:
        input_varnode = phi_op.getInput(backedge_index)
        input_def = getattr(input_varnode, "getDef", lambda: None)()
        if input_def is not None and getattr(input_def, "getMnemonic", lambda: None)() == "MULTIEQUAL":
            nested_parent = getattr(input_def, "getParent", lambda: None)()
            nested_in_size = int(getattr(nested_parent, "getInSize", lambda: 0)() or 0) if nested_parent is not None else 0
            nested_input_count = self._safe_pcode_input_count(input_def)
            for nested_index in range(nested_input_count):
                value = self._build_pcode_expression(
                    input_def.getInput(nested_index),
                    placeholders={phi_output: placeholder},
                )
                if value is None or self._expression_is_unresolved(value):
                    return None
                target_block = nested_parent.getIn(nested_index) if nested_parent is not None and nested_index < nested_in_size else nested_parent
                path_conditions = self._state_transition_predecessor_path_conditions(
                    body_block=body_block,
                    predecessor_block=target_block,
                    join_block=nested_parent,
                    header_block=header_block,
                    exit_block=exit_block,
                    placeholders={phi_output: placeholder},
                )
                if path_conditions is None:
                    return None
                for condition in path_conditions:
                    branches.append((condition, value))
            continue

        value = self._build_pcode_expression(
            input_varnode,
            placeholders={phi_output: placeholder},
        )
        if value is None or self._expression_is_unresolved(value):
            return None
        target_block = None
        if parent_block is not None and backedge_index < int(getattr(parent_block, "getInSize", lambda: 0)() or 0):
            target_block = parent_block.getIn(backedge_index)
        path_conditions = self._state_transition_path_conditions(
            body_block=body_block,
            target_block=target_block,
            header_block=header_block,
            exit_block=exit_block,
            placeholders={phi_output: placeholder},
        )
        if path_conditions is None:
            return None
        for condition in path_conditions:
            branches.append((condition, value))
    if not branches:
        return None
    if len(branches) == 1 and branches[0][0] is None:
        return branches[0][1]
    phi = Expression.phi(branches)
    phi.size = max(1, int(getattr(phi_output, "getSize", lambda: 4)() or 4))
    return phi


def _impl__state_transition_predecessor_path_conditions(
    self,
    *,
    body_block,
    predecessor_block,
    join_block,
    header_block,
    exit_block,
    placeholders: Dict[object, Expression],
) -> Optional[Tuple[Optional[Condition], ...]]:
    if predecessor_block is None:
        return self._state_transition_path_conditions(
            body_block=body_block,
            target_block=join_block,
            header_block=header_block,
            exit_block=exit_block,
            placeholders=placeholders,
        )
    paths, incomplete = self._enumerate_paths_with_conditions_result(
        start_block=body_block,
        target_block=predecessor_block,
        header_block=header_block,
        placeholders=placeholders,
        stop_block=exit_block,
        limit=16,
    )
    if incomplete or not paths:
        return None
    result = []
    edge_condition = None
    if join_block is not None and self._block_key(predecessor_block) != self._block_key(join_block):
        edge_condition = self._build_block_edge_condition(
            predecessor_block,
            join_block,
            placeholders=placeholders,
        )
    for path in paths:
        path_conditions = list(path or [])
        if edge_condition is not None:
            path_conditions.append(edge_condition)
        simplified = ConditionSimplifier.simplify_conditions_object_centric(path_conditions)
        if ConditionSimplifier.object_centric_is_contradiction(simplified):
            continue
        result.append(self._combine_conditions_for_state_transition(simplified))
    if not result:
        return None
    return tuple(result)


def _impl__state_transition_path_conditions(
    self,
    *,
    body_block,
    target_block,
    header_block,
    exit_block,
    placeholders: Dict[object, Expression],
) -> Optional[Tuple[Optional[Condition], ...]]:
    paths, incomplete = self._enumerate_paths_with_conditions_result(
        start_block=body_block,
        target_block=target_block,
        header_block=header_block,
        placeholders=placeholders,
        stop_block=exit_block,
        limit=16,
    )
    if incomplete or not paths:
        return None
    result = []
    for path in paths:
        simplified = ConditionSimplifier.simplify_conditions_object_centric(list(path or []))
        if ConditionSimplifier.object_centric_is_contradiction(simplified):
            continue
        result.append(self._combine_conditions_for_state_transition(simplified))
    if not result:
        return None
    return tuple(result)


def _impl__combine_conditions_for_state_transition(
    self,
    conditions: Sequence[Condition],
) -> Optional[Condition]:
    conditions = tuple(sorted(
        conditions or (),
        key=lambda condition: (
            _runtime_expression_signature(getattr(condition, "expression", None)),
            bool(getattr(condition, "negated", False)),
        ),
    ))
    if not conditions:
        return None
    expr = None
    for condition in conditions:
        cond_expr = getattr(condition, "expression", None)
        if cond_expr is None:
            return None
        if getattr(condition, "negated", False):
            cond_expr = Expression.unary_op("BOOL_NEGATE", cond_expr)
            cond_expr.size = 1
        expr = cond_expr if expr is None else Expression.binary_op("BOOL_AND", expr, cond_expr)
        expr.size = 1
    return Condition(self._canonicalize_expression(expr), False)


def _impl__state_transition_summary_cases(
    self,
    *,
    transition_expr: Expression,
    state_guard: Expression,
    state_placeholder: Expression,
) -> Optional[Tuple[Tuple[Optional[Expression], bool, Expression], ...]]:
    cases = []
    raw_cases = (
        tuple(getattr(transition_expr, "value", ()) or ())
        if getattr(transition_expr, "expr_type", None) == ExpressionType.PHI
        else ((None, transition_expr),)
    )
    canonical_values = []
    for _condition, value in raw_cases:
        canonical_value = self._canonicalize_state_transition_value(
            value,
            state_placeholder=state_placeholder,
            state_guard=state_guard,
        )
        if canonical_value is None:
            return None
        canonical_values.append(canonical_value)
    if len(canonical_values) > 1:
        first_value_key = _runtime_expression_signature(canonical_values[0])
        if all(_runtime_expression_signature(value) == first_value_key for value in canonical_values[1:]):
            return ((None, False, canonical_values[0]),)
    for (condition, value), canonical_value in zip(raw_cases, canonical_values):
        is_source_default = condition is None
        canonical_condition = self._canonicalize_state_transition_condition(
            condition,
            branch_value=value,
            canonical_branch_value=canonical_value,
            state_guard=state_guard,
            state_placeholder=state_placeholder,
        )
        if canonical_condition is _UNSUPPORTED_STATE_TRANSITION_CONDITION:
            return None
        if canonical_condition is None and not is_source_default and len(raw_cases) > 1:
            return None
        cases.append((
            getattr(canonical_condition, "expression", None) if canonical_condition is not None else None,
            bool(getattr(canonical_condition, "negated", False)) if canonical_condition is not None else False,
            canonical_value,
            is_source_default,
        ))
    cases = list(self._complete_default_state_transition_cases(cases))
    cases.sort(
        key=lambda item: (
            _runtime_expression_signature(item[0]) if item[0] is not None else ("none",),
            bool(item[1]),
            _runtime_expression_signature(item[2]),
        )
    )
    return tuple((condition, negated, value) for condition, negated, value, _is_source_default in cases)


def _impl__canonicalize_state_transition_condition(
    self,
    condition: Optional[Condition],
    *,
    branch_value: Expression,
    canonical_branch_value: Optional[Expression] = None,
    state_guard: Expression,
    state_placeholder: Expression,
) -> Optional[Condition]:
    if condition is None:
        return None
    expr = getattr(condition, "expression", None)
    if expr is None:
        return None
    if getattr(condition, "negated", False):
        expr = Expression.unary_op("BOOL_NEGATE", expr)
        expr.size = 1
    expr = self._canonicalize_expression(expr)
    branch_value = self._canonicalize_expression(branch_value)
    canonical_branch_value = (
        self._canonicalize_expression(canonical_branch_value)
        if canonical_branch_value is not None
        else self._canonicalize_state_transition_value(
            branch_value,
            state_placeholder=state_placeholder,
            state_guard=state_guard,
        )
    )
    post_guard = self._substitute_exact_expression(
        state_guard,
        state_placeholder,
        canonical_branch_value,
    )
    post_guard = self._canonicalize_expression(post_guard)
    post_guard_sig = _runtime_expression_signature(post_guard)
    kept = []
    for conjunct in self._flatten_bool_and_expression(expr):
        conjunct = self._canonicalize_expression(conjunct)
        canonical_conjunct = self._canonicalize_state_transition_value(
            conjunct,
            state_placeholder=state_placeholder,
            state_guard=state_guard,
        )
        if _runtime_expression_signature(canonical_conjunct) == post_guard_sig:
            continue
        if (
            not self._expressions_have_same_structural_key(canonical_branch_value, state_placeholder)
            and (
                self._expression_contains_subexpression(conjunct, branch_value)
                or self._expression_contains_subexpression(canonical_conjunct, canonical_branch_value)
            )
        ):
            continue
        if not self._expression_mentions_placeholder(canonical_conjunct, state_placeholder):
            return _UNSUPPORTED_STATE_TRANSITION_CONDITION
        kept.append(canonical_conjunct)
    if not kept:
        return None
    kept.sort(key=_runtime_expression_signature)
    combined = kept[0]
    for conjunct in kept[1:]:
        combined = Expression.binary_op("BOOL_AND", combined, conjunct)
        combined.size = 1
    combined = self._canonicalize_expression(combined)
    normalized_expr, normalized_negated = self._normalize_state_transition_condition_term(combined, False)
    return Condition(normalized_expr, normalized_negated)


def _impl__complete_default_state_transition_cases(
    self,
    cases: Sequence[Tuple[Optional[Expression], bool, Expression, bool]],
) -> Tuple[Tuple[Optional[Expression], bool, Expression, bool], ...]:
    if len(cases) <= 1:
        return tuple(cases)
    default_indices = [
        index
        for index, (expr, _negated, _value, is_source_default) in enumerate(cases)
        if expr is None and is_source_default
    ]
    if len(default_indices) != 1:
        return tuple(cases)
    explicit_terms = [
        (expr, negated)
        for expr, negated, _value, _is_source_default in cases
        if expr is not None
    ]
    if not explicit_terms:
        return tuple(cases)
    complement = self._combine_state_transition_condition_complements(explicit_terms)
    if complement is None:
        return tuple(cases)
    complement_expr, complement_negated = complement
    completed = list(cases)
    index = default_indices[0]
    _expr, _negated, value, is_source_default = completed[index]
    completed[index] = (complement_expr, complement_negated, value, is_source_default)
    return tuple(completed)


def _impl__combine_state_transition_condition_complements(
    self,
    terms: Sequence[Tuple[Expression, bool]],
) -> Optional[Tuple[Expression, bool]]:
    complement_expr = None
    for expr, negated in terms:
        normalized_expr, normalized_negated = self._normalize_state_transition_condition_term(expr, negated)
        term_expr, term_negated = self._normalize_state_transition_condition_term(
            normalized_expr,
            not normalized_negated,
        )
        if complement_expr is None:
            complement_expr = self._condition_term_to_expression(term_expr, term_negated)
        else:
            rhs = self._condition_term_to_expression(term_expr, term_negated)
            complement_expr = Expression.binary_op("BOOL_AND", complement_expr, rhs)
            complement_expr.size = 1
    if complement_expr is None:
        return None
    complement_expr = self._canonicalize_expression(complement_expr)
    return self._normalize_state_transition_condition_term(complement_expr, False)


def _impl__normalize_state_transition_condition_term(
    self,
    expr: Expression,
    negated: bool,
) -> Tuple[Expression, bool]:
    expr = self._canonicalize_expression(expr)
    changed = True
    while changed:
        changed = False
        if (
            expr.expr_type == ExpressionType.UNARY_OP
            and expr.operator == "BOOL_NEGATE"
            and len(expr.operands) == 1
        ):
            expr = self._canonicalize_expression(expr.operands[0])
            negated = not negated
            changed = True
    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "INT_NOTEQUAL"
        and len(expr.operands) == 2
    ):
        expr = Expression.binary_op("INT_EQUAL", expr.operands[0], expr.operands[1])
        expr.size = 1
        expr = self._canonicalize_expression(expr)
        negated = not negated
    return expr, bool(negated)


def _impl__canonicalize_state_transition_value(
    self,
    expr: Optional[Expression],
    *,
    state_placeholder: Expression,
    state_guard: Expression,
) -> Optional[Expression]:
    expr = self._canonicalize_expression(expr)
    if expr is None:
        return None
    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left = self._canonicalize_state_transition_value(
            expr.operands[0],
            state_placeholder=state_placeholder,
            state_guard=state_guard,
        )
        right = self._canonicalize_state_transition_value(
            expr.operands[1],
            state_placeholder=state_placeholder,
            state_guard=state_guard,
        )
        operator = expr.operator
        if (
            operator == "INT_RIGHT"
            and self._expressions_have_same_structural_key(left, state_placeholder)
            and self._state_guard_proves_signed_positive_placeholder(state_guard, state_placeholder)
        ):
            operator = "INT_SRIGHT"
        rebuilt = Expression.binary_op(operator, left, right)
        rebuilt.size = expr.size
        return self._canonicalize_expression(rebuilt)
    if expr.expr_type == ExpressionType.UNARY_OP and len(expr.operands) == 1:
        operand = self._canonicalize_state_transition_value(
            expr.operands[0],
            state_placeholder=state_placeholder,
            state_guard=state_guard,
        )
        rebuilt = Expression.unary_op(expr.operator, operand)
        rebuilt.size = expr.size
        return self._canonicalize_expression(rebuilt)
    if expr.expr_type == ExpressionType.PHI and expr.value:
        branches = []
        for condition, value in expr.value:
            canonical_condition = self._canonicalize_state_transition_condition(
                condition,
                branch_value=value,
                canonical_branch_value=None,
                state_guard=state_guard,
                state_placeholder=state_placeholder,
            )
            if canonical_condition is _UNSUPPORTED_STATE_TRANSITION_CONDITION:
                return None
            branches.append(
                (
                    canonical_condition,
                    self._canonicalize_state_transition_value(
                        value,
                        state_placeholder=state_placeholder,
                        state_guard=state_guard,
                    ),
                )
            )
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return self._canonicalize_expression(rebuilt)
    return expr


def _impl__collect_state_transition_loop_phi_ops(
    self,
    loop_blocks: Sequence[object],
    preferred_phi_ops: Sequence[object],
) -> Tuple[object, ...]:
    result = []
    seen = set()

    def add(phi_op) -> None:
        key = id(phi_op)
        if key not in seen:
            seen.add(key)
            result.append(phi_op)

    for phi_op in preferred_phi_ops or ():
        add(phi_op)
    for block in loop_blocks or ():
        for op in self._iter_block_ops(block):
            if (
                getattr(op, "getMnemonic", lambda: None)() == "MULTIEQUAL"
                and getattr(op, "getOutput", lambda: None)() is not None
            ):
                add(op)
    return tuple(result)


def _impl__normalize_state_transition_state_guard(
    self,
    state_guard: Optional[Expression],
    state_placeholder: Expression,
) -> Optional[Expression]:
    guard = self._canonicalize_expression(state_guard)
    if guard is None:
        return None
    placeholder_key = state_placeholder.structural_key()

    def is_placeholder(value: Optional[Expression]) -> bool:
        if value is None:
            return False
        try:
            return value.structural_key() == placeholder_key
        except (AttributeError, TypeError, ValueError, RecursionError):
            return False

    if (
        guard.expr_type == ExpressionType.UNARY_OP
        and guard.operator == "BOOL_NEGATE"
        and len(guard.operands) == 1
    ):
        inner = self._canonicalize_expression(guard.operands[0])
        if (
            inner.expr_type == ExpressionType.BINARY_OP
            and inner.operator == "INT_SLESS"
            and len(inner.operands) == 2
            and is_placeholder(inner.operands[0])
            and self._raw_constant_value(inner.operands[1]) == 1
        ):
            return self._positive_state_guard_expression(state_placeholder)
    if (
        guard.expr_type == ExpressionType.BINARY_OP
        and guard.operator == "INT_SLESSEQUAL"
        and len(guard.operands) == 2
        and self._raw_constant_value(guard.operands[0]) == 1
        and is_placeholder(guard.operands[1])
    ):
        return self._positive_state_guard_expression(state_placeholder)
    return guard


def _impl__extract_multiplicative_accumulator_transition(
    self,
    expr: Expression,
    accumulator_placeholder: Expression,
) -> Optional[Expression]:
    expr = self._canonicalize_expression(expr)
    if expr is None:
        return None
    multiplier = self._multiplicative_accumulator_delta_multiplier(
        expr,
        accumulator_placeholder,
    )
    if multiplier is None or int(multiplier) in {0, 1}:
        return None
    return expr


def _impl__state_transition_model_priority(
    self,
    model: StateTransitionLoopModel,
) -> Tuple[int, int, int]:
    return (
        1 if self._varnode_reaches_return(model.accumulator_phi_output) else 0,
        len(model.loop_blocks),
        max(1, int(getattr(model.state_phi_output, "getSize", lambda: 0)() or 0)),
    )


def _impl__collect_state_transition_loop_blocks(
    self,
    *,
    header_block,
    body_block,
    exit_block,
    backedge_indices: Sequence[int],
) -> Tuple[object, ...]:
    header_key = self._block_key(header_block)
    exit_key = self._block_key(exit_block)
    blocks_by_key: Dict[object, object] = {}

    def add(block) -> None:
        key = self._block_key(block)
        if key is not None and key != exit_key and key not in blocks_by_key:
            blocks_by_key[key] = block

    add(header_block)
    add(body_block)
    in_size = int(getattr(header_block, "getInSize", lambda: 0)() or 0)
    stack = []
    for index in backedge_indices:
        if index < in_size:
            predecessor = header_block.getIn(index)
            add(predecessor)
            stack.append(predecessor)
    while stack:
        current = stack.pop()
        current_key = self._block_key(current)
        if current_key == header_key:
            continue
        for predecessor in self._collect_block_predecessors(current):
            predecessor_key = self._block_key(predecessor)
            if predecessor_key in {None, exit_key}:
                continue
            if not self._can_reach_block(body_block, predecessor) and predecessor_key != header_key:
                continue
            if predecessor_key not in blocks_by_key:
                blocks_by_key[predecessor_key] = predecessor
                stack.append(predecessor)
    return tuple(blocks_by_key.values())


def _impl__build_state_transition_loop_side_effect_profile(
    self,
    *,
    loop_blocks: Sequence[object],
) -> LoopSideEffectProfileRef:
    memory_reads = False
    memory_writes = False
    calls = False
    escapes = False
    conditional_guards = False
    for block in loop_blocks or ():
        for op in self._iter_block_ops(block):
            mnemonic = getattr(op, "getMnemonic", lambda: None)()
            if mnemonic == "LOAD":
                memory_reads = True
            elif mnemonic == "STORE":
                memory_writes = True
            elif mnemonic in {"CALL", "CALLIND"}:
                calls = True
                escapes = True
            elif mnemonic == "BRANCHIND":
                escapes = True
            elif mnemonic == "CBRANCH":
                conditional_guards = True
    return LoopSideEffectProfileRef(
        profile=self._loop_effect_profile_name(
            memory_reads=memory_reads,
            memory_writes=memory_writes,
            calls=calls,
            escapes=escapes,
            conditional_guards=conditional_guards,
        ),
        memory_reads=memory_reads,
        memory_writes=memory_writes,
        calls=calls,
        escapes=escapes,
        conditional_guards=conditional_guards,
        effect_count=0,
        guard_count=1 if conditional_guards else 0,
    )
