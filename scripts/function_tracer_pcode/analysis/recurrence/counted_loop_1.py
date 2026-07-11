"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.recurrence_summary``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    COUNTED_LOOP_SUM_OPCODE,
    ComposedLoopSummaryRef,
    Condition,
    ConditionSimplifier,
    CountedLoopAccumulator,
    CountedLoopGuard,
    CountedLoopInduction,
    CountedLoopSummaryRef,
    CountedLoopUpdateCase,
    CountedStateTransitionLoopSummaryRef,
    Expression,
    ExpressionType,
    LoopBodyEffectRef,
    LoopCaseRef,
    LoopSideEffectProfileRef,
    LoopSummaryRef,
    LoopTermDescriptorRef,
    PcodeOpRef,
    ReadonlyAccumulatorPhiCandidate,
    ReductionAccumulatorProof,
    ReturnInfo,
    _reduce_expression_under_conditions,
    _runtime_conditions_signature,
    _runtime_expression_signature,
    replace,
)

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl_try_summarize_pre_return_counted_scalar_loop(
    self,
    function,
    high_function,
    analysis,
    return_ops: Sequence,
) -> Optional[Tuple[List[ReturnInfo], str]]:
    if function is None or high_function is None or analysis is None:
        return None
    return_ops = list(return_ops or [])
    if not self._pre_return_counted_scalar_summary_is_cfg_safe(high_function, analysis, return_ops):
        return None
    if not self._analysis_is_safe_for_counted_scalar_summary(analysis):
        return None
    return self._build_counted_scalar_loop_summary(
        function,
        high_function,
        analysis,
        pre_return_ops=return_ops,
    )

def _impl__pre_return_counted_scalar_summary_is_cfg_safe(
    self,
    high_function,
    analysis,
    return_ops: Sequence,
) -> bool:
    if high_function is None:
        return False
    return_ops = list(return_ops or [])
    if not return_ops:
        self._debug("Declined pre-return counted loop summary: no RETURN ops")
        return False
    if any(self._safe_pcode_input_count(return_op) < 2 for return_op in return_ops):
        self._debug("Declined pre-return counted loop summary: RETURN without value")
        return False
    if not self._has_counted_scalar_loop_candidate(high_function):
        self._debug("Declined pre-return counted loop summary: no counted-loop CFG candidate")
        return False
    counted_loop_count = self._count_counted_scalar_loop_models(high_function, analysis)
    if counted_loop_count != 1:
        self._debug(
            "Declined pre-return counted loop summary: prior loop dependency is not proved "
            f"(counted_loop_candidates={counted_loop_count})"
        )
        return False

    forbidden = {"CALL", "CALLIND", "BRANCHIND", "STORE"}
    return_blocks = {getattr(op, "getParent", lambda: None)() for op in return_ops}
    return_blocks.discard(None)
    if not return_blocks:
        return False
    terminal_blocks = []
    for block in self._iter_basic_blocks(high_function):
        if int(getattr(block, "getOutSize", lambda: 0)() or 0) == 0:
            terminal_blocks.append(block)
        for op in self._iter_block_ops(block):
            mnemonic = getattr(op, "getMnemonic", lambda: None)()
            if mnemonic in forbidden:
                self._debug(f"Declined pre-return counted loop summary: forbidden op {mnemonic}")
                return False
    if not terminal_blocks:
        self._debug("Declined pre-return counted loop summary: no terminal CFG blocks")
        return False
    if set(terminal_blocks) != return_blocks:
        self._debug(
            "Declined pre-return counted loop summary: terminal blocks are not exactly RETURN blocks "
            f"(terminal={len(terminal_blocks)}, returns={len(return_blocks)})"
        )
        return False
    return True

def _impl__count_counted_scalar_loop_models(self, high_function, analysis) -> int:
    if high_function is None:
        return 0
    function_body_ranges = self._function_body_address_ranges(high_function, analysis)
    seen = set()
    for header in self._iter_basic_blocks(high_function):
        cbranch = self._find_cbranch_op(header)
        phi_ops = [
            op for op in self._iter_block_ops(header)
            if getattr(op, "getMnemonic", lambda: None)() == "MULTIEQUAL"
        ]
        if len(phi_ops) < 2:
            continue
        induction_candidates = [
            info for info in (
                self._match_counted_loop_induction(phi_op)
                for phi_op in phi_ops
            )
            if info is not None
        ]
        if not induction_candidates:
            continue
        for induction in induction_candidates:
            guards = self._candidate_counted_loop_guards(header, cbranch, induction)
            for guard in guards:
                accumulators = list(
                    self._match_counted_loop_accumulators(
                        phi_ops,
                        induction,
                        guard.body_block,
                        function_body_ranges=function_body_ranges,
                    )
                )
                if not accumulators:
                    continue
                model_key = (
                    self._block_key(header),
                    self._block_key(getattr(guard, "latch_block", None)),
                    self._block_key(getattr(guard, "exit_block", None)),
                    _runtime_expression_signature(getattr(guard, "condition_expr", None)),
                )
                if model_key in seen:
                    continue
                seen.add(model_key)
                if len(seen) > 1:
                    return len(seen)
    return len(seen)

def _impl__has_counted_scalar_loop_candidate(self, high_function) -> bool:
    if high_function is None:
        return False
    for block in self._iter_basic_blocks(high_function):
        phis = [
            op for op in self._iter_block_ops(block)
            if getattr(op, "getMnemonic", lambda: None)() == "MULTIEQUAL"
        ]
        if len(phis) >= 2 and self._find_cbranch_op(block) is not None:
            return True
    return False

def _impl__try_summarize_counted_scalar_loop(
    self,
    function,
    high_function,
    analysis,
) -> Optional[Tuple[List[ReturnInfo], str]]:
    if function is None or high_function is None or analysis is None:
        return None
    if not self._analysis_is_safe_for_counted_scalar_summary(analysis):
        return None
    return self._build_counted_scalar_loop_summary(function, high_function, analysis)

def _impl__analysis_is_safe_for_counted_scalar_summary(self, analysis) -> bool:
    if analysis is None:
        return False
    effect_profile = self._build_loop_side_effect_profile(
        analysis=analysis,
    )
    if (
        effect_profile.calls
        or effect_profile.escapes
        or effect_profile.context_calls
        or effect_profile.context_escapes
    ):
        self._debug("Declined counted scalar loop summary: loop contains calls or escaping control flow")
        return False
    if getattr(analysis, "incomplete_control_flow", False):
        self._debug("Declined counted scalar loop summary: control flow is incomplete")
        return False
    return True

def _impl__build_counted_scalar_loop_summary(
    self,
    function,
    high_function,
    analysis,
    *,
    pre_return_ops: Optional[Sequence] = None,
) -> Optional[Tuple[List[ReturnInfo], str]]:
    if function is None or high_function is None:
        return None

    model = self._extract_counted_scalar_loop_model(high_function, analysis)
    if model is None:
        if pre_return_ops is not None:
            self._debug("Declined pre-return counted loop summary: no validated counted-loop model")
        return None

    induction, accumulator, guard, residue_cases = model
    function_body_ranges = self._function_body_address_ranges(high_function, analysis, function=function)
    if self._residue_cases_contain_readonly_affine_literal_address(
        residue_cases,
        function_body_ranges=function_body_ranges,
    ):
        self._debug("Declined counted scalar loop summary: residue affine uses address-like vector literal")
        return None
    update_cases = self._try_extract_counted_loop_update_cases_for_summary(accumulator, induction, guard)
    loop_cases = self._build_counted_loop_case_refs(update_cases)
    start_expr = induction.init_expr
    limit_expr = guard.bound_expr
    header_block = getattr(induction.phi_op, "getParent", lambda: None)()
    loop_body_blocks = self._collect_loop_body_blocks(
        header_block=header_block,
        guard=guard,
    )
    loop_block_guard_info = self._loop_block_guard_effect_info(
        header_block=header_block,
        guard=guard,
        loop_blocks=loop_body_blocks,
    )
    ignored_branch_ops = [
        self._find_cbranch_op(block)
        for block in (header_block, guard.latch_block)
        if block is not None
    ]
    side_effect_profile = self._build_loop_side_effect_profile(
        analysis=analysis,
        loop_blocks=loop_body_blocks,
        ignored_branch_ops=ignored_branch_ops,
        block_guard_info=loop_block_guard_info,
    )
    if side_effect_profile.calls or side_effect_profile.escapes:
        self._debug("Declined counted scalar loop summary: loop body contains calls or escaping control flow")
        return None
    entry_guard_expr = self._substitute_exact_expression(
        guard.entry_condition_expr or guard.condition_expr,
        induction.placeholder,
        start_expr,
    )
    derived_continue_condition = Condition(entry_guard_expr or guard.condition_expr, False)
    derived_base_condition = derived_continue_condition.negate()
    original_conditions = self._derive_direct_counted_loop_conditions(high_function, induction, guard)
    if original_conditions is None:
        continue_conditions = ConditionSimplifier.simplify_conditions_object_centric([derived_continue_condition])
        base_conditions = ConditionSimplifier.simplify_conditions_object_centric([derived_base_condition])
    else:
        base_conditions, continue_conditions = original_conditions
        base_conditions, continue_conditions = self._repair_two_way_partition_conditions(
            base_conditions,
            continue_conditions,
        )
        if (
            not self._two_way_condition_partition_is_total(base_conditions, continue_conditions)
            or not self._condition_sets_equivalent(continue_conditions, [derived_continue_condition])
            or not self._condition_sets_equivalent(base_conditions, [derived_base_condition])
        ):
            self._debug(
                "Declined direct counted-loop path guards: base/continue partition is not total "
                "or does not match loop-entry orientation; "
                "using entry guard derived from loop condition"
            )
            continue_conditions = ConditionSimplifier.simplify_conditions_object_centric([derived_continue_condition])
            base_conditions = ConditionSimplifier.simplify_conditions_object_centric([derived_base_condition])

    base_return_expr = self._canonicalize_zero_value_under_conditions(
        accumulator.init_expr,
        base_conditions,
    )
    loop_base_expr = self._canonicalize_zero_value_under_conditions(
        accumulator.init_expr,
        continue_conditions,
    )
    prior_state_value = self._prior_counted_state_transition_base_value(
        high_function=high_function,
        analysis=analysis,
        current_induction=induction,
        current_accumulator=accumulator,
        current_guard=guard,
        continue_conditions=continue_conditions,
        result_size=loop_base_expr.size or accumulator.placeholder.size or 4,
    )
    if prior_state_value is not None:
        loop_base_expr = prior_state_value
    else:
        recovered_state_value = self._recover_proved_multiplicative_state_transition_base(
            loop_base_expr=loop_base_expr,
            continue_conditions=continue_conditions,
            start_expr=start_expr,
            limit_expr=limit_expr,
            result_size=loop_base_expr.size or accumulator.placeholder.size or 4,
            signed_loop=induction.signed_guard or guard.signed_comparison,
        )
        if recovered_state_value is not None:
            loop_base_expr = recovered_state_value
    if self._expression_contains_executable_address_constant(
        base_return_expr,
        function_body_ranges=function_body_ranges,
    ) or self._expression_contains_executable_address_constant(
        loop_base_expr,
        function_body_ranges=function_body_ranges,
    ):
        self._debug("Declined counted scalar loop summary: base expression contains function-address constant")
        return None
    loop_summary_source_key = self._counted_loop_summary_source_key_from_parts(
        start_expr=start_expr,
        limit_expr=limit_expr,
        induction_step=induction.step,
        residue_cases=residue_cases,
        result_size=loop_base_expr.size or accumulator.placeholder.size or 4,
        signed_loop=induction.signed_guard or guard.signed_comparison,
        side_effect_profile=side_effect_profile,
        guard_constraints=continue_conditions,
        source="counted_scalar_loop_summary",
    )
    transition_evidence_key = self._counted_loop_transition_evidence_key_from_parts(
        header_block=header_block,
        latch_block=guard.latch_block or accumulator.update_block or guard.body_block,
        exit_block=guard.exit_block,
        induction_phi_op=induction.phi_op,
        accumulator_phi_op=accumulator.phi_op,
        guard=guard,
        accumulator_init_expr=accumulator.init_expr,
        loop_base_expr=loop_base_expr,
        update_cases=update_cases,
        loop_cases=loop_cases,
    )
    loop_value = self._build_counted_loop_summary_value(
        base_expr=loop_base_expr,
        start_expr=start_expr,
        limit_expr=limit_expr,
        induction_step=induction.step,
        residue_cases=residue_cases,
        result_size=loop_base_expr.size or accumulator.placeholder.size or 4,
        signed_loop=induction.signed_guard or guard.signed_comparison,
        side_effect_profile=side_effect_profile,
        guard_constraints=continue_conditions,
        cases=loop_cases,
    )
    if loop_value is None:
        return None
    loop_summary_source_key = loop_summary_source_key or self._summary_value_source_key(loop_value)

    anchor = next(iter((getattr(analysis, "returns", None) or [])), None)
    address = getattr(anchor, "address", getattr(function, "getEntryPoint", lambda: "0x0")())
    pcode_identity = getattr(anchor, "pcode_identity", None)
    pcode_order = getattr(anchor, "pcode_order", None)
    pcode_time = getattr(anchor, "pcode_time", None)
    pcode_op_ref = getattr(anchor, "pcode_op_ref", None)
    base_summary_source_key = loop_summary_source_key if pre_return_ops is not None else None
    base_transition_evidence_key = transition_evidence_key if pre_return_ops is not None else None

    summarized = [
        ReturnInfo(
            address=str(address),
            value=base_return_expr,
            conditions=base_conditions,
            branch_index=20_100,
            pcode_identity=pcode_identity,
            pcode_order=pcode_order,
            pcode_time=pcode_time,
            pcode_op_ref=pcode_op_ref,
            summary_candidate_source_key=base_summary_source_key,
            summary_transition_evidence_key=base_transition_evidence_key,
        )
    ]
    summarized.append(
        ReturnInfo(
            address=str(address),
            value=loop_value,
            conditions=continue_conditions,
            branch_index=20_100 + len(summarized),
            pcode_identity=pcode_identity,
            pcode_order=pcode_order,
            pcode_time=pcode_time,
            pcode_op_ref=pcode_op_ref,
            summary_candidate_source_key=loop_summary_source_key,
            summary_transition_evidence_key=transition_evidence_key,
        )
    )
    loop_case = summarized[-1]
    canonical_value = self._canonicalize_peeled_counted_loop_value(
        loop_case.value,
        continue_conditions=continue_conditions,
        parameters=self._collect_summary_parameter_specs(
            loop_case.value,
            loop_base_expr,
            start_expr,
            limit_expr,
            *(cond.expression for cond in continue_conditions or [] if cond is not None),
        ),
        base_expr=loop_base_expr,
        limit_expr=limit_expr,
        induction_step=induction.step,
        residue_cases=residue_cases,
        result_size=loop_base_expr.size or accumulator.placeholder.size or 4,
        signed_loop=induction.signed_guard or guard.signed_comparison,
        side_effect_profile=side_effect_profile,
        guard_constraints=continue_conditions,
        cases=loop_cases,
    )
    canonical_value = self._canonicalize_zero_prefix_counted_loop_value(
        canonical_value,
        base_expr=loop_base_expr,
        limit_expr=limit_expr,
        induction_step=induction.step,
        residue_cases=residue_cases,
        result_size=loop_base_expr.size or accumulator.placeholder.size or 4,
        signed_loop=induction.signed_guard or guard.signed_comparison,
        side_effect_profile=side_effect_profile,
        guard_constraints=continue_conditions,
        cases=loop_cases,
    )
    if canonical_value is not None and not canonical_value.equals(loop_case.value):
        summarized[-1] = ReturnInfo(
            address=loop_case.address,
            value=canonical_value,
            conditions=list(loop_case.conditions or []),
            branch_index=loop_case.branch_index,
            pcode_identity=loop_case.pcode_identity,
            pcode_order=loop_case.pcode_order,
            pcode_time=loop_case.pcode_time,
            pcode_op_ref=getattr(loop_case, "pcode_op_ref", None),
            return_value_pcode_op_refs=tuple(
                getattr(loop_case, "return_value_pcode_op_refs", ()) or ()
            ),
            summary_candidate_source_key=getattr(loop_case, "summary_candidate_source_key", None)
            or loop_summary_source_key,
            summary_transition_evidence_key=getattr(loop_case, "summary_transition_evidence_key", None)
            or transition_evidence_key,
        )
    effective_loop_value = summarized[-1].value
    effective_start_expr = start_expr
    if (
        effective_loop_value is not None
        and getattr(effective_loop_value, "expr_type", None) == ExpressionType.INTRINSIC
        and len(getattr(effective_loop_value, "operands", None) or []) == 3
    ):
        effective_start_expr = effective_loop_value.operands[1]
    self._debug(
        "Recovered counted scalar loop summary "
        f"(start={self._safe_expr_text(effective_start_expr)}, limit={self._safe_expr_text(limit_expr)}, "
        f"step={induction.step}, "
        f"cases={[(case.modulus, case.residue, case.affine) for case in residue_cases]})"
    )
    return summarized, "counted_scalar_loop_summary"

def _impl__counted_loop_summary_source_key_from_parts(
    self,
    *,
    start_expr: Optional[Expression],
    limit_expr: Optional[Expression],
    induction_step: int,
    residue_cases: Sequence[ResidueLoopCase],
    result_size: int,
    signed_loop: bool,
    side_effect_profile: Optional[LoopSideEffectProfileRef],
    guard_constraints: Sequence[Condition],
    source: str,
) -> Optional[Tuple[Any, ...]]:
    try:
        guard_key = self._summary_guard_constraints_key(guard_constraints)
        side_effect_key = None
        stable_key = getattr(side_effect_profile, "stable_key", None)
        if callable(stable_key):
            try:
                side_effect_key = stable_key()
            except Exception:
                return None
        if side_effect_key is None:
            return None
        return (
            "counted_loop_summary_parts",
            _runtime_expression_signature(start_expr),
            _runtime_expression_signature(limit_expr),
            int(induction_step),
            max(1, int(result_size or 0)),
            bool(signed_loop),
            tuple(
                (
                    int(case.modulus),
                    int(case.residue),
                    int(case.affine[0]),
                    int(case.affine[1]),
                    _runtime_expression_signature(case.bias_expr),
                )
                for case in residue_cases or ()
            ),
            guard_key,
            side_effect_key,
            str(source or "counted_scalar_loop_summary"),
        )
    except Exception:
        return None

def _impl__counted_loop_summary_source_key_fallback(self, runtime_ref: Any) -> Optional[Tuple[Any, ...]]:
    if runtime_ref is None or type(runtime_ref).__name__ != "CountedLoopSummaryRef":
        return None
    loop_summary = getattr(runtime_ref, "loop_summary", None)
    loop_summary_key = None
    if loop_summary is not None:
        guard_keys = []
        for guard in getattr(loop_summary, "guard_constraints", ()) or ():
            key_fn = getattr(guard, "structural_key", None)
            if callable(key_fn):
                try:
                    guard_keys.append(key_fn(budget=256))
                except Exception:
                    return None
            else:
                return None
        guard_keys.sort(key=repr)
        side_effect_profile = getattr(loop_summary, "side_effect_profile", None)
        side_effect_key = None
        stable_key = getattr(side_effect_profile, "stable_key", None)
        if callable(stable_key):
            try:
                side_effect_key = stable_key()
            except Exception:
                return None
        loop_summary_key = (
            "loop_summary_fallback",
            _runtime_expression_signature(getattr(loop_summary, "start_expr", None)),
            _runtime_expression_signature(getattr(loop_summary, "limit_expr", None)),
            _runtime_expression_signature(getattr(loop_summary, "step_expr", None)),
            tuple(guard_keys),
            side_effect_key,
            getattr(loop_summary, "source", None),
        )
    return (
        "counted_loop_summary_fallback",
        int(getattr(runtime_ref, "induction_step", 0) or 0),
        int(getattr(runtime_ref, "result_size", 0) or 0),
        bool(getattr(runtime_ref, "signed_loop", False)),
        tuple(getattr(runtime_ref, "residue_cases", ()) or ()),
        tuple(
            (
                int(modulus),
                int(residue),
                _runtime_expression_signature(bias_expr),
            )
            for modulus, residue, bias_expr in getattr(runtime_ref, "residue_bias_terms", ()) or ()
        ),
        getattr(runtime_ref, "source", None),
        loop_summary_key,
    )

def _impl__build_counted_loop_summary_value(
    self,
    *,
    base_expr: Expression,
    start_expr: Expression,
    limit_expr: Expression,
    induction_step: int,
    residue_cases: Sequence[ResidueLoopCase],
    result_size: int,
    signed_loop: bool,
    side_effect_profile: Optional[LoopSideEffectProfileRef] = None,
    guard_constraints: Sequence[Condition] = (),
    cases: Sequence[LoopCaseRef] = (),
) -> Optional[Expression]:
    if any(
        self._expression_is_unresolved(expr)
        for expr in (base_expr, start_expr, limit_expr)
    ):
        return None
    intrinsic = self._build_counted_loop_summary_intrinsic(
        base_expr=base_expr,
        start_expr=start_expr,
        limit_expr=limit_expr,
        induction_step=induction_step,
        residue_cases=residue_cases,
        result_size=result_size,
        signed_loop=signed_loop,
        side_effect_profile=side_effect_profile,
        guard_constraints=guard_constraints,
        cases=cases,
    )
    if intrinsic is not None:
        return intrinsic
    return None

def _impl__build_counted_loop_summary_intrinsic(
    self,
    *,
    base_expr: Expression,
    start_expr: Expression,
    limit_expr: Expression,
    induction_step: int,
    residue_cases: Sequence[ResidueLoopCase],
    result_size: int,
    signed_loop: bool,
    side_effect_profile: Optional[LoopSideEffectProfileRef] = None,
    guard_constraints: Sequence[Condition] = (),
    cases: Sequence[LoopCaseRef] = (),
) -> Optional[Expression]:
    if induction_step == 0 or not residue_cases:
        return None
    step_expr = Expression.constant(
        int(induction_step),
        size=max(1, int(getattr(start_expr, "size", 0) or getattr(limit_expr, "size", 0) or 4)),
    )
    term_descriptor = LoopTermDescriptorRef(
        kind="affine_residue",
        reduction_kind="sum",
        result_size=max(1, int(result_size or 0)),
        residue_cases=tuple(
            (
                int(case.modulus),
                int(case.residue),
                int(case.affine[0]),
                int(case.affine[1]),
            )
            for case in residue_cases
        ),
        residue_bias_terms=tuple(
            (
                int(case.modulus),
                int(case.residue),
                case.bias_expr,
            )
            for case in residue_cases
            if case.bias_expr is not None
        ),
    )
    loop_summary = LoopSummaryRef(
        start_expr=start_expr,
        limit_expr=limit_expr,
        step_expr=step_expr,
        term_descriptor=term_descriptor,
        seed_terms=(),
        witnesses=(),
        side_effect_profile=side_effect_profile or LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=tuple(guard_constraints or ()),
        cases=tuple(cases or ()),
        loop_var_unit="induction_value",
    )
    loop_summary_for_runtime = loop_summary
    base_runtime_ref = getattr(base_expr, "runtime_ref", None)
    handoff_proof_key = getattr(base_runtime_ref, "handoff_proof_key", None)
    if isinstance(base_runtime_ref, CountedStateTransitionLoopSummaryRef) and handoff_proof_key is not None:
        loop_summary_for_runtime = ComposedLoopSummaryRef(
            prior=base_runtime_ref,
            current=loop_summary,
            handoff_proof_key=handoff_proof_key,
            source="prior_state_transition_then_counted_loop",
        )
    runtime_ref = CountedLoopSummaryRef(
        induction_step=int(induction_step),
        result_size=max(1, int(result_size or 0)),
        signed_loop=bool(signed_loop),
        residue_cases=term_descriptor.residue_cases,
        residue_bias_terms=term_descriptor.residue_bias_terms,
        loop_summary=loop_summary_for_runtime,
    )
    intrinsic = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [base_expr, start_expr, limit_expr],
        size=max(1, int(result_size or 0)),
        runtime_ref=runtime_ref,
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    intrinsic.size = max(1, int(result_size or 0))
    return intrinsic

def _impl__canonicalize_zero_prefix_counted_loop_value(
    self,
    value: Optional[Expression],
    *,
    base_expr: Expression,
    limit_expr: Expression,
    induction_step: int,
    residue_cases: Sequence[ResidueLoopCase],
    result_size: int,
    signed_loop: bool,
    side_effect_profile: Optional[LoopSideEffectProfileRef] = None,
    guard_constraints: Sequence[Condition] = (),
    cases: Sequence[LoopCaseRef] = (),
) -> Optional[Expression]:
    if value is None or getattr(value, "expr_type", None) != ExpressionType.INTRINSIC:
        return value
    if getattr(value, "opcode", None) != COUNTED_LOOP_SUM_OPCODE and getattr(value, "name", None) != "COUNTED_LOOP_SUM":
        return value
    operands = list(getattr(value, "operands", None) or [])
    if len(operands) != 3:
        return value
    start_raw = self._raw_constant_value(operands[1])
    if start_raw is None:
        return value
    start = int(start_raw)
    if start <= 0 or start > 16 or int(induction_step) != 1:
        return value
    if not self._counted_loop_prefix_contributes_zero(start, residue_cases):
        return value
    zero_start = Expression.constant(
        0,
        size=max(1, int(getattr(operands[1], "size", 0) or getattr(limit_expr, "size", 0) or 4)),
    )
    canonical = self._build_counted_loop_summary_intrinsic(
        base_expr=base_expr,
        start_expr=zero_start,
        limit_expr=limit_expr,
        induction_step=induction_step,
        residue_cases=residue_cases,
        result_size=result_size,
        signed_loop=signed_loop,
        side_effect_profile=side_effect_profile,
        guard_constraints=guard_constraints,
        cases=cases,
    )
    if canonical is None:
        return value
    self._debug(
        "Canonicalized counted loop zero-contribution prefix to zero-start summary "
        f"(original start={start})"
    )
    return canonical

def _impl__counted_loop_prefix_contributes_zero(
    self,
    stop: int,
    residue_cases: Sequence[ResidueLoopCase],
) -> bool:
    if stop <= 0 or not residue_cases:
        return False
    for index in range(stop):
        matched = [
            case
            for case in residue_cases
            if int(case.modulus) > 0 and index % int(case.modulus) == int(case.residue)
        ]
        if len(matched) != 1:
            return False
        coeff, bias = matched[0].affine
        if int(coeff) * index + int(bias) != 0:
            return False
    return True

def _impl__canonicalize_peeled_counted_loop_value(
    self,
    value: Expression,
    *,
    continue_conditions: Sequence[Condition],
    parameters: Sequence[dict],
    base_expr: Expression,
    limit_expr: Expression,
    induction_step: int,
    residue_cases: Sequence[ResidueLoopCase],
    result_size: int,
    signed_loop: bool,
    side_effect_profile: Optional[LoopSideEffectProfileRef] = None,
    guard_constraints: Sequence[Condition] = (),
    cases: Sequence[LoopCaseRef] = (),
) -> Optional[Expression]:
    if value is None or getattr(value, "expr_type", None) != ExpressionType.INTRINSIC:
        return value
    if getattr(value, "opcode", None) != COUNTED_LOOP_SUM_OPCODE and getattr(value, "name", None) != "COUNTED_LOOP_SUM":
        return value
    operands = list(getattr(value, "operands", None) or [])
    if len(operands) != 3:
        return value
    start_expr = operands[1]
    if not self._looks_like_peeled_counted_loop_start(start_expr, limit_expr):
        return value

    zero_start = Expression.constant(
        0,
        size=max(1, int(getattr(start_expr, "size", 0) or getattr(limit_expr, "size", 0) or 4)),
    )
    canonical = self._build_counted_loop_summary_intrinsic(
        base_expr=base_expr,
        start_expr=zero_start,
        limit_expr=limit_expr,
        induction_step=induction_step,
        residue_cases=residue_cases,
        result_size=result_size,
        signed_loop=signed_loop,
        side_effect_profile=side_effect_profile,
        guard_constraints=guard_constraints,
        cases=cases,
    )
    if canonical is None:
        return value
    if not self._prove_expression_equivalence_under_conditions(
        value,
        canonical,
        continue_conditions,
        parameters,
    ):
        return value
    self._debug(
        "Canonicalized peeled counted loop start to zero-start counted summary "
        f"(original start={self._safe_expr_text(start_expr)})"
    )
    return canonical

def _impl__looks_like_peeled_counted_loop_start(
    self,
    start_expr: Optional[Expression],
    limit_expr: Optional[Expression],
) -> bool:
    if start_expr is None or limit_expr is None:
        return False
    if getattr(start_expr, "expr_type", None) != ExpressionType.PHI:
        return False
    branches = list(getattr(start_expr, "value", None) or [])
    if len(branches) < 2:
        return False

    limit_signature = _runtime_expression_signature(limit_expr)
    saw_zero = False
    saw_limit_dependent = False
    for _cond, branch_value in branches:
        if branch_value is None:
            continue
        if self._raw_constant_value(branch_value) == 0:
            saw_zero = True
            continue
        if self._expression_depends_on_signature(branch_value, limit_signature):
            saw_limit_dependent = True
    return saw_zero and saw_limit_dependent

def _impl__derive_direct_counted_loop_conditions(
    self,
    high_function,
    induction: CountedLoopInduction,
    guard: CountedLoopGuard,
) -> Optional[Tuple[List[Condition], List[Condition]]]:
    if high_function is None or induction is None:
        return None

    header_block = getattr(induction.phi_op, "getParent", lambda: None)()
    if header_block is None:
        return None
    preheader = None
    in_size = int(getattr(header_block, "getInSize", lambda: 0)() or 0)
    entry_index = self._induction_init_index(induction)
    if entry_index < in_size:
        preheader = header_block.getIn(entry_index)
    if preheader is None:
        return None

    entry_blocks = [
        block
        for block in self._iter_basic_blocks(high_function)
        if int(getattr(block, "getInSize", lambda: 0)() or 0) == 0
    ]
    if not entry_blocks:
        return None

    path_sets: List[List[Condition]] = []
    for entry_block in entry_blocks:
        path_sets.extend(
            self._enumerate_paths_with_conditions(
                start_block=entry_block,
                target_block=preheader,
                header_block=header_block,
                placeholders={},
                stop_block=guard.exit_block,
                limit=16,
            )
        )
    if not path_sets:
        return None
    common = self._common_conditions_across_paths(path_sets)
    if not common:
        return None
    negated = self._negate_simple_condition_set(common)
    if negated is None:
        return None
    return negated, common

def _impl__extract_counted_scalar_loop_model(
    self,
    high_function,
    analysis,
) -> Optional[Tuple[CountedLoopInduction, CountedLoopAccumulator, CountedLoopGuard, Tuple[ResidueLoopCase, ...]]]:
    blocks = list(self._iter_basic_blocks(high_function))
    if not blocks:
        return None
    best_model = None
    best_score = None
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

        induction_candidates = [
            info for info in (
                self._match_counted_loop_induction(phi_op)
                for phi_op in phi_ops
            )
            if info is not None
        ]
        if not induction_candidates:
            continue

        for induction in induction_candidates:
            guards = self._candidate_counted_loop_guards(header, cbranch, induction)
            if not guards:
                continue
            for guard in guards:
                for accumulator in self._match_counted_loop_accumulators(
                    phi_ops,
                    induction,
                    guard.body_block,
                    function_body_ranges=function_body_ranges,
                ):
                    cases = self._extract_counted_loop_update_cases(
                        accumulator,
                        induction,
                        guard,
                    )
                    if not cases:
                        continue
                    residue_cases = self._extract_residue_loop_cases(
                        cases,
                        induction.placeholder.name or "__loop_iv",
                        function_body_ranges=function_body_ranges,
                    )
                    if residue_cases is None:
                        continue
                    if not self._validate_counted_loop_update_cases(
                        cases=cases,
                        residue_cases=residue_cases,
                        induction=induction,
                        accumulator=accumulator,
                    ):
                        continue
                    score = self._counted_loop_model_priority(accumulator, residue_cases)
                    if best_score is None or score > best_score:
                        best_model = (induction, accumulator, guard, residue_cases)
                        best_score = score

    return best_model

def _impl__counted_loop_identity_match_key(
    self,
    left_induction: CountedLoopInduction,
    left_guard: CountedLoopGuard,
    right_induction: CountedLoopInduction,
    right_guard: CountedLoopGuard,
    *,
    result_size: int,
) -> Optional[Tuple[Any, ...]]:
    if int(left_induction.step) != int(right_induction.step):
        return None
    signed_left = bool(left_induction.signed_guard or left_guard.signed_comparison)
    signed_right = bool(right_induction.signed_guard or right_guard.signed_comparison)
    if signed_left != signed_right:
        return None
    try:
        if _runtime_expression_signature(left_induction.init_expr) != _runtime_expression_signature(right_induction.init_expr):
            return None
        if _runtime_expression_signature(left_guard.bound_expr) != _runtime_expression_signature(right_guard.bound_expr):
            return None
        if _runtime_expression_signature(left_guard.condition_expr) != _runtime_expression_signature(right_guard.condition_expr):
            return None
        left_entry = left_guard.entry_condition_expr or left_guard.condition_expr
        right_entry = right_guard.entry_condition_expr or right_guard.condition_expr
        if _runtime_expression_signature(left_entry) != _runtime_expression_signature(right_entry):
            return None
    except Exception:
        return None
    left_width = max(1, int(getattr(left_induction.placeholder, "size", 0) or 4))
    right_width = max(1, int(getattr(right_induction.placeholder, "size", 0) or 4))
    if left_width != right_width:
        return None
    return (
        "loop_identity",
        _runtime_expression_signature(left_induction.init_expr),
        _runtime_expression_signature(left_guard.bound_expr),
        int(left_induction.step),
        _runtime_expression_signature(left_guard.condition_expr),
        _runtime_expression_signature(left_guard.entry_condition_expr or left_guard.condition_expr),
        signed_left,
        "bv_modular",
    )

def _impl__candidate_counted_loop_guards(
    self,
    header_block,
    cbranch_op,
    induction: CountedLoopInduction,
) -> List[CountedLoopGuard]:
    guards: List[CountedLoopGuard] = []
    seen = set()
    for candidate in (
        self._match_latch_counted_loop_guard(header_block, induction),
        self._match_counted_loop_guard(header_block, cbranch_op, induction),
    ):
        if candidate is None:
            continue
        key = (
            _runtime_expression_signature(candidate.condition_expr),
            _runtime_expression_signature(candidate.bound_expr),
            self._block_key(candidate.body_block),
            self._block_key(candidate.exit_block),
            self._block_key(candidate.latch_block),
        )
        if key in seen:
            continue
        seen.add(key)
        guards.append(candidate)
    return guards

def _impl__induction_backedge_indices(
    self,
    induction: CountedLoopInduction,
) -> Tuple[int, ...]:
    indices = tuple(int(index) for index in getattr(induction, "backedge_indices", ()) or ())
    if indices:
        return indices
    return (int(getattr(induction, "backedge_index", 0)),)

def _impl__accumulator_backedge_indices(
    self,
    accumulator: CountedLoopAccumulator,
) -> Tuple[int, ...]:
    indices = tuple(int(index) for index in getattr(accumulator, "backedge_indices", ()) or ())
    if indices:
        return indices
    return (int(getattr(accumulator, "backedge_index", 0)),)

def _impl__match_counted_loop_induction(
    self,
    phi_op,
) -> Optional[CountedLoopInduction]:
    input_count = int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0)
    if input_count < 2:
        return None
    phi_output = getattr(phi_op, "getOutput", lambda: None)()
    if phi_output is None:
        return None

    placeholder = Expression.parameter("__loop_iv", index=-10_000, size=getattr(phi_output, "getSize", lambda: 4)() or 4)
    step_candidates = []
    for backedge_index in range(input_count):
        step = self._extract_index_step(phi_op.getInput(backedge_index), phi_output)
        if step in {None, 0}:
            continue
        step_candidates.append((backedge_index, int(step)))
    if not step_candidates:
        return None

    step_values = {step for _index, step in step_candidates}
    if len(step_values) != 1:
        return None
    init_indices = [index for index in range(input_count) if index not in {candidate for candidate, _step in step_candidates}]
    if len(init_indices) != 1:
        return None

    init_index = init_indices[0]
    step_value = step_candidates[0][1]
    init_expr = self._build_pcode_expression(
        phi_op.getInput(init_index),
        placeholders={phi_output: placeholder},
    )
    if init_expr is None or self._expression_is_unresolved(init_expr):
        return None
    return CountedLoopInduction(
        phi_op=phi_op,
        phi_output=phi_output,
        init_expr=init_expr,
        backedge_index=step_candidates[0][0],
        step=step_value,
        placeholder=placeholder,
        signed_guard=False,
        init_index=init_index,
        backedge_indices=tuple(index for index, _step in step_candidates),
    )
    return None

def _impl__match_counted_loop_guard(
    self,
    header_block,
    cbranch_op,
    induction: CountedLoopInduction,
) -> Optional[CountedLoopGuard]:
    block_info = self._pick_body_and_exit_blocks(header_block)
    if block_info is None:
        return None
    body_block, exit_block, body_on_true = block_info
    if int(getattr(cbranch_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return None

    raw_expr = self._build_pcode_expression(
        cbranch_op.getInput(1),
        placeholders={induction.phi_output: induction.placeholder},
    )
    if raw_expr is None or self._expression_is_unresolved(raw_expr):
        return None

    normalized = self._normalize_loop_continue_guard(
        raw_expr,
        induction.placeholder,
        body_on_true,
        induction.step,
    )
    if normalized is not None:
        condition_expr, entry_condition_expr, bound_expr, signed_comparison = normalized
        return CountedLoopGuard(
            condition_expr=condition_expr,
            bound_expr=bound_expr,
            continue_on_true=body_on_true,
            body_block=body_block,
            exit_block=exit_block,
            signed_comparison=signed_comparison,
            guard_op=cbranch_op,
            entry_condition_expr=entry_condition_expr,
        )
    return None

def _impl__match_latch_counted_loop_guard(
    self,
    header_block,
    induction: CountedLoopInduction,
) -> Optional[CountedLoopGuard]:
    backedge_indices = self._induction_backedge_indices(induction)
    if not backedge_indices:
        return None
    backedge_varnode = induction.phi_op.getInput(backedge_indices[0])
    backedge_def = getattr(backedge_varnode, "getDef", lambda: None)()
    if backedge_def is None:
        return None
    latch_block = getattr(backedge_def, "getParent", lambda: None)()
    if latch_block is None:
        return None
    cbranch_op = self._find_cbranch_op(latch_block)
    if cbranch_op is None or int(getattr(cbranch_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return None

    successors = self._collect_block_successors(latch_block)
    if len(successors) != 2:
        return None
    header_key = self._block_key(header_block)
    backedge_target = next(
        (successor for successor in successors if self._block_key(successor) == header_key),
        None,
    )
    if backedge_target is None:
        return None
    exit_block = successors[0] if successors[1] is backedge_target else successors[1]
    true_out = getattr(latch_block, "getTrueOut", lambda: None)()
    continue_on_true = true_out is not None and self._block_key(true_out) == header_key

    raw_expr = self._build_pcode_expression(
        cbranch_op.getInput(1),
        placeholders={induction.phi_output: induction.placeholder},
    )
    if raw_expr is None or self._expression_is_unresolved(raw_expr):
        return None
    normalized = self._normalize_latch_continue_guard(
        raw_expr,
        induction.placeholder,
        continue_on_true,
        induction.step,
    )
    if normalized is None:
        return None
    condition_expr, entry_condition_expr, bound_expr, signed_comparison = normalized
    return CountedLoopGuard(
        condition_expr=condition_expr,
        bound_expr=bound_expr,
        continue_on_true=continue_on_true,
        body_block=header_block,
        exit_block=exit_block,
        signed_comparison=signed_comparison,
        guard_op=cbranch_op,
        entry_condition_expr=entry_condition_expr,
        latch_block=latch_block,
    )

def _impl__match_counted_loop_accumulators(
    self,
    phi_ops: Sequence,
    induction: CountedLoopInduction,
    body_block,
    *,
    function_body_ranges: Sequence[Tuple[int, int]] = (),
) -> List[CountedLoopAccumulator]:
    induction_input_count = int(getattr(induction.phi_op, "getNumInputs", lambda: 0)() or 0)
    induction_init_index = self._induction_init_index(induction)
    induction_backedge_indices = self._induction_backedge_indices(induction)
    candidate_ops = [
        phi_op for phi_op in phi_ops
        if phi_op is not induction.phi_op
        and int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0) == induction_input_count
        and getattr(phi_op, "getOutput", lambda: None)() is not None
    ]

    candidates: List[CountedLoopAccumulator] = []
    for phi_op in candidate_ops:
        phi_output = getattr(phi_op, "getOutput", lambda: None)()
        init_index = induction_init_index
        try:
            init_expr = self._trace_varnode_expression(phi_op.getInput(init_index))
            if init_expr is None or self._expression_is_unresolved(init_expr):
                init_expr = self._build_pcode_expression(phi_op.getInput(init_index), placeholders={})
        except RecursionError:
            continue
        if init_expr is None or self._expression_is_unresolved(init_expr):
            continue
        if self._expression_contains_executable_address_constant(
            init_expr,
            function_body_ranges=function_body_ranges,
        ):
            self._debug(
                "Declined counted scalar loop accumulator: init expression contains executable address constant"
            )
            continue
        placeholder = self._loop_variable_expression(
            None,
            "accumulator",
            "__loop_acc",
            phi_output,
            getattr(phi_output, "getSize", lambda: 4)() or 4,
        )
        accumulator = CountedLoopAccumulator(
            phi_op=phi_op,
            phi_output=phi_output,
            init_expr=init_expr,
            backedge_index=induction.backedge_index,
            placeholder=placeholder,
            member_outputs=(phi_output,),
            member_placeholders=(placeholder,),
            init_index=init_index,
            backedge_indices=induction_backedge_indices,
        )
        all_backedges_resolved = True
        for backedge_index in self._accumulator_backedge_indices(accumulator):
            backedge_varnode = phi_op.getInput(backedge_index)
            backedge_def = getattr(backedge_varnode, "getDef", lambda: None)()
            parent_block = getattr(backedge_def, "getParent", lambda: None)() if backedge_def is not None else None
            if body_block is not None and parent_block is not None:
                if not self._can_reach_block(body_block, parent_block):
                    all_backedges_resolved = False
                    break
            try:
                resolved_backedge = self._build_pcode_expression(
                    backedge_varnode,
                    placeholders={
                        induction.phi_output: induction.placeholder,
                        accumulator.phi_output: accumulator.placeholder,
                    },
                )
            except RecursionError:
                all_backedges_resolved = False
                break
            if resolved_backedge is None or self._expression_is_unresolved(resolved_backedge):
                all_backedges_resolved = False
                break
        if all_backedges_resolved:
            candidates.append(accumulator)
    candidates.sort(
        key=lambda candidate: self._counted_loop_accumulator_order_key(candidate),
    )
    candidates = self._assign_counted_loop_accumulator_binder_ordinals(candidates)
    return candidates

def _impl__assign_counted_loop_accumulator_binder_ordinals(
    self,
    accumulators: Sequence[CountedLoopAccumulator],
) -> List[CountedLoopAccumulator]:
    loop_variable_binder_scope = self._new_loop_variable_binder_scope()
    rebound: List[CountedLoopAccumulator] = []
    for accumulator in accumulators:
        if accumulator.phi_output is None:
            rebound.append(accumulator)
            continue
        placeholder = self._loop_variable_expression(
            loop_variable_binder_scope,
            "accumulator",
            accumulator.placeholder.name or "__loop_acc",
            accumulator.phi_output,
            getattr(accumulator.phi_output, "getSize", lambda: None)()
            or getattr(accumulator.placeholder, "size", None)
            or 4,
        )
        member_placeholders: List[Expression] = []
        for output in accumulator.member_outputs:
            if output is accumulator.phi_output:
                member_placeholders.append(placeholder)
                continue
            member_placeholders.append(
                self._loop_variable_expression(
                    loop_variable_binder_scope,
                    "accumulator",
                    "__loop_acc",
                    output,
                    getattr(output, "getSize", lambda: None)()
                    or getattr(accumulator.placeholder, "size", None)
                    or 4,
                )
            )
        rebound.append(
            replace(
                accumulator,
                placeholder=placeholder,
                member_placeholders=tuple(member_placeholders),
            )
        )
    return rebound

def _impl__counted_loop_accumulator_priority(
    self,
    accumulator: CountedLoopAccumulator,
) -> Tuple[int, int, int]:
    phi_output = accumulator.phi_output
    output_size = int(getattr(phi_output, "getSize", lambda: 0)() or getattr(accumulator.placeholder, "size", 0) or 0)
    init_const = 1 if self._raw_constant_value(accumulator.init_expr) is not None else 0
    return (
        1 if self._varnode_reaches_return(phi_output) else 0,
        output_size,
        init_const,
    )

def _impl__counted_loop_accumulator_order_key(
    self,
    accumulator: CountedLoopAccumulator,
) -> Tuple[int, int, int, str]:
    priority = self._counted_loop_accumulator_priority(accumulator)
    stable_key = self._counted_loop_accumulator_stable_key(accumulator)
    return (
        -int(priority[0]),
        -int(priority[1]),
        -int(priority[2]),
        repr(stable_key),
    )

def _impl__counted_loop_accumulator_stable_key(
    self,
    accumulator: CountedLoopAccumulator,
) -> Tuple[Any, ...]:
    op_ref = self._make_pcode_op_ref(accumulator.phi_op)
    op_key = op_ref.stable_key() if op_ref is not None else None
    output_key = self._varnode_cache_key(accumulator.phi_output)
    member_keys = tuple(self._varnode_cache_key(member) for member in accumulator.member_outputs)
    update_key = self._varnode_cache_key(accumulator.update_varnode)
    return (
        op_key,
        output_key,
        member_keys,
        update_key,
    )

def _impl__counted_loop_model_priority(
    self,
    accumulator: CountedLoopAccumulator,
    residue_cases: Sequence[ResidueLoopCase],
) -> Tuple[int, int, int, int, int]:
    max_coeff = 0
    max_bias = 0
    for case in residue_cases or ():
        max_coeff = max(max_coeff, abs(int(case.affine[0])))
        max_bias = max(max_bias, abs(int(case.affine[1])))
        if case.bias_expr is not None:
            max_bias = max(max_bias, 1)
    target_varnode = accumulator.phi_output or accumulator.update_varnode
    member_count = len(accumulator.member_outputs) or (1 if target_varnode is not None else 0)
    return (
        1 if self._varnode_reaches_return(target_varnode) else 0,
        1 if max_coeff != 0 else 0,
        max_coeff,
        member_count,
        max_bias,
    )

def _impl__extract_counted_loop_update_cases(
    self,
    accumulator: CountedLoopAccumulator,
    induction: CountedLoopInduction,
    guard: CountedLoopGuard,
) -> List[CountedLoopUpdateCase]:
    header_block = getattr(induction.phi_op, "getParent", lambda: None)()
    placeholders = {
        induction.phi_output: induction.placeholder,
    }
    for output, replacement in zip(accumulator.member_outputs, accumulator.member_placeholders):
        placeholders[output] = replacement
    if not accumulator.member_outputs and accumulator.phi_output is not None:
        placeholders[accumulator.phi_output] = accumulator.placeholder
    placeholders.update(
        self._collect_affine_loop_state_placeholders(
            header_block=header_block,
            induction=induction,
            accumulator=accumulator,
        )
    )

    raw_cases: List[Tuple[List[Condition], Expression]] = []
    if accumulator.update_varnode is not None:
        expr = self._build_pcode_expression(accumulator.update_varnode, placeholders=placeholders)
        if expr is None or self._expression_is_unresolved(expr):
            return []
        target_block = accumulator.update_block or guard.latch_block or guard.body_block
        for conditions in self._enumerate_paths_with_conditions(
            start_block=guard.body_block,
            target_block=target_block,
            header_block=header_block,
            placeholders=placeholders,
            stop_block=guard.exit_block,
            ):
                raw_cases.append((conditions, expr))
    else:
        if accumulator.phi_op is None:
            return []
        parent_block = getattr(accumulator.phi_op, "getParent", lambda: None)()
        in_size = int(getattr(parent_block, "getInSize", lambda: 0)() or 0) if parent_block is not None else 0
        for backedge_index in self._accumulator_backedge_indices(accumulator):
            backedge_varnode = accumulator.phi_op.getInput(backedge_index)
            def_op = getattr(backedge_varnode, "getDef", lambda: None)()
            if def_op is not None and getattr(def_op, "getMnemonic", lambda: None)() == "MULTIEQUAL":
                def_parent = getattr(def_op, "getParent", lambda: None)()
                def_in_size = int(getattr(def_parent, "getInSize", lambda: 0)() or 0) if def_parent is not None else 0
                input_count = int(getattr(def_op, "getNumInputs", lambda: 0)() or 0)
                for index in range(input_count):
                    expr = self._build_pcode_expression(def_op.getInput(index), placeholders=placeholders)
                    if expr is None or self._expression_is_unresolved(expr):
                        continue
                    target_block = None
                    if def_parent is not None and index < def_in_size:
                        target_block = def_parent.getIn(index)
                    if target_block is None:
                        target_block = def_parent or guard.body_block
                    for conditions in self._enumerate_paths_with_conditions(
                        start_block=guard.body_block,
                        target_block=target_block,
                        header_block=header_block,
                        placeholders=placeholders,
                        stop_block=guard.exit_block,
                    ):
                        raw_cases.append((conditions, expr))
                continue
            expr = self._build_pcode_expression(backedge_varnode, placeholders=placeholders)
            if expr is None or self._expression_is_unresolved(expr):
                continue
            target_block = None
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
        if not raw_cases:
            return []

    cases: List[CountedLoopUpdateCase] = []
    seen = set()
    for conditions, update_expr in raw_cases:
        simplified = ConditionSimplifier.simplify_conditions_object_centric(list(conditions or []))
        if ConditionSimplifier.object_centric_is_contradiction(simplified):
            continue
        reduced_update = _reduce_expression_under_conditions(update_expr, simplified) or update_expr
        delta_expr = self._extract_additive_delta(reduced_update, accumulator.placeholder, list(simplified))
        if delta_expr is None:
            continue
        key = (
            _runtime_conditions_signature(simplified),
            _runtime_expression_signature(delta_expr),
        )
        if key in seen:
            continue
        seen.add(key)
        cases.append(
            CountedLoopUpdateCase(
                conditions=tuple(simplified),
                update_expr=reduced_update,
                delta_expr=delta_expr,
            )
        )
    return cases

def _impl__try_extract_counted_loop_update_cases_for_summary(
    self,
    accumulator: CountedLoopAccumulator,
    induction: CountedLoopInduction,
    guard: CountedLoopGuard,
) -> Tuple[CountedLoopUpdateCase, ...]:
    try:
        return tuple(self._extract_counted_loop_update_cases(accumulator, induction, guard))
    except (AttributeError, TypeError, IndexError, RecursionError):
        return ()

def _impl__build_counted_loop_case_refs(
    self,
    cases: Sequence[CountedLoopUpdateCase],
) -> Tuple[LoopCaseRef, ...]:
    refs: List[LoopCaseRef] = []
    for case in cases or ():
        body_effect = LoopBodyEffectRef(
            kind="accumulator_update",
            source="pcode_summary",
            scope="loop",
            guard_constraints=tuple(case.conditions or ()),
            value_expr=case.update_expr,
        )
        refs.append(
            LoopCaseRef(
                path_conditions=tuple(case.conditions or ()),
                body_effect=body_effect,
                term_expr=case.delta_expr,
                case_kind="accumulator_delta",
                source="counted_loop_update_case",
            )
        )
    return tuple(refs)

def _impl__is_counted_loop_bound_expr(self, expr: Optional[Expression]) -> bool:
    if expr is None or self._expression_is_unresolved(expr):
        return False
    expr_size = int(getattr(expr, "size", 0) or 0)
    if expr_size == 1:
        return False
    if getattr(expr, "expr_type", None) == ExpressionType.BINARY_OP:
        if expr.operator in {
            "BOOL_AND",
            "BOOL_OR",
            "BOOL_XOR",
            "INT_EQUAL",
            "INT_NOTEQUAL",
            "INT_LESS",
            "INT_LESSEQUAL",
            "INT_SLESS",
            "INT_SLESSEQUAL",
        }:
            return False
    return True

def _impl__validate_counted_loop_update_cases(
    self,
    *,
    cases: Sequence[CountedLoopUpdateCase],
    residue_cases: Sequence[ResidueLoopCase],
    induction: CountedLoopInduction,
    accumulator: CountedLoopAccumulator,
) -> bool:
    """Require the affine recurrence to match the actual loop update.

    Residue extraction is intentionally syntactic: it classifies already
    extracted deltas.  Before accepting a closed form, prove with SMT that
    each source CFG update case is exactly the accumulator state plus the
    affine delta assigned to that residue.  This keeps direct summaries from
    becoming a shortcut around the real P-code update semantics.
    """
    if not cases or not residue_cases:
        return False

    counter_name = induction.placeholder.name or "__loop_iv"
    by_residue = {
        (int(case.modulus), int(case.residue)): case
        for case in residue_cases
    }
    if len(by_residue) != len(residue_cases):
        return False

    for case in cases:
        residue_info = self._extract_exact_residue_case(case.conditions, counter_name)
        if residue_info is None:
            if len(residue_cases) != 1:
                return False
            only = residue_cases[0]
            if int(only.modulus) != 1 or int(only.residue) != 0:
                return False
            residue_info = (1, 0)

        residue_case = by_residue.get((int(residue_info[0]), int(residue_info[1])))
        if residue_case is None:
            return False

        affine_delta = self._build_affine_delta_expression(
            induction.placeholder,
            residue_case.affine,
            max(
                int(getattr(case.delta_expr, "size", 0) or 0),
                int(getattr(case.update_expr, "size", 0) or 0),
                int(getattr(accumulator.placeholder, "size", 0) or 0),
                int(getattr(induction.placeholder, "size", 0) or 0),
                4,
            ),
            bias_expr=residue_case.bias_expr,
        )
        if affine_delta is None:
            return False

        parameters = self._collect_summary_parameter_specs(
            case.update_expr,
            case.delta_expr,
            affine_delta,
            accumulator.placeholder,
            induction.placeholder,
            *(condition.expression for condition in case.conditions or [] if condition is not None),
        )
        if not self._prove_expression_equivalence_under_conditions(
            case.delta_expr,
            affine_delta,
            case.conditions,
            parameters,
        ):
            self._debug("Declined counted scalar loop summary: extracted delta does not match residue affine case")
            return False

        expected_update = self._sum_expression_terms([accumulator.placeholder, affine_delta])
        if expected_update is None:
            return False
        expected_update.size = max(
            int(getattr(expected_update, "size", 0) or 0),
            int(getattr(case.update_expr, "size", 0) or 0),
            int(getattr(accumulator.placeholder, "size", 0) or 0),
        )
        if not self._prove_expression_equivalence_under_conditions(
            case.update_expr,
            expected_update,
            case.conditions,
            parameters,
        ):
            self._debug("Declined counted scalar loop summary: update expression is not accumulator plus affine delta")
            return False

    return True

def _impl__has_branch_accumulator_candidate(
    self,
    analysis,
) -> bool:
    if analysis is None or not analysis.returns or len(analysis.parameters or []) < 3:
        return False
    effect_summary = getattr(analysis, "effect_summary", None)
    if effect_summary is None or not getattr(effect_summary, "effects", None):
        return False
    if self._infer_loop_parameter_pair(analysis) is None:
        return False
    if not self._infer_pointer_parameter_name(analysis):
        return False
    return True

def _impl__has_exact_accumulator_init_return_at_state_one(
    self,
    *,
    analysis,
    state_expr: Expression,
    accumulator_init: Expression,
    result_size: int,
) -> bool:
    expected_value = self._coerce_summary_expression_to_size(
        accumulator_init,
        max(1, int(result_size or getattr(accumulator_init, "size", 0) or 4)),
        signed=self._expression_prefers_signed_extension(accumulator_init),
    )
    expected_value = self._canonicalize_expression(expected_value)
    if expected_value is None or self._expression_is_unresolved(expected_value):
        return False
    state_one_expr = Expression.binary_op(
        "INT_EQUAL",
        self._canonicalize_expression(state_expr),
        Expression.constant(
            1,
            size=max(1, int(getattr(state_expr, "size", 0) or result_size or 4)),
        ),
    )
    state_one_expr.size = 1
    state_one_condition = Condition(self._canonicalize_expression(state_one_expr), False)
    active_preconditions = self._analysis_active_preconditions(analysis)
    region_conditions = tuple(active_preconditions or ()) + (state_one_condition,)
    exact_anchor_returns: List[ReturnInfo] = []
    for ret in tuple(getattr(analysis, "returns", ()) or ()):
        if not (
            self._return_is_exact_anchor_seed(ret)
            or self._return_is_stable_resolved_phi_anchor_seed(ret)
        ):
            continue
        conditions = tuple(getattr(ret, "conditions", ()) or ())
        if not self._conditions_overlap_conditions(conditions, region_conditions):
            continue
        value = self._coerce_summary_expression_to_size(
            getattr(ret, "value", None),
            max(1, int(result_size or getattr(expected_value, "size", 0) or 4)),
            signed=self._expression_prefers_signed_extension(expected_value),
        )
        value = self._canonicalize_expression(value)
        if value is None or self._expression_is_unresolved(value):
            continue
        if not self._return_value_equals_under_conditions(
            value,
            expected_value,
            region_conditions + conditions,
        ):
            return False
        exact_anchor_returns.append(ret)
    if not exact_anchor_returns:
        return False
    if any(not tuple(getattr(ret, "conditions", None) or ()) for ret in exact_anchor_returns):
        return True
    coverage_key = self._prove_return_conditions_cover_region(
        region_conditions=region_conditions,
        returns=exact_anchor_returns,
    )
    return coverage_key is not None

def _impl__build_state_decrement_accumulator_sum_value(
    self,
    *,
    model: StateTransitionLoopModel,
    result_size: int,
) -> Optional[Expression]:
    if not self._state_guard_proves_signed_positive_placeholder(
        model.state_guard_expr,
        model.state_placeholder,
    ):
        self._debug(
            "Declined state-affine accumulator sum: state guard is not signed-positive "
            f"({model.state_guard_expr.to_string()}); "
            f"transition={model.state_transition_expr.to_string()}; "
            f"delta={model.accumulator_delta_expr.to_string()}"
        )
        return None
    transition_affine = self._extract_affine_placeholder_term(
        model.state_transition_expr,
        model.state_placeholder,
    )
    if transition_affine != (1, -1):
        self._debug(
            "Declined state-affine accumulator sum: transition is not unit decrement "
            f"({model.state_transition_expr.to_string()} -> {transition_affine})"
        )
        return None
    delta_affine = self._extract_affine_placeholder_term(
        model.accumulator_delta_expr,
        model.state_placeholder,
    )
    if delta_affine is None:
        self._debug(
            "Declined state-affine accumulator sum: accumulator delta is not affine in state "
            f"({model.accumulator_delta_expr.to_string()})"
        )
        return None
    coeff, bias = delta_affine
    closed_form = self._build_closed_form(
        model.state_init_expr,
        lower_bound=0,
        coeff=coeff,
        bias=bias,
        base_value=0,
    )
    if closed_form is None:
        return None
    return self._truncate_to_width(closed_form, result_size)

def _impl__try_build_latch_exit_decrement_accumulator_sum_returns(
    self,
    *,
    function,
    model: StateTransitionLoopModel,
    analysis,
    result_size: int,
    accumulator_init: Expression,
) -> Optional[List[ReturnInfo]]:
    if not self._state_guard_is_placeholder_not_equal_one(
        model.state_guard_expr,
        model.state_placeholder,
    ):
        return None
    transition_affine = self._extract_affine_placeholder_term(
        model.state_transition_expr,
        model.state_placeholder,
    )
    if transition_affine != (1, -1):
        return None
    delta_affine = self._extract_affine_placeholder_term(
        model.accumulator_delta_expr,
        model.state_placeholder,
    )
    if delta_affine != (1, 0):
        return None
    witnesses = self._find_latch_exit_decrement_sum_witness_returns(
        analysis=analysis,
        model=model,
        result_size=result_size,
    )
    if witnesses is None:
        self._debug(
            "Declined latch-exit decrement sum: missing n<=0 / n==1 return witness"
        )
        return None
    base_anchor, loop_anchor = witnesses
    loop_value = self._build_peeled_decrement_accumulator_sum_value(
        model.state_init_expr,
        result_size=result_size,
    )
    if loop_value is None:
        return None
    loop_value = self._add_state_transition_accumulator_seed(
        accumulator_init,
        loop_value,
        result_size,
    )
    if loop_value is None:
        return None
    base_value = self._coerce_summary_expression_to_size(
        accumulator_init,
        result_size,
        signed=self._expression_prefers_signed_extension(accumulator_init),
    )
    if self._expression_is_unresolved(base_value):
        return None
    positive_conditions = self._build_recursive_conditions(model.state_init_expr, 0)
    base_conditions = self._build_base_conditions(model.state_init_expr, 0)
    if positive_conditions is None or base_conditions is None:
        return None

    def metadata(anchor, fallback_op):
        pcode_ref = getattr(anchor, "pcode_op_ref", None)
        if pcode_ref is None:
            pcode_ref = self._make_pcode_op_ref(fallback_op)
        return {
            "address": str(
                getattr(anchor, "address", None)
                or getattr(function, "getEntryPoint", lambda: "state_transition_loop")()
            ),
            "pcode_identity": getattr(anchor, "pcode_identity", None),
            "pcode_order": getattr(anchor, "pcode_order", None),
            "pcode_time": getattr(anchor, "pcode_time", None),
            "pcode_op_ref": pcode_ref,
        }

    base_metadata = metadata(base_anchor, self._find_cbranch_op(model.header_block))
    loop_metadata = metadata(loop_anchor, self._find_cbranch_op(model.header_block))
    return [
        ReturnInfo(
            value=base_value,
            conditions=base_conditions,
            branch_index=getattr(base_anchor, "branch_index", 0),
            **base_metadata,
        ),
        ReturnInfo(
            value=loop_value,
            conditions=positive_conditions,
            branch_index=10_300,
            **loop_metadata,
        ),
    ]

def _impl__build_peeled_decrement_accumulator_sum_value(
    self,
    state_init_expr: Expression,
    *,
    result_size: int,
) -> Optional[Expression]:
    state_size = max(1, int(getattr(state_init_expr, "size", 0) or result_size or 4))
    state = self._truncate_to_width(state_init_expr, state_size)
    one = Expression.constant(1, state_size)
    two = Expression.constant(2, state_size)
    state_minus_one = Expression.binary_op("INT_SUB", state, one)
    state_minus_one.size = state_size
    state_minus_two = Expression.binary_op("INT_SUB", state, two)
    state_minus_two.size = state_size
    square = Expression.binary_op("INT_MULT", state_minus_one, state_minus_one)
    square.size = state_size
    wide_size = self._summary_working_size(state_size)
    wide_left = self._zero_extend_bitpattern(state_minus_one, wide_size)
    wide_right = self._zero_extend_bitpattern(state_minus_two, wide_size)
    product = Expression.binary_op("INT_MULT", wide_left, wide_right)
    product.size = wide_size
    half = Expression.binary_op("INT_RIGHT", product, Expression.constant(1, wide_size))
    half.size = wide_size
    half_low = self._truncate_to_width(half, state_size)
    square_plus_state = Expression.binary_op("INT_ADD", square, state)
    square_plus_state.size = state_size
    total = Expression.binary_op("INT_SUB", square_plus_state, half_low)
    total.size = state_size
    return self._canonicalize_expression(self._truncate_to_width(total, result_size))

def _impl__find_state_loop_accumulator(
    self,
    *,
    phi_ops: Sequence[object],
    state_phi,
    state_output,
    state_placeholder: Expression,
    init_index: int,
    backedge_indices: Sequence[int],
    analysis=None,
    loop_variable_binder_scope: Optional[Dict[Tuple[str, Tuple[Any, ...]], int]] = None,
) -> Optional[Tuple[object, object, Expression, Expression, Expression, int, Tuple[int, ...]]]:
    if loop_variable_binder_scope is None:
        loop_variable_binder_scope = self._new_loop_variable_binder_scope()
    candidates = []
    for phi_op in phi_ops:
        if phi_op is state_phi:
            continue
        phi_parent = getattr(phi_op, "getParent", lambda: None)()
        phi_indices = self._state_loop_phi_indices(phi_parent, phi_op) if phi_parent is not None else None
        if phi_indices is None:
            phi_init_index = init_index
            phi_backedge_indices = tuple(backedge_indices)
        else:
            phi_init_index, phi_backedge_indices = phi_indices
        if self._safe_pcode_input_count(phi_op) <= max(phi_backedge_indices or (0,)):
            continue
        phi_output = getattr(phi_op, "getOutput", lambda: None)()
        if phi_output is None:
            continue
        accumulator_placeholder = self._loop_variable_expression(
            loop_variable_binder_scope,
            "accumulator",
            "__loop_acc",
            phi_output,
            max(1, int(getattr(phi_output, "getSize", lambda: 4)() or 4)),
        )
        init_expr = self._build_pcode_expression(
            phi_op.getInput(phi_init_index),
            placeholders={state_output: state_placeholder, phi_output: accumulator_placeholder},
        )
        if init_expr is None or self._expression_is_unresolved(init_expr):
            continue
        delta_expr = self._state_loop_accumulator_delta(
            phi_op=phi_op,
            phi_output=phi_output,
            accumulator_placeholder=accumulator_placeholder,
            state_output=state_output,
            state_placeholder=state_placeholder,
            backedge_indices=phi_backedge_indices,
            parameters=list(getattr(analysis, "parameters", []) or []),
        )
        if delta_expr is None or self._expression_is_unresolved(delta_expr):
            continue
        candidates.append(
            (
                self._state_loop_accumulator_priority(phi_output, init_expr, delta_expr),
                phi_op,
                phi_output,
                self._canonicalize_expression(init_expr),
                self._canonicalize_expression(delta_expr),
                accumulator_placeholder,
                int(phi_init_index),
                tuple(int(index) for index in phi_backedge_indices),
            )
        )
    if not candidates:
        return None
    candidates.sort(key=lambda item: item[0], reverse=True)
    (
        _priority,
        phi_op,
        phi_output,
        init_expr,
        delta_expr,
        placeholder,
        phi_init_index,
        phi_backedge_indices,
    ) = candidates[0]
    return (
        phi_op,
        phi_output,
        init_expr,
        delta_expr,
        placeholder,
        phi_init_index,
        phi_backedge_indices,
    )

def _impl__state_loop_accumulator_delta(
    self,
    *,
    phi_op,
    phi_output,
    accumulator_placeholder: Expression,
    state_output,
    state_placeholder: Expression,
    backedge_indices: Sequence[int],
    parameters: Sequence[dict],
) -> Optional[Expression]:
    delta_keys = []
    delta_exprs = []
    for index in backedge_indices:
        update_expr = self._build_pcode_expression(
            phi_op.getInput(index),
            placeholders={
                state_output: state_placeholder,
                phi_output: accumulator_placeholder,
            },
        )
        if update_expr is None or self._expression_is_unresolved(update_expr):
            return None
        deltas = self._extract_delta_from_possible_phi(
            update_expr,
            accumulator_placeholder,
            parameters,
        )
        if not deltas:
            return None
        for delta in deltas:
            delta = self._canonicalize_expression(delta)
            delta_key = _runtime_expression_signature(delta)
            delta_keys.append(delta_key)
            delta_exprs.append(delta)
    if not delta_exprs:
        return None
    first_key = delta_keys[0]
    if any(key != first_key for key in delta_keys[1:]):
        return None
    return delta_exprs[0]

def _impl__state_loop_accumulator_priority(
    self,
    phi_output,
    init_expr: Expression,
    delta_expr: Expression,
) -> Tuple[int, int, int, int]:
    return (
        1 if self._varnode_reaches_return(phi_output) else 0,
        1 if self._raw_constant_value(init_expr) == 0 else 0,
        1 if self._raw_constant_value(delta_expr) == 1 else 0,
        max(1, int(getattr(phi_output, "getSize", lambda: 0)() or 0)),
    )

def _impl__multiequal_input_is_accumulator_update(self, phi_op, input_varnode) -> bool:
    return self._same_varnode_identity(
        input_varnode,
        self._unique_multiequal_accumulator_update_input(phi_op),
    )

def _impl__unique_multiequal_accumulator_update_input(self, phi_op):
    phi_output = getattr(phi_op, "getOutput", lambda: None)()
    if phi_output is None:
        return None
    update_inputs = []
    seed_inputs = []
    input_count = int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0)
    for index in range(input_count):
        try:
            candidate = phi_op.getInput(index)
        except Exception:
            continue
        if self._varnode_is_accumulator_update_for_phi(candidate, phi_output):
            update_inputs.append((index, candidate))
        else:
            seed_inputs.append((index, candidate))
    if len(update_inputs) != 1:
        return None
    if not seed_inputs:
        return None
    update_indices = tuple(index for index, _candidate in update_inputs)
    for seed_index, seed_input in seed_inputs:
        if self._varnode_depends_on_varnode(seed_input, phi_output):
            return None
        if self._varnode_aliases_accumulator_object(seed_input, phi_output) and not (
            self._phi_input_is_cfg_entry_seed(phi_op, seed_index, update_indices)
        ):
            return None
    return update_inputs[0][1]

def _impl__multiequal_accumulator_update_rejection_reason(self, phi_op) -> str:
    phi_output = getattr(phi_op, "getOutput", lambda: None)()
    if phi_output is None:
        return "no_phi_output"
    update_inputs = []
    seed_inputs = []
    input_count = int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0)
    for index in range(input_count):
        try:
            candidate = phi_op.getInput(index)
        except Exception:
            continue
        if self._varnode_is_accumulator_update_for_phi(candidate, phi_output):
            update_inputs.append((index, candidate))
        else:
            seed_inputs.append((index, candidate))
    seed_depends = [
        self._varnode_depends_on_varnode(seed_input, phi_output)
        for _seed_index, seed_input in seed_inputs
    ]
    seed_aliases = [
        self._varnode_aliases_accumulator_object(seed_input, phi_output)
        for _seed_index, seed_input in seed_inputs
    ]
    update_indices = tuple(index for index, _candidate in update_inputs)
    seed_entry = [
        self._phi_input_is_cfg_entry_seed(phi_op, seed_index, update_indices)
        for seed_index, _seed_input in seed_inputs
    ]
    return (
        f"updates={len(update_inputs)}, seeds={len(seed_inputs)}, "
        f"seed_depends={tuple(seed_depends)}, seed_aliases={tuple(seed_aliases)}, "
        f"seed_entry={tuple(seed_entry)}"
    )

def _impl__varnode_is_accumulator_update_for_phi(self, candidate, phi_output) -> bool:
    def_op = getattr(candidate, "getDef", lambda: None)()
    if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "INT_ADD":
        return False
    if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return False
    for index in range(int(getattr(def_op, "getNumInputs", lambda: 0)() or 0)):
        try:
            candidate = self._follow_passthrough_varnode(def_op.getInput(index))
        except Exception:
            continue
        if self._same_varnode_value(candidate, phi_output):
            return True
    return False

def _impl__varnode_aliases_accumulator_object(self, candidate, phi_output) -> bool:
    """Return True when a non-update PHI input is the accumulator object itself.

    This deliberately avoids storage-address equality: optimized Ghidra SSA can
    place a real entry seed and a loop-carried value in the same register slot.
    HighVariable and representative identity, however, mean the input is not an
    independent seed object but an alias of the accumulator's SSA object.
    """
    if candidate is None or phi_output is None:
        return False
    try:
        candidate_high = candidate.getHigh()
        phi_high = phi_output.getHigh()
    except Exception:
        return False
    if candidate_high is None or phi_high is None:
        return False
    if candidate_high is phi_high:
        return True
    try:
        if candidate_high == phi_high:
            return True
    except Exception:
        pass
    try:
        candidate_rep = candidate_high.getRepresentative()
        phi_rep = phi_high.getRepresentative()
    except Exception:
        candidate_rep = None
        phi_rep = None
    if candidate_rep is not None and phi_rep is not None:
        if candidate_rep is phi_rep:
            return True
        if self._same_varnode_identity(candidate_rep, phi_rep):
            return True
    return False

def _impl__match_accumulator_phi(
    self,
    phi_op,
    analysis,
    pointer_param: dict,
    count_param: dict,
    pointer_base_ref: LocationBaseRef,
    count_expr: Expression,
    counter_signed: bool,
    pointer_phis: Sequence[Dict[str, object]],
    index_phis: Sequence[Dict[str, object]],
    *,
    result_size: int,
    positive_conditions: Sequence[Condition] = (),
) -> Optional[ReductionAccumulatorProof]:
    candidate = self._match_accumulator_phi_candidate(
        phi_op,
        count_param,
        pointer_param,
        pointer_phis,
        index_phis,
        result_size=result_size,
    )
    if candidate is None:
        return None
    load_progressions = self._grouped_accumulator_load_progressions(
        candidate,
        count_param,
        pointer_param,
        pointer_phis,
        index_phis,
        result_size=result_size,
    )
    if not load_progressions:
        self._debug("Declined readonly accumulator proof candidate: no grouped load progressions")
        return None
    first = load_progressions[0]
    if any(
        signature["stride"] != first["stride"]
        or signature.get("start_index", 0) != first.get("start_index", 0)
        or signature.get("index_step", 1) != first.get("index_step", 1)
        or signature.get("index_scale", signature["stride"]) != first.get("index_scale", first["stride"])
        for signature in load_progressions[1:]
    ):
        self._debug("Declined readonly accumulator proof candidate: grouped load progressions disagree")
        return None
    expanded_terms = self._readonly_load_progression_term_counter(
        load_progressions,
        result_size=max(1, int(result_size or first["element_size"])),
    )
    if expanded_terms is None or any(count != 1 for count in expanded_terms.values()):
        self._debug("Declined readonly accumulator proof candidate: expanded term counts are not one-to-one")
        return None
    proof_start_offset = int(first.get("start_offset", 0) or 0)
    lane_terms = set()
    if len(expanded_terms) > 1:
        proof_start_offset = min(int(offset) for offset, _size in expanded_terms.keys())
        lane_terms = {
            (int(offset) - proof_start_offset, max(1, int(size or 0)))
            for offset, size in expanded_terms.keys()
        }
    seed_terms = self._extract_readonly_accumulator_seed_terms(
        candidate.init_varnode,
        pointer_param,
        first,
    )
    if seed_terms is None:
        self._debug("Declined readonly accumulator proof candidate: accumulator seed terms are not proven")
        return None
    load_op_refs = tuple(
        ref for ref in (signature.get("load_op_ref") for signature in load_progressions)
        if isinstance(ref, PcodeOpRef)
    )
    induction_phi_ref = next(
        (
            ref for ref in (signature.get("induction_phi_ref") for signature in load_progressions)
            if isinstance(ref, PcodeOpRef)
        ),
        None,
    )
    projection_kind = str(getattr(candidate, "return_projection_kind", "identity") or "identity")
    candidate_varnodes = (
        getattr(phi_op, "getOutput", lambda: None)(),
        getattr(candidate.back_def, "getOutput", lambda: None)(),
        candidate.back_varnode,
    )
    if projection_kind == "fp_average":
        direct_value_refs, direct_return_refs = self._fp_average_return_value_and_return_refs_from_varnodes(
            candidate_varnodes,
            count_param,
        )
    else:
        direct_value_refs, direct_return_refs = self._direct_return_value_and_return_refs_from_varnodes(
            candidate_varnodes
        )
        if (
            str(getattr(candidate, "reduction_kind", "") or "").startswith("fp_")
            and not direct_return_refs
        ):
            direct_value_refs, direct_return_refs = self._reachable_return_value_and_return_refs_from_varnodes(
                candidate_varnodes
            )
    return_op_refs = self._dedupe_pcode_refs(tuple(direct_return_refs))
    return_value_op_refs = self._dedupe_pcode_refs(tuple(direct_value_refs))
    proof_result_size = max(1, int(result_size or first["element_size"]))
    if str(getattr(candidate, "reduction_kind", "") or "").startswith("fp_"):
        proof_result_size = max(
            1,
            int(
                getattr(getattr(candidate.back_def, "getOutput", lambda: None)(), "getSize", lambda: 0)()
                or getattr(candidate.back_varnode, "getSize", lambda: 0)()
                or proof_result_size
            ),
        )
    proof = ReductionAccumulatorProof(
        reduction_kind=str(getattr(candidate, "reduction_kind", "memory_sum") or "memory_sum"),
        pointer_base_ref=pointer_base_ref,
        count_parameter_name=count_param.get("name", "count"),
        count_parameter_index=count_param.get("index"),
        count_parameter_storage_identity_key=self._parameter_storage_identity_key(count_param),
        limit_expr=count_expr,
        result_size=proof_result_size,
        stride=int(first["stride"]),
        element_size=int(first["element_size"]),
        start_offset=proof_start_offset,
        start_index=int(first.get("start_index", 0) or 0),
        index_step=int(first.get("index_step", 1) or 1),
        index_scale=int(first.get("index_scale", first["stride"]) or first["stride"]),
        signed_counter=counter_signed,
        seed_terms=tuple(seed_terms),
        lane_terms=tuple(sorted(lane_terms)),
        guard_constraints=tuple(positive_conditions or ()),
        induction_phi_ref=induction_phi_ref,
        accumulator_phi_ref=self._make_pcode_op_ref(phi_op),
        update_op_ref=self._make_pcode_op_ref(candidate.back_def),
        load_op_refs=load_op_refs,
        return_op_refs=return_op_refs,
        return_value_op_refs=return_value_op_refs,
        entry_block_ref=self._make_pcode_block_ref(getattr(phi_op, "getParent", lambda: None)()),
        backedge_block_ref=self._make_pcode_block_ref(getattr(candidate.back_def, "getParent", lambda: None)()),
        return_region_value_proven=bool(return_op_refs or return_value_op_refs),
        source="recurrence_summary",
    )
    self._debug(
        "Readonly accumulator proof candidate: "
        f"start_index={proof.start_index}, start_offset={proof.start_offset}, "
        f"seed_terms={[term.byte_offset for term in proof.seed_terms]}, "
        f"return_refs={[ref.to_dict() for ref in proof.return_op_refs]}, "
        f"return_value_refs={[ref.to_dict() for ref in proof.return_value_op_refs]}"
    )
    return proof

def _impl__match_accumulator_phi_candidate(
    self,
    phi_op,
    count_param: Optional[dict],
    pointer_param: dict,
    pointer_phis: Sequence[Dict[str, object]],
    index_phis: Sequence[Dict[str, object]],
    *,
    result_size: Optional[int] = None,
) -> Optional[ReadonlyAccumulatorPhiCandidate]:
    output = getattr(phi_op, "getOutput", lambda: None)()
    if output is None:
        return None

    input_count = int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0)
    for init_index in range(input_count):
        init_varnode = self._follow_passthrough_varnode(
            self._phi_input_value_varnode(phi_op, init_index)
        )
        for back_index in range(input_count):
            if back_index == init_index:
                continue
            back_varnode = self._follow_passthrough_varnode(
                self._phi_input_value_varnode(phi_op, back_index)
            )
            back_def = getattr(back_varnode, "getDef", lambda: None)()
            if back_def is None:
                continue
            back_mnemonic = getattr(back_def, "getMnemonic", lambda: None)()
            if back_mnemonic not in {"INT_ADD", "FLOAT_ADD"}:
                continue
            input0 = self._follow_passthrough_varnode(back_def.getInput(0))
            input1 = self._follow_passthrough_varnode(back_def.getInput(1))
            if self._same_varnode_value(input0, output):
                addend_varnode = input1
            elif self._same_varnode_value(input1, output):
                addend_varnode = input0
            else:
                continue
            load_progressions = self._collect_load_progressions_from_varnode(
                addend_varnode,
                pointer_param,
                pointer_phis,
                index_phis,
                count_param=count_param,
                result_size=result_size,
            )
            if load_progressions is None or not load_progressions:
                if back_mnemonic == "FLOAT_ADD":
                    self._debug("Declined readonly FP accumulator candidate: addend load progression not proven")
                continue
            reduction_kind = "memory_sum"
            return_projection_kind = "identity"
            if back_mnemonic == "FLOAT_ADD":
                reduction_kind = self._readonly_float_addend_reduction_kind(
                    addend_varnode,
                    count_param,
                )
                if reduction_kind is None:
                    self._debug("Declined readonly FP accumulator candidate: addend transform not proven")
                    continue
            first = load_progressions[0]
            if any(
                signature["stride"] != first["stride"]
                or signature.get("start_index", 0) != first.get("start_index", 0)
                or signature.get("index_step", 1) != first.get("index_step", 1)
                or signature.get("index_scale", signature["stride"]) != first.get("index_scale", first["stride"])
                for signature in load_progressions[1:]
            ):
                continue
            return ReadonlyAccumulatorPhiCandidate(
                phi_op=phi_op,
                init_varnode=init_varnode,
                back_varnode=back_varnode,
                back_def=back_def,
                load_progressions=tuple(load_progressions),
                reduction_kind=reduction_kind,
                return_projection_kind=return_projection_kind,
            )
    return None

def _impl__accumulator_phi_candidates_can_group(
    self,
    base: ReadonlyAccumulatorPhiCandidate,
    sibling: ReadonlyAccumulatorPhiCandidate,
) -> bool:
    base_parent = getattr(base.phi_op, "getParent", lambda: None)()
    sibling_parent = getattr(sibling.phi_op, "getParent", lambda: None)()
    if (
        base_parent is None
        or sibling_parent is None
        or self._pcode_block_group_key(base_parent) != self._pcode_block_group_key(sibling_parent)
    ):
        return False
    if self._pcode_block_group_key(getattr(base.back_def, "getParent", lambda: None)()) != self._pcode_block_group_key(
        getattr(sibling.back_def, "getParent", lambda: None)()
    ):
        return False
    if self._varnode_constant_value(base.init_varnode) != self._varnode_constant_value(sibling.init_varnode):
        return False
    if str(getattr(base, "reduction_kind", "memory_sum")) != str(getattr(sibling, "reduction_kind", "memory_sum")):
        return False
    if str(getattr(base, "return_projection_kind", "identity")) != str(
        getattr(sibling, "return_projection_kind", "identity")
    ):
        return False
    return self._accumulator_load_group_signature(base.load_progressions) == self._accumulator_load_group_signature(
        sibling.load_progressions
    )
