"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.recurrence_summary``."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Sequence, Tuple
from ._shared import (
    Condition,
    ConditionSimplifier,
    CountedLoopAccumulator,
    Expression,
    PcodeOpRef,
    ReturnInfo,
)

def _impl__accumulator_load_group_signature(
    self,
    load_progressions: Sequence[Dict[str, object]],
) -> Optional[Tuple[object, ...]]:
    if not load_progressions:
        return None
    first = load_progressions[0]
    induction_ref = first.get("induction_phi_ref")
    return (
        induction_ref.stable_key() if isinstance(induction_ref, PcodeOpRef) else None,
        int(first.get("stride", 0) or 0),
        int(first.get("start_index", 0) or 0),
        int(first.get("index_step", 1) or 1),
        int(first.get("index_scale", first.get("stride", 0)) or first.get("stride", 0) or 0),
    )

def _impl__choose_return_reaching_accumulator(
    self,
    candidates: Sequence[CountedLoopAccumulator],
) -> CountedLoopAccumulator:
    reaching = [
        candidate for candidate in candidates
        if self._varnode_reaches_return(candidate.phi_output)
    ]
    if reaching:
        return reaching[0]
    return candidates[0]

def _impl__try_summarize_branch_accumulator_loop(
    self,
    analysis,
) -> Optional[Tuple[List[ReturnInfo], str]]:
    if analysis is None or not analysis.returns or len(analysis.parameters or []) < 3:
        self._debug("Declined branch-accumulator summary: insufficient returns/parameters")
        return None
    effect_summary = getattr(analysis, "effect_summary", None)
    if effect_summary is None:
        self._debug("Declined branch-accumulator summary: no effect summary")
        return None

    loop_params = self._infer_loop_parameter_pair(analysis)
    if loop_params is None:
        self._debug("Declined branch-accumulator summary: could not infer loop parameter pair")
        return None
    start_name, limit_name = loop_params

    pointer_param = self._infer_pointer_parameter_name(analysis)
    if not pointer_param:
        self._debug("Declined branch-accumulator summary: could not infer pointer parameter")
        return None

    working_returns = list(analysis.returns)
    null_case = self._find_pointer_null_case(working_returns, pointer_param)
    require_pointer_nonnull = null_case is not None
    base_case = self._find_no_loop_base_case(
        working_returns,
        pointer_param,
        start_name,
        limit_name,
        require_pointer_nonnull=require_pointer_nonnull,
    )
    if base_case is None:
        self._debug(
            "Declined branch-accumulator summary: could not identify no-loop base case "
            f"(pointer={pointer_param}, start={start_name}, limit={limit_name})"
        )
        return None

    step_cases = self._find_one_step_cases(
        working_returns,
        pointer_param,
        start_name,
        limit_name,
        require_pointer_nonnull=require_pointer_nonnull,
    )
    if step_cases is None:
        synthesized = self._synthesize_one_step_cases_from_effects(
            analysis,
            base_case,
            pointer_param,
            start_name,
            limit_name,
            require_pointer_nonnull=require_pointer_nonnull,
        )
        if not synthesized:
            self._debug("Declined branch-accumulator summary: could not synthesize one-step cases from effects")
            return None
        working_returns.extend(synthesized)
        step_cases = self._find_one_step_cases(
            working_returns,
            pointer_param,
            start_name,
            limit_name,
            require_pointer_nonnull=require_pointer_nonnull,
        )
        if step_cases is None:
            self._debug("Declined branch-accumulator summary: synthesized one-step cases still did not match")
            return None

    even_case, odd_case = step_cases
    base_expr = base_case.value
    even_delta = self._extract_additive_delta(even_case.value, base_expr, analysis.parameters or [])
    odd_delta = self._extract_additive_delta(odd_case.value, base_expr, analysis.parameters or [])
    if even_delta is None or odd_delta is None:
        self._debug("Declined branch-accumulator summary: could not isolate additive deltas")
        return None

    even_affine = self._extract_affine_term(even_delta, start_name)
    odd_affine = self._extract_affine_term(odd_delta, start_name)
    if even_affine is None or odd_affine is None:
        self._debug("Declined branch-accumulator summary: one-step deltas are not affine in the loop counter")
        return None

    loop_even_value = self._build_parity_split_loop_value(
        base_expr,
        start_name,
        limit_name,
        even_affine,
        odd_affine,
        start_is_even=True,
    )
    loop_odd_value = self._build_parity_split_loop_value(
        base_expr,
        start_name,
        limit_name,
        even_affine,
        odd_affine,
        start_is_even=False,
    )
    if loop_even_value is None or loop_odd_value is None:
        self._debug("Declined branch-accumulator summary: failed to build closed-form loop values")
        return None

    loop_conditions_common = [
        self._pointer_nonnull_condition(pointer_param, analysis),
        Condition(
            Expression.binary_op(
                "INT_SLESS",
                self._param_expr(analysis, start_name),
                self._param_expr(analysis, limit_name),
            ),
            False,
        ),
    ]
    even_start_cond = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.binary_op(
                "INT_AND",
                self._param_expr(analysis, start_name),
                Expression.constant(1, self._param_expr(analysis, start_name).size or 4),
            ),
            Expression.constant(0, self._param_expr(analysis, start_name).size or 4),
        ),
        False,
    )
    odd_start_cond = even_start_cond.negate()

    summarized: List[ReturnInfo] = []
    if null_case is not None:
        summarized.append(null_case)
    summarized.append(base_case)
    summarized.append(
        ReturnInfo(
            address=base_case.address,
            value=loop_even_value,
            conditions=ConditionSimplifier.simplify_conditions_object_centric(loop_conditions_common + [even_start_cond]),
            branch_index=10_100,
            pcode_identity=base_case.pcode_identity,
            pcode_order=base_case.pcode_order,
            pcode_time=base_case.pcode_time,
            pcode_op_ref=getattr(base_case, "pcode_op_ref", None),
            return_value_pcode_op_refs=tuple(
                getattr(base_case, "return_value_pcode_op_refs", ()) or ()
            ),
        )
    )
    summarized.append(
        ReturnInfo(
            address=base_case.address,
            value=loop_odd_value,
            conditions=ConditionSimplifier.simplify_conditions_object_centric(loop_conditions_common + [odd_start_cond]),
            branch_index=10_101,
            pcode_identity=base_case.pcode_identity,
            pcode_order=base_case.pcode_order,
            pcode_time=base_case.pcode_time,
            pcode_op_ref=getattr(base_case, "pcode_op_ref", None),
            return_value_pcode_op_refs=tuple(
                getattr(base_case, "return_value_pcode_op_refs", ()) or ()
            ),
        )
    )
    self._debug(
        "Recovered counted loop branch-accumulator summary "
        f"(start={start_name}, limit={limit_name}, even={even_affine}, odd={odd_affine})"
    )
    return summarized, "counted_loop_branch_accumulator_summary"
