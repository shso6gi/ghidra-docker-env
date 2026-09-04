"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.recurrence.summarizer``."""

from __future__ import annotations

from typing import Any, List, Optional, Sequence, Tuple
from dataclasses import replace
from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
    LoopSideEffectProfileRef,
    ReturnInfo,
)
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    ConditionSMTOracle,
    ResidueLoopCase,
    _runtime_conditions_signature,
    _runtime_expression_signature,
)

def _impl__try_summarize_multiplicative_phi_return_region(
    self,
    function,
    high_function,
    analysis,
) -> Optional[Tuple[List[ReturnInfo], str]]:
    parameters = list(getattr(analysis, "parameters", []) or [])
    returns = tuple(getattr(analysis, "returns", ()) or ())
    if len(parameters) != 1 or len(returns) < 2:
        self._debug(
            "Declined multiplicative PHI return summary: parameter/return shape unsupported "
            f"(params={len(parameters)}, returns={len(returns)})"
        )
        return None
    count_expr = self._parameter_expression(parameters[0])
    positive_conditions = self._build_recursive_conditions(count_expr, 0)
    if not positive_conditions:
        return None
    if any(
        self._expression_is_unresolved(getattr(condition, "expression", None))
        for condition in positive_conditions
    ):
        return None

    seed_returns = tuple(
        ret
        for ret in returns
        if self._raw_constant_value(getattr(ret, "value", None)) == 1
        and self._return_overlaps_conditions(ret, positive_conditions)
    )
    if not seed_returns:
        self._debug("Declined multiplicative PHI return summary: seed return missing")
        return None
    recursive_returns = tuple(
        ret
        for ret in returns
        if self._return_overlaps_conditions(ret, positive_conditions)
        and self._return_value_contains_phi_circular(getattr(ret, "value", None))
    )
    if not recursive_returns:
        self._debug("Declined multiplicative PHI return summary: recursive return missing")
        return None
    summary_conditions = self._multiplicative_phi_return_summary_conditions(
        positive_conditions=positive_conditions,
        seed_returns=seed_returns,
        recursive_returns=recursive_returns,
    )
    if not summary_conditions:
        self._debug("Declined multiplicative PHI return summary: summary guard proof unavailable")
        return None
    model = self._find_state_transition_loop_model(high_function, analysis=analysis)
    if model is None:
        self._debug("Declined multiplicative PHI return summary: loop counter model missing")
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
        self._debug("Declined multiplicative PHI return summary: loop has side effects")
        return None

    result_size = max(
        1,
        int(getattr(count_expr, "size", 0) or 4),
        max(int(getattr(getattr(ret, "value", None), "size", 0) or 0) for ret in returns),
    )
    count_expr = self._coerce_summary_expression_to_size(
        count_expr,
        max(1, int(getattr(count_expr, "size", 0) or result_size or 4)),
        signed=True,
    )
    base_conditions = self._build_base_conditions(count_expr, 0)
    if base_conditions is None:
        return None
    base_witness_returns = self._zero_base_return_witnesses_for_region(
        returns=returns,
        base_conditions=base_conditions,
        result_size=result_size,
    )
    coverage_key = self._prove_summary_conditions_plus_exact_returns_cover_active_precondition(
        active_preconditions=self._analysis_active_preconditions(analysis),
        summary_conditions=summary_conditions,
        exact_returns=returns,
        parameters=parameters,
    )
    if coverage_key is None:
        self._debug("Declined multiplicative PHI return summary: coverage proof unavailable")
        return None
    multiplier = self._single_multiplicative_phi_transition_multiplier(recursive_returns)
    if multiplier is None:
        self._debug("Declined multiplicative PHI return summary: recursive multipliers are not uniform")
        return None

    base_anchor: Optional[ReturnInfo] = None
    if base_witness_returns and self._base_witnesses_exactly_cover_region(
        base_witness_returns,
        base_conditions,
    ):
        base_anchor_source = base_witness_returns[0]
        base_anchor = ReturnInfo(
            address=str(
                getattr(base_anchor_source, "address", None)
                or getattr(function, "getEntryPoint", lambda: "0x0")()
            ),
            value=Expression.constant(0, size=result_size),
            conditions=list(base_conditions),
            branch_index=30_199,
            pcode_identity=getattr(base_anchor_source, "pcode_identity", None),
            pcode_order=getattr(base_anchor_source, "pcode_order", None),
            pcode_time=getattr(base_anchor_source, "pcode_time", None),
            pcode_op_ref=getattr(base_anchor_source, "pcode_op_ref", None),
            return_value_pcode_op_refs=tuple(
                getattr(base_anchor_source, "return_value_pcode_op_refs", ()) or ()
            ),
        )

    summary_value = self._build_direct_multiplicative_state_value(
        count_expr=count_expr,
        multiplier=int(multiplier),
        result_size=result_size,
        guard_constraints=summary_conditions,
    )
    if summary_value is None:
        return None
    proof_ref = self._record_structural_multiplicative_return_region_proof(
        analysis=analysis,
        summary_value=summary_value,
        summary_conditions=summary_conditions,
        seed_returns=seed_returns,
        recursive_returns=recursive_returns,
        base_witness_returns=base_witness_returns,
        superseded_returns=tuple(seed_returns)
        + tuple(recursive_returns)
        + (tuple(base_witness_returns) if base_anchor is not None else ()),
        coverage_key=coverage_key,
        multiplier=int(multiplier),
    )
    if proof_ref is None:
        return None
    anchor = (recursive_returns or seed_returns)[0]
    source_key = self._summary_value_source_key(summary_value)
    if source_key is None:
        source_key = (
            "multiplicative_phi_return_region",
            _runtime_expression_signature(summary_value),
            int(multiplier),
        )
    summary_return = ReturnInfo(
        address=str(getattr(anchor, "address", None) or getattr(function, "getEntryPoint", lambda: "0x0")()),
        value=summary_value,
        conditions=list(summary_conditions),
        branch_index=30_200,
        pcode_identity=getattr(anchor, "pcode_identity", None),
        pcode_order=getattr(anchor, "pcode_order", None),
        pcode_time=getattr(anchor, "pcode_time", None),
        pcode_op_ref=getattr(anchor, "pcode_op_ref", None),
        return_value_pcode_op_refs=tuple(getattr(anchor, "return_value_pcode_op_refs", ()) or ()),
        return_kind="summary_derived",
        summary_candidate_source_key=source_key,
        summary_transition_evidence_key=proof_ref,
    )
    proposed_returns = [summary_return]
    if base_anchor is not None:
        proposed_returns.insert(
            0,
            replace(
                base_anchor,
                return_kind="summary_derived",
                summary_candidate_source_key=source_key,
                summary_transition_evidence_key=proof_ref,
            ),
        )
    self._debug(
        "Recovered multiplicative PHI return-region summary "
        f"(multiplier={int(multiplier)})"
    )
    return proposed_returns, "multiplicative_phi_return_region_summary"

def _impl__multiplicative_phi_return_summary_conditions(
    self,
    *,
    positive_conditions: Sequence[Condition],
    seed_returns: Sequence[ReturnInfo],
    recursive_returns: Sequence[ReturnInfo],
) -> Tuple[Condition, ...]:
    """Build a narrow guard for multiplicative PHI summaries.

    The old fallback used only ``n > 0``.  That is too broad for bounded
    callers such as ``if (x < 5) return lib(x); else return 0`` because it
    would overlap the outer zero-return region.  Keep only resolved guard
    conditions that are common to the seed and recursive return witnesses,
    then add the positive induction guard.
    """

    witness_returns = tuple(seed_returns or ()) + tuple(recursive_returns or ())
    if not witness_returns:
        return ()
    common: List[Condition] = []
    first_conditions = tuple(getattr(witness_returns[0], "conditions", None) or ())
    remaining = [
        tuple(getattr(ret, "conditions", None) or ())
        for ret in witness_returns[1:]
    ]
    for condition in first_conditions:
        if condition is None:
            continue
        if self._expression_is_unresolved(getattr(condition, "expression", None)):
            continue
        condition_key = _runtime_conditions_signature((condition,))
        if all(
            any(
                condition.equals(other)
                or _runtime_conditions_signature((other,)) == condition_key
                for other in conditions
                if other is not None
            )
            for conditions in remaining
        ):
            common.append(condition)

    result: List[Condition] = []
    for condition in list(common) + list(positive_conditions or ()):
        if condition is None:
            continue
        if self._expression_is_unresolved(getattr(condition, "expression", None)):
            return ()
        if not any(condition.equals(existing) for existing in result):
            result.append(condition)
    if not result:
        return ()
    try:
        if ConditionSMTOracle.conjunction_is_unsat(result) is not False:
            return ()
    except Exception:
        return ()
    return tuple(result)

def _impl__build_direct_multiplicative_state_value(
    self,
    *,
    count_expr: Expression,
    multiplier: int,
    result_size: int,
    guard_constraints: Sequence[Condition],
) -> Optional[Expression]:
    result_size = max(1, int(result_size or getattr(count_expr, "size", 0) or 4))
    count_size = max(1, int(getattr(count_expr, "size", 0) or result_size or 4))
    one = Expression.constant(1, size=count_size)
    state_placeholder = Expression.variable("__loop_state", size=result_size)
    transition = Expression.binary_op(
        "INT_MULT",
        state_placeholder,
        Expression.constant(int(multiplier), size=result_size),
    )
    transition.size = result_size
    return self._build_counted_state_transition_value(
        initial_state=Expression.constant(1, size=result_size),
        start_expr=one,
        limit_expr=count_expr,
        induction_step=1,
        transition_cases=(((), transition),),
        state_placeholder=state_placeholder,
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=tuple(guard_constraints or ()),
        result_size=result_size,
        signed_loop=True,
    )

def _impl__record_structural_multiplicative_return_region_proof(
    self,
    *,
    analysis,
    summary_value: Expression,
    summary_conditions: Sequence[Condition],
    seed_returns: Sequence[ReturnInfo],
    recursive_returns: Sequence[ReturnInfo],
    base_witness_returns: Sequence[ReturnInfo],
    superseded_returns: Sequence[ReturnInfo],
    coverage_key: Tuple[Any, ...],
    multiplier: int,
) -> Optional[Tuple[Any, ...]]:
    if not self.enable_completed_recovery_proofs:
        return None
    source_key = self._summary_value_source_key(summary_value)
    if source_key is None:
        source_key = ("summary_value", _runtime_expression_signature(summary_value))
    seed_key = tuple(
        (
            "seed_return",
            _runtime_conditions_signature(tuple(getattr(ret, "conditions", None) or ())),
            _runtime_expression_signature(getattr(ret, "value", None)),
            getattr(ret, "pcode_identity", None),
            getattr(ret, "branch_index", None),
        )
        for ret in seed_returns or ()
    )
    recursive_key = tuple(
        (
            "recursive_return",
            _runtime_conditions_signature(tuple(getattr(ret, "conditions", None) or ())),
            _runtime_expression_signature(getattr(ret, "value", None)),
            getattr(ret, "pcode_identity", None),
            getattr(ret, "branch_index", None),
        )
        for ret in recursive_returns or ()
    )
    base_witness_key = tuple(
        (
            "base_return",
            _runtime_conditions_signature(tuple(getattr(ret, "conditions", None) or ())),
            _runtime_expression_signature(getattr(ret, "value", None)),
            getattr(ret, "pcode_identity", None),
            getattr(ret, "branch_index", None),
        )
        for ret in base_witness_returns or ()
    )
    witness_key = (
        "structural_multiplicative_phi_witness",
        int(multiplier),
        seed_key,
        recursive_key,
        base_witness_key,
    )
    superseded_key = tuple(
        self._return_info_summary_identity_key(ret)
        for ret in superseded_returns or ()
    )
    object_target_key = (
        "return_region_summary_target",
        _runtime_expression_signature(summary_value),
        _runtime_conditions_signature(tuple(summary_conditions or ())),
        witness_key,
        coverage_key,
        source_key,
        ("superseded_return_keys", superseded_key),
    )
    proof_id = ("proof_obligation_id", "return_region_summary", object_target_key)
    proof_ref = ("return_region_summary_proof_ref", proof_id, object_target_key)
    existing = tuple(getattr(analysis, "completed_recovery_proof_evidence", ()) or ())
    if any(item.get("proof_obligation_id") == proof_id for item in existing if isinstance(item, dict)):
        return proof_ref
    evidence = {
        "proof_obligation_id": proof_id,
        "reason_id": "return_region_summary",
        "status": "complete",
        "proof_stage": "return_region_summary",
        "evidence_kind": "smt_value_equivalence",
        "object_target_key": object_target_key,
        "proof_source": "multiplicative_phi_return_region_summary",
        "proof_content": {
            "proof_status": "proved",
            "object_target_key": object_target_key,
            "summary_value_key": object_target_key[1],
            "summary_conditions_key": object_target_key[2],
            "exact_witnesses_key": witness_key,
            "coverage_key": coverage_key,
            "source_key": source_key,
            "superseded_return_keys": superseded_key,
            "checks": (
                ("summary_value_equivalence", "proved"),
                ("summary_region_coverage", "proved"),
                ("summary_side_effects", "pure"),
                ("base_return_value", "proved"),
                ("phi_seed", "proved"),
                ("phi_transition", "proved"),
            ),
        },
    }
    analysis.completed_recovery_proof_evidence = existing + (evidence,)
    return proof_ref

def _impl__build_multiplicative_state_then_triangular_sum_value(
    self,
    *,
    count_expr: Expression,
    multiplier: int,
    result_size: int,
    guard_constraints: Sequence[Condition],
) -> Optional[Expression]:
    result_size = max(1, int(result_size or getattr(count_expr, "size", 0) or 4))
    count_size = max(1, int(getattr(count_expr, "size", 0) or result_size or 4))
    one = Expression.constant(1, size=count_size)
    limit = Expression.binary_op("INT_ADD", count_expr, one)
    limit.size = count_size
    state_placeholder = Expression.variable("__loop_state", size=result_size)
    transition = Expression.binary_op(
        "INT_MULT",
        state_placeholder,
        Expression.constant(int(multiplier), size=result_size),
    )
    transition.size = result_size
    state_value = self._build_counted_state_transition_value(
        initial_state=Expression.constant(1, size=result_size),
        start_expr=one,
        limit_expr=limit,
        induction_step=1,
        transition_cases=(((), transition),),
        state_placeholder=state_placeholder,
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=tuple(guard_constraints or ()),
        result_size=result_size,
        signed_loop=True,
    )
    if state_value is None:
        return None
    return self._build_counted_loop_summary_value(
        base_expr=state_value,
        start_expr=one,
        limit_expr=limit,
        induction_step=1,
        residue_cases=(ResidueLoopCase(modulus=1, residue=0, affine=(1, 0)),),
        result_size=result_size,
        signed_loop=True,
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=tuple(guard_constraints or ()),
        cases=(),
    )

def _impl__multiplicative_accumulator_delta_multiplier(
    self,
    delta_expr: Optional[Expression],
    accumulator_placeholder: Optional[Expression],
) -> Optional[int]:
    if delta_expr is None or accumulator_placeholder is None:
        return None
    if getattr(delta_expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    operator = getattr(delta_expr, "operator", None)
    if operator not in {"INT_MULT", "INT_LEFT"}:
        return None
    operands = list(getattr(delta_expr, "operands", ()) or ())
    if len(operands) != 2:
        return None
    if operator == "INT_LEFT":
        maybe_acc, maybe_shift = operands
        try:
            accumulator_matches = maybe_acc.equals(accumulator_placeholder)
        except Exception:
            accumulator_matches = False
        if not accumulator_matches:
            return None
        shift = self._raw_constant_value(maybe_shift)
        if shift is None:
            return None
        try:
            shift_int = int(shift)
        except (TypeError, ValueError):
            return None
        if shift_int < 0 or shift_int > 30:
            return None
        return 1 << shift_int
    for maybe_acc, maybe_const in ((operands[0], operands[1]), (operands[1], operands[0])):
        try:
            accumulator_matches = maybe_acc.equals(accumulator_placeholder)
        except Exception:
            accumulator_matches = False
        if not accumulator_matches:
            continue
        multiplier = self._raw_constant_value(maybe_const)
        if multiplier is None:
            return None
        return int(multiplier)
    return None
