# -*- coding: utf-8 -*-
"""Structural recurrence summaries for simple recursion/loop patterns."""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, replace
import re
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

from ..model import (
    COUNTED_LOOP_SUM_OPCODE,
    READONLY_SUM_OPCODE,
    STATE_TRANSITION_LOOP_COUNT_OPCODE,
    Condition,
    CountedLoopSummaryRef,
    Expression,
    ExpressionType,
    LoopBodyEffectRef,
    LoopCaseRef,
    LoopSideEffectProfileRef,
    LoopSummaryRef,
    LoopTermDescriptorRef,
    LoopVariableIdentityRef,
    LocationBaseRef,
    PcodeBlockRef,
    PcodeOpRef,
    ReductionAccumulatorProof,
    ReadonlyReductionRef,
    ReadonlyReductionTermRef,
    ReadonlyReductionWitness,
    ReturnInfo,
    StorageInfo,
    StateTransitionLoopSummaryRef,
)
from ..model.render_smt import (
    collect_intrinsic_smt_declarations,
    collect_unknown_smt_declarations,
    expression_smt_bit_width,
)
from ..model.signature import (
    get_declared_type_signedness,
    is_integral_data_type,
    is_pointer_data_type,
)
from ..model.runtime_refs import UnknownValueRef
from ..smt.interface import SolverStatus
from ..smt.solvers.z3 import Z3Solver
from ..equivalence.formula.returns import coerce_value_to_bitvec_width
from ..equivalence.formula.types import ParameterInfo
from ..equivalence.param_semantics import (
    parameter_identity_key_from_descriptor,
    parameter_identity_key_from_expression,
)
from .condition import ConditionConstraintSet, ConditionSimplifier, ConditionNormalizer
from .condition.bitvector import eval_constant_raw
from .condition.smt_oracle import ConditionSMTOracle
from .effect_summary import (
    CanonicalLocation,
    _expressions_equivalent_under_conditions,
    _reduce_expression_under_conditions,
    canonicalize_location,
)


def _runtime_expression_signature(expr: Optional[Expression]):
    if expr is None:
        return ("none",)
    return ConditionNormalizer.expression_signature(expr)


def _runtime_conditions_signature(conditions: Sequence[Condition]):
    return ConditionNormalizer.conditions_signature(conditions)


_UNSUPPORTED_STATE_TRANSITION_CONDITION = object()


@dataclass(frozen=True)
class CountedLoopInduction:
    phi_op: object
    phi_output: object
    init_expr: Expression
    backedge_index: int
    step: int
    placeholder: Expression
    signed_guard: bool
    init_index: Optional[int] = None
    backedge_indices: Tuple[int, ...] = ()


@dataclass(frozen=True)
class CountedLoopAccumulator:
    phi_op: Optional[object]
    phi_output: Optional[object]
    init_expr: Expression
    backedge_index: int
    placeholder: Expression
    member_outputs: Tuple[object, ...] = ()
    member_placeholders: Tuple[Expression, ...] = ()
    update_varnode: Optional[object] = None
    update_block: Optional[object] = None
    init_index: Optional[int] = None
    backedge_indices: Tuple[int, ...] = ()


@dataclass(frozen=True)
class CountedLoopGuard:
    condition_expr: Expression
    bound_expr: Expression
    continue_on_true: bool
    body_block: object
    exit_block: object
    signed_comparison: bool
    entry_condition_expr: Optional[Expression] = None
    latch_block: Optional[object] = None


@dataclass(frozen=True)
class CountedLoopUpdateCase:
    conditions: Tuple[Condition, ...]
    update_expr: Expression
    delta_expr: Expression


@dataclass(frozen=True)
class StateTransitionLoopModel:
    header_block: object
    body_block: object
    exit_block: object
    state_phi_op: object
    state_phi_output: object
    state_init_expr: Expression
    state_placeholder: Expression
    state_guard_expr: Expression
    state_transition_expr: Expression
    accumulator_phi_op: object
    accumulator_phi_output: object
    accumulator_init_expr: Expression
    accumulator_delta_expr: Expression
    accumulator_placeholder: Expression
    continue_on_true: bool
    loop_blocks: Tuple[object, ...]


@dataclass(frozen=True)
class ResidueLoopCase:
    modulus: int
    residue: int
    affine: Tuple[int, int]
    bias_expr: Optional[Expression] = None


@dataclass(frozen=True)
class ReadonlyRoundedCountCandidate:
    rounded_varnode: object
    lane_count: int
    start_index: int = 0
    tail_start_index_delta: int = 0
    tail_index_source_varnode: Optional[object] = None


@dataclass(frozen=True)
class ReadonlyAccumulatorPhiCandidate:
    phi_op: object
    init_varnode: object
    back_varnode: object
    back_def: object
    load_progressions: Tuple[Dict[str, object], ...]


class StructuralRecurrenceSummarizer:
    """
    Recover conservative closed-form summaries for simple scalar recurrences.

    The current implementation intentionally focuses on a sound, reusable subset:
    single-parameter, unit-step, additive self-recursive functions of the form

      f(n) = base                  when n <= L
      f(n) = f(n - 1) + (a*n + b)  when n > L

    If the pattern cannot be proved from the already recovered return cases and the
    function's direct self-call site, the summarizer declines and the caller falls
    back to the existing path-sensitive analysis.
    """

    _SIGNED_GT_OPS = {"INT_SLESS", "INT_SLESSEQUAL"}

    def __init__(self, tracer, debug: bool = False):
        self.tracer = tracer
        self.debug = debug

    def has_summary_candidate(self, function, high_function, analysis) -> bool:
        if function is None or high_function is None or analysis is None:
            return False
        if not getattr(analysis, "returns", None):
            return False

        function_name = getattr(function, "getName", lambda: "")()
        if len(getattr(analysis, "parameters", []) or []) == 1 and any(
            self._expression_contains_recursive_unknown(ret.value, function_name)
            for ret in (analysis.returns or [])
        ):
            return True

        if self._has_readonly_pointer_reduction_candidate(high_function, analysis):
            return True

        if self._has_counted_scalar_loop_candidate(high_function):
            return True

        if self._has_state_transition_loop_candidate(high_function):
            return True

        if self._has_branch_accumulator_candidate(analysis):
            return True

        return False

    def try_summarize_function(self, function, high_function, analysis) -> Optional[Tuple[List[ReturnInfo], str]]:
        if function is None or high_function is None or analysis is None:
            return None

        if len(getattr(analysis, "parameters", []) or []) == 1:
            summary = self._try_summarize_linear_self_recursion(function, high_function, analysis)
            if summary is not None:
                return summary

        summary = self._try_summarize_readonly_pointer_reduction(function, high_function, analysis)
        if summary is not None:
            return summary

        summary = self._try_summarize_counted_scalar_loop(function, high_function, analysis)
        if summary is not None:
            return summary

        summary = self._try_summarize_vectorized_affine_progression_sum(function, high_function, analysis)
        if summary is not None:
            return summary

        summary = self._try_summarize_state_transition_loop(function, high_function, analysis)
        if summary is not None:
            return summary

        summary = self._try_summarize_branch_accumulator_loop(analysis)
        if summary is not None:
            return summary
        return None

    def try_summarize_pre_return_counted_scalar_loop(
        self,
        function,
        high_function,
        analysis,
        return_ops: Sequence,
    ) -> Optional[Tuple[List[ReturnInfo], str]]:
        if function is None or high_function is None or analysis is None:
            return None
        return_ops = list(return_ops or [])
        if not self._pre_return_counted_scalar_summary_is_cfg_safe(high_function, return_ops):
            return None
        if not self._analysis_is_safe_for_counted_scalar_summary(analysis):
            return None
        return self._build_counted_scalar_loop_summary(
            function,
            high_function,
            analysis,
            pre_return_ops=return_ops,
        )

    def _pre_return_counted_scalar_summary_is_cfg_safe(
        self,
        high_function,
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

    def _has_readonly_pointer_reduction_candidate(
        self,
        high_function,
        analysis,
    ) -> bool:
        if analysis is None or not analysis.returns:
            return False
        if getattr(getattr(analysis, "effect_summary", None), "effects", None):
            return False
        if len(getattr(analysis, "parameters", []) or []) < 2:
            return False

        pointer_param, count_param = self._infer_readonly_pointer_reduction_parameters(
            analysis,
            high_function,
        )
        if pointer_param is None or count_param is None:
            return False

        for counter_signed in (True, False):
            positive_conditions = self._readonly_reduction_positive_conditions(
                analysis,
                pointer_param,
                count_param,
                signed_counter=counter_signed,
            )
            if ConditionSimplifier.object_centric_is_contradiction(positive_conditions):
                continue
            overlapping_positive_returns = self._readonly_reduction_region_returns(
                analysis,
                positive_conditions,
            )
            if not overlapping_positive_returns:
                continue

            accumulator_proof = self._detect_readonly_sum_accumulator_proof(
                high_function,
                analysis,
                pointer_param,
                count_param,
                counter_signed=counter_signed,
                positive_conditions=positive_conditions,
            )
            if accumulator_proof is not None:
                return True
        return False

    def _has_counted_scalar_loop_candidate(self, high_function) -> bool:
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

    def _try_summarize_counted_scalar_loop(
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

    def _analysis_is_safe_for_counted_scalar_summary(self, analysis) -> bool:
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

    def _try_summarize_vectorized_affine_progression_sum(
        self,
        function,
        high_function,
        analysis,
    ) -> Optional[Tuple[List[ReturnInfo], str]]:
        if function is None or high_function is None or analysis is None:
            return None
        if not self._analysis_is_safe_for_counted_scalar_summary(analysis):
            self._debug("Declined vectorized affine progression summary: unsafe counted scalar profile")
            return None
        if getattr(getattr(analysis, "effect_summary", None), "effects", None):
            self._debug("Declined vectorized affine progression summary: function has memory side effects")
            return None
        side_effect_profile = self._build_loop_side_effect_profile(
            analysis=analysis,
            high_function=high_function,
        )
        requires_effect_proof = getattr(side_effect_profile, "requires_effect_proof", None)
        if callable(requires_effect_proof) and requires_effect_proof():
            self._debug("Declined vectorized affine progression summary: high-function effects require proof")
            return None
        parameters = list(getattr(analysis, "parameters", None) or [])
        if len(parameters) != 2:
            self._debug(
                "Declined vectorized affine progression summary: expected two parameters "
                f"(found {len(parameters)})"
            )
            return None
        if not all(is_integral_data_type(param.get("data_type_obj"), param.get("data_type")) for param in parameters):
            self._debug("Declined vectorized affine progression summary: non-integral parameter")
            return None
        if any(int(param.get("size", 0) or 0) > 4 for param in parameters):
            self._debug("Declined vectorized affine progression summary: parameter wider than 32 bits")
            return None

        step = self._readonly_affine_progression_literal_step(analysis)
        if step is None or step <= 0:
            self._debug("Declined vectorized affine progression summary: no readonly affine literal")
            return None

        count_expr = self._parameter_expression(parameters[0])
        bias_expr = self._parameter_expression(parameters[1])
        signed_counter_guard = self._vectorized_affine_counter_guard_signedness(analysis, parameters[0])
        if signed_counter_guard is None:
            self._debug("Declined vectorized affine progression summary: counter guard signedness is ambiguous")
            return None
        result_size = max(
            1,
            int(getattr(count_expr, "size", 0) or 0),
            int(getattr(bias_expr, "size", 0) or 0),
            4,
        )
        zero = Expression.constant(0, size=result_size)
        positive_operator = "INT_SLESS" if signed_counter_guard else "INT_LESS"
        positive_guard = Condition(
            Expression.binary_op(
                positive_operator,
                zero,
                self._coerce_summary_expression_to_size(count_expr, result_size, signed=signed_counter_guard),
            ),
            False,
        )
        base_guard = self._zero_base_guard_cover_for_positive_counter_guard(
            analysis,
            parameters[0],
            positive_guard,
        )
        if base_guard is None:
            self._debug("Declined vectorized affine progression summary: missing proven zero base coverage")
            return None
        if not self._nonzero_returns_are_disjoint_from_base_guard(analysis, base_guard):
            self._debug("Declined vectorized affine progression summary: nonzero return overlaps zero base guard")
            return None
        summary_bias_expr = self._coerce_summary_expression_to_size(
            bias_expr,
            result_size,
            signed=self._expression_prefers_signed_extension(bias_expr),
        )
        loop_value = self._build_counted_loop_summary_value(
            base_expr=zero,
            start_expr=zero,
            limit_expr=self._coerce_summary_expression_to_size(count_expr, result_size, signed=signed_counter_guard),
            induction_step=1,
            residue_cases=(
                ResidueLoopCase(
                    modulus=1,
                    residue=0,
                    affine=(int(step), 0),
                    bias_expr=summary_bias_expr,
                ),
            ),
            result_size=result_size,
            signed_loop=signed_counter_guard,
            guard_constraints=(positive_guard,),
        )
        if loop_value is None:
            self._debug("Declined vectorized affine progression summary: failed to build counted-loop value")
            return None
        if not self._positive_returns_match_vectorized_affine_summary(
            analysis,
            parameters[0],
            step=int(step),
            bias_expr=summary_bias_expr,
            result_size=result_size,
            signed_counter_guard=signed_counter_guard,
        ):
            self._debug("Declined vectorized affine progression summary: positive return proof failed")
            return None

        anchor = next(iter((getattr(analysis, "returns", None) or [])), None)
        address = getattr(anchor, "address", getattr(function, "getEntryPoint", lambda: "0x0")())
        pcode_identity = getattr(anchor, "pcode_identity", None)
        pcode_order = getattr(anchor, "pcode_order", None)
        pcode_time = getattr(anchor, "pcode_time", None)
        pcode_op_ref = getattr(anchor, "pcode_op_ref", None)
        return [
            ReturnInfo(
                address=address,
                value=zero,
                conditions=[base_guard],
                branch_index=0,
                pcode_identity=pcode_identity,
                pcode_order=pcode_order,
                pcode_time=pcode_time,
                pcode_op_ref=pcode_op_ref,
            ),
            ReturnInfo(
                address=address,
                value=loop_value,
                conditions=[positive_guard],
                branch_index=1,
                pcode_identity=pcode_identity,
                pcode_order=pcode_order,
                pcode_time=pcode_time,
                pcode_op_ref=pcode_op_ref,
            ),
        ], "vectorized_affine_progression_sum_summary"

    def _positive_returns_match_vectorized_affine_summary(
        self,
        analysis,
        counter_param: dict,
        *,
        step: int,
        bias_expr: Expression,
        result_size: int,
        signed_counter_guard: bool,
    ) -> bool:
        count_expr = self._parameter_expression(counter_param)
        default_summary_closed = self._build_affine_progression_sum_closed_expression(
            count_expr=count_expr,
            step=int(step),
            bias_expr=bias_expr,
            result_size=result_size,
            signed_count=signed_counter_guard,
        )
        if default_summary_closed is None:
            return False
        positive_case_count = 0
        for ret in getattr(analysis, "returns", None) or ():
            value = getattr(ret, "value", None)
            if value is None:
                return False
            conditions = list(getattr(ret, "conditions", None) or [])
            positive_counter_cases = self._positive_counter_conditions_for_return(
                conditions,
                counter_param,
                signed_counter_guard=signed_counter_guard,
            )
            if positive_counter_cases is None:
                self._debug(
                    "Declined vectorized affine progression summary: positive return overlap proof unknown "
                    f"(branch_index={getattr(ret, 'branch_index', None)}, "
                    f"conditions={[condition.to_string() for condition in conditions]})"
                )
                return False
            if len(positive_counter_cases) == 0:
                continue
            positive_case_count += 1
            if not any(
                self._return_value_matches_affine_progression_summary(
                    value=value,
                    conditions=list(conditions),
                    positive_condition=positive_condition,
                    counter_expr=counter_expr,
                    bias_expr=bias_expr,
                    step=int(step),
                    result_size=result_size,
                    signed_counter_guard=signed_counter_guard,
                )
                for positive_condition, counter_expr in positive_counter_cases
            ):
                self._debug(
                    "Declined vectorized affine progression summary: positive return fragment mismatch "
                    f"(branch_index={getattr(ret, 'branch_index', None)}, "
                    f"conditions={[condition.to_string() for condition in conditions]}, "
                    f"value={value.to_string()[:240]})"
                )
                return False
        return positive_case_count > 0

    def _return_value_matches_affine_progression_summary(
        self,
        *,
        value: Expression,
        conditions: Sequence[Condition],
        positive_condition: Condition,
        counter_expr: Expression,
        bias_expr: Expression,
        step: int,
        result_size: int,
        signed_counter_guard: bool,
    ) -> bool:
        proof_conditions = list(conditions) + [positive_condition]
        direct_count = (
            self._implied_counter_constant_expression(conditions, counter_expr)
            or counter_expr
        )
        direct_summary = self._build_affine_progression_sum_closed_expression(
            count_expr=direct_count,
            step=int(step),
            bias_expr=bias_expr,
            result_size=result_size,
            signed_count=signed_counter_guard,
        )
        if direct_summary is not None and self._prove_return_value_equals_summary_closed_form(
            value,
            direct_summary,
            proof_conditions,
            result_size=result_size,
        ):
            return True

        finite_counts = self._complete_counter_constant_cover(
            proof_conditions,
            counter_expr,
        )
        if finite_counts is None:
            return False
        for count_value in finite_counts:
            count_const = Expression.constant(count_value, size=max(1, int(getattr(counter_expr, "size", 0) or 4)))
            exact_count = Condition(
                Expression.binary_op("INT_EQUAL", counter_expr, count_const),
                False,
            )
            summary = self._build_affine_progression_sum_closed_expression(
                count_expr=count_const,
                step=int(step),
                bias_expr=bias_expr,
                result_size=result_size,
                signed_count=signed_counter_guard,
            )
            if summary is None:
                return False
            if not self._prove_return_value_equals_summary_closed_form(
                value,
                summary,
                proof_conditions + [exact_count],
                result_size=result_size,
            ):
                return False
        return True

    def _complete_counter_constant_cover(
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
            try:
                is_unsat = ConditionSMTOracle.conjunction_is_unsat(list(conditions) + [equality])
            except Exception:
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
        try:
            cover_complete = ConditionSMTOracle.conjunction_is_unsat(list(conditions) + [outside_cover])
        except Exception:
            return None
        if cover_complete is not True:
            return None
        return tuple(possible_values)

    def _implied_counter_constant_expression(
        self,
        conditions: Sequence[Condition],
        counter_expr: Expression,
        *,
        search_limit: int = 64,
    ) -> Optional[Expression]:
        if not conditions:
            return None
        size = max(1, int(getattr(counter_expr, "size", 0) or 4))
        for value in range(0, int(search_limit) + 1):
            diseq = Condition(
                Expression.binary_op(
                    "INT_NOTEQUAL",
                    counter_expr,
                    Expression.constant(value, size=size),
                ),
                False,
            )
            proof_conditions = list(conditions) + [diseq]
            try:
                if ConditionSMTOracle.conjunction_is_unsat(proof_conditions) is True:
                    return Expression.constant(value, size=size)
            except Exception:
                pass
            try:
                usable, script = ConditionSMTOracle._build_script(proof_conditions)
            except Exception:
                continue
            if not usable or not script:
                continue
            try:
                result = Z3Solver(timeout=2, debug=False).check_equivalence_direct(script)
            except Exception:
                continue
            if result.status == SolverStatus.UNSAT:
                return Expression.constant(value, size=size)
        return None

    def _build_affine_progression_sum_closed_expression(
        self,
        *,
        count_expr: Expression,
        step: int,
        bias_expr: Expression,
        result_size: int,
        signed_count: bool = True,
    ) -> Optional[Expression]:
        target_size = max(1, int(result_size or 0))
        count = self._coerce_summary_expression_to_size(count_expr, target_size, signed=bool(signed_count))
        bias = self._coerce_summary_expression_to_size(bias_expr, target_size, signed=True)
        wide_size = max(8, target_size * 2)
        wide_count = Expression.unary_op("INT_ZEXT", count)
        wide_count.size = wide_size
        count_minus_one = Expression.binary_op(
            "INT_SUB",
            count,
            Expression.constant(1, size=target_size),
        )
        count_minus_one.size = target_size
        wide_count_minus_one = Expression.unary_op("INT_ZEXT", count_minus_one)
        wide_count_minus_one.size = wide_size
        product = Expression.binary_op("INT_MULT", wide_count, wide_count_minus_one)
        product.size = wide_size
        half = Expression.binary_op("INT_RIGHT", product, Expression.constant(1, size=wide_size))
        half.size = wide_size
        triangular = Expression.binary_op("SUBPIECE", half, Expression.constant(0, size=4))
        triangular.size = target_size
        step_term = triangular
        if int(step) != 1:
            step_term = Expression.binary_op(
                "INT_MULT",
                triangular,
                Expression.constant(int(step), size=target_size),
            )
            step_term.size = target_size
        bias_term = Expression.binary_op("INT_MULT", count, bias)
        bias_term.size = target_size
        total = Expression.binary_op("INT_ADD", step_term, bias_term)
        total.size = target_size
        return total

    def _positive_counter_conditions_for_return(
        self,
        conditions: Sequence[Condition],
        counter_param: dict,
        *,
        signed_counter_guard: bool = True,
    ) -> Optional[Tuple[Tuple[Condition, Expression], ...]]:
        positives: List[Tuple[Condition, Expression]] = []
        candidates = self._counter_guard_parameter_candidates(counter_param, conditions)
        if not candidates:
            return None
        operator = "INT_SLESS" if bool(signed_counter_guard) else "INT_LESS"
        for counter_expr in candidates:
            positive = Condition(
                Expression.binary_op(
                    operator,
                    Expression.constant(0, size=counter_expr.size or 4),
                    counter_expr,
                ),
                False,
            )
            try:
                is_unsat = ConditionSMTOracle.conjunction_is_unsat(list(conditions) + [positive])
            except Exception:
                return None
            if is_unsat is False:
                positives.append((positive, counter_expr))
            elif is_unsat is not True:
                return None
        return tuple(positives)

    def _prove_return_value_equals_summary_closed_form(
        self,
        value: Expression,
        summary_closed: Expression,
        conditions: Sequence[Condition],
        *,
        result_size: int,
    ) -> bool:
        reduced_value = _reduce_expression_under_conditions(value, conditions)
        if reduced_value is not None:
            value = reduced_value
        reduced_summary = _reduce_expression_under_conditions(summary_closed, conditions)
        if reduced_summary is not None:
            summary_closed = reduced_summary
        actual = self._coerce_summary_expression_to_size(
            value,
            result_size,
            signed=self._expression_prefers_signed_extension(value),
        )
        expected = self._coerce_summary_expression_to_size(
            summary_closed,
            result_size,
            signed=False,
        )
        disequality = Condition(Expression.binary_op("INT_NOTEQUAL", actual, expected), False)
        proof_conditions = list(conditions or []) + [disequality]
        try:
            if ConditionSMTOracle.conjunction_is_unsat(proof_conditions) is True:
                return True
        except Exception:
            pass
        try:
            usable, script = ConditionSMTOracle._build_script(proof_conditions)
        except Exception:
            return False
        if not usable or not script:
            return False
        try:
            result = Z3Solver(timeout=2, debug=False).check_equivalence_direct(script)
        except Exception:
            return False
        return result.status == SolverStatus.UNSAT

    def _expression_prefers_signed_extension(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        data_type = str(getattr(expr, "data_type", "") or "").lower()
        if "unsigned" in data_type or data_type.startswith("u"):
            return False
        if any(token in data_type for token in ("signed", "int", "long", "short", "char")):
            return True
        return False

    def _coerce_summary_expression_to_size(
        self,
        expr: Expression,
        target_size: int,
        *,
        signed: bool = False,
    ) -> Expression:
        target_size = max(1, int(target_size or 0))
        expr_size = int(getattr(expr, "size", 0) or 0)
        if expr_size <= 0:
            expr_size = target_size
        if expr_size == target_size:
            return expr
        if expr_size > target_size:
            narrowed = Expression.binary_op("SUBPIECE", expr, Expression.constant(0, size=4))
            narrowed.size = target_size
            return narrowed
        widened = Expression.unary_op("INT_SEXT" if signed else "INT_ZEXT", expr)
        widened.size = target_size
        return widened

    def _readonly_affine_progression_literal_step(self, analysis) -> Optional[int]:
        program = getattr(self.tracer, "program", None)
        if program is None:
            return None
        constants: List[int] = []
        for ret in getattr(analysis, "returns", None) or ():
            constants.extend(self._expression_integer_constants(getattr(ret, "value", None)))
        for value in constants:
            for base in (int(value), int(value) & ~0xF):
                lanes = self._read_readonly_int32_lanes(base, 4)
                if lanes is None or len(lanes) < 4:
                    continue
                if lanes[0] != 0:
                    continue
                step = lanes[1] - lanes[0]
                if step <= 0:
                    continue
                if all((lanes[index] - lanes[index - 1]) == step for index in range(1, len(lanes))):
                    return int(step)
        return None

    def _expression_integer_constants(self, expr: Optional[Expression]) -> List[int]:
        values: List[int] = []
        for node in self._iter_expression_nodes(expr):
            if getattr(node, "expr_type", None) != ExpressionType.CONSTANT:
                continue
            value = self._raw_constant_value(node)
            if value is not None:
                values.append(int(value))
        return values

    def _read_readonly_int32_lanes(self, address_value: int, lane_count: int) -> Optional[Tuple[int, ...]]:
        if address_value < 0 or lane_count <= 0:
            return None
        program = getattr(self.tracer, "program", None)
        if program is None:
            return None
        try:
            memory = program.getMemory()
            address_factory = program.getAddressFactory()
            default_space = address_factory.getDefaultAddressSpace()
            address = default_space.getAddress(int(address_value))
        except Exception:
            return None
        if memory is None or address is None:
            return None
        try:
            block = memory.getBlock(address)
        except Exception:
            block = None
        if block is None:
            return None
        try:
            if block.isExecute() or block.isWrite() or not block.isRead():
                return None
        except Exception:
            return None
        lanes: List[int] = []
        try:
            is_big_endian = bool(program.getLanguage().isBigEndian())
        except Exception:
            is_big_endian = False
        try:
            for lane in range(int(lane_count)):
                raw_bytes = [
                    int(memory.getByte(address.add(lane * 4 + offset))) & 0xFF
                    for offset in range(4)
                ]
                ordered = raw_bytes if is_big_endian else list(reversed(raw_bytes))
                value = 0
                for byte_value in ordered:
                    value = (value << 8) | byte_value
                if value & 0x80000000:
                    value -= 0x100000000
                lanes.append(value)
        except Exception:
            return None
        return tuple(lanes)

    def _zero_base_guard_cover_for_positive_counter_guard(
        self,
        analysis,
        counter_param: dict,
        positive_guard: Condition,
    ) -> Optional[Condition]:
        zero_return_count = 0
        zero_guard_clauses: List[Expression] = []
        for ret in getattr(analysis, "returns", None) or ():
            if self._raw_constant_value(getattr(ret, "value", None)) != 0:
                continue
            zero_return_count += 1
            conditions = ConditionSimplifier.simplify_conditions_object_centric(
                list(getattr(ret, "conditions", None) or [])
            )
            if ConditionSimplifier.object_centric_is_contradiction(conditions):
                continue
            clause = self._condition_clause_expression(conditions)
            if clause is not None:
                zero_guard_clauses.append(clause)
        if not zero_guard_clauses:
            self._debug(
                "Declined vectorized affine progression summary: zero base guard check failed "
                f"(zero_returns={zero_return_count}, zero_guard_clauses=0)"
            )
            return None
        covered_expr = zero_guard_clauses[0]
        for clause in zero_guard_clauses[1:]:
            covered_expr = Expression.binary_op("BOOL_OR", covered_expr, clause)
            covered_expr.size = 1
        base_guard = Condition(covered_expr, False)
        try:
            uncovered_is_unsat = ConditionSMTOracle.conjunction_is_unsat(
                [positive_guard.negate(), base_guard.negate()]
            )
        except Exception:
            uncovered_is_unsat = None
        if uncovered_is_unsat is True:
            return base_guard
        self._debug(
            "Declined vectorized affine progression summary: zero base guard check failed "
            f"(zero_returns={zero_return_count}, zero_guard_clauses={len(zero_guard_clauses)})"
        )
        return None

    def _nonzero_returns_are_disjoint_from_base_guard(self, analysis, base_guard: Condition) -> bool:
        for ret in getattr(analysis, "returns", None) or ():
            if self._raw_constant_value(getattr(ret, "value", None)) == 0:
                continue
            conditions = ConditionSimplifier.simplify_conditions_object_centric(
                list(getattr(ret, "conditions", None) or [])
            )
            if ConditionSimplifier.object_centric_is_contradiction(conditions):
                continue
            try:
                is_unsat = ConditionSMTOracle.conjunction_is_unsat(list(conditions) + [base_guard])
            except Exception:
                is_unsat = None
            if is_unsat is not True:
                self._debug(
                    "Declined vectorized affine progression summary: nonzero return/base overlap proof failed "
                    f"(branch_index={getattr(ret, 'branch_index', None)}, "
                    f"conditions={[condition.to_string() for condition in conditions]})"
                )
                return False
        return True

    def _vectorized_affine_counter_guard_signedness(self, analysis, counter_param: dict) -> Optional[bool]:
        signedness_values: set[bool] = set()
        for ret in getattr(analysis, "returns", None) or ():
            conditions = list(getattr(ret, "conditions", None) or [])
            candidates = self._counter_guard_parameter_candidates(counter_param, conditions)
            for condition in conditions:
                value = self._counter_guard_signedness_from_condition(condition, candidates)
                if value is not None:
                    signedness_values.add(value)
        if len(signedness_values) == 1:
            return next(iter(signedness_values))
        return None

    def _counter_guard_signedness_from_condition(
        self,
        condition: Condition,
        counter_candidates: Sequence[Expression],
    ) -> Optional[bool]:
        expr = getattr(condition, "expression", None)
        if expr is None or getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
            return None
        operator = getattr(expr, "operator", None)
        if operator not in {"INT_LESS", "INT_SLESS"}:
            return None
        operands = list(getattr(expr, "operands", None) or [])
        if len(operands) != 2:
            return None
        left, right = operands
        mentions_counter = any(
            self._same_counter_expression(left, candidate)
            or self._same_counter_expression(right, candidate)
            for candidate in counter_candidates or ()
        )
        if not mentions_counter:
            return None
        left_const = self._raw_constant_value(left)
        right_const = self._raw_constant_value(right)
        if left_const not in {0, 1} and right_const not in {0, 1}:
            return None
        return operator == "INT_SLESS"

    def _same_counter_expression(self, expr: Optional[Expression], counter_expr: Optional[Expression]) -> bool:
        if expr is None or counter_expr is None:
            return False
        try:
            if expr.equals(counter_expr):
                return True
        except Exception:
            pass
        if getattr(expr, "expr_type", None) != ExpressionType.PARAMETER:
            return False
        if getattr(counter_expr, "expr_type", None) != ExpressionType.PARAMETER:
            return False
        try:
            expr_index = int(getattr(expr, "value", -1))
            counter_index = int(getattr(counter_expr, "value", -1))
        except (TypeError, ValueError):
            expr_index = counter_index = -1
        if expr_index >= 0 and counter_index >= 0 and expr_index == counter_index:
            return True
        expr_name = getattr(expr, "name", None)
        counter_name = getattr(counter_expr, "name", None)
        if expr_name is not None and counter_name is not None and expr_name == counter_name:
            return True
        expr_storage = getattr(expr, "storage_info", None)
        counter_storage = getattr(counter_expr, "storage_info", None)
        return expr_storage is not None and counter_storage is not None and expr_storage == counter_storage

    def _condition_clause_expression(self, conditions: Sequence[Condition]) -> Optional[Expression]:
        if not conditions:
            return Expression.constant(1, size=1)
        combined = Condition.combine_and(list(conditions))
        if combined is None:
            return Expression.constant(1, size=1)
        if bool(getattr(combined, "negated", False)):
            expr = Expression.unary_op("BOOL_NEGATE", combined.expression)
            expr.size = 1
            return expr
        return combined.expression

    def _counter_guard_parameter_candidates(
        self,
        counter_param: dict,
        conditions: Sequence[Condition],
    ) -> Tuple[Expression, ...]:
        primary = self._parameter_expression(counter_param)
        return self._parameter_expression_candidates(
            counter_param,
            [getattr(condition, "expression", None) for condition in conditions or ()],
            include_primary=True,
            primary=primary,
        )

    def _parameter_expression_candidates(
        self,
        parameter: dict,
        expressions: Sequence[Optional[Expression]],
        *,
        include_primary: bool = True,
        primary: Optional[Expression] = None,
    ) -> Tuple[Expression, ...]:
        primary = primary or self._parameter_expression(parameter)
        candidates: List[Expression] = []

        def add(expr: Expression) -> None:
            if expr is None:
                return
            if any(
                existing.equals(expr)
                and getattr(existing, "data_type", None) == getattr(expr, "data_type", None)
                and getattr(existing, "data_type_obj", None) is getattr(expr, "data_type_obj", None)
                for existing in candidates
            ):
                return
            candidates.append(expr)

        expected_name = parameter.get("name")
        try:
            expected_index = int(parameter.get("index")) if parameter.get("index") is not None else -1
        except (TypeError, ValueError):
            expected_index = -1
        expected_size = int(parameter.get("size") or getattr(primary, "size", 0) or 0)
        expected_storage = getattr(primary, "storage_info", None)
        for expr in expressions or ():
            for node in self._iter_expression_nodes(expr):
                if getattr(node, "expr_type", None) != ExpressionType.PARAMETER:
                    continue
                same_index = expected_index >= 0 and int(getattr(node, "value", -1) or -1) == expected_index
                same_name = expected_name is not None and getattr(node, "name", None) == expected_name
                same_storage = (
                    expected_storage is not None
                    and getattr(node, "storage_info", None) is not None
                    and getattr(node, "storage_info", None) == expected_storage
                )
                same_size = expected_size <= 0 or int(getattr(node, "size", 0) or 0) == expected_size
                if same_size and (same_index or same_name or same_storage):
                    add(node)
        if include_primary:
            add(primary)
        return tuple(candidates)

    def _loop_effect_profile_name(
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

    def _build_loop_side_effect_profile(
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

    def _store_effect_ref_for_op(
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

    def _store_address_space_ref_for_op(self, op):
        if op is None or self._safe_pcode_input_count(op) < 1:
            return None
        space_varnode = op.getInput(0)

        try:
            address = getattr(space_varnode, "getAddress", lambda: None)()
        except Exception:
            address = None
        address_space = getattr(address, "getAddressSpace", lambda: None)() if address is not None else None
        input_space_ref = self._address_space_ref(address_space)
        try:
            offset = getattr(space_varnode, "getOffset", lambda: None)()
        except Exception:
            offset = None
        try:
            size = getattr(space_varnode, "getSize", lambda: None)()
        except Exception:
            size = None
        offset_int = self._safe_int(offset)
        size_int = self._safe_int(size)
        target_space_ref = self._resolve_store_target_address_space_ref(offset_int)
        space_name = (input_space_ref or {}).get("space_name")
        space_id = (input_space_ref or {}).get("space_id")
        if space_name is None:
            name = getattr(space_varnode, "_name", None)
            if name:
                space_name = str(name)
        if target_space_ref is not None:
            return {
                "encoding": "ghidra_store_space_id",
                "space_name": target_space_ref.get("space_name"),
                "space_id": target_space_ref.get("space_id"),
                "space_type": target_space_ref.get("space_type"),
                "is_memory_space": target_space_ref.get("is_memory_space"),
                "is_register_space": target_space_ref.get("is_register_space"),
                "is_stack_space": target_space_ref.get("is_stack_space"),
                "pcode_input_space": input_space_ref,
                "pcode_space_id_constant": offset_int,
                "size": size_int,
            }
        if space_name is None and space_id is None and offset_int is None and size_int is None:
            name = getattr(space_varnode, "_name", None)
            if name:
                return {"space_name": str(name)}
            try:
                expr = self._build_pcode_expression(space_varnode, placeholders={})
            except RecursionError:
                expr = None
            if expr is not None and not self._expression_is_unresolved(expr):
                return expr
            return None
        return {
            "encoding": "pcode_input_space_metadata",
            "space_name": space_name,
            "space_id": space_id,
            "offset": offset_int,
            "size": size_int,
        }

    def _resolve_store_target_address_space_ref(self, space_id: Optional[int]) -> Optional[Dict[str, Any]]:
        if space_id is None:
            return None
        program = getattr(self.tracer, "program", None)
        address_factory_getter = getattr(program, "getAddressFactory", None)
        if not callable(address_factory_getter):
            return None
        try:
            address_factory = address_factory_getter()
        except (AttributeError, TypeError, ValueError, RuntimeError, LookupError):
            return None
        get_address_space = getattr(address_factory, "getAddressSpace", None)
        if not callable(get_address_space):
            return None
        try:
            address_space = get_address_space(int(space_id))
        except (AttributeError, TypeError, ValueError, RuntimeError, LookupError):
            return None
        return self._address_space_ref(address_space)

    def _address_space_ref(self, address_space) -> Optional[Dict[str, Any]]:
        if address_space is None:
            return None
        space_name = self._safe_call(address_space, "getName")
        space_id = self._safe_int(self._safe_call(address_space, "getSpaceID"))
        if space_name is None and space_id is None:
            return None
        return {
            "space_name": None if space_name is None else str(space_name),
            "space_id": space_id,
            "space_type": self._safe_int(self._safe_call(address_space, "getType")),
            "is_memory_space": self._safe_bool_call(address_space, "isMemorySpace"),
            "is_register_space": self._safe_bool_call(address_space, "isRegisterSpace"),
            "is_stack_space": self._safe_bool_call(address_space, "isStackSpace"),
        }

    def _safe_call(self, obj, method_name: str):
        method = getattr(obj, method_name, None)
        if not callable(method):
            return None
        try:
            return method()
        except (AttributeError, TypeError, ValueError, RuntimeError):
            return None

    def _safe_bool_call(self, obj, method_name: str) -> Optional[bool]:
        value = self._safe_call(obj, method_name)
        if value is None:
            return None
        return bool(value)

    def _safe_int(self, value) -> Optional[int]:
        if value is None:
            return None
        try:
            return int(value)
        except (TypeError, ValueError, OverflowError):
            return None

    def _pcode_op_order_key(self, op) -> Optional[int]:
        sequence = getattr(op, "getSeqnum", lambda: None)()
        if sequence is not None:
            order = getattr(sequence, "getOrder", lambda: None)()
            if order is not None:
                try:
                    return int(order)
                except (TypeError, ValueError):
                    pass
        order = getattr(op, "getOrder", lambda: None)()
        if order is not None:
            try:
                return int(order)
            except (TypeError, ValueError):
                return None
        return None

    def _call_target_ref_for_op(self, op):
        if op is None or self._safe_pcode_input_count(op) < 1:
            return None
        resolver = getattr(self.tracer, "resolve_call_target_ref", None)
        if not callable(resolver):
            return None
        try:
            return resolver(op.getInput(0))
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None

    def _condition_for_cbranch_op(self, op) -> Optional[Condition]:
        if op is None or self._safe_pcode_input_count(op) < 2:
            return None
        try:
            expr = self._build_pcode_expression(op.getInput(1), placeholders={})
        except RecursionError:
            return None
        if expr is None or self._expression_is_unresolved(expr):
            return None
        return Condition(expr, False)

    def _build_counted_scalar_loop_summary(
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
            guard.condition_expr,
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

        base_return_expr = self._canonicalize_zero_value_under_conditions(
            accumulator.init_expr,
            base_conditions,
        )
        loop_base_expr = self._canonicalize_zero_value_under_conditions(
            accumulator.init_expr,
            continue_conditions,
        )
        function_body_ranges = self._function_body_address_ranges(high_function, analysis, function=function)
        if self._expression_contains_executable_address_constant(
            base_return_expr,
            function_body_ranges=function_body_ranges,
        ) or self._expression_contains_executable_address_constant(
            loop_base_expr,
            function_body_ranges=function_body_ranges,
        ):
            self._debug("Declined counted scalar loop summary: base expression contains function-address constant")
            return None
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

        anchor = next(iter((getattr(analysis, "returns", None) or [])), None)
        address = getattr(anchor, "address", getattr(function, "getEntryPoint", lambda: "0x0")())
        pcode_identity = getattr(anchor, "pcode_identity", None)
        pcode_order = getattr(anchor, "pcode_order", None)
        pcode_time = getattr(anchor, "pcode_time", None)
        pcode_op_ref = getattr(anchor, "pcode_op_ref", None)

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

    def _safe_pcode_input_count(self, op) -> int:
        try:
            value = getattr(op, "getNumInputs", lambda: 0)()
            if not isinstance(value, (int, float, str, bytes)):
                return 0
            return int(value or 0)
        except Exception:
            return 0

    def _build_counted_loop_summary_value(
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

    def _build_counted_loop_summary_intrinsic(
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
        runtime_ref = CountedLoopSummaryRef(
            induction_step=int(induction_step),
            result_size=max(1, int(result_size or 0)),
            signed_loop=bool(signed_loop),
            residue_cases=term_descriptor.residue_cases,
            residue_bias_terms=term_descriptor.residue_bias_terms,
            loop_summary=loop_summary,
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

    def _canonicalize_zero_value_under_conditions(
        self,
        expr: Expression,
        conditions: Sequence[Condition],
    ) -> Expression:
        if expr is None:
            return expr
        zero = Expression.constant(0, size=max(1, int(getattr(expr, "size", 0) or 4)))
        if expr.equals(zero):
            return expr
        parameters = self._collect_summary_parameter_specs(
            expr,
            *(condition.expression for condition in conditions or [] if condition is not None),
        )
        if not self._prove_expression_equivalence_under_conditions(
            expr,
            zero,
            conditions,
            parameters,
        ):
            return expr
        self._debug(
            "Canonicalized counted loop summary base to zero under case conditions "
            f"(original={self._safe_expr_text(expr)})"
        )
        return zero

    def _canonicalize_zero_prefix_counted_loop_value(
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

    def _counted_loop_prefix_contributes_zero(
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

    def _canonicalize_peeled_counted_loop_value(
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

    def _looks_like_peeled_counted_loop_start(
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

    def _expression_depends_on_signature(
        self,
        expr: Optional[Expression],
        target_signature,
    ) -> bool:
        if expr is None:
            return False
        if _runtime_expression_signature(expr) == target_signature:
            return True
        expr_type = getattr(expr, "expr_type", None)
        if expr_type == ExpressionType.PHI:
            for cond, branch_value in getattr(expr, "value", None) or []:
                if cond is not None and self._expression_depends_on_signature(getattr(cond, "expression", None), target_signature):
                    return True
                if self._expression_depends_on_signature(branch_value, target_signature):
                    return True
            return False
        for operand in getattr(expr, "operands", None) or []:
            if self._expression_depends_on_signature(operand, target_signature):
                return True
        return False

    def _collect_summary_parameter_specs(
        self,
        *exprs: Optional[Expression],
    ) -> Optional[List[dict]]:
        return self._collect_expression_symbol_specs(*exprs)

    def _collect_expression_symbol_specs(
        self,
        *exprs: Optional[Expression],
    ) -> Optional[List[dict]]:
        specs: Dict[Tuple[Any, ...], dict] = {}
        unresolved_symbol = False

        def add_symbol(identity: Optional[Tuple[Any, ...]], candidate: dict) -> None:
            if identity is None:
                return
            size = max(1, int(candidate.get("size", 0) or 4))
            candidate = {
                **candidate,
                "identity": identity,
                "size": size,
            }
            existing = specs.get(identity)
            if existing is None or int(existing.get("size", 0) or 0) < size:
                specs[identity] = candidate

        def visit(expr: Optional[Expression]) -> None:
            nonlocal unresolved_symbol
            if expr is None:
                return
            expr_type = getattr(expr, "expr_type", None)
            if expr_type == ExpressionType.PARAMETER:
                identity = self._summary_symbol_identity_from_expression(expr)
                if identity is None:
                    unresolved_symbol = True
                    return
                add_symbol(identity, self._summary_symbol_spec_from_expression(expr))
                return
            if expr_type == ExpressionType.VARIABLE:
                identity = self._summary_symbol_identity_from_expression(expr)
                if identity is None:
                    unresolved_symbol = True
                    return
                add_symbol(identity, self._summary_symbol_spec_from_expression(expr))
                return
            if expr_type == ExpressionType.PHI:
                for cond, branch_value in getattr(expr, "value", None) or []:
                    if cond is not None:
                        visit(getattr(cond, "expression", None))
                    visit(branch_value)
                return
            for operand in getattr(expr, "operands", None) or []:
                visit(operand)

        for expr in exprs:
            visit(expr)
        if unresolved_symbol:
            return None
        ordered = sorted(
            specs.values(),
            key=lambda item: (
                self._summary_symbol_identity_sort_key(item.get("identity")),
                int(item.get("size", 0) or 0),
            ),
        )
        for ordinal, spec in enumerate(ordered):
            spec["aux_name"] = f"aux_sym_{ordinal}"
            spec["aux_index"] = ordinal
        return ordered

    def _summary_symbol_identity_from_descriptor(
        self,
        parameter: dict,
    ) -> Optional[Tuple[Any, ...]]:
        identity = parameter_identity_key_from_descriptor(parameter)
        if identity is not None:
            return identity
        try:
            index = int(parameter.get("index", -1))
        except (TypeError, ValueError):
            return None
        if index < -1:
            return ("synthetic_parameter_index", index)
        return None

    def _summary_symbol_identity_from_expression(
        self,
        expr: Expression,
    ) -> Optional[Tuple[Any, ...]]:
        expr_type = getattr(expr, "expr_type", None)
        if expr_type == ExpressionType.PARAMETER:
            identity = parameter_identity_key_from_expression(expr)
            if identity is not None:
                return identity
            try:
                index = int(getattr(expr, "value", -1) or -1)
            except (TypeError, ValueError):
                return None
            if index < -1:
                return ("synthetic_parameter_index", index)
            return None
        if expr_type == ExpressionType.VARIABLE:
            storage_key = self._summary_storage_identity_key(getattr(expr, "storage_info", None))
            if storage_key is not None:
                return ("variable_storage", storage_key)
            runtime_ref = getattr(expr, "runtime_ref", None)
            semantic_key = getattr(runtime_ref, "semantic_key", None)
            if callable(semantic_key):
                try:
                    key = semantic_key()
                except (AttributeError, TypeError, ValueError):
                    key = None
                if key is not None:
                    return ("variable_runtime_semantic", key)
            stable_key = getattr(runtime_ref, "stable_key", None)
            if callable(stable_key):
                try:
                    key = stable_key()
                except (AttributeError, TypeError, ValueError):
                    key = None
                if key is not None:
                    return ("variable_runtime_stable", key)
            return ("expression_object", id(expr))
        return None

    def _summary_symbol_spec_from_expression(
        self,
        expr: Expression,
    ) -> dict:
        result = {
            "name": str(getattr(expr, "name", None) or ""),
            "index": int(getattr(expr, "value", -1) or -1),
            "size": max(1, int(getattr(expr, "size", 0) or 4)),
            "data_type": getattr(expr, "data_type", None),
            "is_signed": bool(getattr(expr, "is_signed", True)),
        }
        storage_info = getattr(expr, "storage_info", None)
        if storage_info is not None:
            result["storage_info"] = storage_info
        return result

    def _summary_storage_identity_key(self, storage_info) -> Optional[Tuple[Any, ...]]:
        if isinstance(storage_info, dict):
            try:
                storage_info = StorageInfo(**storage_info)
            except Exception:
                return None
        storage_key_fn = getattr(storage_info, "storage_identity_key", None)
        if callable(storage_key_fn):
            try:
                return storage_key_fn()
            except (AttributeError, TypeError, ValueError):
                return None
        return None

    def _summary_storage_info_from_parameter(self, param: dict) -> Optional[StorageInfo]:
        storage_info = param.get("storage_info", param.get("storage")) if isinstance(param, dict) else None
        if isinstance(storage_info, StorageInfo):
            return storage_info
        if isinstance(storage_info, dict):
            try:
                return StorageInfo(**storage_info)
            except Exception:
                return None
        return None

    def _parameter_storage_identity_key(self, param: dict) -> Optional[Tuple[Any, ...]]:
        return self._summary_storage_identity_key(
            param.get("storage_info", param.get("storage")) if isinstance(param, dict) else None
        )

    def _location_base_ref_from_parameter(self, param: dict, *, default_name: str) -> LocationBaseRef:
        name = param.get("name", default_name) if isinstance(param, dict) else default_name
        try:
            index = int(param.get("index")) if isinstance(param, dict) and param.get("index") is not None else None
        except (TypeError, ValueError):
            index = None
        if index is not None and index >= 0:
            return LocationBaseRef.parameter(
                name,
                index=index,
                owner_program_id=param.get("owner_program_id") if isinstance(param, dict) else None,
                owner_entry_offset=param.get("owner_entry_offset") if isinstance(param, dict) else None,
            )
        storage_info = self._summary_storage_info_from_parameter(param if isinstance(param, dict) else {})
        storage_key = self._summary_storage_identity_key(storage_info)
        if storage_info is not None and storage_key is not None:
            offset = (
                int(getattr(storage_info, "base_register_offset", 0) or 0)
                if bool(getattr(storage_info, "is_register", False))
                else int(getattr(storage_info, "offset", 0) or 0)
            )
            size = max(1, int(getattr(storage_info, "size", 0) or 0))
            return LocationBaseRef.storage(
                space_id=getattr(storage_info, "space_id", None),
                space_name=getattr(storage_info, "space_name", None),
                offset=offset,
                size=size,
                storage_identity_key=storage_key,
                display_hint=name,
            )
        return LocationBaseRef.parameter(name, index=None)

    def _summary_symbol_identity_sort_key(self, identity) -> Tuple[int, str]:
        if not isinstance(identity, tuple) or not identity:
            return (9, "")
        kind = identity[0]
        if kind == "parameter_index" and len(identity) >= 2:
            try:
                return (0, f"{int(identity[1]):08d}")
            except (TypeError, ValueError):
                return (0, repr(identity[1]))
        if kind == "parameter_storage" and len(identity) >= 2:
            return (1, repr(identity[1]))
        if kind == "synthetic_parameter_index" and len(identity) >= 2:
            try:
                return (2, f"{int(identity[1]):08d}")
            except (TypeError, ValueError):
                return (2, repr(identity[1]))
        if kind == "variable_storage" and len(identity) >= 2:
            return (3, repr(identity[1]))
        if kind in {"variable_runtime_semantic", "variable_runtime_stable"} and len(identity) >= 2:
            return (4, repr(identity[1]))
        if kind == "expression_object" and len(identity) >= 2:
            try:
                return (8, f"{int(identity[1]):020d}")
            except (TypeError, ValueError):
                return (8, repr(identity[1]))
        return (8, repr(identity))

    def _prove_expression_equivalence_under_conditions(
        self,
        left: Expression,
        right: Expression,
        conditions: Sequence[Condition],
        parameters: Optional[Sequence[dict]],
    ) -> bool:
        if left.equals(right):
            return True
        query = self._build_expression_equivalence_query(left, right, conditions, parameters)
        if not query:
            return False
        solver = Z3Solver(timeout=2, debug=self.debug)
        result = solver.check_equivalence_direct(query)
        return result.status == SolverStatus.UNSAT

    def _build_expression_equivalence_query(
        self,
        left: Expression,
        right: Expression,
        conditions: Sequence[Condition],
        parameters: Optional[Sequence[dict]],
    ) -> Optional[str]:
        if left is None or right is None:
            return None
        memory_widths = self._collect_expression_memory_widths(
            left,
            right,
            *(condition.expression for condition in conditions or [] if condition is not None),
        )
        declarations = ["(set-logic QF_AUFBV)" if memory_widths else "(set-logic QF_BV)"]

        expression_symbols = self._collect_expression_symbol_specs(
            left,
            right,
            *(condition.expression for condition in conditions or [] if condition is not None),
        )
        if expression_symbols is None:
            return None
        symbol_specs: Dict[Tuple[Any, ...], dict] = {
            item.get("identity"): dict(item)
            for item in expression_symbols
            if item.get("identity") is not None
        }
        for parameter in parameters or []:
            identity = self._summary_symbol_identity_from_descriptor(dict(parameter))
            if identity is None:
                continue
            candidate = dict(parameter)
            candidate["identity"] = identity
            candidate["size"] = max(1, int(candidate.get("size", 0) or 4))
            existing = symbol_specs.get(identity)
            if existing is None or int(existing.get("size", 0) or 0) < int(parameter.get("size", 0) or 0):
                symbol_specs[identity] = candidate
        ordered_symbol_specs = self._assign_summary_auxiliary_symbols(symbol_specs.values())

        symbol_infos = self._build_auxiliary_parameter_infos(
            ordered_symbol_specs,
        )
        for symbol in symbol_infos:
            declarations.append(f"(declare-const {symbol.smt_name} (_ BitVec {symbol.bit_width}))")
        for mem_bits in sorted(memory_widths):
            declarations.append(
                f"(declare-const mem{mem_bits} (Array (_ BitVec 64) (_ BitVec {mem_bits})))"
            )
        seen_unknown_decls = set()
        for expr in (left, right):
            for decl in collect_unknown_smt_declarations(expr):
                if decl in seen_unknown_decls:
                    continue
                seen_unknown_decls.add(decl)
                declarations.append(f"(declare-const {decl[0]} (_ BitVec {decl[1]}))")
        for condition in conditions or []:
            if condition is None:
                continue
            for decl in collect_unknown_smt_declarations(condition.expression):
                if decl in seen_unknown_decls:
                    continue
                seen_unknown_decls.add(decl)
                declarations.append(f"(declare-const {decl[0]} (_ BitVec {decl[1]}))")
        intrinsic_declarations: List[str] = []
        for expr in (left, right):
            for declaration in collect_intrinsic_smt_declarations(expr):
                if declaration not in intrinsic_declarations:
                    intrinsic_declarations.append(declaration)
        for condition in conditions or []:
            if condition is None:
                continue
            for declaration in collect_intrinsic_smt_declarations(condition.expression):
                if declaration not in intrinsic_declarations:
                    intrinsic_declarations.append(declaration)
        declarations.extend(intrinsic_declarations)

        assertions = []
        for condition in conditions or []:
            if condition is None:
                continue
            rendered_condition = self._render_summary_auxiliary_smt(condition, ordered_symbol_specs)
            if rendered_condition is None:
                return None
            assertions.append(f"(assert {rendered_condition})")
        target_bits = max(1, self._expression_equivalence_target_bits(left, right))
        left_rendered = self._render_summary_auxiliary_smt(left, ordered_symbol_specs)
        right_rendered = self._render_summary_auxiliary_smt(right, ordered_symbol_specs)
        if left_rendered is None or right_rendered is None:
            return None
        left_smt = coerce_value_to_bitvec_width(
            left,
            left_rendered,
            target_bits,
            use_sign_extension=False,
        )
        right_smt = coerce_value_to_bitvec_width(
            right,
            right_rendered,
            target_bits,
            use_sign_extension=False,
        )
        assertions.append(f"(assert (not (= {left_smt} {right_smt})))")
        return "\n".join(declarations + assertions + ["(check-sat)"])

    def _assign_summary_auxiliary_symbols(
        self,
        symbol_specs: Iterable[dict],
    ) -> List[dict]:
        ordered = sorted(
            (dict(spec) for spec in symbol_specs or [] if spec.get("identity") is not None),
            key=lambda item: (
                self._summary_symbol_identity_sort_key(item.get("identity")),
                int(item.get("size", 0) or 0),
            ),
        )
        for ordinal, spec in enumerate(ordered):
            spec["aux_name"] = spec.get("aux_name") or f"aux_sym_{ordinal}"
            spec["aux_index"] = ordinal
        return ordered

    def _collect_expression_memory_widths(
        self,
        *exprs: Optional[Expression],
    ) -> List[int]:
        widths: set[int] = set()

        def visit(expr: Optional[Expression]) -> None:
            if expr is None:
                return
            if getattr(expr, "expr_type", None) == ExpressionType.MEMORY:
                bits = max(1, int(expression_smt_bit_width(expr) or 0))
                if bits in {8, 16, 32, 64}:
                    widths.add(bits)
            for operand in getattr(expr, "operands", None) or []:
                visit(operand)
            if getattr(expr, "expr_type", None) == ExpressionType.PHI:
                for cond, branch_value in getattr(expr, "value", None) or []:
                    if cond is not None:
                        visit(getattr(cond, "expression", None))
                    visit(branch_value)

        for expr in exprs:
            visit(expr)
        return sorted(widths)

    def _expression_equivalence_target_bits(
        self,
        left: Expression,
        right: Expression,
    ) -> int:
        left_bits = int(getattr(left, "get_bit_width", lambda: 0)() or 0)
        right_bits = int(getattr(right, "get_bit_width", lambda: 0)() or 0)
        try:
            from ..model.render_smt import expression_smt_bit_width

            left_bits = max(left_bits, int(expression_smt_bit_width(left) or 0))
            right_bits = max(right_bits, int(expression_smt_bit_width(right) or 0))
        except Exception:
            pass
        return max(left_bits, right_bits, 32)

    def _build_auxiliary_parameter_infos(
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

    def _render_summary_auxiliary_smt(
        self,
        node,
        symbol_specs: Sequence[dict],
    ) -> Optional[str]:
        identity_to_spec = {
            spec.get("identity"): spec
            for spec in symbol_specs or []
            if spec.get("identity") is not None and spec.get("aux_name")
        }
        if isinstance(node, Condition):
            cloned_expr = self._clone_summary_expression_for_smt(node.expression, identity_to_spec)
            if cloned_expr is None:
                return None
            return Condition(cloned_expr, bool(getattr(node, "negated", False))).to_smt()
        if isinstance(node, Expression):
            cloned_expr = self._clone_summary_expression_for_smt(node, identity_to_spec)
            return cloned_expr.to_smt() if cloned_expr is not None else None
        return None

    def _clone_summary_expression_for_smt(
        self,
        expr: Optional[Expression],
        identity_to_spec: Dict[Tuple[Any, ...], dict],
    ) -> Optional[Expression]:
        if expr is None:
            return None
        expr_type = getattr(expr, "expr_type", None)
        if expr_type in {ExpressionType.PARAMETER, ExpressionType.VARIABLE}:
            identity = self._summary_symbol_identity_from_expression(expr)
            if identity is None:
                return None
            symbol_spec = identity_to_spec.get(identity)
            if symbol_spec is None:
                return None
            aux_name = str(symbol_spec.get("aux_name") or "")
            if not aux_name:
                return None
            try:
                occurrence_size = max(1, int(getattr(expr, "size", 0) or 4))
                symbol_size = max(1, int(symbol_spec.get("size", 0) or occurrence_size))
            except (TypeError, ValueError):
                return None
            if occurrence_size > symbol_size:
                return None
            aux_expr = Expression.parameter(
                aux_name,
                index=int(symbol_spec.get("aux_index", -1) or -1),
                data_type=getattr(expr, "data_type", None),
                data_type_obj=getattr(expr, "data_type_obj", None),
                size=symbol_size,
                storage_info=getattr(expr, "storage_info", None),
            )
            if occurrence_size == symbol_size:
                return aux_expr
            return Expression(
                ExpressionType.BINARY_OP,
                operator="SUBPIECE",
                operands=[
                    aux_expr,
                    Expression.constant(0, size=8),
                ],
                size=occurrence_size,
            )
        if expr_type == ExpressionType.PHI:
            branches = []
            for condition, value in getattr(expr, "value", None) or []:
                cloned_condition = None
                if condition is not None:
                    cloned_condition_expr = self._clone_summary_expression_for_smt(
                        condition.expression,
                        identity_to_spec,
                    )
                    if cloned_condition_expr is None:
                        return None
                    cloned_condition = Condition(
                        cloned_condition_expr,
                        bool(getattr(condition, "negated", False)),
                    )
                cloned_value = self._clone_summary_expression_for_smt(value, identity_to_spec)
                if cloned_value is None:
                    return None
                branches.append((cloned_condition, cloned_value))
            return expr.clone_with(value=branches)
        operands = getattr(expr, "operands", None) or []
        if not operands:
            return expr
        cloned_operands = []
        for operand in operands:
            cloned_operand = self._clone_summary_expression_for_smt(operand, identity_to_spec)
            if cloned_operand is None:
                return None
            cloned_operands.append(cloned_operand)
        return expr.clone_with(operands=cloned_operands)

    def _negate_simple_condition_set(
        self,
        conditions: Sequence[Condition],
    ) -> Optional[List[Condition]]:
        simplified = ConditionSimplifier.simplify_conditions_object_centric(list(conditions or []))
        if len(simplified) != 1:
            return None
        return ConditionSimplifier.simplify_conditions_object_centric([simplified[0].negate()])

    def _repair_two_way_partition_conditions(
        self,
        base_conditions: Sequence[Condition],
        continue_conditions: Sequence[Condition],
    ) -> Tuple[List[Condition], List[Condition]]:
        base_simplified = ConditionSimplifier.simplify_conditions_object_centric(list(base_conditions or []))
        continue_simplified = ConditionSimplifier.simplify_conditions_object_centric(list(continue_conditions or []))

        if not base_simplified and continue_simplified:
            negated_continue = self._negate_simple_condition_set(continue_simplified)
            if negated_continue is not None:
                base_simplified = negated_continue
        elif not continue_simplified and base_simplified:
            negated_base = self._negate_simple_condition_set(base_simplified)
            if negated_base is not None:
                continue_simplified = negated_base

        return base_simplified, continue_simplified

    def _derive_direct_counted_loop_conditions(
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

    def _common_conditions_across_paths(
        self,
        path_sets: Sequence[Sequence[Condition]],
    ) -> List[Condition]:
        if not path_sets:
            return []
        normalized_sets = [
            ConditionSimplifier.simplify_conditions_object_centric(list(conditions or []))
            for conditions in path_sets
        ]
        common = list(normalized_sets[0])
        for conditions in normalized_sets[1:]:
            condition_map = {
                _runtime_conditions_signature([condition]): condition
                for condition in conditions
            }
            common = [
                condition
                for condition in common
                if _runtime_conditions_signature([condition]) in condition_map
            ]
            if not common:
                break
        return ConditionSimplifier.simplify_conditions_object_centric(common)

    def _extract_counted_scalar_loop_model(
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

    def _candidate_counted_loop_guards(
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

    def _iter_basic_blocks(self, high_function) -> Iterable:
        try:
            for block in high_function.getBasicBlocks():
                yield block
        except Exception:
            return

    def _iter_block_ops(self, block) -> Iterable:
        iterator = getattr(block, "getIterator", lambda: None)()
        if iterator is None:
            return
        while iterator.hasNext():
            yield iterator.next()

    def _find_cbranch_op(self, block):
        for op in self._iter_block_ops(block):
            if getattr(op, "getMnemonic", lambda: None)() == "CBRANCH":
                return op
        return None

    def _make_pcode_op_ref(self, pcode_op) -> Optional[PcodeOpRef]:
        return PcodeOpRef.from_pcode_op(
            pcode_op,
            binary_id=getattr(self.tracer, "_function_binary_id", None),
            program_uid=getattr(self.tracer, "_function_program_id", None),
            function_entry_space=getattr(self.tracer, "_function_entry_space", None),
            function_entry_offset=getattr(self.tracer, "_function_entry_offset", None),
        )

    def _make_pcode_block_ref(self, block) -> Optional[PcodeBlockRef]:
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
        )

    def _collect_block_successors(self, block) -> List[object]:
        successors = []
        out_size = int(getattr(block, "getOutSize", lambda: 0)() or 0)
        for index in range(out_size):
            successor = getattr(block, "getOut", lambda _idx: None)(index)
            if successor is not None:
                successors.append(successor)
        return successors

    def _collect_block_predecessors(self, block) -> List[object]:
        predecessors = []
        in_size = int(getattr(block, "getInSize", lambda: 0)() or 0)
        for index in range(in_size):
            predecessor = getattr(block, "getIn", lambda _idx: None)(index)
            if predecessor is not None:
                predecessors.append(predecessor)
        return predecessors

    def _collect_loop_body_blocks(
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

    def _collect_natural_loop_blocks(
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

    def _collect_reachable_loop_body_blocks(
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

    def _loop_block_guard_conditions(
        self,
        *,
        header_block,
        guard: CountedLoopGuard,
        loop_blocks: Sequence[object],
    ) -> Dict[object, Tuple[Condition, ...]]:
        return {
            block_key: tuple(info.get("common", ()))
            for block_key, info in self._loop_block_guard_effect_info(
                header_block=header_block,
                guard=guard,
                loop_blocks=loop_blocks,
            ).items()
        }

    def _loop_block_guard_effect_info(
        self,
        *,
        header_block,
        guard: CountedLoopGuard,
        loop_blocks: Sequence[object],
    ) -> Dict[object, Dict[str, Any]]:
        if guard is None or guard.body_block is None:
            return {}
        result: Dict[object, Dict[str, Any]] = {}
        header_key = self._block_key(header_block)
        body_key = self._block_key(guard.body_block)
        for block in loop_blocks or ():
            block_key = self._block_key(block)
            if block_key in {header_key, body_key}:
                result[block_key] = {
                    "common": (),
                    "paths": ((),),
                    "incomplete": False,
                }
                continue
            paths, incomplete = self._enumerate_paths_with_conditions_result(
                start_block=guard.body_block,
                target_block=block,
                header_block=header_block,
                placeholders={},
                stop_block=guard.exit_block,
                limit=16,
            )
            if not paths:
                result[block_key] = {
                    "common": (),
                    "paths": (),
                    "incomplete": incomplete,
                }
                continue
            result[block_key] = {
                "common": tuple(self._common_conditions_across_paths(paths)),
                "paths": tuple(tuple(path) for path in paths),
                "incomplete": incomplete,
            }
        return result

    def _block_key(self, block) -> object:
        if block is None:
            return None
        block_index = getattr(block, "getIndex", lambda: None)()
        if block_index is not None:
            return ("index", int(block_index))
        return ("id", id(block))

    def _can_reach_block(self, start_block, target_block) -> bool:
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

    def _pick_body_and_exit_blocks(self, header_block) -> Optional[Tuple[object, object, bool]]:
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

    def _induction_backedge_indices(
        self,
        induction: CountedLoopInduction,
    ) -> Tuple[int, ...]:
        indices = tuple(int(index) for index in getattr(induction, "backedge_indices", ()) or ())
        if indices:
            return indices
        return (int(getattr(induction, "backedge_index", 0)),)

    def _induction_init_index(
        self,
        induction: CountedLoopInduction,
    ) -> int:
        indices = self._induction_backedge_indices(induction)
        init_index = getattr(induction, "init_index", None)
        if isinstance(init_index, int):
            return init_index
        if len(indices) == 1:
            return 1 - indices[0]
        return 0

    def _accumulator_backedge_indices(
        self,
        accumulator: CountedLoopAccumulator,
    ) -> Tuple[int, ...]:
        indices = tuple(int(index) for index in getattr(accumulator, "backedge_indices", ()) or ())
        if indices:
            return indices
        return (int(getattr(accumulator, "backedge_index", 0)),)

    def _accumulator_init_index(
        self,
        accumulator: CountedLoopAccumulator,
        induction: CountedLoopInduction,
    ) -> int:
        init_index = getattr(accumulator, "init_index", None)
        if isinstance(init_index, int):
            return init_index
        return self._induction_init_index(induction)

    def _match_counted_loop_induction(
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

    def _match_counted_loop_guard(
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
            condition_expr, bound_expr, signed_comparison = normalized
            return CountedLoopGuard(
                condition_expr=condition_expr,
                bound_expr=bound_expr,
                continue_on_true=body_on_true,
                body_block=body_block,
                exit_block=exit_block,
                signed_comparison=signed_comparison,
                entry_condition_expr=condition_expr,
            )
        return None

    def _match_latch_counted_loop_guard(
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
            entry_condition_expr=entry_condition_expr,
            latch_block=latch_block,
        )

    def _match_counted_loop_accumulators(
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

    def _assign_counted_loop_accumulator_binder_ordinals(
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

    def _counted_loop_accumulator_priority(
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

    def _expression_contains_executable_address_constant(
        self,
        expr: Optional[Expression],
        *,
        function_body_ranges: Sequence[Tuple[int, int]] = (),
    ) -> bool:
        program = getattr(self.tracer, "program", None)
        if program is None and not function_body_ranges:
            return False
        if expr is None:
            return False
        for node in self._iter_expression_nodes(expr):
            if getattr(node, "expr_type", None) != ExpressionType.CONSTANT:
                continue
            value = self._raw_constant_value(node)
            if value is None:
                continue
            if self._constant_resolves_to_function_body_address(value, function_body_ranges):
                return True
            if self._constant_resolves_to_executable_address(value):
                return True
        return False

    def _constant_resolves_to_function_body_address(
        self,
        value: int,
        function_body_ranges: Sequence[Tuple[int, int]],
    ) -> bool:
        try:
            value = int(value)
        except (TypeError, ValueError):
            return False
        for start, end in function_body_ranges or ():
            try:
                start_int = int(start)
                end_int = int(end)
            except (TypeError, ValueError):
                continue
            if start_int <= value <= end_int:
                return True
        return False

    def _constant_resolves_to_executable_address(self, value: int) -> bool:
        try:
            value = int(value)
        except (TypeError, ValueError):
            return False
        if value < 0:
            return False
        program = getattr(self.tracer, "program", None)
        if program is None:
            return False
        try:
            memory = program.getMemory()
        except Exception:
            memory = None
        if memory is None:
            return False
        address = None
        try:
            address_factory = program.getAddressFactory()
            default_space = address_factory.getDefaultAddressSpace()
            address = default_space.getAddress(value)
        except Exception:
            address = None
        if address is None:
            return False
        try:
            block = memory.getBlock(address)
        except Exception:
            block = None
        if block is None:
            return False
        try:
            return bool(block.isExecute())
        except Exception:
            return False

    def _function_body_address_ranges(self, high_function, analysis, *, function=None) -> Tuple[Tuple[int, int], ...]:
        ranges: List[Tuple[int, int]] = []

        def add_range(start, end) -> None:
            try:
                start_int = int(start)
                end_int = int(end)
            except (TypeError, ValueError):
                return
            if start_int < 0 or end_int < 0:
                return
            if end_int < start_int:
                start_int, end_int = end_int, start_int
            ranges.append((start_int, end_int))

        if function is None:
            getter = getattr(high_function, "getFunction", None)
        else:
            getter = None
        if function is None and callable(getter):
            try:
                function = getter()
            except Exception:
                function = None
        body = None
        body_getter = getattr(function, "getBody", None)
        if callable(body_getter):
            try:
                body = body_getter()
            except Exception:
                body = None
        if body is not None:
            try:
                min_address = body.getMinAddress()
                max_address = body.getMaxAddress()
                add_range(min_address.getOffset(), max_address.getOffset())
            except Exception:
                pass

        entry_value = None
        entry_getter = getattr(function, "getEntryPoint", None)
        if callable(entry_getter):
            try:
                entry_point = entry_getter()
                entry_value = int(entry_point.getOffset())
            except Exception:
                entry_value = None
        function_ref = getattr(analysis, "function_ref", None)
        if entry_value is None and function_ref is not None:
            entry_value = getattr(function_ref, "entry_offset", None)
        if entry_value is None:
            entry_point = getattr(analysis, "entry_point", None)
            if entry_point is not None:
                try:
                    entry_value = int(str(entry_point), 16)
                except (TypeError, ValueError):
                    entry_value = None
        if entry_value is not None:
            max_seen = int(entry_value)
            for ret in getattr(analysis, "returns", None) or ():
                address = getattr(ret, "address", None)
                if address is None:
                    continue
                try:
                    max_seen = max(max_seen, int(str(address), 16))
                except (TypeError, ValueError):
                    continue
            if max_seen > int(entry_value):
                add_range(int(entry_value), max(max_seen + 0x100, int(entry_value) + 0x1000))
            else:
                add_range(int(entry_value), int(entry_value) + 0x1000)

        return tuple(dict.fromkeys(ranges))

    def _counted_loop_accumulator_order_key(
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

    def _counted_loop_accumulator_stable_key(
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

    def _counted_loop_model_priority(
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

    def _extract_counted_loop_update_cases(
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

    def _try_extract_counted_loop_update_cases_for_summary(
        self,
        accumulator: CountedLoopAccumulator,
        induction: CountedLoopInduction,
        guard: CountedLoopGuard,
    ) -> Tuple[CountedLoopUpdateCase, ...]:
        try:
            return tuple(self._extract_counted_loop_update_cases(accumulator, induction, guard))
        except (AttributeError, TypeError, IndexError, RecursionError):
            return ()

    def _build_counted_loop_case_refs(
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

    def _collect_affine_loop_state_placeholders(
        self,
        *,
        header_block,
        induction: CountedLoopInduction,
        accumulator: CountedLoopAccumulator,
    ) -> Dict[object, Expression]:
        placeholders: Dict[object, Expression] = {}
        if header_block is None:
            return placeholders
        member_output_keys = {
            self._varnode_cache_key(output)
            for output in accumulator.member_outputs
            if output is not None
        }
        for op in self._iter_block_ops(header_block):
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            if op is induction.phi_op or op is accumulator.phi_op:
                continue
            output = getattr(op, "getOutput", lambda: None)()
            if output is not None and self._varnode_cache_key(output) in member_output_keys:
                continue
            expr = self._summarize_affine_loop_state_phi(op, induction)
            if expr is None:
                continue
            if output is None:
                continue
            placeholders[output] = expr
        return placeholders

    def _summarize_affine_loop_state_phi(
        self,
        phi_op,
        induction: CountedLoopInduction,
    ) -> Optional[Expression]:
        if phi_op is None or induction is None:
            return None
        if int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0) != 2:
            return None
        phi_output = getattr(phi_op, "getOutput", lambda: None)()
        if phi_output is None:
            return None

        backedge_index = None
        delta = None
        for candidate_index in range(2):
            candidate_delta = self._extract_index_step(phi_op.getInput(candidate_index), phi_output)
            if candidate_delta is None:
                continue
            backedge_index = candidate_index
            delta = candidate_delta
            break
        if backedge_index is None or delta is None:
            return None

        init_expr = self._build_pcode_expression(
            phi_op.getInput(1 - backedge_index),
            placeholders={
                induction.phi_output: induction.placeholder,
                induction.phi_op.getInput(self._induction_init_index(induction)): induction.placeholder,
            },
        )
        if init_expr is None or self._expression_is_unresolved(init_expr):
            return None

        size = getattr(phi_output, "getSize", lambda: 0)() or induction.placeholder.size or init_expr.size or 4
        counter_name = induction.placeholder.name or "__loop_iv"
        init_affine = self._extract_affine_term(init_expr, counter_name)
        induction_step = int(induction.step or 0)
        if induction_step == 0 or delta % induction_step != 0:
            return None
        ratio = delta // induction_step
        if init_affine is not None and init_affine[0] == ratio:
            linear_term = self._scale_term(induction.placeholder, ratio, size)
            if linear_term is None:
                return None
            if init_affine[1] == 0:
                linear_term.size = size
                return linear_term
            bias_expr = Expression.constant(init_affine[1], size)
            expr = Expression.binary_op("INT_ADD", linear_term, bias_expr)
            expr.size = size
            return expr

        current_offset = Expression.binary_op("INT_SUB", induction.placeholder, induction.init_expr)
        current_offset.size = size
        if ratio == 0:
            expr = init_expr
        elif ratio == 1:
            expr = Expression.binary_op("INT_ADD", init_expr, current_offset)
            expr.size = size
        elif ratio == -1:
            expr = Expression.binary_op("INT_SUB", init_expr, current_offset)
            expr.size = size
        else:
            scale = Expression.constant(abs(ratio), size)
            scaled_offset = Expression.binary_op("INT_MULT", current_offset, scale)
            scaled_offset.size = size
            operator = "INT_ADD" if ratio > 0 else "INT_SUB"
            expr = Expression.binary_op(operator, init_expr, scaled_offset)
            expr.size = size
        expr.size = size
        return expr

    def _enumerate_paths_with_conditions(
        self,
        *,
        start_block,
        target_block,
        header_block,
        placeholders: Dict[object, Expression],
        stop_block=None,
        limit: int = 8,
    ) -> List[List[Condition]]:
        paths, _incomplete = self._enumerate_paths_with_conditions_result(
            start_block=start_block,
            target_block=target_block,
            header_block=header_block,
            placeholders=placeholders,
            stop_block=stop_block,
            limit=limit,
        )
        return paths

    def _enumerate_paths_with_conditions_result(
        self,
        *,
        start_block,
        target_block,
        header_block,
        placeholders: Dict[object, Expression],
        stop_block=None,
        limit: int = 8,
    ) -> Tuple[List[List[Condition]], bool]:
        if start_block is None or target_block is None:
            return [[]], False
        target_key = self._block_key(target_block)
        header_key = self._block_key(header_block)
        stop_key = self._block_key(stop_block)
        paths: List[List[Condition]] = []
        incomplete = False

        def dfs(current, active_conditions: List[Condition], visited: set) -> None:
            nonlocal incomplete
            if len(paths) >= limit:
                incomplete = True
                return
            current_key = self._block_key(current)
            if current_key == target_key:
                paths.append(list(active_conditions))
                return
            if current_key == stop_key:
                return
            visited = set(visited)
            visited.add(current_key)
            for successor in self._collect_block_successors(current):
                successor_key = self._block_key(successor)
                if successor_key in visited or successor_key == header_key:
                    continue
                branch_condition = self._build_block_edge_condition(
                    current,
                    successor,
                    placeholders=placeholders,
                )
                next_conditions = list(active_conditions)
                if branch_condition is not None:
                    next_conditions.append(branch_condition)
                dfs(successor, next_conditions, visited)

        dfs(start_block, [], set())
        return paths, incomplete

    def _build_block_edge_condition(
        self,
        block,
        successor,
        *,
        placeholders: Dict[object, Expression],
    ) -> Optional[Condition]:
        cbranch = self._find_cbranch_op(block)
        if cbranch is None or int(getattr(cbranch, "getNumInputs", lambda: 0)() or 0) < 2:
            return None
        expr = self._build_pcode_expression(cbranch.getInput(1), placeholders=placeholders)
        if expr is None or self._expression_is_unresolved(expr):
            return None

        true_out = getattr(block, "getTrueOut", lambda: None)()
        false_out = getattr(block, "getFalseOut", lambda: None)()
        successor_key = self._block_key(successor)
        if true_out is not None and self._block_key(true_out) == successor_key:
            return Condition(expr, False)
        if false_out is not None and self._block_key(false_out) == successor_key:
            return Condition(expr, True)
        return None

    def _build_pcode_expression(
        self,
        varnode,
        *,
        placeholders: Dict[object, Expression],
        _seen=None,
        _memo=None,
    ) -> Optional[Expression]:
        if varnode is None:
            return None
        if _memo is None:
            _memo = {}

        placeholder_keys = tuple(sorted(id(candidate) for candidate in placeholders))
        memo_key = (self._varnode_cache_key(varnode), placeholder_keys)
        cached = _memo.get(memo_key)
        if cached is not None:
            if cached is False:
                return None
            return cached
        _memo[memo_key] = False

        for candidate, replacement in placeholders.items():
            if self._same_placeholder_varnode(varnode, candidate):
                _memo[memo_key] = replacement
                return replacement

        current = self._follow_passthrough_varnode(varnode)
        current_memo_key = memo_key
        if current is not varnode:
            current_memo_key = (self._varnode_cache_key(current), placeholder_keys)
            cached = _memo.get(current_memo_key)
            if cached is not None:
                if cached is False:
                    return None
                _memo[memo_key] = cached
                return cached
            _memo[current_memo_key] = False
        for candidate, replacement in placeholders.items():
            if self._same_placeholder_varnode(current, candidate):
                _memo[memo_key] = replacement
                _memo[current_memo_key] = replacement
                return replacement

        if _seen is None:
            _seen = set()
        current_id = id(current)
        if current_id in _seen:
            return None
        _seen = set(_seen)
        _seen.add(current_id)

        def_op = getattr(current, "getDef", lambda: None)()
        if def_op is None:
            traced = self._trace_varnode_expression(current)
            if traced is None or self._expression_is_unresolved(traced):
                return None
            _memo[memo_key] = traced
            _memo[current_memo_key] = traced
            return traced

        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        output = getattr(def_op, "getOutput", lambda: None)()
        output_size = max(1, int(getattr(output, "getSize", lambda: 0)() or getattr(current, "getSize", lambda: 0)() or 1))

        if mnemonic == "MULTIEQUAL":
            parent_block = getattr(def_op, "getParent", lambda: None)()
            input_count = int(getattr(def_op, "getNumInputs", lambda: 0)() or 0)
            branches = []
            for index in range(input_count):
                value = self._build_pcode_expression(
                    def_op.getInput(index),
                    placeholders=placeholders,
                    _seen=_seen,
                    _memo=_memo,
                )
                if value is None:
                    continue
                condition = None
                if parent_block is not None and index < int(getattr(parent_block, "getInSize", lambda: 0)() or 0):
                    predecessor = parent_block.getIn(index)
                    condition = self._build_block_edge_condition(
                        predecessor,
                        parent_block,
                        placeholders=placeholders,
                    )
                branches.append((condition, value))
            if not branches:
                return None
            if len(branches) == 1 and branches[0][0] is None:
                result = branches[0][1]
                _memo[memo_key] = result
                _memo[current_memo_key] = result
                return result
            phi = Expression.phi(branches)
            phi.size = output_size
            _memo[memo_key] = phi
            _memo[current_memo_key] = phi
            return phi

        if mnemonic in {"COPY", "CAST", "INT_ZEXT", "INT_SEXT", "SUBPIECE"}:
            expr = self._build_pcode_expression(
                def_op.getInput(0),
                placeholders=placeholders,
                _seen=_seen,
                _memo=_memo,
            )
            if expr is None:
                return None
            if mnemonic in {"COPY", "CAST"}:
                expr.size = output_size
                _memo[memo_key] = expr
                _memo[current_memo_key] = expr
                return expr
            if mnemonic in {"INT_ZEXT", "INT_SEXT"}:
                widened = Expression.unary_op(mnemonic, expr)
                widened.size = output_size
                _memo[memo_key] = widened
                _memo[current_memo_key] = widened
                return widened
            if mnemonic == "SUBPIECE":
                if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
                    return None
                offset_expr = self._build_pcode_expression(
                    def_op.getInput(1),
                    placeholders=placeholders,
                    _seen=_seen,
                    _memo=_memo,
                )
                if offset_expr is None:
                    return None
                subpiece = Expression.binary_op("SUBPIECE", expr, offset_expr)
                subpiece.size = output_size
                _memo[memo_key] = subpiece
                _memo[current_memo_key] = subpiece
                return subpiece

        if mnemonic in {"INT_NEGATE", "INT_2COMP", "BOOL_NEGATE"}:
            if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) != 1:
                return None
            operand = self._build_pcode_expression(
                def_op.getInput(0),
                placeholders=placeholders,
                _seen=_seen,
                _memo=_memo,
            )
            if operand is None:
                return None
            unary = Expression.unary_op(mnemonic, operand)
            unary.size = output_size
            _memo[memo_key] = unary
            _memo[current_memo_key] = unary
            return unary

        if mnemonic in {
            "INT_ADD",
            "INT_SUB",
            "INT_MULT",
            "INT_AND",
            "INT_OR",
            "INT_XOR",
            "PIECE",
            "INT_LEFT",
            "INT_RIGHT",
            "INT_SRIGHT",
            "INT_EQUAL",
            "INT_NOTEQUAL",
            "INT_LESS",
            "INT_LESSEQUAL",
            "INT_SLESS",
            "INT_SLESSEQUAL",
            "BOOL_AND",
            "BOOL_OR",
            "BOOL_XOR",
        }:
            if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) != 2:
                return None
            left = self._build_pcode_expression(
                def_op.getInput(0),
                placeholders=placeholders,
                _seen=_seen,
                _memo=_memo,
            )
            right = self._build_pcode_expression(
                def_op.getInput(1),
                placeholders=placeholders,
                _seen=_seen,
                _memo=_memo,
            )
            if left is None or right is None:
                return None
            expr = Expression.binary_op(mnemonic, left, right)
            expr.size = output_size
            _memo[memo_key] = expr
            _memo[current_memo_key] = expr
            return expr

        return None

    def _normalize_loop_continue_guard(
        self,
        raw_expr: Expression,
        counter_placeholder: Expression,
        body_on_true: bool,
        step: int,
    ) -> Optional[Tuple[Expression, Expression, bool]]:
        counter_name = counter_placeholder.name or "__loop_iv"
        parsed = self._parse_counter_comparison(raw_expr, counter_name)
        if parsed is None:
            return None
        relation, other_expr, signed = parsed
        if not self._is_counted_loop_bound_expr(other_expr):
            return None
        if not body_on_true:
            relation = {
                "<": ">=",
                "<=": ">",
                ">": "<=",
                ">=": "<",
            }.get(relation)
        if step > 0:
            if relation == "<=":
                other_expr = self._adjust_loop_bound_for_strict_relation(other_expr, +1)
                relation = "<"
            if relation != "<":
                return None
            operator = "INT_SLESS" if signed else "INT_LESS"
            condition_expr = Expression.binary_op(operator, counter_placeholder, other_expr)
            condition_expr.size = 1
            return condition_expr, other_expr, signed

        if relation == ">=":
            other_expr = self._adjust_loop_bound_for_strict_relation(other_expr, -1)
            relation = ">"
        if relation != ">":
            return None
        operator = "INT_SLESS" if signed else "INT_LESS"
        condition_expr = Expression.binary_op(operator, other_expr, counter_placeholder)
        condition_expr.size = 1
        return condition_expr, other_expr, signed

    def _normalize_latch_continue_guard(
        self,
        raw_expr: Expression,
        counter_placeholder: Expression,
        continue_on_true: bool,
        step: int,
    ) -> Optional[Tuple[Expression, Expression, Expression, bool]]:
        counter_name = counter_placeholder.name or "__loop_iv"
        if raw_expr.expr_type != ExpressionType.BINARY_OP or len(raw_expr.operands) != 2:
            return None
        operator = raw_expr.operator
        left, right = raw_expr.operands

        counter_side = None
        bound_expr = None
        signed = operator.startswith("INT_S")
        affine_left = self._extract_affine_term(left, counter_name)
        affine_right = self._extract_affine_term(right, counter_name)
        if affine_left is not None and affine_left[0] == 1 and affine_right is None:
            counter_side = "left"
            bound_expr = right
            bias = affine_left[1]
        elif affine_right is not None and affine_right[0] == 1 and affine_left is None:
            counter_side = "right"
            bound_expr = left
            bias = affine_right[1]
        else:
            return None

        if bias != abs(step):
            return None
        if not self._is_counted_loop_bound_expr(bound_expr):
            return None

        continue_when_equal = operator == "INT_EQUAL"
        if raw_expr.operator not in {"INT_EQUAL", "INT_NOTEQUAL"}:
            return None
        keep_looping = continue_when_equal if continue_on_true else not continue_when_equal
        if keep_looping:
            return None

        compare_op = "INT_SLESS" if signed else "INT_LESS"
        if step > 0:
            condition_expr = Expression.binary_op(compare_op, counter_placeholder, bound_expr)
        else:
            condition_expr = Expression.binary_op(compare_op, bound_expr, counter_placeholder)
        condition_expr.size = 1
        entry_op = "INT_NOTEQUAL" if counter_side == "left" else "INT_NOTEQUAL"
        entry_condition_expr = Expression.binary_op(entry_op, counter_placeholder, bound_expr)
        entry_condition_expr.size = 1
        return condition_expr, entry_condition_expr, bound_expr, signed

    def _is_counted_loop_bound_expr(self, expr: Optional[Expression]) -> bool:
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

    def _adjust_loop_bound_for_strict_relation(
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

    def _parse_counter_comparison(
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

    def _expr_matches_counter_placeholder(
        self,
        expr: Optional[Expression],
        counter_name: str,
    ) -> bool:
        normalized = self._normalize_counter_view(expr, counter_name)
        return bool(normalized is not None and getattr(normalized[0], "name", None) == counter_name)

    def _extract_residue_loop_cases(
        self,
        cases: Sequence[CountedLoopUpdateCase],
        counter_name: str,
    ) -> Optional[Tuple[ResidueLoopCase, ...]]:
        if not cases:
            return None
        if len(cases) == 1 and not cases[0].conditions:
            affine_case = self._extract_affine_loop_case(cases[0].delta_expr, counter_name)
            if affine_case is None:
                return None
            affine, bias_expr = affine_case
            return (ResidueLoopCase(modulus=1, residue=0, affine=affine, bias_expr=bias_expr),)

        residue_cases: List[ResidueLoopCase] = []
        modulus = None
        seen_residues = set()
        for case in cases:
            affine_case = self._extract_affine_loop_case(case.delta_expr, counter_name)
            if affine_case is None:
                return None
            affine, bias_expr = affine_case
            residue_info = self._extract_exact_residue_case(case.conditions, counter_name)
            if residue_info is None:
                return None
            case_modulus, residue = residue_info
            if modulus is None:
                modulus = case_modulus
            if modulus != case_modulus:
                return None
            if residue in seen_residues:
                return None
            seen_residues.add(residue)
            residue_cases.append(
                ResidueLoopCase(
                    modulus=case_modulus,
                    residue=residue,
                    affine=affine,
                    bias_expr=bias_expr,
                )
            )
        if modulus is None or seen_residues != set(range(modulus)):
            return None
        return tuple(sorted(residue_cases, key=lambda item: item.residue))

    def _extract_affine_loop_case(
        self,
        expr: Expression,
        counter_name: str,
    ) -> Optional[Tuple[Tuple[int, int], Optional[Expression]]]:
        affine = self._extract_affine_term(expr, counter_name)
        if affine is not None:
            return affine, None

        coeff = 0
        constant_bias = 0
        bias_terms: List[Expression] = []
        for sign, term in self._flatten_add_terms(expr):
            term_affine = self._extract_affine_term(term, counter_name)
            if term_affine is not None:
                coeff += int(sign) * int(term_affine[0])
                constant_bias += int(sign) * int(term_affine[1])
                continue
            if any(
                self._expr_matches_counter_placeholder(node, counter_name)
                for node in self._iter_expression_nodes(term)
            ):
                return None
            scaled = self._scale_expression(term, int(sign))
            if scaled is None:
                continue
            bias_terms.append(scaled)

        if not bias_terms:
            return None
        bias_expr = self._sum_expression_terms(bias_terms)
        if bias_expr is None or self._expression_is_unresolved(bias_expr):
            return None
        if not self._expression_is_loop_invariant_bias(bias_expr):
            return None
        return (coeff, constant_bias), bias_expr

    def _validate_counted_loop_update_cases(
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

    def _build_affine_delta_expression(
        self,
        counter_expr: Expression,
        affine: Tuple[int, int],
        size: int,
        *,
        bias_expr: Optional[Expression] = None,
    ) -> Optional[Expression]:
        coeff, bias = int(affine[0]), int(affine[1])
        terms: List[Expression] = []
        counter = self._copy_symbol_expression(counter_expr, max(1, size))
        coeff_term = self._scale_expression(counter, coeff)
        if coeff_term is not None:
            coeff_term.size = max(1, size)
            terms.append(coeff_term)
        if bias != 0:
            terms.append(Expression.constant(bias, max(1, size)))
        if bias_expr is not None:
            terms.append(bias_expr)
        if not terms:
            return Expression.constant(0, max(1, size))
        result = self._sum_expression_terms(terms)
        if result is not None:
            result.size = max(1, size)
        return result

    def _copy_symbol_expression(self, expr: Expression, size: int) -> Expression:
        if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER:
            return Expression.parameter(
                getattr(expr, "name", None) or "param",
                index=int(getattr(expr, "value", -1) or -1),
                data_type=getattr(expr, "data_type", None),
                data_type_obj=getattr(expr, "data_type_obj", None),
                size=max(1, int(size or getattr(expr, "size", 0) or 4)),
                storage_info=getattr(expr, "storage_info", None),
                runtime_ref=getattr(expr, "runtime_ref", None),
            )
        if getattr(expr, "expr_type", None) == ExpressionType.VARIABLE:
            return Expression.variable(
                getattr(expr, "name", None) or "var",
                data_type=getattr(expr, "data_type", None),
                data_type_obj=getattr(expr, "data_type_obj", None),
                size=max(1, int(size or getattr(expr, "size", 0) or 4)),
                storage_info=getattr(expr, "storage_info", None),
                runtime_ref=getattr(expr, "runtime_ref", None),
            )
        return expr

    def _extract_exact_residue_case(
        self,
        conditions: Sequence[Condition],
        counter_name: str,
    ) -> Optional[Tuple[int, int]]:
        residue_cases = []
        for condition in conditions or []:
            residue = self._condition_to_exact_residue(condition, counter_name)
            if residue is not None:
                residue_cases.append(residue)
                continue
            if self._condition_mentions_counter(condition, counter_name):
                return None
        if not residue_cases:
            return None
        first = residue_cases[0]
        if any(item != first for item in residue_cases[1:]):
            return None
        return first

    def _condition_to_exact_residue(
        self,
        condition: Condition,
        counter_name: str,
    ) -> Optional[Tuple[int, int]]:
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None
        if expr.operator not in {"INT_EQUAL", "INT_NOTEQUAL"}:
            return None

        is_equal = expr.operator == "INT_EQUAL"
        if condition.negated:
            is_equal = not is_equal

        bitand = None
        residue_value = None
        if self._raw_constant_value(expr.operands[0]) is not None:
            bitand = expr.operands[1]
            residue_value = self._raw_constant_value(expr.operands[0])
        elif self._raw_constant_value(expr.operands[1]) is not None:
            bitand = expr.operands[0]
            residue_value = self._raw_constant_value(expr.operands[1])
        if bitand is None or residue_value is None:
            return None
        if bitand.expr_type != ExpressionType.BINARY_OP or bitand.operator != "INT_AND" or len(bitand.operands) != 2:
            return None

        counter_expr = None
        mask_value = None
        if self._raw_constant_value(bitand.operands[0]) is not None and self._expr_matches_counter_placeholder(bitand.operands[1], counter_name):
            mask_value = self._raw_constant_value(bitand.operands[0])
            counter_expr = bitand.operands[1]
        elif self._raw_constant_value(bitand.operands[1]) is not None and self._expr_matches_counter_placeholder(bitand.operands[0], counter_name):
            mask_value = self._raw_constant_value(bitand.operands[1])
            counter_expr = bitand.operands[0]
        if counter_expr is None or mask_value is None:
            return None
        if mask_value <= 0 or (mask_value & (mask_value + 1)) != 0:
            return None

        modulus = int(mask_value) + 1
        residue = int(residue_value) & int(mask_value)
        if is_equal:
            return modulus, residue
        if modulus == 2:
            return modulus, residue ^ 1
        return None

    def _condition_mentions_counter(
        self,
        condition: Condition,
        counter_name: str,
    ) -> bool:
        expr = getattr(condition, "expression", None)
        if expr is None:
            return False
        return any(
            self._expr_matches_counter_placeholder(node, counter_name)
            for node in self._iter_expression_nodes(expr)
        )

    def _expression_is_unresolved(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return True
        if expr.expr_type in {ExpressionType.UNKNOWN, ExpressionType.CALL}:
            return True
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None and self._expression_is_unresolved(cond.expression):
                    return True
                if self._expression_is_unresolved(value):
                    return True
            return False
        return any(self._expression_is_unresolved(operand) for operand in getattr(expr, "operands", []) or [])

    def _expression_is_loop_invariant_bias(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        expr_type = getattr(expr, "expr_type", None)
        if expr_type in {ExpressionType.CONSTANT, ExpressionType.PARAMETER}:
            return True
        runtime_ref = getattr(expr, "runtime_ref", None)
        if runtime_ref is not None and not (
            bool(getattr(runtime_ref, "loop_invariant", False))
            or bool(getattr(runtime_ref, "is_loop_invariant", False))
        ):
            return False
        if expr_type in {ExpressionType.UNKNOWN, ExpressionType.CALL, ExpressionType.VARIABLE, ExpressionType.PHI}:
            return False
        operands = tuple(getattr(expr, "operands", ()) or ())
        if not operands:
            return False
        return all(self._expression_is_loop_invariant_bias(operand) for operand in operands)

    def _safe_expr_text(self, expr: Optional[Expression]) -> str:
        signature = _runtime_expression_signature(expr)
        return repr(signature)

    def _substitute_exact_expression(
        self,
        expr: Optional[Expression],
        needle: Expression,
        replacement: Expression,
    ) -> Optional[Expression]:
        if expr is None:
            return None
        if expr.structural_key() == needle.structural_key():
            return replacement

        if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
            left = self._substitute_exact_expression(expr.operands[0], needle, replacement)
            right = self._substitute_exact_expression(expr.operands[1], needle, replacement)
            if left is expr.operands[0] and right is expr.operands[1]:
                return expr
            rebuilt = Expression.binary_op(expr.operator, left, right)
            rebuilt.size = expr.size
            return rebuilt

        if expr.expr_type == ExpressionType.UNARY_OP and len(expr.operands) == 1:
            operand = self._substitute_exact_expression(expr.operands[0], needle, replacement)
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
                    condition_expr = self._substitute_exact_expression(
                        condition.expression,
                        needle,
                        replacement,
                    )
                    if condition_expr is not condition.expression:
                        new_condition = Condition(condition_expr, condition.negated)
                        changed = True
                new_value = self._substitute_exact_expression(value, needle, replacement)
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
                self._substitute_exact_expression(operand, needle, replacement)
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

    def _has_branch_accumulator_candidate(
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

    def _has_state_transition_loop_candidate(self, high_function) -> bool:
        return self._find_state_transition_loop_model(high_function, analysis=None) is not None

    def _try_summarize_state_transition_loop(
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

        if self._raw_constant_value(model.accumulator_init_expr) != 0:
            self._debug("Declined state-transition loop summary: accumulator seed is not zero")
            return None
        result_size = max(1, int(getattr(model.accumulator_phi_output, "getSize", lambda: 4)() or 4))
        state_size = max(1, int(getattr(model.state_phi_output, "getSize", lambda: 4)() or 4))
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
        loop_value = None
        if self._raw_constant_value(model.accumulator_delta_expr) == 1:
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
                )
                if latch_exit_returns is not None:
                    self._debug("Recovered latch-exit decrement accumulator sum summary")
                    return latch_exit_returns, "state_transition_loop_summary"
                self._debug(
                    "Declined state-transition loop summary: accumulator delta is not one "
                    "or supported state affine"
                )
                return None
        returns = [
            ReturnInfo(
                address=address,
                value=Expression.constant(0, result_size),
                conditions=[Condition(entry_guard_expr, True)],
                branch_index=0,
                **site_metadata,
            ),
            ReturnInfo(
                address=address,
                value=loop_value,
                conditions=[Condition(entry_guard_expr, False)],
                branch_index=10_200,
                **site_metadata,
            ),
        ]
        self._debug("Recovered state-transition loop summary")
        return returns, "state_transition_loop_summary"

    def _build_state_decrement_accumulator_sum_value(
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

    def _try_build_latch_exit_decrement_accumulator_sum_returns(
        self,
        *,
        function,
        model: StateTransitionLoopModel,
        analysis,
        result_size: int,
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
                value=Expression.constant(0, result_size),
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

    def _build_peeled_decrement_accumulator_sum_value(
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

    def _find_latch_exit_decrement_sum_witness_returns(
        self,
        *,
        analysis,
        model: StateTransitionLoopModel,
        result_size: int,
    ) -> Optional[Tuple[ReturnInfo, ReturnInfo]]:
        returns = tuple(getattr(analysis, "returns", ()) or ())
        if not returns:
            return None
        state = self._truncate_to_width(model.state_init_expr, result_size)
        base_anchor = None
        peeled_anchor = None
        for return_info in returns:
            value = self._canonicalize_expression(getattr(return_info, "value", None))
            conditions = tuple(getattr(return_info, "conditions", ()) or ())
            if (
                self._raw_constant_value(value) == 0
                and self._conditions_include_nonpositive_state(conditions, model.state_init_expr)
            ):
                base_anchor = return_info
            if (
                self._extract_affine_placeholder_term(value, state) == (1, 0)
                and self._conditions_include_positive_state(conditions, model.state_init_expr)
                and self._conditions_include_state_equals_one(conditions, model.state_init_expr)
            ):
                peeled_anchor = return_info
        if base_anchor is None or peeled_anchor is None:
            return None
        return base_anchor, peeled_anchor

    def _state_guard_is_placeholder_not_equal_one(
        self,
        state_guard: Optional[Expression],
        state_placeholder: Expression,
    ) -> bool:
        guard = self._canonicalize_expression(state_guard)
        if guard is None or guard.expr_type != ExpressionType.BINARY_OP or len(guard.operands) != 2:
            return False
        if guard.operator != "INT_NOTEQUAL":
            return False
        return self._binary_comparison_matches_affine_constant(
            guard,
            state_placeholder,
            coeff=1,
            bias=-1,
            constant=0,
        ) or self._binary_comparison_matches_affine_constant(
            guard,
            state_placeholder,
            coeff=1,
            bias=0,
            constant=1,
        )

    def _conditions_include_positive_state(
        self,
        conditions: Sequence[Condition],
        state_expr: Expression,
    ) -> bool:
        return any(self._condition_is_positive_state(condition, state_expr) for condition in conditions or ())

    def _conditions_include_nonpositive_state(
        self,
        conditions: Sequence[Condition],
        state_expr: Expression,
    ) -> bool:
        return any(self._condition_is_nonpositive_state(condition, state_expr) for condition in conditions or ())

    def _conditions_include_state_equals_one(
        self,
        conditions: Sequence[Condition],
        state_expr: Expression,
    ) -> bool:
        return any(self._condition_is_state_equals_one(condition, state_expr) for condition in conditions or ())

    def _condition_is_positive_state(
        self,
        condition: Condition,
        state_expr: Expression,
    ) -> bool:
        expr = self._canonicalize_expression(getattr(condition, "expression", None))
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return False
        if bool(getattr(condition, "negated", False)):
            return False
        if expr.operator == "INT_SLESS":
            left, right = expr.operands
            return self._raw_constant_value(left) == 0 and self._expr_matches_placeholder(right, state_expr)
        if expr.operator == "INT_SLESSEQUAL":
            left, right = expr.operands
            return self._raw_constant_value(left) == 1 and self._expr_matches_placeholder(right, state_expr)
        return False

    def _condition_is_nonpositive_state(
        self,
        condition: Condition,
        state_expr: Expression,
    ) -> bool:
        expr = self._canonicalize_expression(getattr(condition, "expression", None))
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return False
        negated = bool(getattr(condition, "negated", False))
        left, right = expr.operands
        if not negated and expr.operator == "INT_SLESSEQUAL":
            return self._expr_matches_placeholder(left, state_expr) and self._raw_constant_value(right) == 0
        if not negated and expr.operator == "INT_SLESS":
            return self._expr_matches_placeholder(left, state_expr) and self._raw_constant_value(right) == 1
        if negated and expr.operator == "INT_SLESS":
            return self._raw_constant_value(left) == 0 and self._expr_matches_placeholder(right, state_expr)
        return False

    def _condition_is_state_equals_one(
        self,
        condition: Condition,
        state_expr: Expression,
    ) -> bool:
        expr = self._canonicalize_expression(getattr(condition, "expression", None))
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return False
        negated = bool(getattr(condition, "negated", False))
        if expr.operator == "INT_EQUAL" and not negated:
            return self._binary_comparison_matches_affine_constant(
                expr,
                state_expr,
                coeff=1,
                bias=0,
                constant=1,
            ) or self._binary_comparison_matches_affine_constant(
                expr,
                state_expr,
                coeff=1,
                bias=-1,
                constant=0,
            )
        if expr.operator == "INT_NOTEQUAL" and negated:
            return self._binary_comparison_matches_affine_constant(
                expr,
                state_expr,
                coeff=1,
                bias=0,
                constant=1,
            ) or self._binary_comparison_matches_affine_constant(
                expr,
                state_expr,
                coeff=1,
                bias=-1,
                constant=0,
            )
        return False

    def _binary_comparison_matches_affine_constant(
        self,
        expr: Expression,
        base_expr: Expression,
        *,
        coeff: int,
        bias: int,
        constant: int,
    ) -> bool:
        if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return False
        left, right = expr.operands
        left_affine = self._extract_affine_placeholder_term(left, base_expr)
        right_affine = self._extract_affine_placeholder_term(right, base_expr)
        left_const = self._raw_constant_value(left)
        right_const = self._raw_constant_value(right)
        return (
            left_affine == (coeff, bias)
            and right_const == constant
        ) or (
            right_affine == (coeff, bias)
            and left_const == constant
        )

    def _expr_matches_placeholder(self, expr: Optional[Expression], placeholder: Expression) -> bool:
        expr = self._canonicalize_expression(expr)
        if expr is None:
            return False
        try:
            return expr.structural_key() == placeholder.structural_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return False

    def _find_state_transition_loop_model(
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

    def _try_build_latch_guarded_state_transition_model_for_phi(
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
        accumulator_phi, accumulator_output, accumulator_init, accumulator_delta, accumulator_placeholder = accumulator_model

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
        )

    def _try_build_state_transition_model_for_phi(
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
        accumulator_phi, accumulator_output, accumulator_init, accumulator_delta, accumulator_placeholder = accumulator_model

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
        )

    def _state_loop_phi_indices(self, header_block, phi_op) -> Optional[Tuple[int, Tuple[int, ...]]]:
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

    def _build_state_transition_expression(
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

    def _state_transition_predecessor_path_conditions(
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

    def _state_transition_path_conditions(
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

    def _combine_conditions_for_state_transition(
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

    def _state_transition_summary_cases(
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

    def _canonicalize_state_transition_condition(
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

    def _complete_default_state_transition_cases(
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

    def _combine_state_transition_condition_complements(
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

    def _condition_term_to_expression(self, expr: Expression, negated: bool) -> Expression:
        expr = self._canonicalize_expression(expr)
        if not negated:
            return expr
        result = Expression.unary_op("BOOL_NEGATE", expr)
        result.size = 1
        return self._canonicalize_expression(result)

    def _normalize_state_transition_condition_term(
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

    def _flatten_bool_and_expression(self, expr: Optional[Expression]) -> Tuple[Expression, ...]:
        if expr is None:
            return ()
        expr = self._canonicalize_expression(expr)
        if (
            expr.expr_type == ExpressionType.BINARY_OP
            and expr.operator == "BOOL_AND"
            and len(expr.operands) == 2
        ):
            return self._flatten_bool_and_expression(expr.operands[0]) + self._flatten_bool_and_expression(expr.operands[1])
        return (expr,)

    def _expression_contains_subexpression(
        self,
        expr: Optional[Expression],
        needle: Optional[Expression],
    ) -> bool:
        if expr is None or needle is None:
            return False
        try:
            needle_key = needle.structural_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return False
        for node in self._iter_expression_nodes(expr):
            try:
                if node.structural_key() == needle_key:
                    return True
            except (AttributeError, TypeError, ValueError, RecursionError):
                continue
        return False

    def _expressions_have_same_structural_key(
        self,
        left: Optional[Expression],
        right: Optional[Expression],
    ) -> bool:
        if left is None or right is None:
            return False
        try:
            return left.structural_key() == right.structural_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return False

    def _canonicalize_state_transition_value(
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

    def _collect_state_transition_loop_phi_ops(
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

    def _state_guard_proves_signed_positive_placeholder(
        self,
        state_guard: Optional[Expression],
        state_placeholder: Expression,
    ) -> bool:
        guard = self._canonicalize_expression(state_guard)
        if guard is None or guard.expr_type != ExpressionType.BINARY_OP or len(guard.operands) != 2:
            return False
        left, right = guard.operands
        placeholder_key = state_placeholder.structural_key()

        def is_placeholder(value: Expression) -> bool:
            try:
                return value.structural_key() == placeholder_key
            except (AttributeError, TypeError, ValueError, RecursionError):
                return False

        if guard.operator == "INT_SLESS":
            return self._raw_constant_value(left) == 0 and is_placeholder(right)
        if guard.operator == "INT_SLESSEQUAL":
            return self._raw_constant_value(left) == 1 and is_placeholder(right)
        return False

    def _normalize_state_transition_state_guard(
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

    def _positive_state_guard_expression(self, state_placeholder: Expression) -> Expression:
        zero = Expression.constant(0, max(1, int(getattr(state_placeholder, "size", 0) or 4)))
        guard = Expression.binary_op("INT_SLESS", zero, state_placeholder)
        guard.size = 1
        return self._canonicalize_expression(guard)

    def _find_state_loop_accumulator(
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
    ) -> Optional[Tuple[object, object, Expression, Expression, Expression]]:
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
                )
            )
        if not candidates:
            return None
        candidates.sort(key=lambda item: item[0], reverse=True)
        _priority, phi_op, phi_output, init_expr, delta_expr, placeholder = candidates[0]
        return phi_op, phi_output, init_expr, delta_expr, placeholder

    def _state_loop_accumulator_delta(
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

    def _extract_delta_from_possible_phi(
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
        if delta is None:
            return ()
        return (delta,)

    def _state_loop_accumulator_priority(
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

    def _state_transition_model_priority(
        self,
        model: StateTransitionLoopModel,
    ) -> Tuple[int, int, int]:
        return (
            1 if self._varnode_reaches_return(model.accumulator_phi_output) else 0,
            len(model.loop_blocks),
            max(1, int(getattr(model.state_phi_output, "getSize", lambda: 0)() or 0)),
        )

    def _collect_state_transition_loop_blocks(
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

    def _build_state_transition_loop_side_effect_profile(
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

    def _expression_mentions_placeholder(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
    ) -> bool:
        placeholder_key = placeholder.structural_key()
        for node in self._iter_expression_nodes(expr):
            try:
                if node.structural_key() == placeholder_key:
                    return True
            except (AttributeError, TypeError, ValueError, RecursionError):
                continue
        return False

    def _canonicalize_expression(self, expr: Optional[Expression]) -> Optional[Expression]:
        if expr is None:
            return None
        if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
            left = self._canonicalize_expression(expr.operands[0])
            right = self._canonicalize_expression(expr.operands[1])
            operator = expr.operator
            if operator in {
                "INT_ADD",
                "INT_MULT",
                "INT_AND",
                "INT_OR",
                "INT_XOR",
                "BOOL_AND",
                "BOOL_OR",
                "BOOL_XOR",
                "INT_EQUAL",
                "INT_NOTEQUAL",
            } and _runtime_expression_signature(right) < _runtime_expression_signature(left):
                left, right = right, left
            if left is expr.operands[0] and right is expr.operands[1]:
                return expr
            rebuilt = Expression.binary_op(operator, left, right)
            rebuilt.size = expr.size
            return rebuilt
        if expr.expr_type == ExpressionType.UNARY_OP and len(expr.operands) == 1:
            operand = self._canonicalize_expression(expr.operands[0])
            if expr.operator == "BOOL_NEGATE" and operand.expr_type == ExpressionType.UNARY_OP and operand.operator == "BOOL_NEGATE" and operand.operands:
                return self._canonicalize_expression(operand.operands[0])
            if expr.operator == "BOOL_NEGATE" and operand.expr_type == ExpressionType.BINARY_OP and len(operand.operands) == 2:
                if operand.operator == "INT_NOTEQUAL":
                    rebuilt = Expression.binary_op("INT_EQUAL", operand.operands[0], operand.operands[1])
                    rebuilt.size = operand.size or expr.size
                    return self._canonicalize_expression(rebuilt)
                if operand.operator == "INT_EQUAL":
                    rebuilt = Expression.binary_op("INT_NOTEQUAL", operand.operands[0], operand.operands[1])
                    rebuilt.size = operand.size or expr.size
                    return self._canonicalize_expression(rebuilt)
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
                    new_condition_expr = self._canonicalize_expression(condition.expression)
                    if new_condition_expr is not condition.expression:
                        new_condition = Condition(new_condition_expr, condition.negated)
                        changed = True
                new_value = self._canonicalize_expression(value)
                if new_value is not value:
                    changed = True
                branches.append((new_condition, new_value))
            branches.sort(
                key=lambda item: (
                    _runtime_expression_signature(item[0].expression) if item[0] is not None else ("none",),
                    bool(getattr(item[0], "negated", False)) if item[0] is not None else False,
                    _runtime_expression_signature(item[1]),
                )
            )
            if tuple(branches) != tuple(expr.value):
                changed = True
            if not changed:
                return expr
            rebuilt = Expression.phi(branches)
            rebuilt.size = expr.size
            return rebuilt
        return expr

    def _debug(self, message: str) -> None:
        if self.debug:
            print(f"[RecurrenceSummary] {message}")

    def _try_summarize_linear_self_recursion(self, function, high_function, analysis) -> Optional[Tuple[List[ReturnInfo], str]]:
        function_name = function.getName()
        recursive_returns = [
            ret for ret in (analysis.returns or [])
            if self._expression_contains_recursive_unknown(ret.value, function_name)
        ]
        if len(recursive_returns) != 1:
            self._debug(
                f"Declined '{function_name}': expected exactly one recursive return, found {len(recursive_returns)}"
            )
            return None

        base_returns = [
            ret for ret in (analysis.returns or [])
            if ret not in recursive_returns and self._is_constant_expression(ret.value)
        ]
        if len(base_returns) != 1:
            self._debug(
                f"Declined '{function_name}': expected exactly one constant base return, found {len(base_returns)}"
            )
            return None

        param_info = dict(analysis.parameters[0])
        if not self._parameter_can_be_counter(param_info):
            self._debug(f"Declined '{function_name}': parameter is not a scalar counter candidate")
            return None

        param_expr = self._parameter_expression(param_info)
        param_name = param_expr.name
        if not param_name:
            self._debug(f"Declined '{function_name}': parameter name is unavailable")
            return None
        recursive_ret = recursive_returns[0]
        base_ret = base_returns[0]

        lower_bound = self._infer_lower_bound_from_conditions(recursive_ret.conditions, param_name)
        if lower_bound is None:
            lower_bound = self._infer_lower_bound_from_base_conditions(base_ret.conditions, param_name)
        if lower_bound is None:
            self._debug(f"Declined '{function_name}': could not infer recursion/base split bound")
            return None

        self_call_ops = [
            op for op in self._iter_pcode_ops(high_function)
            if op.getMnemonic() == "CALL"
            and op.getNumInputs() >= 2
            and self._is_direct_self_call(op, function_name)
        ]
        if len(self_call_ops) != 1:
            self._debug(
                f"Declined '{function_name}': expected exactly one direct self-call, found {len(self_call_ops)}"
            )
            return None

        call_arg_expr = self.tracer.trace_varnode(self_call_ops[0].getInput(1), use_cache=False)
        step = self._extract_unit_step_from_call_argument(call_arg_expr, param_name)
        if step != -1:
            self._debug(
                f"Declined '{function_name}': recursive call argument is not a unit decrement "
                f"({call_arg_expr.to_string()})"
            )
            return None

        addend_expr = self._extract_addend_expression(recursive_ret.value, function_name)
        if addend_expr is None:
            self._debug(
                f"Declined '{function_name}': could not isolate non-recursive addend from "
                f"{recursive_ret.value.to_string()}"
            )
            return None

        affine = self._extract_affine_term(addend_expr, param_name)
        if affine is None:
            self._debug(
                f"Declined '{function_name}': addend is not affine in the counter "
                f"({addend_expr.to_string()})"
            )
            return None
        coeff, bias = affine

        base_value = self._constant_value(base_ret.value)
        if base_value is None:
            self._debug(f"Declined '{function_name}': base value is not a concrete constant")
            return None

        recursive_value = self._build_closed_form(
            param_expr=param_expr,
            lower_bound=lower_bound,
            coeff=coeff,
            bias=bias,
            base_value=base_value,
        )
        if recursive_value is None:
            self._debug(f"Declined '{function_name}': failed to construct closed-form summary")
            return None

        recursive_conditions = self._build_recursive_conditions(param_expr, lower_bound)
        base_conditions = self._build_base_conditions(param_expr, lower_bound)
        if recursive_conditions is None or base_conditions is None:
            self._debug(f"Declined '{function_name}': failed to build guard conditions for summary")
            return None

        summarized_returns = [
            ReturnInfo(
                address=base_ret.address,
                value=Expression.constant(base_value, recursive_value.size or param_expr.size or 4),
                conditions=base_conditions,
                branch_index=base_ret.branch_index,
                pcode_identity=base_ret.pcode_identity,
                pcode_order=base_ret.pcode_order,
                pcode_time=base_ret.pcode_time,
                pcode_op_ref=getattr(base_ret, "pcode_op_ref", None),
                return_value_pcode_op_refs=tuple(
                    getattr(base_ret, "return_value_pcode_op_refs", ()) or ()
                ),
            ),
            ReturnInfo(
                address=recursive_ret.address,
                value=recursive_value,
                conditions=recursive_conditions,
                branch_index=recursive_ret.branch_index,
                pcode_identity=recursive_ret.pcode_identity,
                pcode_order=recursive_ret.pcode_order,
                pcode_time=recursive_ret.pcode_time,
                pcode_op_ref=getattr(recursive_ret, "pcode_op_ref", None),
                return_value_pcode_op_refs=tuple(
                    getattr(recursive_ret, "return_value_pcode_op_refs", ()) or ()
                ),
            ),
        ]

        self._debug(
            f"Recovered linear self-recursive summary for '{function_name}' "
            f"(lower_bound={lower_bound}, coeff={coeff}, bias={bias}, base={base_value})"
        )
        return summarized_returns, "linear_self_recursion_summary"

    def _try_summarize_readonly_pointer_reduction(
        self,
        function,
        high_function,
        analysis,
    ) -> Optional[Tuple[List[ReturnInfo], str]]:
        if analysis is None or not analysis.returns:
            return None
        if getattr(getattr(analysis, "effect_summary", None), "effects", None):
            self._debug("Declined readonly reduction summary: function mutates memory")
            return None

        pointer_param, count_param = self._infer_readonly_pointer_reduction_parameters(
            analysis,
            high_function,
        )
        if pointer_param is None or count_param is None:
            self._debug("Declined readonly reduction summary: pointer/count parameters not identified")
            return None

        viable_candidates = []
        for counter_signed in (True, False):
            broad_positive_conditions = self._readonly_reduction_positive_conditions(
                analysis,
                pointer_param,
                count_param,
                signed_counter=counter_signed,
            )
            if ConditionSimplifier.object_centric_is_contradiction(broad_positive_conditions):
                continue
            accumulator_proofs = self._collect_readonly_sum_accumulator_proofs(
                high_function,
                analysis,
                pointer_param,
                count_param,
                counter_signed=counter_signed,
                positive_conditions=broad_positive_conditions,
            )
            if not accumulator_proofs:
                continue

            for accumulator_proof in accumulator_proofs:
                positive_conditions = self._readonly_reduction_positive_conditions(
                    analysis,
                    pointer_param,
                    count_param,
                    loop_start_index=int(accumulator_proof.start_index),
                    signed_counter=counter_signed,
                )
                if ConditionSimplifier.object_centric_is_contradiction(positive_conditions):
                    continue
                overlapping_positive_returns = self._readonly_reduction_replaceable_positive_returns(
                    analysis,
                    pointer_param,
                    count_param,
                    broad_positive_conditions,
                    positive_conditions,
                    expected_signed=counter_signed,
                    declared_signedness=self._analysis_parameter_declared_signedness(
                        analysis,
                        count_param,
                    ),
                    accumulator_proof=accumulator_proof,
                )
                if not overlapping_positive_returns:
                    synthetic_positive_return = self._readonly_synthetic_positive_return_from_proof(
                        accumulator_proof,
                        positive_conditions,
                        result_size=self._readonly_reduction_result_size(
                            analysis,
                            positive_conditions=positive_conditions,
                        ),
                    )
                    if synthetic_positive_return is None:
                        continue
                    if not self._readonly_region_returns_are_subsumable_by_proof(
                        analysis,
                        pointer_param,
                        count_param,
                        positive_conditions,
                        accumulator_proof,
                    ):
                        continue
                    overlapping_positive_returns = [synthetic_positive_return]
                if not overlapping_positive_returns:
                    continue
                viable_candidates.append(
                    (
                        counter_signed,
                        broad_positive_conditions,
                        accumulator_proof,
                        positive_conditions,
                        overlapping_positive_returns,
                    )
                )

        if not viable_candidates:
            self._debug("Declined readonly reduction summary: no proven positive-region counter signedness candidate")
            return None

        selected_candidate = self._select_readonly_reduction_candidate(
            analysis,
            pointer_param,
            count_param,
            viable_candidates,
        )
        if selected_candidate is None:
            self._debug(
                "Declined readonly reduction summary: positive-region counter/proof candidate remains ambiguous"
            )
            return None

        (
            counter_signed,
            broad_positive_conditions,
            accumulator_proof,
            positive_conditions,
            overlapping_positive_returns,
        ) = selected_candidate
        normalized_candidate = self._normalize_readonly_reduction_candidate(
            analysis,
            pointer_param,
            count_param,
            broad_positive_conditions,
            positive_conditions,
            counter_signed=counter_signed,
            accumulator_proof=accumulator_proof,
            overlapping_positive_returns=overlapping_positive_returns,
        )
        if normalized_candidate is None:
            return None
        (
            preliminary_proof,
            positive_conditions,
            overlapping_positive_returns,
            result_size,
            exact_return_candidates,
            initial_exact_witnesses,
            semantic_witnesses,
        ) = normalized_candidate
        summary_positive_conditions = list(positive_conditions)
        preserved_exact_positive_returns: List[ReturnInfo] = []
        retained_positive_returns: List[ReturnInfo] = []
        preserved_exact_counts: set[int] = set()
        ordered_overlapping_positive_returns = self._order_readonly_exact_positive_returns(
            overlapping_positive_returns,
            analysis,
            pointer_param,
            count_param,
            preliminary_proof,
        )
        for ret in ordered_overlapping_positive_returns:
            exact_count = self._exact_counter_value_from_conditions(
                ret.conditions or [],
                str(count_param.get("name") or ""),
            )
            if exact_count is None:
                retained_positive_returns.append(ret)
                continue
            absorbable = self._readonly_exact_positive_return_is_absorbable(
                analysis,
                pointer_param,
                ret,
                preliminary_proof,
                exact_count=int(exact_count),
            )
            prefix_score = self._readonly_exact_positive_return_prefix_score(
                analysis,
                pointer_param,
                ret,
                preliminary_proof,
                exact_count=int(exact_count),
            )
            if prefix_score <= 0 and absorbable:
                retained_positive_returns.append(ret)
                continue
            if not self._readonly_exact_count_region_is_fully_covered_by_return(
                ret,
                positive_conditions,
                count_param,
                int(exact_count),
            ):
                return None
            preserved_exact_positive_returns.append(ret)
            preserved_exact_counts.add(int(exact_count))
            summary_positive_conditions.append(
                Condition(
                    Expression.binary_op(
                        "INT_EQUAL",
                        summary_count_expr := self._parameter_expression(count_param),
                        Expression.constant(int(exact_count), summary_count_expr.size or 4),
                    ),
                    True,
                )
            )
        ordered_analysis_returns = self._order_readonly_exact_positive_returns(
            analysis.returns or [],
            analysis,
            pointer_param,
            count_param,
            preliminary_proof,
        )
        for ret in ordered_analysis_returns:
            if ret in preserved_exact_positive_returns:
                continue
            if not self._return_overlaps_conditions(ret, positive_conditions):
                continue
            exact_count = self._exact_counter_value_from_conditions(
                ret.conditions or [],
                str(count_param.get("name") or ""),
            )
            if exact_count is None or int(exact_count) in preserved_exact_counts:
                continue
            absorbable = self._readonly_exact_positive_return_is_absorbable(
                analysis,
                pointer_param,
                ret,
                preliminary_proof,
                exact_count=int(exact_count),
            )
            prefix_score = self._readonly_exact_positive_return_prefix_score(
                analysis,
                pointer_param,
                ret,
                preliminary_proof,
                exact_count=int(exact_count),
            )
            if prefix_score <= 0 and absorbable:
                continue
            if not self._readonly_exact_count_region_is_fully_covered_by_return(
                ret,
                positive_conditions,
                count_param,
                int(exact_count),
            ):
                return None
            preserved_exact_positive_returns.append(ret)
            preserved_exact_counts.add(int(exact_count))
            summary_positive_conditions.append(
                Condition(
                    Expression.binary_op(
                        "INT_EQUAL",
                        summary_count_expr := self._parameter_expression(count_param),
                        Expression.constant(int(exact_count), summary_count_expr.size or 4),
                    ),
                    True,
                )
            )
        if retained_positive_returns:
            overlapping_positive_returns = retained_positive_returns
        if not overlapping_positive_returns:
            return None
        preserved_returns = [
            ret for ret in (analysis.returns or [])
            if ret not in overlapping_positive_returns and ret not in preserved_exact_positive_returns
        ]
        if not preserved_returns and not overlapping_positive_returns:
            return None
        for ret in preserved_returns:
            if ret not in exact_return_candidates:
                exact_return_candidates.append(ret)
        for ret in preserved_exact_positive_returns:
            if ret not in exact_return_candidates:
                exact_return_candidates.append(ret)

        summary_pointer_expr = self._parameter_expression(pointer_param)
        summary_count_expr = self._parameter_expression(count_param)
        exact_return_witnesses = self._extract_readonly_reduction_exact_witnesses(
            analysis,
            pointer_param,
            count_param,
            exact_return_candidates,
            preliminary_proof,
        )
        accumulator_proof = preliminary_proof.with_runtime_evidence(
            limit_expr=summary_count_expr,
            result_size=result_size,
            loop_body_witnesses=semantic_witnesses,
            exact_return_witnesses=exact_return_witnesses,
            guard_constraints=summary_positive_conditions,
            signed_counter=counter_signed,
        )
        reduction_ref = accumulator_proof.lower_to_readonly_reduction_ref()
        if reduction_ref is None:
            self._debug("Declined readonly reduction summary: accumulator proof cannot lower to READONLY_SUM")
            return None
        preserved_returns = [
            ret for ret in preserved_returns
            if not self._readonly_preserved_summary_is_subsumed_by_replacement(
                analysis,
                pointer_param,
                count_param,
                ret,
                summary_positive_conditions,
                positive_conditions,
                accumulator_proof,
                reduction_ref,
            )
            and not self._readonly_unresolved_preserved_return_is_subsumed_by_replacement(
                ret,
                summary_positive_conditions,
                accumulator_proof,
                reduction_ref,
            )
        ]
        summary_expr = Expression.intrinsic(
            "READONLY_SUM",
            [summary_pointer_expr, summary_count_expr],
            size=result_size,
            runtime_ref=reduction_ref,
            opcode=READONLY_SUM_OPCODE,
        )
        positive_anchor = overlapping_positive_returns[0]
        summary_return = ReturnInfo(
            address=positive_anchor.address,
            value=summary_expr,
            conditions=list(summary_positive_conditions),
            branch_index=10_200,
            pcode_identity=positive_anchor.pcode_identity,
            pcode_order=positive_anchor.pcode_order,
            pcode_time=positive_anchor.pcode_time,
            pcode_op_ref=getattr(positive_anchor, "pcode_op_ref", None),
            return_value_pcode_op_refs=tuple(
                getattr(positive_anchor, "return_value_pcode_op_refs", ()) or ()
            ),
        )
        summarized_returns: List[ReturnInfo] = []
        inserted_summary = False
        for preserved_return in preserved_returns:
            if (
                not inserted_summary
                and self._readonly_summary_return_should_precede_preserved_return(
                    summary_return,
                    preserved_return,
                    reduction_ref,
                )
            ):
                summarized_returns.append(summary_return)
                inserted_summary = True
            summarized_returns.append(preserved_return)
        if not inserted_summary:
            summarized_returns.append(summary_return)
        summarized_returns.extend(preserved_exact_positive_returns)
        summarized_returns = self._synthesize_exact_returns_from_readonly_witnesses(
            analysis,
            pointer_param,
            count_param,
            broad_positive_conditions=broad_positive_conditions,
            summary_positive_conditions=summary_positive_conditions,
            existing_returns=summarized_returns,
            reduction_ref=reduction_ref,
            result_size=result_size,
        )
        summarized_returns = self._synthesize_bounded_prefix_exact_returns(
            analysis,
            high_function,
            pointer_param,
            count_param,
            counter_signed=counter_signed,
            broad_positive_conditions=broad_positive_conditions,
            existing_returns=summarized_returns,
            result_size=result_size,
        )
        self._debug(f"Readonly reduction summary return count after bounded synthesis: {len(summarized_returns)}")
        self._debug(
            f"Recovered readonly pointer-reduction summary for '{function.getName()}' "
            f"(pointer={pointer_param.get('name')}, count={count_param.get('name')}, "
            f"stride={accumulator_proof.stride}, element_size={accumulator_proof.element_size})"
        )
        return summarized_returns, "readonly_pointer_reduction_summary"

    def _select_readonly_reduction_candidate(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        candidates: Sequence[
            Tuple[bool, List[Condition], ReductionAccumulatorProof, List[Condition], List[ReturnInfo]]
        ],
    ) -> Optional[Tuple[bool, List[Condition], ReductionAccumulatorProof, List[Condition], List[ReturnInfo]]]:
        """Choose the proof that best explains the object-level return terms.

        Ghidra sometimes assigns a wider or unsigned local declaration to a
        counter whose loop body is proven through a narrower or signed P-code
        view.  The declaration is useful as a tie-breaker, but the stronger
        evidence is whether a proof's seed/start contract explains the
        materialized return-site loads and the proven return value site.
        """

        candidates = tuple(candidates or ())
        if not candidates:
            return None
        if len(candidates) == 1:
            return candidates[0]

        declared_signedness = self._analysis_parameter_declared_signedness(
            analysis,
            count_param,
        )
        scored = [
            (
                self._readonly_reduction_candidate_score(
                    analysis,
                    pointer_param,
                    count_param,
                    candidate,
                    declared_signedness=declared_signedness,
                ),
                index,
                candidate,
            )
            for index, candidate in enumerate(candidates)
        ]
        scored.sort(key=lambda item: item[0], reverse=True)
        best_score = scored[0][0]
        tied = [item for item in scored if item[0] == best_score]
        if len(tied) == 1:
            return tied[0][2]

        tied_contract_keys = {
            candidate[2].readonly_term_sequence_contract_key()
            for _score, _index, candidate in tied
        }
        tied_counter_signedness = {bool(candidate[0]) for _score, _index, candidate in tied}
        if len(tied_counter_signedness) > 1 and declared_signedness is None:
            return None
        if len(tied_contract_keys) == 1 and None not in tied_contract_keys:
            first_conditions = tied[0][2][3]
            if all(
                self._conditions_equivalent_object_centric(
                    first_conditions,
                    candidate[3],
                )
                for _score, _index, candidate in tied[1:]
            ):
                return min(tied, key=lambda item: item[1])[2]
        return None

    def _readonly_reduction_candidate_score(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        candidate: Tuple[bool, List[Condition], ReductionAccumulatorProof, List[Condition], List[ReturnInfo]],
        *,
        declared_signedness: Optional[bool],
    ) -> Tuple[int, int, int, int, int, int]:
        counter_signed, _broad_conditions, proof, positive_conditions, overlapping_returns = candidate
        contract_score = 0
        region_site_score = 0
        anchor_score = 0
        for ret in overlapping_returns or ():
            if self._readonly_materialized_positive_return_matches_accumulator_contract(
                analysis,
                pointer_param,
                count_param,
                ret,
                proof,
            ):
                contract_score += 100
            anchor_count = self._readonly_positive_return_accumulator_anchor_count(
                analysis,
                pointer_param,
                count_param,
                ret,
                proof,
            )
            if anchor_count is not None:
                anchor_score += 20 + min(16, int(anchor_count))
            if self._readonly_return_region_value_is_proven(
                ret,
                positive_conditions,
                proof,
            ):
                region_site_score += 10
        score_fn = getattr(proof, "readonly_term_sequence_specificity_score", None)
        try:
            seed_score = max(0, int(score_fn())) if callable(score_fn) else 0
        except (TypeError, ValueError):
            seed_score = 0
        return_site_evidence_score = (
            30
            if bool(getattr(proof, "return_region_value_proven", False))
            else 0
        )
        return_site_evidence_score += min(16, len(tuple(getattr(proof, "return_op_refs", ()) or ())))
        return_site_evidence_score += min(16, len(tuple(getattr(proof, "return_value_op_refs", ()) or ())))
        declared_score = (
            1
            if declared_signedness is not None and bool(counter_signed) == bool(declared_signedness)
            else 0
        )
        return (
            int(region_site_score),
            int(return_site_evidence_score),
            int(seed_score),
            int(anchor_score),
            int(contract_score),
            int(declared_score),
        )

    def _synthesize_exact_returns_from_readonly_witnesses(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        *,
        broad_positive_conditions: Sequence[Condition],
        summary_positive_conditions: Sequence[Condition],
        existing_returns: Sequence[ReturnInfo],
        reduction_ref: ReadonlyReductionRef,
        result_size: int,
    ) -> List[ReturnInfo]:
        synthesized = list(existing_returns or ())
        witnesses = tuple(getattr(reduction_ref, "semantic_witnesses", ()) or ())
        if not witnesses:
            return synthesized

        anchor = next(iter(synthesized), None)
        for witness in witnesses:
            exact_count = int(getattr(witness, "exact_count", 0) or 0)
            if exact_count <= 0 or exact_count > 16:
                continue
            if self._conditions_allow_counter_value(summary_positive_conditions, count_param, exact_count):
                continue
            if not self._conditions_allow_counter_value(broad_positive_conditions, count_param, exact_count):
                continue
            terms = tuple(getattr(witness, "terms", ()) or ())
            if not self._readonly_witness_terms_form_scalar_prefix(
                terms,
                exact_count=exact_count,
                result_size=result_size,
            ):
                continue
            existing_count_returns = [
                ret for ret in synthesized
                if self._conditions_imply_counter_value(ret.conditions or [], count_param, exact_count)
            ]
            if any(
                self._readonly_exact_positive_return_prefix_score(
                    analysis,
                    pointer_param,
                    ret,
                    None,
                    exact_count=exact_count,
                )
                > 0
                for ret in existing_count_returns
            ):
                continue
            if existing_count_returns:
                self._debug(
                    "Skipped exact readonly witness synthesis: existing exact-count return "
                    f"already materializes count={exact_count}"
                )
                continue

            value = self._build_readonly_reduction_expression_from_terms(
                pointer_param,
                terms,
                constant_bias=int(getattr(reduction_ref, "constant_bias", 0) or 0),
                result_size=result_size,
            )
            if value is None:
                continue

            conditions = ConditionSimplifier.simplify_conditions_object_centric(
                list(broad_positive_conditions or []) + [self._counter_equality_condition(count_param, exact_count)]
            )
            if ConditionSimplifier.object_centric_is_contradiction(conditions):
                continue

            site_anchor = anchor or next(iter(existing_returns or ()), None)
            synthesized.append(
                ReturnInfo(
                    address=getattr(site_anchor, "address", "readonly_exact_witness") if site_anchor is not None else "readonly_exact_witness",
                    value=value,
                    conditions=conditions,
                    branch_index=10_400 + exact_count,
                    pcode_identity=getattr(site_anchor, "pcode_identity", None) if site_anchor is not None else None,
                    pcode_order=getattr(site_anchor, "pcode_order", None) if site_anchor is not None else None,
                    pcode_time=getattr(site_anchor, "pcode_time", None) if site_anchor is not None else None,
                    pcode_op_ref=getattr(site_anchor, "pcode_op_ref", None) if site_anchor is not None else None,
                    return_value_pcode_op_refs=tuple(
                        getattr(site_anchor, "return_value_pcode_op_refs", ()) or ()
                    ) if site_anchor is not None else (),
                )
            )
            self._debug(
                "Synthesized exact readonly return from semantic witness "
                f"for count={exact_count} terms={[int(term.byte_offset) for term in terms]}"
            )
        return synthesized

    def _readonly_witness_terms_form_scalar_prefix(
        self,
        terms: Sequence[ReadonlyReductionTermRef],
        *,
        exact_count: int,
        result_size: int,
    ) -> bool:
        if exact_count <= 0 or len(tuple(terms or ())) != int(exact_count):
            return False
        access_size = max(1, int(result_size or 0))
        sorted_terms = tuple(sorted(terms or (), key=lambda term: (int(term.byte_offset), int(term.access_size))))
        expected_offsets = [index * access_size for index in range(int(exact_count))]
        return (
            [int(term.byte_offset) for term in sorted_terms] == expected_offsets
            and all(max(1, int(term.access_size or 0)) == access_size for term in sorted_terms)
        )

    def _readonly_synthetic_positive_return_from_proof(
        self,
        accumulator_proof: Optional[ReductionAccumulatorProof],
        positive_conditions: Sequence[Condition],
        *,
        result_size: int,
    ) -> Optional[ReturnInfo]:
        """Create a positive-region anchor from object-centric return proof.

        Some decompiler/P-code expansions fail to materialize the return value
        candidate for the loop body even though the accumulator proof has
        concrete return-site def-use evidence.  In that case the object proof is
        stronger than the missing return case: it identifies the accumulator,
        its memory terms, and the return op/value refs.  The synthetic return is
        only a carrier for conditions and site identity; the caller immediately
        replaces its value with the structured READONLY_SUM summary.
        """

        if accumulator_proof is None:
            return None
        if not bool(getattr(accumulator_proof, "return_region_value_proven", False)):
            return None
        site_refs = tuple(getattr(accumulator_proof, "return_op_refs", ()) or ()) + tuple(
            getattr(accumulator_proof, "return_value_op_refs", ()) or ()
        )
        if not site_refs:
            return None
        site_ref = site_refs[0]
        address_offset = getattr(site_ref, "address_offset", None)
        seq_time = getattr(site_ref, "seq_time", None)
        seq_order = getattr(site_ref, "seq_order", None)
        address = (
            f"{int(address_offset):08x}"
            if address_offset is not None
            else "synthetic_readonly_positive"
        )
        pcode_identity = (
            f"{address}:t{int(seq_time)}"
            if seq_time is not None
            else f"{address}:synthetic_readonly_positive"
        )
        return ReturnInfo(
            address=address,
            value=Expression.constant(0, size=max(1, int(result_size or 0))),
            conditions=list(positive_conditions or []),
            branch_index=10_250,
            pcode_identity=pcode_identity,
            pcode_order=None if seq_order is None else int(seq_order),
            pcode_time=None if seq_time is None else int(seq_time),
            pcode_op_ref=site_ref,
        )

    def _synthesize_bounded_prefix_exact_returns(
        self,
        analysis,
        high_function,
        pointer_param: dict,
        count_param: dict,
        *,
        counter_signed: bool,
        broad_positive_conditions: Sequence[Condition],
        existing_returns: Sequence[ReturnInfo],
        result_size: int,
    ) -> List[ReturnInfo]:
        synthesized = list(existing_returns or ())
        proofs = self._collect_readonly_prefix_accumulator_proofs(
            analysis,
            high_function,
            pointer_param,
            count_param,
            counter_signed=counter_signed,
            positive_conditions=broad_positive_conditions,
            result_size=result_size,
        )
        if not proofs:
            self._debug("Skipped bounded prefix exact synthesis: no prefix accumulator proofs")
            return synthesized
        self._debug(f"Bounded prefix exact synthesis: considering {len(proofs)} prefix proof(s)")
        count_name = str(count_param.get("name") or "")
        existing_exact_counts = {
            int(exact_count)
            for ret in synthesized
            for exact_count in [self._exact_counter_value_from_conditions(ret.conditions or [], count_name)]
            if exact_count is not None and int(exact_count) > 0
        }
        for proof in proofs:
            anchor_returns = []
            bounded_region_anchors: List[Tuple[ReturnInfo, List[Condition]]] = []
            max_upper_bound = None
            for ret in getattr(analysis, "returns", None) or ():
                exact_count = self._exact_counter_value_from_conditions(ret.conditions or [], count_name)
                exact_count_was_inferred_from_terms = False
                if exact_count is None:
                    extracted = self._extract_readonly_return_terms_and_bias(
                        analysis,
                        pointer_param,
                        ret,
                        proof,
                    )
                    if extracted is not None:
                        extracted_terms, _constant_bias = extracted
                        exact_count = self._infer_exact_count_from_readonly_terms(
                            ret.conditions or [],
                            extracted_terms,
                            count_param,
                            proof,
                        )
                        if exact_count is None:
                            candidate_count = len(tuple(extracted_terms or ()))
                            expected_terms = proof.full_terms_for_count_value(int(candidate_count))
                            if (
                                candidate_count > 0
                                and expected_terms is not None
                                and tuple(term.stable_key() for term in extracted_terms) == tuple(
                                    term.stable_key() for term in expected_terms
                                )
                                and self._conditions_imply_counter_value(
                                    ret.conditions or [],
                                    count_param,
                                    int(candidate_count),
                                )
                            ):
                                exact_count = int(candidate_count)
                                exact_count_was_inferred_from_terms = True
                        else:
                            exact_count_was_inferred_from_terms = True
                upper_bound = self._infer_upper_bound_from_conditions(ret.conditions or [], count_name)
                if exact_count is not None and int(exact_count) > 0:
                    if not exact_count_was_inferred_from_terms and not self._readonly_positive_return_proves_count_value(
                        analysis,
                        pointer_param,
                        count_param,
                        ret,
                        proof,
                        count_value=int(exact_count),
                    ):
                        continue
                    if upper_bound is None or int(upper_bound) < int(exact_count):
                        continue
                    anchor_returns.append(ret)
                    if int(upper_bound) > int(exact_count):
                        bounded_conditions = self._bounded_prefix_region_conditions_from_exact_anchor(
                            ret.conditions or [],
                            count_param,
                            exact_count=int(exact_count),
                            upper_bound=int(upper_bound),
                        )
                        if bounded_conditions is not None:
                            bounded_region_anchors.append((ret, bounded_conditions))
                    max_upper_bound = int(upper_bound) if max_upper_bound is None else max(max_upper_bound, int(upper_bound))
                    continue
                if upper_bound is None or int(upper_bound) <= 0 or int(upper_bound) > 16:
                    continue
                if not self._readonly_return_region_value_is_proven(
                    ret,
                    tuple(getattr(proof, "guard_constraints", ()) or broad_positive_conditions or ()),
                    proof,
                ):
                    continue
                if any(proof.full_terms_for_count_value(count_value) is None for count_value in range(1, int(upper_bound) + 1)):
                    continue
                anchor_returns.append(ret)
                bounded_region_anchors.append((ret, list(ret.conditions or [])))
                max_upper_bound = int(upper_bound) if max_upper_bound is None else max(max_upper_bound, int(upper_bound))
            if not anchor_returns or max_upper_bound is None or max_upper_bound <= 0 or max_upper_bound > 16:
                self._debug("Skipped bounded prefix exact synthesis: no bounded/exact anchor returns")
                continue
            anchor = anchor_returns[0]
            synthesis_base_conditions = (
                list(bounded_region_anchors[0][1])
                if bounded_region_anchors
                else list(anchor.conditions or broad_positive_conditions or [])
            )
            added_for_anchor: Dict[int, ReturnInfo] = {}
            for count_value in range(1, max_upper_bound + 1):
                if count_value in existing_exact_counts and not bounded_region_anchors:
                    continue
                terms = proof.full_terms_for_count_value(count_value)
                if terms is None:
                    continue
                value = self._build_readonly_reduction_expression_from_terms(
                    pointer_param,
                    terms,
                    constant_bias=int(getattr(proof, "constant_bias", 0) or 0),
                    result_size=result_size,
                )
                if value is None:
                    continue
                conditions = list(synthesis_base_conditions)
                conditions.append(self._counter_equality_condition(count_param, count_value))
                exact_return = ReturnInfo(
                    address=anchor.address,
                    value=value,
                    conditions=conditions,
                    branch_index=10_300 + count_value,
                    pcode_identity=anchor.pcode_identity,
                    pcode_order=anchor.pcode_order,
                    pcode_time=anchor.pcode_time,
                    pcode_op_ref=getattr(anchor, "pcode_op_ref", None),
                    return_value_pcode_op_refs=tuple(
                        getattr(anchor, "return_value_pcode_op_refs", ()) or ()
                    ),
                )
                if bounded_region_anchors:
                    insert_at = self._bounded_prefix_exact_insert_index(
                        synthesized,
                        bounded_region_anchors,
                    )
                    synthesized.insert(insert_at + len(added_for_anchor), exact_return)
                else:
                    synthesized.append(exact_return)
                self._debug(
                    "Synthesized bounded prefix exact return "
                    f"for count={count_value} from proof start_index={proof.start_index} "
                    f"terms={[term.byte_offset for term in terms]}"
                )
                added_for_anchor[int(count_value)] = exact_return
                existing_exact_counts.add(count_value)
            for bounded_anchor, bounded_conditions in bounded_region_anchors:
                exact_cover = [
                    exact_return
                    for count_value, exact_return in sorted(added_for_anchor.items())
                    if self._conditions_allow_counter_value(
                        bounded_conditions,
                        count_param,
                        int(count_value),
                    )
                ]
                if exact_cover and (
                    self._readonly_region_is_covered_by_returns(
                        bounded_conditions,
                        exact_cover,
                    )
                    or self._readonly_bounded_counter_region_is_covered_by_exact_returns(
                        bounded_conditions,
                        exact_cover,
                        count_param,
                    )
                ):
                    synthesized = [
                        ret for ret in synthesized
                        if ret is not bounded_anchor
                        and not self._conditions_equivalent_object_centric(
                            ret.conditions or [],
                            bounded_conditions,
                        )
                    ]
        return synthesized

    def _bounded_prefix_exact_insert_index(
        self,
        existing_returns: Sequence[ReturnInfo],
        bounded_region_anchors: Sequence[Tuple[ReturnInfo, Sequence[Condition]]],
    ) -> int:
        for index, existing in enumerate(existing_returns or []):
            if any(existing is bounded_anchor for bounded_anchor, _ in bounded_region_anchors or []):
                return index
        for index, existing in enumerate(existing_returns or []):
            if any(
                self._conditions_equivalent_object_centric(existing.conditions or [], bounded_conditions)
                for _bounded_anchor, bounded_conditions in bounded_region_anchors or []
            ):
                return index
        return len(existing_returns or [])

    def _conditions_equivalent_object_centric(
        self,
        left: Sequence[Condition],
        right: Sequence[Condition],
    ) -> bool:
        left_set = ConditionConstraintSet.from_conditions(left or [])
        right_set = ConditionConstraintSet.from_conditions(right or [])
        if left_set.implies_all(right or []) and right_set.implies_all(left or []):
            return True
        return self._conditions_imply_with_smt(left or [], right or []) and self._conditions_imply_with_smt(
            right or [],
            left or [],
        )

    def _conditions_imply_with_smt(
        self,
        source: Sequence[Condition],
        target: Sequence[Condition],
    ) -> bool:
        for condition in target or []:
            unsat = ConditionSMTOracle.conjunction_is_unsat(
                list(source or []) + [condition.negate()]
            )
            if unsat is not True:
                return False
        return True

    def _readonly_bounded_counter_region_is_covered_by_exact_returns(
        self,
        region_conditions: Sequence[Condition],
        exact_returns: Sequence[ReturnInfo],
        count_param: dict,
    ) -> bool:
        count_name = str(count_param.get("name") or "")
        if not count_name:
            return False
        upper_bound = self._infer_upper_bound_from_conditions(region_conditions or [], count_name)
        if upper_bound is None or int(upper_bound) <= 0 or int(upper_bound) > 16:
            return False
        saw_reachable_count = False
        for count_value in range(1, int(upper_bound) + 1):
            if not self._conditions_allow_counter_value(region_conditions or [], count_param, int(count_value)):
                continue
            saw_reachable_count = True
            if not any(
                self._conditions_imply_counter_value(ret.conditions or [], count_param, int(count_value))
                and self._readonly_exact_count_region_is_fully_covered_by_return(
                    ret,
                    region_conditions,
                    count_param,
                    int(count_value),
                )
                for ret in exact_returns or []
            ):
                return False
        return saw_reachable_count

    def _bounded_prefix_region_conditions_from_exact_anchor(
        self,
        conditions: Sequence[Condition],
        count_param: dict,
        *,
        exact_count: int,
        upper_bound: int,
    ) -> Optional[List[Condition]]:
        """Recover the bounded prefix region around an exact materialized witness.

        Some compilers expose only one exact return from a bounded prefix loop
        after PHI expansion, e.g. count==1 under 0<count<4.  The exact-count
        predicate is a witness selector, not part of the enclosing bounded
        region.  Drop only object-identified singleton counter predicates for
        the same count, then require SMT satisfiability for every synthesized
        count.  This keeps non-counter guards and non-singleton counter bounds
        intact.
        """

        if upper_bound <= 0 or exact_count <= 0 or exact_count > upper_bound:
            return None
        count_name = str(count_param.get("name") or "")
        if not count_name:
            return None
        retained: List[Condition] = []
        dropped_singleton = False
        for condition in ConditionSimplifier.simplify_conditions_object_centric(list(conditions or [])):
            if (
                self._condition_references_only_counter_parameter(condition, count_name)
                and self._exact_counter_value_from_conditions([condition], count_name) == int(exact_count)
            ):
                dropped_singleton = True
                continue
            retained.append(condition)
        if not dropped_singleton:
            return None
        retained = ConditionSimplifier.simplify_conditions_object_centric(retained)
        for count_value in range(1, int(upper_bound) + 1):
            if not self._conditions_allow_counter_value(retained, count_param, int(count_value)):
                return None
        return retained

    def _condition_references_only_counter_parameter(
        self,
        condition: Optional[Condition],
        param_name: str,
    ) -> bool:
        expr = getattr(condition, "expression", None)
        if expr is None or not param_name:
            return False
        saw_counter = False
        for node in self._iter_expression_nodes(expr):
            if getattr(node, "expr_type", None) != ExpressionType.PARAMETER:
                continue
            if getattr(node, "name", None) != param_name:
                return False
            saw_counter = True
        return saw_counter

    def _collect_readonly_prefix_accumulator_proofs(
        self,
        analysis,
        high_function,
        pointer_param: dict,
        count_param: dict,
        *,
        counter_signed: bool,
        positive_conditions: Sequence[Condition],
        result_size: int,
    ) -> List[ReductionAccumulatorProof]:
        if high_function is None or not callable(getattr(high_function, "getBasicBlocks", None)):
            return []
        pointer_base_ref = self._location_base_ref_from_parameter(pointer_param, default_name="ptr")
        count_expr = self._parameter_expression(count_param)
        all_ops = list(self._iter_pcode_ops(high_function))
        pointer_phis: List[Dict[str, object]] = []
        index_phis: List[Dict[str, object]] = []
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            pointer_match = self._match_pointer_progression_phi(op, pointer_param)
            if pointer_match is not None:
                pointer_phis.append(pointer_match)
            index_match = self._match_index_progression_phi(op)
            if index_match is not None:
                index_phis.append(index_match)
        proofs: List[ReductionAccumulatorProof] = []
        seen = set()
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            proof = self._match_accumulator_phi(
                op,
                analysis,
                pointer_param,
                count_param,
                pointer_base_ref,
                count_expr,
                counter_signed,
                pointer_phis,
                index_phis,
                result_size=result_size,
                positive_conditions=positive_conditions,
            )
            if proof is None:
                continue
            if int(getattr(proof, "start_index", 0) or 0) != 0:
                continue
            if int(getattr(proof, "start_offset", 0) or 0) != 0:
                continue
            if tuple(getattr(proof, "seed_terms", ()) or ()) or getattr(proof, "seed_term_count", None) not in {None, 0}:
                continue
            key = proof.stable_key() or repr(proof)
            if key in seen:
                continue
            seen.add(key)
            proofs.append(proof)
        return proofs

    def _infer_upper_bound_from_conditions(
        self,
        conditions: Sequence[Condition],
        param_name: str,
    ) -> Optional[int]:
        upper_bounds: List[int] = []
        for condition in conditions or []:
            relation = self._condition_relation(condition, param_name)
            if relation is None:
                continue
            relation_name, constant = relation
            if relation_name == "<=":
                upper_bounds.append(int(constant))
            elif relation_name == "<":
                upper_bounds.append(int(constant) - 1)
        if not upper_bounds:
            return None
        return min(upper_bounds)

    def _readonly_reduction_condition_signature(
        self,
        conditions: Sequence[Condition],
    ) -> tuple:
        return tuple(condition.structural_key() for condition in (conditions or ()))

    def _readonly_reduction_return_signature(
        self,
        ret: ReturnInfo,
    ) -> tuple:
        value_key = None
        if getattr(ret, "value", None) is not None and hasattr(ret.value, "structural_key"):
            value_key = ret.value.structural_key()
        return (
            ret.site_key(),
            ret.branch_index,
            ret.address,
            ret.pcode_time,
            ret.pcode_order,
            self._readonly_reduction_condition_signature(ret.conditions or ()),
            value_key,
        )

    def _readonly_reduction_normalization_state_key(
        self,
        accumulator_proof: ReductionAccumulatorProof,
        positive_conditions: Sequence[Condition],
        overlapping_positive_returns: Sequence[ReturnInfo],
    ) -> tuple:
        proof_key = accumulator_proof.stable_key()
        if proof_key is None:
            proof_key = (
                "reduction_accumulator_proof_fallback",
                int(getattr(accumulator_proof, "start_index", 0) or 0),
                int(getattr(accumulator_proof, "start_offset", 0) or 0),
                int(getattr(accumulator_proof, "stride", 0) or 0),
                int(getattr(accumulator_proof, "element_size", 0) or 0),
                int(getattr(accumulator_proof, "result_size", 0) or 0),
                self._readonly_reduction_condition_signature(
                    getattr(accumulator_proof, "guard_constraints", ()) or ()
                ),
                tuple(
                    witness.stable_key()
                    for witness in (getattr(accumulator_proof, "exact_return_witnesses", ()) or ())
                ),
                tuple(
                    witness.stable_key()
                    for witness in (getattr(accumulator_proof, "loop_body_witnesses", ()) or ())
                ),
            )
        return (
            proof_key,
            self._readonly_reduction_condition_signature(positive_conditions or ()),
            tuple(
                self._readonly_reduction_return_signature(ret)
                for ret in (overlapping_positive_returns or ())
            ),
        )

    def _normalize_readonly_reduction_candidate(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        broad_positive_conditions: Sequence[Condition],
        positive_conditions: Sequence[Condition],
        *,
        counter_signed: bool,
        accumulator_proof: ReductionAccumulatorProof,
        overlapping_positive_returns: Sequence[ReturnInfo],
    ) -> Optional[
        Tuple[
            ReductionAccumulatorProof,
            List[Condition],
            List[ReturnInfo],
            int,
            List[ReturnInfo],
            Tuple[ReadonlyReductionWitness, ...],
            Tuple[ReadonlyReductionWitness, ...],
        ]
    ]:
        exact_return_candidates = [
            ret for ret in (analysis.returns or [])
            if self._return_overlaps_conditions(ret, broad_positive_conditions)
        ]
        if not overlapping_positive_returns:
            return None
        result_size = max(1, int(getattr(overlapping_positive_returns[0].value, "size", 0) or 0) or 4)
        declared_signedness = self._analysis_parameter_declared_signedness(
            analysis,
            count_param,
        )

        normalized_positive_conditions = list(positive_conditions or [])
        normalized_overlapping_positive_returns = list(overlapping_positive_returns or [])
        normalized_proof = accumulator_proof
        current_state_key = self._readonly_reduction_normalization_state_key(
            normalized_proof,
            normalized_positive_conditions,
            normalized_overlapping_positive_returns,
        )
        seen_state_keys = {current_state_key}

        while True:
            exact_witnesses = self._extract_readonly_reduction_exact_witnesses(
                analysis,
                pointer_param,
                count_param,
                exact_return_candidates,
                normalized_proof,
            )
            semantic_witnesses = self._build_readonly_reduction_semantic_witnesses(
                analysis,
                pointer_param,
                count_param,
                normalized_overlapping_positive_returns,
                normalized_proof,
                result_size=result_size,
                exact_witnesses=exact_witnesses,
            )
            next_proof = normalized_proof.with_runtime_evidence(
                limit_expr=self._parameter_expression(count_param),
                result_size=result_size,
                loop_body_witnesses=semantic_witnesses,
                exact_return_witnesses=exact_witnesses,
                guard_constraints=tuple(normalized_positive_conditions),
                signed_counter=counter_signed,
            )
            next_positive_conditions = self._readonly_reduction_positive_conditions(
                analysis,
                pointer_param,
                count_param,
                loop_start_index=int(next_proof.start_index),
                signed_counter=counter_signed,
            )
            if ConditionSimplifier.object_centric_is_contradiction(next_positive_conditions):
                return None
            next_overlapping_positive_returns = self._readonly_reduction_replaceable_positive_returns(
                analysis,
                pointer_param,
                count_param,
                broad_positive_conditions,
                next_positive_conditions,
                expected_signed=counter_signed,
                declared_signedness=declared_signedness,
                accumulator_proof=next_proof,
            )
            if not next_overlapping_positive_returns:
                synthetic_positive_return = self._readonly_synthetic_positive_return_from_proof(
                    next_proof,
                    next_positive_conditions,
                    result_size=result_size,
                )
                if synthetic_positive_return is None:
                    return None
                if not self._readonly_region_returns_are_subsumable_by_proof(
                    analysis,
                    pointer_param,
                    count_param,
                    next_positive_conditions,
                    next_proof,
                ):
                    return None
                next_overlapping_positive_returns = [synthetic_positive_return]
            next_state_key = self._readonly_reduction_normalization_state_key(
                next_proof,
                next_positive_conditions,
                next_overlapping_positive_returns,
            )
            if next_state_key == current_state_key:
                return (
                    next_proof,
                    list(next_positive_conditions),
                    list(next_overlapping_positive_returns),
                    result_size,
                    exact_return_candidates,
                    exact_witnesses,
                    semantic_witnesses,
                )
            if next_state_key in seen_state_keys:
                self._debug(
                    "Declined readonly reduction summary: proof normalization did not converge to a fixed point"
                )
                return None
            seen_state_keys.add(next_state_key)
            current_state_key = next_state_key
            normalized_proof = next_proof
            normalized_positive_conditions = list(next_positive_conditions)
            normalized_overlapping_positive_returns = list(next_overlapping_positive_returns)

    def _infer_readonly_pointer_reduction_parameters(
        self,
        analysis,
        high_function,
    ) -> Tuple[Optional[dict], Optional[dict]]:
        parameters = list(analysis.parameters or [])
        if not parameters:
            return None, None

        pointer_ranked: List[Tuple[int, int, dict]] = []
        for param in parameters:
            score = self._readonly_pointer_candidate_score(
                analysis,
                high_function,
                param,
            )
            if score <= 0:
                continue
            pointer_ranked.append((score, -int(param.get("index", 0) or 0), param))
        pointer_ranked.sort(reverse=True)
        pointer_param = pointer_ranked[0][2] if pointer_ranked else None

        counter_ranked: List[Tuple[int, int, dict]] = []
        for param in parameters:
            if pointer_param is not None and int(param.get("index", -1)) == int(pointer_param.get("index", -2)):
                continue
            score = self._readonly_counter_candidate_score(analysis, param)
            if score <= 0:
                continue
            counter_ranked.append((score, -int(param.get("index", 0) or 0), param))
        counter_ranked.sort(reverse=True)
        counter_param = counter_ranked[0][2] if counter_ranked else None

        if pointer_param is None and counter_param is not None and len(parameters) == 2:
            pointer_param = next(
                (param for param in parameters if int(param.get("index", -1)) != int(counter_param.get("index", -1))),
                None,
            )
        if counter_param is None and pointer_param is not None and len(parameters) == 2:
            counter_param = next(
                (param for param in parameters if int(param.get("index", -1)) != int(pointer_param.get("index", -1))),
                None,
            )
        return pointer_param, counter_param

    def _readonly_pointer_candidate_score(
        self,
        analysis,
        high_function,
        param: dict,
    ) -> int:
        score = 0
        if is_pointer_data_type(
            param.get("data_type_obj"),
            param.get("data_type"),
            program=getattr(self.tracer, "program", None),
        ):
            score += 8
        if self._parameter_has_pointer_progression(high_function, param):
            score += 6
        if self._parameter_bases_memory_reads(analysis, param):
            score += 4
        if self._parameter_has_pointer_guards(analysis, param):
            score += 1
        return score

    def _readonly_counter_candidate_score(
        self,
        analysis,
        param: dict,
    ) -> int:
        score = 0
        if self._parameter_can_be_counter(param):
            score += 4
        if self._analysis_mentions_parameter_in_conditions(analysis, str(param.get("name", "") or "")):
            score += 3
        return score

    def _parameter_has_pointer_progression(
        self,
        high_function,
        param: dict,
    ) -> bool:
        if high_function is None:
            return False
        for op in self._iter_pcode_ops(high_function):
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            if self._match_pointer_progression_phi(op, param) is not None:
                return True
        return False

    def _parameter_bases_memory_reads(
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

    def _parameter_has_pointer_guards(
        self,
        analysis,
        param: dict,
    ) -> bool:
        pointer_name = str(param.get("name", "") or "")
        if not pointer_name:
            return False
        for ret in analysis.returns or []:
            for condition in ret.conditions or []:
                if (
                    self._condition_is_pointer_null(condition, pointer_name)
                    or self._condition_is_pointer_nonnull(condition, pointer_name)
                ):
                    return True
        return False

    def _iter_expression_nodes(self, expr: Optional[Expression]):
        if expr is None:
            return
        stack = [expr]
        seen = set()
        while stack:
            current = stack.pop()
            if current is None:
                continue
            current_id = id(current)
            if current_id in seen:
                continue
            seen.add(current_id)
            yield current
            if current.expr_type == ExpressionType.PHI and current.value:
                for cond, value in current.value:
                    if cond is not None and getattr(cond, "expression", None) is not None:
                        stack.append(cond.expression)
                    if value is not None:
                        stack.append(value)
                continue
            for operand in reversed(list(getattr(current, "operands", None) or [])):
                stack.append(operand)

    def _readonly_reduction_positive_conditions(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        *,
        loop_start_index: int = 0,
        signed_counter: Optional[bool] = None,
    ) -> List[Condition]:
        pointer_expr = self._parameter_expression(pointer_param)
        count_expr = self._parameter_expression(count_param)
        lower_bound = max(0, int(loop_start_index or 0))
        compare_op = self._readonly_reduction_count_compare_op(
            count_param,
            signed_counter=signed_counter,
        )
        return [
            Condition(
                Expression.binary_op(
                    "INT_NOTEQUAL",
                    pointer_expr,
                    Expression.constant(0, pointer_expr.size or 8),
                ),
                False,
            ),
            Condition(
                Expression.binary_op(
                    compare_op,
                    Expression.constant(lower_bound, count_expr.size or 4),
                    count_expr,
                ),
                False,
            ),
        ]

    def _readonly_reduction_region_returns_with_signedness(
        self,
        analysis,
        count_param: dict,
        conditions: Sequence[Condition],
        *,
        expected_signed: bool,
    ) -> List[ReturnInfo]:
        if analysis is None:
            return []
        relevant_returns = [
            ret for ret in (getattr(analysis, "returns", None) or [])
            if self._return_conditions_imply_conditions(ret, conditions)
        ]
        return [
            ret for ret in relevant_returns
            if self._readonly_reduction_counter_is_signed([ret], count_param) == expected_signed
        ]

    def _readonly_reduction_region_returns(
        self,
        analysis,
        conditions: Sequence[Condition],
    ) -> List[ReturnInfo]:
        if analysis is None:
            return []
        return [
            ret for ret in (getattr(analysis, "returns", None) or [])
            if self._return_conditions_imply_conditions(ret, conditions)
        ]

    def _readonly_region_returns_are_subsumable_by_proof(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        conditions: Sequence[Condition],
        accumulator_proof: Optional[ReductionAccumulatorProof],
    ) -> bool:
        """Check whether existing region returns can coexist with a proof anchor.

        When a broad loop region is proven from PHI/def-use evidence, optimized
        code may still expose one or more exact-count returns inside that
        region.  Those exact returns should not block the synthetic anchor if
        each one is itself explained by the same object-centric term sequence.
        """

        region_returns = self._readonly_reduction_region_returns(analysis, conditions)
        if not region_returns:
            return True
        if accumulator_proof is None:
            return False
        if self._readonly_proof_return_sites_cover_returns(accumulator_proof, region_returns):
            return True
        count_name = str(count_param.get("name") or "")
        for ret in region_returns:
            exact_count = self._exact_counter_value_from_conditions(
                ret.conditions or [],
                count_name,
            )
            if exact_count is None or int(exact_count) <= 0:
                return False
            if not self._readonly_positive_return_proves_count_value(
                analysis,
                pointer_param,
                count_param,
                ret,
                accumulator_proof,
                count_value=int(exact_count),
            ):
                return False
        return True

    def _readonly_proof_return_sites_cover_returns(
        self,
        accumulator_proof: Optional[ReductionAccumulatorProof],
        returns: Sequence[ReturnInfo],
    ) -> bool:
        if accumulator_proof is None or not bool(getattr(accumulator_proof, "return_region_value_proven", False)):
            return False
        return_refs = tuple(getattr(accumulator_proof, "return_op_refs", ()) or ())
        if not return_refs:
            return False
        for ret in returns or ():
            if not any(self._return_info_matches_pcode_op_ref(ret, ref) for ref in return_refs):
                return False
        return True

    def _readonly_reduction_replaceable_positive_returns(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        broad_positive_conditions: Sequence[Condition],
        conditions: Sequence[Condition],
        *,
        expected_signed: bool,
        declared_signedness: Optional[bool] = None,
        accumulator_proof: Optional[ReductionAccumulatorProof],
    ) -> List[ReturnInfo]:
        if analysis is None:
            return []
        overlapping_returns = [
            ret for ret in (getattr(analysis, "returns", None) or [])
            if self._return_overlaps_conditions(ret, conditions)
        ]
        if not overlapping_returns:
            return []
        if self._readonly_exact_materialized_returns_conflict_with_accumulator_proof(
            analysis,
            pointer_param,
            count_param,
            conditions,
            accumulator_proof,
        ):
            return []

        replaceable_returns: List[ReturnInfo] = []
        coverage_returns: List[ReturnInfo] = []
        for ret in overlapping_returns:
            ret_constraint_set = ConditionConstraintSet.from_conditions(ret.conditions or [])
            signed_evidence, unsigned_evidence = self._readonly_reduction_counter_signedness_evidence(
                [ret],
                count_param,
            )
            has_expected_signedness = (
                (expected_signed and signed_evidence and not unsigned_evidence)
                or (not expected_signed and unsigned_evidence and not signed_evidence)
            )
            has_conflicting_signedness = signed_evidence and unsigned_evidence
            has_opposite_signedness = (
                (expected_signed and unsigned_evidence and not signed_evidence)
                or (not expected_signed and signed_evidence and not unsigned_evidence)
            )
            lacks_signedness_evidence = not signed_evidence and not unsigned_evidence
            declared_supports_candidate = (
                declared_signedness is not None
                and bool(declared_signedness) == bool(expected_signed)
                and lacks_signedness_evidence
            )
            has_candidate_signedness_support = (
                has_expected_signedness or declared_supports_candidate
            )
            exact_count = self._exact_counter_value_from_conditions(
                ret.conditions or [],
                str(count_param.get("name") or ""),
            )
            has_exact_count_proof = (
                exact_count is not None
                and int(exact_count) > 0
                and self._readonly_positive_return_proves_count_value(
                    analysis,
                    pointer_param,
                    count_param,
                    ret,
                    accumulator_proof,
                    count_value=int(exact_count),
                )
            )
            has_exact_witness = has_exact_count_proof or self._readonly_positive_return_matches_accumulator_proof(
                analysis,
                pointer_param,
                count_param,
                ret,
                accumulator_proof,
            )
            if has_exact_count_proof:
                replaceable_returns.append(ret)
                if self._readonly_region_value_proof_allows_broadened_positive_coverage(
                    analysis,
                    pointer_param,
                    count_param,
                    ret,
                    conditions,
                    accumulator_proof,
                ):
                    coverage_returns.append(
                        replace(
                            ret,
                            conditions=list(conditions or []),
                        )
                    )
                else:
                    coverage_returns.append(ret)
                continue
            loop_anchor_count = self._readonly_positive_return_accumulator_anchor_count(
                analysis,
                pointer_param,
                count_param,
                ret,
                accumulator_proof,
            )
            has_loop_anchor = (
                loop_anchor_count is not None
                and self._readonly_loop_anchor_covers_return_region(
                    ret,
                    conditions,
                    count_param,
                    int(loop_anchor_count),
                    accumulator_proof,
                )
            )
            has_region_value_proof = self._readonly_return_region_value_is_proven(
                ret,
                conditions,
                accumulator_proof,
            )
            has_vectorized_region_sequence_proof = (
                self._readonly_vectorized_return_region_sequence_is_proven(
                    ret,
                    conditions,
                    accumulator_proof,
                )
            )
            has_materialized_readonly_terms = loop_anchor_count is not None or (
                self._readonly_positive_return_has_materialized_readonly_terms(
                    analysis,
                    pointer_param,
                    ret,
                    accumulator_proof,
                )
            )
            if has_vectorized_region_sequence_proof and not has_exact_count_proof:
                replaceable_returns.append(ret)
                coverage_returns.append(
                    replace(
                        ret,
                        conditions=list(conditions or []),
                    )
                )
                continue
            if (
                has_materialized_readonly_terms
                and has_region_value_proof
                and not has_loop_anchor
                and not has_exact_count_proof
                and not self._readonly_materialized_positive_return_matches_accumulator_contract(
                    analysis,
                    pointer_param,
                    count_param,
                    ret,
                    accumulator_proof,
                )
            ):
                extracted_for_debug = self._extract_readonly_return_terms_and_bias(
                    analysis,
                    pointer_param,
                    ret,
                    accumulator_proof,
                )
                if extracted_for_debug is not None:
                    debug_terms, debug_bias = extracted_for_debug
                    self._debug(
                        "Readonly materialized region contract mismatch: "
                        f"terms={[(term.byte_offset, term.access_size) for term in debug_terms]}, "
                        f"bias={debug_bias}, "
                        f"proof_start_index={getattr(accumulator_proof, 'start_index', None)}, "
                        f"proof_start_offset={getattr(accumulator_proof, 'start_offset', None)}, "
                        f"proof_seed_terms={[(term.byte_offset, term.access_size) for term in (getattr(accumulator_proof, 'seed_terms', ()) or ())]}"
                    )
                self._debug(
                    "Declined readonly reduction summary: materialized positive return "
                    "flows to the return region but does not match the accumulator term contract"
                )
                return []
            if (
                has_materialized_readonly_terms
                and not has_region_value_proof
                and not has_loop_anchor
                and not has_exact_count_proof
            ):
                self._debug(
                    "Declined readonly reduction summary: materialized positive return "
                    "has no exact-count, loop-anchor, or return-region value proof"
                )
                return []
            if not ret_constraint_set.implies_all(conditions or []):
                counter_only_extra_guards = self._readonly_return_has_only_counter_guards_beyond_conditions(
                    ret.conditions or [],
                    broad_positive_conditions,
                    count_param,
                )
                if not ret_constraint_set.implies_all(broad_positive_conditions or []):
                    if not (has_loop_anchor and counter_only_extra_guards):
                        return []
                if (
                    (has_conflicting_signedness or has_opposite_signedness)
                    and not has_loop_anchor
                    and not has_exact_count_proof
                ):
                    return []
                if not self._readonly_positive_prefix_is_exactly_covered(
                    analysis,
                    pointer_param,
                    count_param,
                    ret,
                    accumulator_proof,
                ):
                    return []
                replaceable_returns.append(ret)
                if self._readonly_region_value_proof_allows_broadened_positive_coverage(
                    analysis,
                    pointer_param,
                    count_param,
                    ret,
                    conditions,
                    accumulator_proof,
                ):
                    coverage_returns.append(
                        replace(
                            ret,
                            conditions=list(conditions or []),
                        )
                    )
                else:
                    coverage_returns.append(ret)
                continue
            residual_conditions = ret_constraint_set.residual_against(conditions or [])
            if (
                residual_conditions
                and not has_exact_count_proof
                and not has_loop_anchor
                and not self._readonly_residual_conditions_are_counter_only(
                    residual_conditions,
                    count_param,
                )
            ):
                return []
            if has_conflicting_signedness or has_opposite_signedness:
                if not (has_exact_count_proof or has_loop_anchor):
                    return []
            if (
                has_candidate_signedness_support
                or has_exact_count_proof
                or has_loop_anchor
                or has_region_value_proof
                or lacks_signedness_evidence
            ):
                replaceable_returns.append(ret)
                if self._readonly_region_value_proof_allows_broadened_positive_coverage(
                    analysis,
                    pointer_param,
                    count_param,
                    ret,
                    conditions,
                    accumulator_proof,
                ):
                    coverage_returns.append(
                        replace(
                            ret,
                            conditions=list(conditions or []),
                        )
                    )
                else:
                    coverage_returns.append(ret)
                continue
            return []
        if not replaceable_returns:
            return []
        if not self._readonly_region_is_covered_by_returns(conditions, coverage_returns):
            return []
        return replaceable_returns

    def _readonly_exact_materialized_returns_conflict_with_accumulator_proof(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        conditions: Sequence[Condition],
        accumulator_proof: Optional[ReductionAccumulatorProof],
    ) -> bool:
        """Reject a loop summary proof contradicted by exact return evidence.

        A broad PHI proof can reach a return region while still describing the
        wrong memory sequence.  Exact materialized returns inside that same
        guarded region are stronger object-level witnesses: if the proof cannot
        reproduce their readonly term sequence for the exact counter value, the
        proof must not be promoted to a summary even when the final summary case
        later excludes that one exact value.
        """

        if analysis is None or accumulator_proof is None:
            return False
        count_name = str(count_param.get("name") or "")
        if not count_name:
            return False

        for ret in getattr(analysis, "returns", None) or ():
            exact_count = self._exact_counter_value_from_conditions(
                ret.conditions or [],
                count_name,
            )
            if exact_count is None or int(exact_count) <= 0:
                continue
            exact_count = int(exact_count)
            if not self._conditions_allow_counter_value(conditions or [], count_param, exact_count):
                continue
            if ConditionSimplifier.object_centric_is_contradiction(
                list(ret.conditions or []) + list(conditions or [])
            ):
                continue
            overlap_unsat = ConditionSMTOracle.conjunction_is_unsat(
                list(ret.conditions or []) + list(conditions or [])
            )
            if overlap_unsat is True:
                continue

            extracted = self._extract_readonly_return_terms_and_bias(
                analysis,
                pointer_param,
                ret,
                accumulator_proof,
            )
            if extracted is None:
                continue
            expected_terms = accumulator_proof.full_terms_for_count_value(exact_count)
            if expected_terms is None:
                self._debug(
                    "Declined readonly reduction summary: exact materialized return "
                    f"count={exact_count} has no proof term contract"
                )
                return True
            if self._readonly_positive_return_proves_count_value(
                analysis,
                pointer_param,
                count_param,
                ret,
                accumulator_proof,
                count_value=exact_count,
            ):
                continue
            terms, constant_bias = extracted
            self._debug(
                "Declined readonly reduction summary: exact materialized return "
                f"count={exact_count} conflicts with accumulator term contract "
                f"(terms={[(term.byte_offset, term.access_size) for term in terms]}, "
                f"expected={[(term.byte_offset, term.access_size) for term in expected_terms]}, "
                f"bias={constant_bias})"
            )
            return True
        return False

    def _readonly_preserved_summary_is_subsumed_by_replacement(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        ret: ReturnInfo,
        replacement_conditions: Sequence[Condition],
        proof_region_conditions: Sequence[Condition],
        replacement_proof: Optional[ReductionAccumulatorProof],
        replacement_ref: Optional[ReadonlyReductionRef],
    ) -> bool:
        if replacement_proof is None or replacement_ref is None:
            return False
        existing_ref = self._readonly_reduction_ref_from_return(ret)
        if existing_ref is None:
            return False
        result_size = max(
            1,
            int(getattr(replacement_ref, "result_size", 0) or getattr(ret.value, "size", 0) or 0),
        )
        existing_key = existing_ref.readonly_term_sequence_contract_key(result_size=result_size)
        replacement_key = replacement_ref.readonly_term_sequence_contract_key(result_size=result_size)
        if existing_key is not None and existing_key == replacement_key:
            return False
        if self._readonly_reduction_ref_specificity(replacement_ref) < self._readonly_reduction_ref_specificity(
            existing_ref
        ):
            return False
        replacement_proves_return_site = self._readonly_return_region_value_is_proven(
            ret,
            replacement_conditions,
            replacement_proof,
        )
        existing_proof = getattr(existing_ref, "accumulator_proof", None)
        existing_contract_conflicts = (
            existing_proof is not None
            and self._readonly_exact_materialized_returns_conflict_with_accumulator_proof(
                analysis,
                pointer_param,
                count_param,
                proof_region_conditions,
                existing_proof,
            )
        )
        if not replacement_proves_return_site and not existing_contract_conflicts:
            return False
        if not self._conditions_imply_with_smt(ret.conditions or [], replacement_conditions or []):
            return False
        self._debug(
            "Dropped preserved readonly summary subsumed by proof-backed replacement "
            f"(existing_contract={existing_key}, replacement_contract={replacement_key})"
        )
        return True

    def _readonly_unresolved_preserved_return_is_subsumed_by_replacement(
        self,
        ret: ReturnInfo,
        replacement_conditions: Sequence[Condition],
        replacement_proof: Optional[ReductionAccumulatorProof],
        replacement_ref: Optional[ReadonlyReductionRef],
    ) -> bool:
        """Drop less-precise unresolved artifacts covered by a proven summary.

        Optimized readonly reductions can leave PHI-circular expansion artifacts
        at the same RETURN site and guard as the object-centric accumulator
        proof.  Those artifacts are not independent semantic regions; keeping
        them lets the monolithic fallback choose an unconstrained UNKNOWN value
        even though the proof-backed READONLY_SUM already models that return
        site.  Only same-site, guard-covered, unresolved values are removed.
        Precise materialized returns remain as evidence and can still reject a
        bad summary contract earlier.
        """

        if replacement_proof is None or replacement_ref is None:
            return False
        if not self._expression_tree_contains_type(getattr(ret, "value", None), ExpressionType.UNKNOWN):
            return False
        if not bool(getattr(replacement_proof, "return_region_value_proven", False)):
            return False
        contract_key_fn = getattr(replacement_ref, "readonly_term_sequence_contract_key", None)
        if not callable(contract_key_fn):
            return False
        try:
            contract_key = contract_key_fn(result_size=getattr(replacement_ref, "result_size", None))
        except (AttributeError, TypeError, ValueError):
            contract_key = None
        if contract_key is None:
            return False
        if ConditionSimplifier.object_centric_is_contradiction(
            list(ret.conditions or []) + list(replacement_conditions or [])
        ):
            return False
        if not self._readonly_return_region_value_is_proven(
            ret,
            replacement_conditions,
            replacement_proof,
        ):
            return False
        self._debug(
            "Dropped unresolved readonly return artifact subsumed by proof-backed summary "
            f"(contract={contract_key})"
        )
        return True

    def _readonly_reduction_ref_specificity(
        self,
        reduction_ref: ReadonlyReductionRef,
    ) -> int:
        score_fn = getattr(reduction_ref, "readonly_term_sequence_specificity_score", None)
        if callable(score_fn):
            try:
                return max(0, int(score_fn()))
            except (TypeError, ValueError):
                return 0
        return 0

    def _readonly_reduction_ref_from_return(
        self,
        ret: ReturnInfo,
    ) -> Optional[ReadonlyReductionRef]:
        value = getattr(ret, "value", None)
        if getattr(value, "expr_type", None) != ExpressionType.INTRINSIC:
            return None
        runtime_ref = getattr(value, "runtime_ref", None)
        if isinstance(runtime_ref, ReadonlyReductionRef):
            return runtime_ref
        return None

    def _readonly_summary_return_should_precede_preserved_return(
        self,
        summary_return: ReturnInfo,
        preserved_return: ReturnInfo,
        summary_ref: ReadonlyReductionRef,
    ) -> bool:
        preserved_ref = self._readonly_reduction_ref_from_return(preserved_return)
        if preserved_ref is None:
            return False
        result_size = max(
            1,
            int(getattr(summary_ref, "result_size", 0) or getattr(summary_return.value, "size", 0) or 0),
        )
        summary_key = summary_ref.readonly_term_sequence_contract_key(result_size=result_size)
        preserved_key = preserved_ref.readonly_term_sequence_contract_key(result_size=result_size)
        if summary_key is not None and summary_key == preserved_key:
            return False
        if self._readonly_reduction_ref_specificity(summary_ref) < self._readonly_reduction_ref_specificity(
            preserved_ref
        ):
            return False
        if not self._conditions_imply_with_smt(
            summary_return.conditions or [],
            preserved_return.conditions or [],
        ):
            return False
        return True

    def _readonly_vectorized_return_region_sequence_is_proven(
        self,
        ret: ReturnInfo,
        positive_conditions: Sequence[Condition],
        accumulator_proof: Optional[ReductionAccumulatorProof],
    ) -> bool:
        if accumulator_proof is None:
            return False
        if getattr(accumulator_proof, "source", None) != "vectorized_readonly_prefix_sum":
            return False
        if not bool(getattr(accumulator_proof, "return_region_value_proven", False)):
            return False
        if not self._readonly_return_region_value_is_proven(
            ret,
            positive_conditions,
            accumulator_proof,
        ):
            return False
        side_effect_profile = getattr(accumulator_proof, "side_effect_profile", None)
        requires_effect_proof = getattr(side_effect_profile, "requires_effect_proof", None)
        if callable(requires_effect_proof) and requires_effect_proof():
            return False
        return True

    def _readonly_positive_prefix_is_exactly_covered(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        ret: ReturnInfo,
        accumulator_proof: Optional[ReductionAccumulatorProof],
    ) -> bool:
        if analysis is None or accumulator_proof is None:
            return False
        prefix_limit = int(getattr(accumulator_proof, "start_index", 0) or 0)
        if prefix_limit <= 0:
            return False

        candidate_returns = [
            candidate for candidate in (getattr(analysis, "returns", None) or [])
            if candidate is not ret
        ]
        for count_value in range(1, prefix_limit + 1):
            if not self._conditions_allow_counter_value(ret.conditions or [], count_param, count_value):
                continue
            covered_region = list(ret.conditions or []) + [
                self._counter_equality_condition(count_param, count_value)
            ]
            if not any(
                self._conditions_imply_counter_value(candidate.conditions or [], count_param, count_value)
                and ConditionConstraintSet.from_conditions(covered_region).implies_all(
                    candidate.conditions or []
                )
                and self._readonly_positive_return_proves_count_value(
                    analysis,
                    pointer_param,
                    count_param,
                    candidate,
                    accumulator_proof,
                    count_value=int(count_value),
                )
                for candidate in candidate_returns
            ):
                return False
        return True

    def _readonly_positive_return_proves_count_value(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        ret: ReturnInfo,
        accumulator_proof: Optional[ReductionAccumulatorProof],
        *,
        count_value: int,
    ) -> bool:
        if accumulator_proof is None or int(count_value) <= 0:
            return False
        if not self._conditions_allow_counter_value(ret.conditions or [], count_param, count_value):
            return False
        if self._readonly_positive_return_materializes_count_value(
            analysis,
            pointer_param,
            count_param,
            ret,
            accumulator_proof,
            count_value=int(count_value),
        ):
            return True
        if self._readonly_positive_return_matches_accumulator_proof(
            analysis,
            pointer_param,
            count_param,
            ret,
            accumulator_proof,
        ):
            return True
        anchor_count = self._readonly_positive_return_accumulator_anchor_count(
            analysis,
            pointer_param,
            count_param,
            ret,
            accumulator_proof,
        )
        if anchor_count is not None and int(anchor_count) == int(count_value):
            return True
        positive_conditions = tuple(getattr(accumulator_proof, "guard_constraints", ()) or ())
        if not positive_conditions:
            positive_conditions = tuple(
                self._readonly_reduction_positive_conditions(
                    analysis,
                    pointer_param,
                    count_param,
                    loop_start_index=int(getattr(accumulator_proof, "start_index", 0) or 0),
                    signed_counter=getattr(accumulator_proof, "signed_counter", None),
                )
            )
        if positive_conditions and self._readonly_return_region_value_is_proven(
            ret,
            positive_conditions,
            accumulator_proof,
        ):
            if self._readonly_positive_return_has_materialized_readonly_terms(
                analysis,
                pointer_param,
                ret,
                accumulator_proof,
            ):
                return self._readonly_positive_return_materializes_count_value(
                    analysis,
                    pointer_param,
                    count_param,
                    ret,
                    accumulator_proof,
                    count_value=int(count_value),
                )
            expected_terms = accumulator_proof.full_terms_for_count_value(int(count_value))
            return expected_terms is not None
        return False

    def _readonly_region_value_proof_allows_broadened_positive_coverage(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        ret: ReturnInfo,
        positive_conditions: Sequence[Condition],
        accumulator_proof: Optional[ReductionAccumulatorProof],
    ) -> bool:
        if analysis is None or accumulator_proof is None:
            return False
        if not self._readonly_return_region_value_is_proven(
            ret,
            positive_conditions,
            accumulator_proof,
        ):
            return False
        ret_constraints = ConditionConstraintSet.from_conditions(ret.conditions or [])
        residual_conditions = ret_constraints.residual_against(positive_conditions or [])
        if not residual_conditions:
            return True
        if not self._readonly_residual_conditions_are_counter_only(
            residual_conditions,
            count_param,
        ):
            return False

        for candidate in getattr(analysis, "returns", None) or ():
            if candidate is ret:
                continue
            if not self._return_overlaps_conditions(candidate, positive_conditions):
                continue
            candidate_constraints = ConditionConstraintSet.from_conditions(candidate.conditions or [])
            if candidate_constraints.implies_all(ret.conditions or []):
                continue
            exact_count = self._exact_counter_value_from_conditions(
                candidate.conditions or [],
                str(count_param.get("name") or ""),
            )
            if exact_count is None:
                return False
            if not self._readonly_positive_return_proves_count_value(
                analysis,
                pointer_param,
                count_param,
                candidate,
                accumulator_proof,
                count_value=int(exact_count),
            ):
                return False
        return True

    def _readonly_positive_return_materializes_count_value(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        ret: ReturnInfo,
        accumulator_proof: Optional[ReductionAccumulatorProof],
        *,
        count_value: int,
    ) -> bool:
        if analysis is None or accumulator_proof is None or int(count_value) <= 0:
            return False
        if not self._conditions_allow_counter_value(ret.conditions or [], count_param, count_value):
            return False
        expected_terms = accumulator_proof.full_terms_for_count_value(int(count_value))
        if expected_terms is None:
            return False
        extracted = self._extract_readonly_return_terms_and_bias(
            analysis,
            pointer_param,
            ret,
            accumulator_proof,
        )
        extracted_terms = None
        constant_bias = 0
        if extracted is not None:
            extracted_terms, constant_bias = extracted
        witness_terms = self._resolve_readonly_exact_witness_terms(
            analysis,
            pointer_param,
            ret,
            accumulator_proof,
            exact_count=int(count_value),
            expected_trip_count=len(expected_terms),
            expected_terms=expected_terms,
            extracted_terms=extracted_terms,
            constant_bias=int(constant_bias),
        )
        return witness_terms is not None

    def _readonly_positive_return_matches_accumulator_proof(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        ret: ReturnInfo,
        accumulator_proof: Optional[ReductionAccumulatorProof],
    ) -> bool:
        if accumulator_proof is None:
            return False
        exact_witnesses = self._extract_readonly_reduction_exact_witnesses(
            analysis,
            pointer_param,
            count_param,
            [ret],
            accumulator_proof,
        )
        return bool(exact_witnesses)

    def _readonly_positive_return_accumulator_anchor_count(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        ret: ReturnInfo,
        accumulator_proof: Optional[ReductionAccumulatorProof],
    ) -> Optional[int]:
        if analysis is None or accumulator_proof is None:
            return None
        extracted = self._extract_readonly_return_terms_and_bias(
            analysis,
            pointer_param,
            ret,
            accumulator_proof,
        )
        if extracted is None:
            return None
        terms, _ = extracted
        term_key = tuple(term.stable_key() for term in terms)
        if not term_key:
            return None

        candidate_counts = self._readonly_candidate_counts_from_term_contract(
            terms,
            accumulator_proof,
        )
        for witness in tuple(getattr(accumulator_proof, "loop_body_witnesses", ()) or ()):
            candidate_counts.add(max(1, int(getattr(witness, "exact_count", 0) or 0)))
        for witness in tuple(getattr(accumulator_proof, "exact_return_witnesses", ()) or ()):
            candidate_counts.add(max(1, int(getattr(witness, "exact_count", 0) or 0)))

        for count_value in sorted(candidate_counts):
            if count_value <= 0:
                continue
            expected_terms = accumulator_proof.full_terms_for_count_value(int(count_value))
            if expected_terms is None:
                continue
            if term_key == tuple(term.stable_key() for term in expected_terms):
                return int(count_value)
        return None

    def _readonly_materialized_positive_return_matches_accumulator_contract(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        ret: ReturnInfo,
        accumulator_proof: Optional[ReductionAccumulatorProof],
    ) -> bool:
        """Validate a materialized return against the accumulator term sequence.

        Return-site def-use reachability proves that a PHI/update reaches a
        RETURN, but it does not by itself prove that every condition region
        using that return has the same memory term sequence.  If the returned
        expression is already materialized as readonly load terms, the terms
        must match a count value allowed by the return guard and by the proof's
        explicit semantic contract.
        """

        if analysis is None or accumulator_proof is None:
            return False
        extracted = self._extract_readonly_return_terms_and_bias(
            analysis,
            pointer_param,
            ret,
            accumulator_proof,
        )
        if extracted is None:
            return False
        terms, constant_bias = extracted
        result_size = max(
            1,
            int(getattr(accumulator_proof, "result_size", 0) or getattr(ret.value, "size", 0) or 0),
        )
        expected_bias = int(getattr(accumulator_proof, "constant_bias", 0) or 0)
        if self._normalize_readonly_constant_bias(int(constant_bias), result_size) != self._normalize_readonly_constant_bias(
            expected_bias,
            result_size,
        ):
            return False

        count_name = str(count_param.get("name") or "")
        candidate_counts = set()
        exact_count = self._exact_counter_value_from_conditions(ret.conditions or [], count_name)
        if exact_count is not None and int(exact_count) > 0:
            candidate_counts.add(int(exact_count))
        inferred_count = self._infer_exact_count_from_readonly_terms(
            ret.conditions or [],
            terms,
            count_param,
            accumulator_proof,
        )
        if inferred_count is not None and int(inferred_count) > 0:
            candidate_counts.add(int(inferred_count))
        candidate_counts.update(
            self._readonly_candidate_counts_from_term_contract(
                terms,
                accumulator_proof,
            )
        )
        for witness in tuple(getattr(accumulator_proof, "loop_body_witnesses", ()) or ()):
            witness_count = int(getattr(witness, "exact_count", 0) or 0)
            if witness_count > 0:
                candidate_counts.add(witness_count)
        for witness in tuple(getattr(accumulator_proof, "exact_return_witnesses", ()) or ()):
            witness_count = int(getattr(witness, "exact_count", 0) or 0)
            if witness_count > 0:
                candidate_counts.add(witness_count)

        term_key = tuple(term.stable_key() for term in terms)
        for count_value in sorted(candidate_counts):
            if count_value <= 0:
                continue
            if not self._conditions_allow_counter_value(ret.conditions or [], count_param, count_value):
                continue
            expected_terms = accumulator_proof.full_terms_for_count_value(int(count_value))
            if expected_terms is None:
                continue
            if term_key == tuple(term.stable_key() for term in expected_terms):
                return True
        return False

    def _readonly_candidate_counts_from_term_contract(
        self,
        terms: Sequence[ReadonlyReductionTermRef],
        accumulator_proof: Optional[ReductionAccumulatorProof],
    ) -> set[int]:
        term_count = len(tuple(terms or ()))
        candidate_counts = {max(1, int(term_count))}
        if accumulator_proof is None:
            return candidate_counts
        start_index = int(getattr(accumulator_proof, "start_index", 0) or 0)
        index_step = int(getattr(accumulator_proof, "index_step", 1) or 1)
        candidate_counts.add(max(1, start_index + 1))
        explicit_seed_count = len(tuple(getattr(accumulator_proof, "seed_terms", ()) or ()))
        if explicit_seed_count > 0 and term_count >= explicit_seed_count and index_step > 0:
            candidate_counts.add(max(1, start_index + (term_count - explicit_seed_count) * index_step))
        seed_term_count = getattr(accumulator_proof, "seed_term_count", None)
        if seed_term_count is not None:
            try:
                implicit_seed_count = int(seed_term_count)
            except (TypeError, ValueError):
                implicit_seed_count = -1
            if implicit_seed_count >= 0 and term_count >= implicit_seed_count and index_step > 0:
                candidate_counts.add(max(1, start_index + (term_count - implicit_seed_count) * index_step))
        return candidate_counts

    def _readonly_loop_anchor_covers_return_region(
        self,
        ret: ReturnInfo,
        positive_conditions: Sequence[Condition],
        count_param: dict,
        anchor_count: int,
        accumulator_proof: Optional[ReductionAccumulatorProof],
    ) -> bool:
        if anchor_count <= 0:
            return False
        if self._conditions_imply_counter_value(ret.conditions or [], count_param, anchor_count):
            return True
        return self._readonly_return_region_value_is_proven(
            ret,
            positive_conditions,
            accumulator_proof,
        )

    def _readonly_return_region_value_is_proven(
        self,
        ret: ReturnInfo,
        positive_conditions: Sequence[Condition],
        accumulator_proof: Optional[ReductionAccumulatorProof],
    ) -> bool:
        if not bool(getattr(accumulator_proof, "return_region_value_proven", False)):
            return False
        return_refs = tuple(getattr(accumulator_proof, "return_op_refs", ()) or ())
        return_value_refs = tuple(getattr(accumulator_proof, "return_value_op_refs", ()) or ())
        site_refs = return_refs + return_value_refs
        if not site_refs:
            return False
        matches_return_site = any(
            self._return_info_matches_pcode_op_ref(ret, ref) for ref in return_refs
        )
        matches_value_site = any(
            self._return_info_matches_reachable_value_pcode_op_ref(ret, ref) for ref in return_value_refs
        )
        if not matches_return_site and not matches_value_site:
            return False
        if ConditionConstraintSet.from_conditions(ret.conditions or []).implies_all(
            positive_conditions or []
        ):
            return True
        return self._conditions_imply_with_smt(ret.conditions or [], positive_conditions or [])

    def _return_info_matches_reachable_value_pcode_op_ref(
        self,
        ret: ReturnInfo,
        ref: PcodeOpRef,
    ) -> bool:
        """Match a value op only when ReturnInfo carries that exact value site.

        Def-use proof from a value op to RETURN is represented by separately
        recording the reachable RETURN refs.  This method is intentionally
        strict so a nearby sequence number cannot stand in for reachability.
        """

        if ref is None:
            return False
        return self._return_info_matches_pcode_op_ref(ret, ref)

    def _return_info_matches_pcode_op_ref(
        self,
        ret: ReturnInfo,
        ref: PcodeOpRef,
    ) -> bool:
        if ref is None:
            return False
        ret_ref = getattr(ret, "pcode_op_ref", None)
        if isinstance(ret_ref, PcodeOpRef):
            return ret_ref.stable_key() == ref.stable_key()
        _ret_address, ret_time, ret_order = self._return_info_pcode_site(ret)
        if ret_time is not None and ref.seq_time is not None:
            if int(ret_time) == int(ref.seq_time):
                return self._return_info_address_matches_pcode_ref(ret, ref)
            if self._return_info_matches_adjacent_value_copy(ret, ref, int(ret_time), ret_order):
                return True
            else:
                return False
        if ret_order is not None and ref.seq_order is not None:
            if int(ret_order) != int(ref.seq_order):
                return False
            return self._return_info_address_matches_pcode_ref(ret, ref)
        return False

    def _return_info_matches_adjacent_value_copy(
        self,
        ret: ReturnInfo,
        ref: PcodeOpRef,
        ret_time: int,
        ret_order: Optional[int],
    ) -> bool:
        if getattr(ref, "mnemonic", None) != "COPY" or ref.seq_time is None:
            return False
        if int(ret_time) != int(ref.seq_time) + 1:
            return False
        if ret_order is not None and ref.seq_order is not None and int(ret_order) != int(ref.seq_order) + 1:
            return False
        return self._return_info_address_matches_pcode_ref(ret, ref)

    def _return_info_address_matches_pcode_ref(
        self,
        ret: ReturnInfo,
        ref: PcodeOpRef,
    ) -> bool:
        if ref.address_offset is None:
            return True
        address = self._return_info_address_offset(ret)
        return address is not None and int(address) == int(ref.address_offset)

    def _return_info_address_offset(self, ret: ReturnInfo) -> Optional[int]:
        ret_ref = getattr(ret, "pcode_op_ref", None)
        if isinstance(ret_ref, PcodeOpRef) and ret_ref.address_offset is not None:
            return int(ret_ref.address_offset)
        candidates = [getattr(ret, "address", None), getattr(ret, "pcode_identity", None)]
        for candidate in candidates:
            if not isinstance(candidate, str) or not candidate:
                continue
            address_offset, _time, _order = self._parse_pcode_site_text(candidate)
            if address_offset is not None:
                return address_offset
        return None

    def _pcode_op_ref_from_return_info(
        self,
        ret: ReturnInfo,
    ) -> Optional[PcodeOpRef]:
        ret_ref = getattr(ret, "pcode_op_ref", None)
        if isinstance(ret_ref, PcodeOpRef):
            return ret_ref
        address_offset, ret_time, ret_order = self._return_info_pcode_site(ret)
        if ret_time is None and ret_order is None:
            return None
        return PcodeOpRef(
            address_offset=address_offset,
            seq_time=None if ret_time is None else int(ret_time),
            seq_order=None if ret_order is None else int(ret_order),
            mnemonic=None,
        )

    def _return_info_pcode_site(
        self,
        ret: ReturnInfo,
    ) -> Tuple[Optional[int], Optional[int], Optional[int]]:
        address_offset = self._return_info_address_offset(ret)
        ret_time = self._coerce_pcode_site_int(getattr(ret, "pcode_time", None))
        ret_order = self._coerce_pcode_site_int(getattr(ret, "pcode_order", None))
        identity = getattr(ret, "pcode_identity", None)
        if isinstance(identity, str):
            identity_address, identity_time, identity_order = self._parse_pcode_site_text(identity)
            if address_offset is None:
                address_offset = identity_address
            if ret_time is None:
                ret_time = identity_time
            if ret_order is None:
                ret_order = identity_order
        return address_offset, ret_time, ret_order

    def _parse_pcode_site_text(
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

    def _parse_pcode_address_offset(self, text: str) -> Optional[int]:
        if not isinstance(text, str):
            return None
        token = text.strip()
        if not token:
            return None
        token = token.rsplit(":", 1)[-1].strip()
        if not token:
            return None
        try:
            return int(token, 16)
        except Exception:
            try:
                return int(token, 0)
            except Exception:
                return None

    def _coerce_pcode_site_int(self, value: object) -> Optional[int]:
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

    def _readonly_positive_return_has_materialized_readonly_terms(
        self,
        analysis,
        pointer_param: dict,
        ret: ReturnInfo,
        accumulator_proof: Optional[ReductionAccumulatorProof],
    ) -> bool:
        return self._extract_readonly_return_terms_and_bias(
            analysis,
            pointer_param,
            ret,
            accumulator_proof,
        ) is not None

    def _extract_readonly_return_terms_and_bias(
        self,
        analysis,
        pointer_param: dict,
        ret: ReturnInfo,
        accumulator_proof: Optional[ReductionAccumulatorProof],
    ) -> Optional[Tuple[Tuple[ReadonlyReductionTermRef, ...], int]]:
        reduced_value = _reduce_expression_under_conditions(ret.value, ret.conditions or [])
        extracted_value = reduced_value
        extracted = self._extract_readonly_reduction_terms_and_bias(
            reduced_value,
            analysis.parameters or [],
            pointer_param,
        )
        if extracted is None and reduced_value is not ret.value:
            extracted_value = ret.value
            extracted = self._extract_readonly_reduction_terms_and_bias(
                ret.value,
                analysis.parameters or [],
                pointer_param,
            )
        if extracted is None:
            return None
        terms, constant_bias = extracted
        expected_bias = (
            int(getattr(accumulator_proof, "constant_bias", 0) or 0)
            if accumulator_proof is not None
            else 0
        )
        result_size = max(
            1,
            int(
                getattr(accumulator_proof, "result_size", 0)
                if accumulator_proof is not None
                else getattr(ret.value, "size", 0)
            )
            or 0,
        )
        exact_bits = int(expression_smt_bit_width(extracted_value) or 0)
        if exact_bits != result_size * 8:
            return None
        if self._normalize_readonly_constant_bias(constant_bias, result_size) != self._normalize_readonly_constant_bias(
            expected_bias,
            result_size,
        ):
            return None
        return tuple(terms), int(constant_bias)

    def _readonly_exact_count_region_is_fully_covered_by_return(
        self,
        ret: ReturnInfo,
        positive_conditions: Sequence[Condition],
        count_param: dict,
        exact_count: int,
    ) -> bool:
        if exact_count <= 0:
            return False
        full_region = ConditionConstraintSet.from_conditions(
            list(positive_conditions or []) + [self._counter_equality_condition(count_param, exact_count)]
        )
        return full_region.implies_all(ret.conditions or [])

    def _readonly_residual_conditions_are_counter_only(
        self,
        conditions: Sequence[Condition],
        count_param: dict,
    ) -> bool:
        param_name = str(count_param.get("name") or "")
        if not param_name:
            return False
        relevant_conditions = list(conditions or [])
        if not relevant_conditions:
            return True
        return all(
            self._readonly_reduction_condition_references_only_counter(condition, param_name)
            for condition in relevant_conditions
        )

    def _readonly_region_is_covered_by_returns(
        self,
        region_conditions: Sequence[Condition],
        covering_returns: Sequence[ReturnInfo],
    ) -> bool:
        uncovered_regions = [list(region_conditions or [])]
        for ret in covering_returns or []:
            uncovered_regions = self._readonly_subtract_condition_regions(
                uncovered_regions,
                ret.conditions or [],
            )
            if not uncovered_regions:
                return True
        if not uncovered_regions:
            return True
        return False

    def _readonly_subtract_condition_regions(
        self,
        base_regions: Sequence[Sequence[Condition]],
        subtract_conditions: Sequence[Condition],
    ) -> List[List[Condition]]:
        residual_regions: List[List[Condition]] = []
        for base_region in base_regions or []:
            residual_regions.extend(
                self._readonly_subtract_condition_region(
                    list(base_region or []),
                    list(subtract_conditions or []),
                )
            )
        return residual_regions

    def _readonly_subtract_condition_region(
        self,
        base_conditions: Sequence[Condition],
        subtract_conditions: Sequence[Condition],
    ) -> List[List[Condition]]:
        base = ConditionSimplifier.simplify_conditions_object_centric(list(base_conditions or []))
        subtract = ConditionSimplifier.simplify_conditions_object_centric(list(subtract_conditions or []))
        if not subtract:
            return [base]
        if ConditionSimplifier.object_centric_is_contradiction(base + subtract):
            return [base]
        base_constraint_set = ConditionSimplifier.build_constraint_set(base)
        if base_constraint_set.implies_all(subtract):
            return []

        subtract_constraint_set = ConditionSimplifier.build_constraint_set(subtract)
        subtract_residual = subtract_constraint_set.residual_against(base)
        if not subtract_residual:
            return []

        residual_regions: List[List[Condition]] = []
        required_prefix: List[Condition] = []
        for condition in subtract_residual:
            candidate = ConditionSimplifier.simplify_conditions_object_centric(
                list(base) + list(required_prefix) + [condition.negate()]
            )
            if not ConditionSimplifier.object_centric_is_contradiction(candidate):
                residual_regions.append(candidate)
            required_prefix.append(condition)
        return residual_regions

    def _readonly_return_has_only_counter_guards_beyond_conditions(
        self,
        return_conditions: Sequence[Condition],
        base_conditions: Sequence[Condition],
        count_param: dict,
    ) -> bool:
        residual_conditions: List[Condition] = []
        base_condition_list = list(base_conditions or [])
        for condition in list(return_conditions or []):
            if any(condition.equals(base_condition) for base_condition in base_condition_list):
                continue
            residual_conditions.append(condition)
        if not residual_conditions:
            return False
        return self._readonly_residual_conditions_are_counter_only(residual_conditions, count_param)

    def _readonly_reduction_count_compare_op(
        self,
        count_param: Optional[Dict[str, Any]],
        *,
        signed_counter: Optional[bool] = None,
        inclusive: bool = False,
    ) -> str:
        if signed_counter is not None:
            if inclusive:
                return "INT_SLESSEQUAL" if signed_counter else "INT_LESSEQUAL"
            return "INT_SLESS" if signed_counter else "INT_LESS"

        if not isinstance(count_param, dict):
            return "INT_SLESSEQUAL" if inclusive else "INT_SLESS"

        raw_dt = count_param.get("data_type_obj")
        type_name = count_param.get("data_type")
        is_signed = get_declared_type_signedness(
            raw_dt,
            type_name,
            fallback_signed=bool(count_param.get("is_signed", True)),
        )
        if inclusive:
            return "INT_SLESSEQUAL" if is_signed else "INT_LESSEQUAL"
        return "INT_SLESS" if is_signed else "INT_LESS"

    def _analysis_parameter_declared_signedness(
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

    def _readonly_reduction_counter_is_signed(
        self,
        returns: Sequence[ReturnInfo],
        count_param: Optional[Dict[str, Any]],
    ) -> Optional[bool]:
        saw_signed, saw_unsigned = self._readonly_reduction_counter_signedness_evidence(
            returns,
            count_param,
        )
        if saw_signed and saw_unsigned:
            return None
        if saw_signed:
            return True
        if saw_unsigned:
            return False
        return None

    def _readonly_reduction_counter_signedness_evidence(
        self,
        returns: Sequence[ReturnInfo],
        count_param: Optional[Dict[str, Any]],
    ) -> Tuple[bool, bool]:
        param_name = str(getattr(count_param, "get", lambda *_args, **_kwargs: "")("name", "") or "")
        if param_name:
            saw_signed = False
            saw_unsigned = False
            for ret in returns or ():
                for condition in getattr(ret, "conditions", None) or []:
                    condition_signed = self._readonly_reduction_condition_signedness(
                        condition,
                        param_name,
                    )
                    if condition_signed is True:
                        saw_signed = True
                    elif condition_signed is False:
                        saw_unsigned = True
            return saw_signed, saw_unsigned
        return False, False

    def _readonly_reduction_condition_signedness(
        self,
        condition: Optional[Condition],
        param_name: str,
    ) -> Optional[bool]:
        expr = getattr(condition, "expression", None)
        if (
            expr is None
            or expr.expr_type != ExpressionType.BINARY_OP
            or len(expr.operands) != 2
        ):
            return None
        if expr.operator not in {"INT_SLESS", "INT_SLESSEQUAL", "INT_LESS", "INT_LESSEQUAL"}:
            return None
        left, right = expr.operands
        if self._is_condition_counter_view(left, param_name) or self._is_condition_counter_view(right, param_name):
            return expr.operator.startswith("INT_S")
        return None

    def _readonly_reduction_condition_references_only_counter(
        self,
        condition: Optional[Condition],
        param_name: str,
    ) -> bool:
        expr = getattr(condition, "expression", None)
        if (
            expr is None
            or expr.expr_type != ExpressionType.BINARY_OP
            or len(expr.operands) != 2
        ):
            return False
        left, right = expr.operands
        left_affine = self._extract_affine_term(left, param_name)
        right_affine = self._extract_affine_term(right, param_name)
        left_const = getattr(left, "expr_type", None) == ExpressionType.CONSTANT
        right_const = getattr(right, "expr_type", None) == ExpressionType.CONSTANT
        if left_affine is not None and right_const:
            return True
        if right_affine is not None and left_const:
            return True
        return False

    def _return_overlaps_conditions(
        self,
        ret: ReturnInfo,
        conditions: Sequence[Condition],
    ) -> bool:
        ret_constraint_set = ConditionConstraintSet.from_conditions(ret.conditions or [])
        return ret_constraint_set.overlaps_with(conditions or [])

    def _return_conditions_imply_conditions(
        self,
        ret: ReturnInfo,
        conditions: Sequence[Condition],
    ) -> bool:
        return ConditionConstraintSet.from_conditions(ret.conditions or []).implies_all(
            conditions or []
        )

    def _detect_readonly_sum_accumulator_proof(
        self,
        high_function,
        analysis,
        pointer_param: dict,
        count_param: dict,
        *,
        counter_signed: bool,
        positive_conditions: Sequence[Condition] = (),
    ) -> Optional[ReductionAccumulatorProof]:
        proofs = self._collect_readonly_sum_accumulator_proofs(
            high_function,
            analysis,
            pointer_param,
            count_param,
            counter_signed=counter_signed,
            positive_conditions=positive_conditions,
        )
        return proofs[0] if proofs else None

    def _collect_readonly_sum_accumulator_proofs(
        self,
        high_function,
        analysis,
        pointer_param: dict,
        count_param: dict,
        *,
        counter_signed: bool,
        positive_conditions: Sequence[Condition] = (),
    ) -> List[ReductionAccumulatorProof]:
        patched_detect = self.__dict__.get("_detect_readonly_sum_accumulator_proof")
        if patched_detect is not None:
            proof = patched_detect(
                high_function,
                analysis,
                pointer_param,
                count_param,
                counter_signed=counter_signed,
                positive_conditions=positive_conditions,
            )
            return [proof] if proof is not None else []
        if high_function is None or not callable(getattr(high_function, "getBasicBlocks", None)):
            return []
        pointer_phis: List[Dict[str, object]] = []
        index_phis: List[Dict[str, object]] = []
        pointer_base_ref = self._location_base_ref_from_parameter(pointer_param, default_name="ptr")
        count_expr = self._parameter_expression(count_param)
        result_size = self._readonly_reduction_result_size(
            analysis,
            positive_conditions=positive_conditions,
        )
        all_ops = list(self._iter_pcode_ops(high_function))
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            pointer_match = self._match_pointer_progression_phi(op, pointer_param)
            if pointer_match is not None:
                pointer_phis.append(pointer_match)
            index_match = self._match_index_progression_phi(op)
            if index_match is not None:
                index_phis.append(index_match)

        vectorized_match = self._detect_vectorized_readonly_prefix_sum_accumulator_proof(
            all_ops,
            pointer_param,
            count_param,
            pointer_base_ref,
            count_expr,
            analysis,
            counter_signed=counter_signed,
            positive_conditions=positive_conditions,
        )
        matches: List[ReductionAccumulatorProof] = []
        seen_keys = set()
        if vectorized_match is not None:
            key = vectorized_match.stable_key() or repr(vectorized_match)
            seen_keys.add(key)
            matches.append(vectorized_match)

        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            accumulator_match = self._match_accumulator_phi(
                op,
                analysis,
                pointer_param,
                count_param,
                pointer_base_ref,
                count_expr,
                counter_signed,
                pointer_phis,
                index_phis,
                result_size=result_size,
                positive_conditions=positive_conditions,
            )
            if accumulator_match is not None:
                key = accumulator_match.stable_key() or repr(accumulator_match)
                if key in seen_keys:
                    continue
                seen_keys.add(key)
                matches.append(accumulator_match)

        if not pointer_phis and not index_phis:
            self._debug("Declined readonly reduction summary: no pointer/index progression PHI found")
        return matches

    def _detect_vectorized_readonly_prefix_sum_accumulator_proof(
        self,
        all_ops: Sequence[object],
        pointer_param: dict,
        count_param: dict,
        pointer_base_ref: LocationBaseRef,
        count_expr: Expression,
        analysis,
        counter_signed: Optional[bool] = None,
        *,
        positive_conditions: Sequence[Condition] = (),
    ) -> Optional[ReductionAccumulatorProof]:
        """Recognize a vector-body plus scalar-tail readonly prefix sum.

        Optimizing compilers often lower ``sum(base[0:count])`` into two
        loops: a vector/unrolled body over ``count & -K`` elements and a
        scalar tail from that rounded count to ``count``.  The normal
        recurrence detector intentionally expects a single canonical induction
        PHI, so this recognizer proves the object-level coverage of the two
        loops before collapsing them back to the scalar prefix-sum summary.
        """

        result_size = self._readonly_reduction_result_size(
            analysis,
            positive_conditions=positive_conditions,
        )
        if result_size <= 0:
            return None

        rounded_candidates = self._readonly_round_down_candidates(all_ops, count_param)
        if not rounded_candidates:
            self._debug("Declined vectorized readonly prefix-sum shape: no rounded-count candidate")
            return None

        if counter_signed is None:
            self._debug("Declined vectorized readonly prefix-sum shape: counter signedness is ambiguous")
            return None

        for rounded_candidate in rounded_candidates:
            rounded_vn = rounded_candidate.rounded_varnode
            lane_count = int(rounded_candidate.lane_count)
            start_index = int(rounded_candidate.start_index)
            tail_start_index_delta = int(getattr(rounded_candidate, "tail_start_index_delta", 0) or 0)
            if lane_count <= 1:
                continue
            vector_stride = lane_count * result_size
            start_offset = start_index * result_size
            vector_pointer = self._match_vector_prefix_pointer(
                all_ops,
                pointer_param,
                vector_stride=vector_stride,
                element_size=result_size,
                expected_start_offset=start_offset,
            )
            if vector_pointer is None:
                self._debug(
                    "Declined vectorized readonly prefix-sum candidate: "
                    f"no vector pointer progression for lanes={lane_count}, start_index={start_index}"
                )
                continue
            pointer_phi, vector_lane_base_offset, vector_pointer_base_offset = vector_pointer
            if not self._vector_prefix_lanes_cover_block(
                all_ops,
                pointer_phi,
                base_offset=vector_lane_base_offset,
                vector_stride=vector_stride,
                element_size=result_size,
            ):
                self._debug(
                    "Declined vectorized readonly prefix-sum candidate: "
                    f"vector lanes do not cover one contiguous block (lanes={lane_count}, start_index={start_index})"
                )
                continue
            vector_region_conditions = list(positive_conditions or [])
            count_expr = self._parameter_expression(count_param)
            vector_region_conditions.append(
                Condition(
                    Expression.binary_op(
                        self._readonly_reduction_count_compare_op(
                            count_param,
                            signed_counter=counter_signed,
                            inclusive=True,
                        ),
                        Expression.constant(start_index + lane_count, count_expr.size or 4),
                        count_expr,
                    ),
                    False,
                )
            )
            return_term_proof = self._vector_prefix_lanes_have_unit_terms_in_positive_return(
                analysis,
                pointer_param,
                vector_region_conditions,
                global_start_offset=start_offset,
                vector_stride=vector_stride,
                element_size=result_size,
            )
            def_use_term_proof = self._vector_prefix_lanes_contribute_additively_to_return(
                all_ops,
                pointer_phi,
                base_offset=vector_lane_base_offset,
                vector_stride=vector_stride,
                element_size=result_size,
            )
            return_term_refs = self._vector_prefix_unit_term_positive_return_refs(
                analysis,
                pointer_param,
                vector_region_conditions,
                global_start_offset=start_offset,
                vector_stride=vector_stride,
                element_size=result_size,
            )
            (
                def_use_return_refs,
                def_use_return_value_refs,
            ) = self._vector_prefix_lane_return_refs(
                all_ops,
                pointer_phi,
                base_offset=vector_lane_base_offset,
                vector_stride=vector_stride,
                element_size=result_size,
            )
            if not return_term_refs:
                if return_term_proof is False:
                    self._debug(
                        "Vectorized readonly prefix-sum candidate has no exact positive-return witness; "
                        "falling back to def-use return-site proof "
                        f"(lanes={lane_count}, start_index={start_index})"
                    )
                elif return_term_proof is None:
                    self._debug(
                        "Vectorized readonly prefix-sum candidate found no overlapping exact positive-return witness; "
                        "falling back to def-use return-site proof "
                        f"(lanes={lane_count}, start_index={start_index})"
                    )
            if not def_use_term_proof:
                self._debug(
                    "Declined vectorized readonly prefix-sum candidate: "
                    f"vector lanes do not flow additively to the return (lanes={lane_count}, start_index={start_index})"
                )
                continue
            if not def_use_return_refs and not def_use_return_value_refs and not return_term_refs:
                self._debug(
                    "Declined vectorized readonly prefix-sum candidate: "
                    "vector lane def-use proof has no concrete return-site refs "
                    f"(lanes={lane_count}, start_index={start_index})"
                )
                continue
            if not (
                self._has_vector_countdown_loop(
                    all_ops,
                    rounded_vn,
                    lane_count=lane_count,
                )
                or self._has_vector_loop_bound_to_rounded_count(
                    all_ops,
                    pointer_phi,
                    pointer_param,
                    rounded_vn,
                    element_size=result_size,
                    base_offset=vector_pointer_base_offset,
                    vector_stride=vector_stride,
                )
            ):
                self._debug(
                    "Declined vectorized readonly prefix-sum candidate: "
                    "no object-centric bound tying vector cursor to rounded count "
                    f"(lanes={lane_count}, start_index={start_index})"
                )
                continue
            if not self._has_scalar_tail_from_rounded_count(
                all_ops,
                pointer_param,
                count_param,
                rounded_vn,
                element_size=result_size,
                start_offset=start_offset + tail_start_index_delta * result_size,
                start_index=start_index + tail_start_index_delta,
                max_unrolled_terms=max(0, lane_count - 1),
                tail_index_source_varnode=getattr(rounded_candidate, "tail_index_source_varnode", None),
                lane_count=lane_count,
            ):
                self._debug(
                    "Declined vectorized readonly prefix-sum candidate: "
                    f"no scalar tail from rounded count to full count (lanes={lane_count}, start_index={start_index})"
                )
                continue
            seed_terms = self._vector_prefix_seed_terms_from_exact_returns(
                analysis,
                pointer_param,
                count_param,
                positive_conditions,
                start_index=start_index,
                element_size=result_size,
            )
            seed_term_count = None
            if seed_terms is None:
                seed_terms = ()
                seed_term_count = int(start_index) if int(start_index) > 0 else None
            self._debug(
                "Recovered vectorized readonly prefix-sum accumulator proof "
                f"(lanes={lane_count}, start_index={start_index}, element_size={result_size})"
            )
            return ReductionAccumulatorProof(
                reduction_kind="memory_sum",
                pointer_base_ref=pointer_base_ref,
                count_parameter_name=count_param.get("name", "count"),
                count_parameter_index=count_param.get("index"),
                count_parameter_storage_identity_key=self._parameter_storage_identity_key(count_param),
                limit_expr=count_expr,
                result_size=max(1, int(result_size)),
                stride=int(result_size),
                element_size=int(result_size),
                start_offset=int(start_offset),
                start_index=int(start_index),
                index_step=1,
                index_scale=int(result_size),
                signed_counter=counter_signed,
                seed_terms=tuple(seed_terms),
                seed_term_count=seed_term_count,
                lane_terms=(),
                guard_constraints=tuple(positive_conditions or ()),
                entry_block_ref=self._make_pcode_block_ref(getattr(pointer_phi, "getParent", lambda: None)()),
                return_op_refs=self._dedupe_pcode_refs(tuple(return_term_refs) + tuple(def_use_return_refs)),
                return_value_op_refs=self._dedupe_pcode_refs(tuple(def_use_return_value_refs)),
                return_region_value_proven=bool(return_term_refs or def_use_return_refs or def_use_return_value_refs),
                source="vectorized_readonly_prefix_sum",
            )
        return None

    def _vector_prefix_seed_terms_from_exact_returns(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        seed_region_conditions: Sequence[Condition],
        *,
        start_index: int,
        element_size: int,
    ) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        """Recover pre-loop seed terms for vectorized reductions.

        A vectorized reduction can start at a peeled logical index without
        being a true prefix.  For example, wrong-tail uses seed terms at
        offsets 0 and 8, then starts the loop at index 3.  Treating every
        skipped index as an implicit prefix seed would be unsound, so this
        derives the seed set only from exact object-level return witnesses.
        """

        if analysis is None or int(start_index) <= 0 or int(element_size) <= 0:
            return None
        start_offset = int(start_index) * int(element_size)
        count_name = str(count_param.get("name") or "")
        candidates: Dict[Tuple[Tuple[Any, ...], ...], Tuple[ReadonlyReductionTermRef, ...]] = {}
        for ret in getattr(analysis, "returns", None) or ():
            if not self._return_overlaps_conditions(ret, seed_region_conditions):
                continue
            exact_count = self._exact_counter_value_from_conditions(ret.conditions or [], count_name)
            if exact_count is None or int(exact_count) <= int(start_index):
                continue
            extracted = self._extract_readonly_return_terms_and_bias(
                analysis,
                pointer_param,
                ret,
                None,
            )
            if extracted is None:
                self._debug(
                    "Skipped vectorized readonly seed witness: "
                    f"no readonly term extraction for count={exact_count}"
                )
                continue
            terms, constant_bias = extracted
            result_size = max(1, int(getattr(ret.value, "size", 0) or element_size))
            if self._normalize_readonly_constant_bias(int(constant_bias), result_size) != 0:
                self._debug(
                    "Skipped vectorized readonly seed witness: "
                    f"non-zero constant bias for count={exact_count}"
                )
                continue
            term_counts = Counter((int(term.byte_offset), int(term.access_size)) for term in terms or ())
            expected_loop_offsets = tuple(
                range(start_offset, int(exact_count) * int(element_size), int(element_size))
            )
            if not expected_loop_offsets:
                continue
            missing_loop_term = False
            for offset in expected_loop_offsets:
                key = (int(offset), int(element_size))
                if term_counts.get(key, 0) <= 0:
                    missing_loop_term = True
                    break
                term_counts[key] -= 1
                if term_counts[key] <= 0:
                    term_counts.pop(key, None)
            if missing_loop_term:
                self._debug(
                    "Skipped vectorized readonly seed witness: "
                    f"missing suffix term for count={exact_count}, expected_offsets={list(expected_loop_offsets)}"
                )
                continue
            seed_terms: List[ReadonlyReductionTermRef] = []
            valid_seed = True
            for (byte_offset, access_size), count in sorted(term_counts.items()):
                if count != 1:
                    valid_seed = False
                    break
                if int(access_size) != int(element_size):
                    valid_seed = False
                    break
                if int(byte_offset) < 0 or int(byte_offset) >= start_offset:
                    valid_seed = False
                    break
                if int(byte_offset) % int(element_size) != 0:
                    valid_seed = False
                    break
                seed_terms.append(
                    ReadonlyReductionTermRef(
                        byte_offset=int(byte_offset),
                        access_size=int(access_size),
                    )
                )
            if not valid_seed:
                self._debug(
                    "Skipped vectorized readonly seed witness: "
                    f"remaining terms are not valid seed terms for count={exact_count}"
                )
                continue
            seed_key = tuple(term.stable_key() for term in seed_terms)
            candidates.setdefault(seed_key, tuple(seed_terms))
        if not candidates:
            candidates.update(
                self._vector_prefix_seed_terms_from_materialized_region_returns(
                    analysis,
                    pointer_param,
                    seed_region_conditions,
                    start_offset=start_offset,
                    element_size=element_size,
                )
            )
        if len(candidates) != 1:
            if len(candidates) > 1:
                self._debug("Declined vectorized readonly prefix-sum seed recovery: ambiguous seed witnesses")
            return None
        recovered = next(iter(candidates.values()))
        self._debug(
            "Recovered vectorized readonly prefix-sum seed terms from object-level returns: "
            f"offsets={[term.byte_offset for term in recovered]}"
        )
        return recovered

    def _vector_prefix_seed_terms_from_materialized_region_returns(
        self,
        analysis,
        pointer_param: dict,
        seed_region_conditions: Sequence[Condition],
        *,
        start_offset: int,
        element_size: int,
    ) -> Dict[Tuple[Tuple[Any, ...], ...], Tuple[ReadonlyReductionTermRef, ...]]:
        candidates: Dict[Tuple[Tuple[Any, ...], ...], Tuple[ReadonlyReductionTermRef, ...]] = {}
        if analysis is None or int(start_offset) <= 0 or int(element_size) <= 0:
            return candidates
        for ret in getattr(analysis, "returns", None) or ():
            if not self._return_overlaps_conditions(ret, seed_region_conditions):
                continue
            extracted = self._extract_readonly_return_terms_and_bias(
                analysis,
                pointer_param,
                ret,
                None,
            )
            if extracted is None:
                continue
            terms, constant_bias = extracted
            result_size = max(1, int(getattr(ret.value, "size", 0) or element_size))
            if self._normalize_readonly_constant_bias(int(constant_bias), result_size) != 0:
                continue
            term_counts = Counter((int(term.byte_offset), int(term.access_size)) for term in terms or ())
            loop_offsets = sorted(
                byte_offset
                for byte_offset, access_size in term_counts
                if int(access_size) == int(element_size) and int(byte_offset) >= int(start_offset)
            )
            if not loop_offsets:
                continue
            expected_loop_offsets = list(range(int(start_offset), max(loop_offsets) + int(element_size), int(element_size)))
            if loop_offsets != expected_loop_offsets:
                continue
            for offset in expected_loop_offsets:
                key = (int(offset), int(element_size))
                if term_counts.get(key, 0) != 1:
                    term_counts.clear()
                    break
                term_counts.pop(key, None)
            if not term_counts:
                continue
            seed_terms: List[ReadonlyReductionTermRef] = []
            valid_seed = True
            for (byte_offset, access_size), count in sorted(term_counts.items()):
                if (
                    count != 1
                    or int(access_size) != int(element_size)
                    or int(byte_offset) < 0
                    or int(byte_offset) >= int(start_offset)
                    or int(byte_offset) % int(element_size) != 0
                ):
                    valid_seed = False
                    break
                seed_terms.append(
                    ReadonlyReductionTermRef(
                        byte_offset=int(byte_offset),
                        access_size=int(access_size),
                    )
                )
            if not valid_seed:
                continue
            seed_key = tuple(term.stable_key() for term in seed_terms)
            candidates.setdefault(seed_key, tuple(seed_terms))
        return candidates

    def _readonly_reduction_result_size(
        self,
        analysis,
        *,
        positive_conditions: Sequence[Condition] = (),
    ) -> int:
        returns = list(getattr(analysis, "returns", None) or [])
        if positive_conditions:
            overlapping = [
                ret for ret in returns
                if self._return_overlaps_conditions(ret, positive_conditions)
            ]
            if overlapping:
                returns = overlapping
        for ret in returns:
            value = getattr(ret, "value", None)
            size = int(getattr(value, "size", 0) or 0)
            if size > 0:
                return size
        return 4

    def _readonly_round_down_candidates(
        self,
        all_ops: Sequence[object],
        count_param: dict,
    ) -> List[ReadonlyRoundedCountCandidate]:
        candidates: List[ReadonlyRoundedCountCandidate] = []
        seen: set[Tuple[Any, ...]] = set()
        for op in all_ops:
            candidate = self._readonly_round_down_candidate_from_op(op, count_param)
            if candidate is None:
                continue
            key = (
                self._varnode_cache_key(candidate.rounded_varnode),
                int(candidate.lane_count),
                int(candidate.start_index),
                int(candidate.tail_start_index_delta),
                self._varnode_cache_key(candidate.tail_index_source_varnode),
            )
            if key in seen:
                continue
            seen.add(key)
            candidates.append(candidate)
        return candidates

    def _readonly_round_down_candidate_from_op(
        self,
        op,
        count_param: dict,
    ) -> Optional[ReadonlyRoundedCountCandidate]:
        mnemonic = getattr(op, "getMnemonic", lambda: None)()
        if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
            return None
        if mnemonic == "INT_AND":
            return self._readonly_round_down_mask_candidate(op, count_param)
        if mnemonic == "INT_MULT":
            return self._readonly_round_down_multiply_candidate(op, count_param)
        if mnemonic == "INT_LEFT":
            return self._readonly_round_down_shift_candidate(op, count_param)
        return None

    def _readonly_round_down_mask_candidate(
        self,
        op,
        count_param: dict,
    ) -> Optional[ReadonlyRoundedCountCandidate]:
        left = self._follow_passthrough_varnode(op.getInput(0))
        right = self._follow_passthrough_varnode(op.getInput(1))
        mask = self._varnode_unsigned_constant_value(left)
        value = right
        if mask is None:
            mask = self._varnode_unsigned_constant_value(right)
            value = left
        if mask is None:
            return None
        source = self._rounded_count_source(value, count_param)
        if source is None:
            return None
        source_vn, start_index = source
        count_width_bits = self._infer_counter_bit_width(
            self._trace_varnode_expression(value),
            str(count_param.get("name", "") or ""),
        )
        if count_width_bits is None:
            count_width_bits = self._varnode_bit_width(source_vn)
        if count_width_bits is None:
            count_width_bits = self._varnode_bit_width(value)
        if count_width_bits is None:
            count_width_bits = max(1, int(count_param.get("size", 0) or 0)) * 8
        lane_count = self._power_of_two_rounding_from_mask(mask, count_width_bits=count_width_bits)
        if lane_count is None:
            return None
        output = getattr(op, "getOutput", lambda: None)()
        if output is None:
            return None
        return ReadonlyRoundedCountCandidate(
            rounded_varnode=output,
            lane_count=int(lane_count),
            start_index=int(start_index),
        )

    def _readonly_round_down_multiply_candidate(
        self,
        op,
        count_param: dict,
    ) -> Optional[ReadonlyRoundedCountCandidate]:
        left = self._follow_passthrough_varnode(op.getInput(0))
        right = self._follow_passthrough_varnode(op.getInput(1))
        lane_count = self._varnode_unsigned_constant_value(right)
        quotient = left
        if lane_count is None:
            lane_count = self._varnode_unsigned_constant_value(left)
            quotient = right
        lane_count = self._valid_power_of_two_lane_count(lane_count)
        if lane_count is None:
            return None
        source = self._round_down_quotient_source(quotient, count_param, lane_count)
        if source is None:
            return None
        output = getattr(op, "getOutput", lambda: None)()
        if output is None:
            return None
        source_vn, start_index, tail_start_index_delta = source
        return ReadonlyRoundedCountCandidate(
            rounded_varnode=output,
            lane_count=int(lane_count),
            start_index=int(start_index),
            tail_start_index_delta=int(tail_start_index_delta),
            tail_index_source_varnode=source_vn if int(tail_start_index_delta) > 0 else None,
        )

    def _readonly_round_down_shift_candidate(
        self,
        op,
        count_param: dict,
    ) -> Optional[ReadonlyRoundedCountCandidate]:
        value = self._follow_passthrough_varnode(op.getInput(0))
        shift = self._varnode_unsigned_constant_value(op.getInput(1))
        if shift is None:
            return None
        lane_count = self._valid_power_of_two_lane_count(1 << int(shift))
        if lane_count is None:
            return None
        source = self._round_down_quotient_source(value, count_param, lane_count)
        if source is None:
            return None
        output = getattr(op, "getOutput", lambda: None)()
        if output is None:
            return None
        source_vn, start_index, tail_start_index_delta = source
        return ReadonlyRoundedCountCandidate(
            rounded_varnode=output,
            lane_count=int(lane_count),
            start_index=int(start_index),
            tail_start_index_delta=int(tail_start_index_delta),
            tail_index_source_varnode=source_vn if int(tail_start_index_delta) > 0 else None,
        )

    def _round_down_quotient_source(
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

    def _valid_power_of_two_lane_count(self, value: Optional[int]) -> Optional[int]:
        if value is None:
            return None
        lane_count = int(value)
        if lane_count <= 1:
            return None
        if lane_count & (lane_count - 1):
            return None
        return lane_count

    def _rounded_count_source(
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

    def _power_of_two_rounding_from_mask(self, mask: int, *, count_width_bits: int) -> Optional[int]:
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

    def _varnode_bit_width(self, varnode) -> Optional[int]:
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

    def _match_vector_prefix_pointer(
        self,
        all_ops: Sequence[object],
        pointer_param: dict,
        *,
        vector_stride: int,
        element_size: int,
        expected_start_offset: int = 0,
    ) -> Optional[Tuple[object, int, int]]:
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            phi_output = getattr(op, "getOutput", lambda: None)()
            if phi_output is None:
                continue
            if not self._phi_has_pointer_step(
                all_ops,
                phi_output,
                step_bytes=vector_stride,
            ):
                continue
            lane_offsets = self._load_byte_offsets_from_pointer(all_ops, phi_output, element_size=element_size)
            if not lane_offsets:
                continue
            min_offset = min(lane_offsets)
            lane_base_offset = -int(min_offset)
            if lane_base_offset < 0:
                continue
            seed_offsets = self._pointer_phi_seed_offsets(op, pointer_param)
            for seed_offset in seed_offsets:
                global_lane_start = int(seed_offset) + int(min_offset)
                if global_lane_start == int(expected_start_offset):
                    return phi_output, lane_base_offset, int(seed_offset)
            if int(expected_start_offset) == 0 and not seed_offsets and self._has_pointer_base_plus_constant(
                all_ops,
                pointer_param,
                0,
            ):
                return phi_output, lane_base_offset, 0
            if int(expected_start_offset) == 0 and 0 in seed_offsets:
                return phi_output, lane_base_offset, 0
        return None

    def _pointer_phi_seed_offsets(
        self,
        phi_op,
        pointer_param: dict,
    ) -> Tuple[int, ...]:
        offsets: List[int] = []
        input_count = int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0)
        for index in range(input_count):
            try:
                value = self._follow_passthrough_varnode(phi_op.getInput(index))
            except Exception:
                continue
            offset = self._byte_offset_from_parameter_pointer(value, pointer_param)
            if offset is not None:
                offsets.append(int(offset))
        return tuple(dict.fromkeys(offsets))

    def _byte_offset_from_parameter_pointer(
        self,
        candidate_vn,
        pointer_param: dict,
    ) -> Optional[int]:
        candidate_vn = self._follow_passthrough_varnode(candidate_vn)
        def_op = getattr(candidate_vn, "getDef", lambda: None)()
        if def_op is not None:
            mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
            if mnemonic in {"INT_ADD", "PTRSUB"} and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
                left = self._follow_passthrough_varnode(def_op.getInput(0))
                right = self._follow_passthrough_varnode(def_op.getInput(1))
                right_const = self._signed_varnode_constant_value(right)
                if right_const is not None:
                    left_offset = self._byte_offset_from_parameter_pointer(left, pointer_param)
                    if left_offset is not None:
                        return int(left_offset) + int(right_const)
                if mnemonic == "INT_ADD":
                    left_const = self._signed_varnode_constant_value(left)
                    if left_const is not None:
                        right_offset = self._byte_offset_from_parameter_pointer(right, pointer_param)
                        if right_offset is not None:
                            return int(right_offset) + int(left_const)
                return None
            if mnemonic == "PTRADD" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 3:
                base = self._follow_passthrough_varnode(def_op.getInput(0))
                index = self._signed_varnode_constant_value(self._follow_passthrough_varnode(def_op.getInput(1)))
                elem = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(2)))
                if index is None or elem is None:
                    return None
                base_offset = self._byte_offset_from_parameter_pointer(base, pointer_param)
                if base_offset is None:
                    return None
                return int(base_offset) + int(index) * int(elem)
        if self._varnode_matches_parameter(candidate_vn, pointer_param):
            return 0
        return None

    def _phi_has_pointer_step(
        self,
        all_ops: Sequence[object],
        phi_output,
        *,
        step_bytes: int,
    ) -> bool:
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "PTRADD":
                continue
            if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 3:
                continue
            base = self._follow_passthrough_varnode(op.getInput(0))
            if not self._same_varnode_value(base, phi_output):
                continue
            index = self._signed_varnode_constant_value(self._follow_passthrough_varnode(op.getInput(1)))
            elem = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(op.getInput(2)))
            if index is not None and elem is not None and int(index) * int(elem) == int(step_bytes):
                return True
        return False

    def _has_pointer_base_plus_constant(
        self,
        all_ops: Sequence[object],
        pointer_param: dict,
        byte_offset: int,
    ) -> bool:
        if int(byte_offset) == 0:
            return True
        for op in all_ops:
            mnemonic = getattr(op, "getMnemonic", lambda: None)()
            if mnemonic in {"INT_ADD", "PTRSUB"} and int(getattr(op, "getNumInputs", lambda: 0)() or 0) >= 2:
                left = self._follow_passthrough_varnode(op.getInput(0))
                right = self._follow_passthrough_varnode(op.getInput(1))
                if (
                    self._varnode_matches_parameter(left, pointer_param)
                    and self._signed_varnode_constant_value(right) == int(byte_offset)
                ):
                    return True
                if (
                    mnemonic == "INT_ADD"
                    and self._varnode_matches_parameter(right, pointer_param)
                    and self._signed_varnode_constant_value(left) == int(byte_offset)
                ):
                    return True
            if mnemonic == "PTRADD" and int(getattr(op, "getNumInputs", lambda: 0)() or 0) >= 3:
                base = self._follow_passthrough_varnode(op.getInput(0))
                index = self._signed_varnode_constant_value(self._follow_passthrough_varnode(op.getInput(1)))
                elem = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(op.getInput(2)))
                if (
                    self._varnode_matches_parameter(base, pointer_param)
                    and index is not None
                    and elem is not None
                    and int(index) * int(elem) == int(byte_offset)
                ):
                    return True
        return False

    def _load_byte_offsets_from_pointer(
        self,
        all_ops: Sequence[object],
        pointer_phi,
        *,
        element_size: int,
    ) -> List[int]:
        offsets: List[int] = []
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "LOAD":
                continue
            if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
                continue
            output = getattr(op, "getOutput", lambda: None)()
            load_size = max(1, int(getattr(output, "getSize", lambda: element_size)() or element_size))
            address = self._follow_passthrough_varnode(op.getInput(1))
            byte_offset = self._byte_offset_from_pointer(address, pointer_phi)
            if byte_offset is None:
                continue
            for lane_delta in range(0, load_size, element_size):
                offsets.append(int(byte_offset) + int(lane_delta))
        return offsets

    def _byte_offset_from_pointer(self, address_varnode, pointer_phi) -> Optional[int]:
        def_op = getattr(address_varnode, "getDef", lambda: None)()
        if def_op is not None and getattr(def_op, "getMnemonic", lambda: None)() == "PTRADD":
            if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 3:
                base = self._follow_passthrough_varnode(def_op.getInput(0))
                if self._same_varnode_value(base, pointer_phi):
                    index = self._signed_varnode_constant_value(self._follow_passthrough_varnode(def_op.getInput(1)))
                    elem = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(2)))
                    if index is not None and elem is not None:
                        return int(index) * int(elem)
        if self._same_varnode_value(address_varnode, pointer_phi):
            return 0
        return None

    def _vector_prefix_lanes_cover_block(
        self,
        all_ops: Sequence[object],
        pointer_phi,
        *,
        base_offset: int,
        vector_stride: int,
        element_size: int,
    ) -> bool:
        raw_offsets = self._load_byte_offsets_from_pointer(all_ops, pointer_phi, element_size=element_size)
        normalized = sorted({int(offset) + int(base_offset) for offset in raw_offsets})
        expected = list(range(0, int(vector_stride), int(element_size)))
        return normalized == expected

    def _vector_prefix_lanes_have_unit_terms_in_positive_return(
        self,
        analysis,
        pointer_param: dict,
        vector_region_conditions: Sequence[Condition],
        *,
        global_start_offset: int = 0,
        vector_stride: int,
        element_size: int,
    ) -> Optional[bool]:
        status, _refs = self._vector_prefix_positive_return_term_proof(
            analysis,
            pointer_param,
            vector_region_conditions,
            global_start_offset=global_start_offset,
            vector_stride=vector_stride,
            element_size=element_size,
            require_site_refs=False,
        )
        return status

    def _vector_prefix_unit_term_positive_return_refs(
        self,
        analysis,
        pointer_param: dict,
        vector_region_conditions: Sequence[Condition],
        *,
        global_start_offset: int = 0,
        vector_stride: int,
        element_size: int,
    ) -> Tuple[PcodeOpRef, ...]:
        status, refs = self._vector_prefix_positive_return_term_proof(
            analysis,
            pointer_param,
            vector_region_conditions,
            global_start_offset=global_start_offset,
            vector_stride=vector_stride,
            element_size=element_size,
            require_site_refs=True,
        )
        if status is not True:
            return ()
        return refs

    def _vector_prefix_positive_return_term_proof(
        self,
        analysis,
        pointer_param: dict,
        vector_region_conditions: Sequence[Condition],
        *,
        global_start_offset: int = 0,
        vector_stride: int,
        element_size: int,
        require_site_refs: bool,
    ) -> Tuple[Optional[bool], Tuple[PcodeOpRef, ...]]:
        expected = {
            (int(byte_offset), int(element_size))
            for byte_offset in range(
                0,
                int(global_start_offset) + int(vector_stride),
                int(element_size),
            )
        }
        expected_counts = Counter({term_key: 1 for term_key in expected})
        refs: Dict[Tuple[Any, ...], PcodeOpRef] = {}
        saw_overlapping_return = False
        for ret in getattr(analysis, "returns", None) or ():
            if not self._return_overlaps_conditions(ret, vector_region_conditions):
                continue
            saw_overlapping_return = True
            value = _reduce_expression_under_conditions(ret.value, ret.conditions or ())
            terms = self._extract_readonly_reduction_terms(
                value,
                getattr(analysis, "parameters", None) or (),
                pointer_param,
            )
            if terms is None and value is not ret.value:
                terms = self._extract_readonly_reduction_terms(
                    ret.value,
                    getattr(analysis, "parameters", None) or (),
                    pointer_param,
                )
            if terms is None:
                return False, ()
            counts = Counter((int(term.byte_offset), int(term.access_size)) for term in terms)
            if counts != expected_counts:
                return False, ()
            ref = self._pcode_op_ref_from_return_info(ret)
            if ref is None:
                if require_site_refs:
                    return False, ()
                continue
            refs.setdefault(ref.stable_key(), ref)
        if not saw_overlapping_return:
            return None, ()
        return True, tuple(sorted(refs.values(), key=lambda ref: repr(ref.stable_key())))

    def _vector_prefix_lanes_contribute_additively_to_return(
        self,
        all_ops: Sequence[object],
        pointer_phi,
        *,
        base_offset: int,
        vector_stride: int,
        element_size: int,
    ) -> bool:
        expected_offsets = set(range(0, int(vector_stride), int(element_size)))
        expected_counts = Counter({offset: 1 for offset in expected_offsets})
        contributing_counts: Counter[int] = Counter()
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "LOAD":
                continue
            if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
                continue
            output = getattr(op, "getOutput", lambda: None)()
            if output is None:
                continue
            load_size = max(1, int(getattr(output, "getSize", lambda: element_size)() or element_size))
            address = self._follow_passthrough_varnode(op.getInput(1))
            byte_offset = self._byte_offset_from_pointer(address, pointer_phi)
            if byte_offset is None:
                continue
            normalized_offsets = [
                int(byte_offset) + int(base_offset) + lane_delta
                for lane_delta in range(0, load_size, element_size)
            ]
            if any(offset not in expected_offsets for offset in normalized_offsets):
                if self._load_lanes_flow_additively_to_return(
                    output,
                    load_size=load_size,
                    element_size=element_size,
                    pointer_phi=pointer_phi,
                    expected_offsets=expected_offsets,
                    base_offset=base_offset,
                ):
                    self._debug(
                        "Declined vectorized readonly prefix-sum load contribution: "
                        f"unexpected_offsets={tuple(normalized_offsets)}"
                    )
                    return False
                continue
            if self._load_lanes_flow_additively_to_return(
                output,
                load_size=load_size,
                element_size=element_size,
                pointer_phi=pointer_phi,
                expected_offsets=expected_offsets,
                base_offset=base_offset,
            ):
                contributing_counts.update(normalized_offsets)
        return contributing_counts == expected_counts

    def _vector_prefix_lane_return_refs(
        self,
        all_ops: Sequence[object],
        pointer_phi,
        *,
        base_offset: int,
        vector_stride: int,
        element_size: int,
    ) -> Tuple[Tuple[PcodeOpRef, ...], Tuple[PcodeOpRef, ...]]:
        expected_offsets = set(range(0, int(vector_stride), int(element_size)))
        expected_counts = Counter({offset: 1 for offset in expected_offsets})
        contributing_counts: Counter[int] = Counter()
        return_refs: Dict[Tuple[Any, ...], PcodeOpRef] = {}
        return_value_refs: Dict[Tuple[Any, ...], PcodeOpRef] = {}
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "LOAD":
                continue
            if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
                continue
            output = getattr(op, "getOutput", lambda: None)()
            if output is None:
                continue
            load_size = max(1, int(getattr(output, "getSize", lambda: element_size)() or element_size))
            address = self._follow_passthrough_varnode(op.getInput(1))
            byte_offset = self._byte_offset_from_pointer(address, pointer_phi)
            if byte_offset is None:
                continue
            normalized_offsets = [
                int(byte_offset) + int(base_offset) + lane_delta
                for lane_delta in range(0, load_size, element_size)
            ]
            if any(offset not in expected_offsets for offset in normalized_offsets):
                continue
            if not self._load_lanes_flow_additively_to_return(
                output,
                load_size=load_size,
                element_size=element_size,
                pointer_phi=pointer_phi,
                expected_offsets=expected_offsets,
                base_offset=base_offset,
            ):
                continue
            contributing_counts.update(normalized_offsets)
            for ref in self._reachable_return_op_refs_from_varnodes((output,)):
                return_refs.setdefault(ref.stable_key(), ref)
            for ref in self._reachable_return_value_op_refs_from_varnodes((output,)):
                return_value_refs.setdefault(ref.stable_key(), ref)
        if contributing_counts != expected_counts:
            return (), ()
        return (
            tuple(sorted(return_refs.values(), key=lambda ref: repr(ref.stable_key()))),
            tuple(sorted(return_value_refs.values(), key=lambda ref: repr(ref.stable_key()))),
        )

    def _vector_prefix_lane_return_value_refs(
        self,
        all_ops: Sequence[object],
        pointer_phi,
        *,
        base_offset: int,
        vector_stride: int,
        element_size: int,
    ) -> Tuple[PcodeOpRef, ...]:
        _return_refs, return_value_refs = self._vector_prefix_lane_return_refs(
            all_ops,
            pointer_phi,
            base_offset=base_offset,
            vector_stride=vector_stride,
            element_size=element_size,
        )
        return return_value_refs

    def _dedupe_pcode_refs(
        self,
        refs: Sequence[PcodeOpRef],
    ) -> Tuple[PcodeOpRef, ...]:
        unique: Dict[Tuple[Any, ...], PcodeOpRef] = {}
        for ref in refs or ():
            if ref is None:
                continue
            unique[ref.stable_key()] = ref
        return tuple(sorted(unique.values(), key=lambda ref: repr(ref.stable_key())))

    def _load_lanes_flow_additively_to_return(
        self,
        load_output,
        *,
        load_size: int,
        element_size: int,
        pointer_phi=None,
        expected_offsets: Sequence[int] = (),
        base_offset: int = 0,
    ) -> bool:
        required_lanes = max(1, int(load_size) // max(1, int(element_size)))
        if required_lanes <= 1:
            count = self._varnode_additive_return_contribution_count(load_output)
            if count != 1:
                self._debug(
                    "Declined vectorized readonly prefix-sum load contribution: "
                    f"load={self._varnode_cache_key(load_output)} contribution_count={count}"
                )
            return count == 1
        lane_roots = self._collect_scalar_lane_roots(load_output, element_size=element_size)
        if len(lane_roots) != required_lanes:
            self._debug(
                "Declined vectorized readonly prefix-sum load contribution: "
                f"load={self._varnode_cache_key(load_output)} "
                f"lane_roots={len(lane_roots)} required_lanes={required_lanes}"
            )
            return False
        counts = tuple(
            self._varnode_additive_return_contribution_count(lane)
            for lane in lane_roots
        )
        if any(count != 1 for count in counts):
            self._debug(
                "Declined vectorized readonly prefix-sum load contribution: "
                f"load={self._varnode_cache_key(load_output)} lane_counts={counts}"
            )
            return False
        return True

    def _load_lanes_flow_additively_to_any_return(
        self,
        load_output,
        *,
        load_size: int,
        element_size: int,
    ) -> bool:
        required_lanes = max(1, int(load_size) // max(1, int(element_size)))
        if required_lanes <= 1:
            return self._varnode_has_additive_return_contribution(load_output)
        lane_roots = self._collect_scalar_lane_roots(load_output, element_size=element_size)
        if len(lane_roots) != required_lanes:
            return False
        return all(self._varnode_has_additive_return_contribution(lane) for lane in lane_roots)

    def _collect_scalar_lane_roots(
        self,
        start_varnode,
        *,
        element_size: int,
        budget: int = 64,
    ) -> Tuple[object, ...]:
        lanes: List[object] = []
        stack = [start_varnode]
        seen = set()
        while stack and len(seen) < budget:
            current = stack.pop()
            key = self._varnode_cache_key(current)
            if key in seen:
                continue
            seen.add(key)
            for op in self._iter_varnode_descendant_ops(current):
                mnemonic = getattr(op, "getMnemonic", lambda: None)()
                output = getattr(op, "getOutput", lambda: None)()
                if output is None:
                    continue
                output_size = max(1, int(getattr(output, "getSize", lambda: element_size)() or element_size))
                if mnemonic == "SUBPIECE" and output_size == int(element_size):
                    lanes.append(output)
                    continue
                if mnemonic in {"INT_RIGHT", "COPY", "CAST", "INT_ZEXT", "INT_SEXT"}:
                    stack.append(output)
        unique: Dict[Tuple[Any, ...], object] = {}
        for lane in lanes:
            key = self._varnode_cache_key(lane)
            if key is not None:
                unique[key] = lane
        return tuple(unique.values())

    def _varnode_additive_return_contribution_count(
        self,
        start_varnode,
        *,
        budget: int = 128,
    ) -> int:
        allowed = {
            "INT_ADD",
            "COPY",
            "CAST",
            "INT_ZEXT",
            "INT_SEXT",
            "SUBPIECE",
            "MULTIEQUAL",
        }
        stack = [(start_varnode, 1)]
        seen_coefficients: Dict[Tuple[Any, ...], int] = {}
        return_count = 0
        steps = 0
        while stack and steps < budget:
            current, coefficient = stack.pop()
            steps += 1
            if coefficient <= 0:
                continue
            key = self._varnode_cache_key(current)
            previous = seen_coefficients.get(key)
            if previous is not None and previous >= coefficient:
                continue
            seen_coefficients[key] = coefficient
            for op in self._iter_varnode_descendant_ops(current):
                mnemonic = getattr(op, "getMnemonic", lambda: None)()
                input_multiplicity = self._varnode_input_multiplicity(op, current)
                if input_multiplicity <= 0:
                    continue
                if mnemonic == "RETURN":
                    return_count += coefficient * input_multiplicity
                    if return_count > 1:
                        return 2
                    continue
                if mnemonic not in allowed:
                    continue
                if mnemonic == "MULTIEQUAL":
                    accepted_phi_input = self._multiequal_input_is_accumulator_update(
                        op,
                        current,
                    )
                    if not accepted_phi_input:
                        self._debug(
                            "Declined vectorized readonly prefix-sum accumulator PHI contribution: "
                            f"phi={self._varnode_cache_key(getattr(op, 'getOutput', lambda: None)())} "
                            f"input={self._varnode_cache_key(current)} "
                            f"reason={self._multiequal_accumulator_update_rejection_reason(op)}"
                        )
                        continue
                output = getattr(op, "getOutput", lambda: None)()
                if output is not None:
                    next_coefficient = coefficient
                    if mnemonic == "INT_ADD":
                        next_coefficient *= input_multiplicity
                    if next_coefficient > 1:
                        return 2
                    stack.append((output, next_coefficient))
        return min(return_count, 2)

    def _varnode_has_additive_return_contribution(
        self,
        start_varnode,
        *,
        budget: int = 128,
    ) -> bool:
        allowed = {
            "INT_ADD",
            "COPY",
            "CAST",
            "INT_ZEXT",
            "INT_SEXT",
            "SUBPIECE",
            "MULTIEQUAL",
        }
        stack = [(start_varnode, 1)]
        seen_coefficients: Dict[Tuple[Any, ...], int] = {}
        steps = 0
        while stack and steps < budget:
            current, coefficient = stack.pop()
            steps += 1
            if coefficient != 1:
                return False
            key = self._varnode_cache_key(current)
            previous = seen_coefficients.get(key)
            if previous is not None and previous >= coefficient:
                continue
            seen_coefficients[key] = coefficient
            for op in self._iter_varnode_descendant_ops(current):
                mnemonic = getattr(op, "getMnemonic", lambda: None)()
                input_multiplicity = self._varnode_input_multiplicity(op, current)
                if input_multiplicity <= 0:
                    continue
                if mnemonic == "RETURN":
                    return True
                if mnemonic not in allowed:
                    continue
                if mnemonic == "MULTIEQUAL":
                    accepted_phi_input = self._multiequal_input_is_accumulator_update(
                        op,
                        current,
                    )
                    if not accepted_phi_input:
                        continue
                output = getattr(op, "getOutput", lambda: None)()
                if output is None:
                    continue
                next_coefficient = coefficient
                if mnemonic == "INT_ADD":
                    next_coefficient *= input_multiplicity
                if next_coefficient != 1:
                    return False
                stack.append((output, next_coefficient))
        return False

    def _multiequal_input_is_accumulator_update(self, phi_op, input_varnode) -> bool:
        return self._same_varnode_identity(
            input_varnode,
            self._unique_multiequal_accumulator_update_input(phi_op),
        )

    def _unique_multiequal_accumulator_update_input(self, phi_op):
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

    def _multiequal_accumulator_update_rejection_reason(self, phi_op) -> str:
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

    def _varnode_is_accumulator_update_for_phi(self, candidate, phi_output) -> bool:
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

    def _varnode_depends_on_varnode(self, start_varnode, target_varnode, *, budget: int = 64) -> bool:
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

    def _varnode_aliases_accumulator_object(self, candidate, phi_output) -> bool:
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

    def _phi_input_is_cfg_entry_seed(
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

    def _cfg_block_reachable_without_reentering_header(
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

    def _block_identity_key(self, block) -> object:
        if block is None:
            return None
        try:
            return ("block_index", int(block.getIndex()))
        except Exception:
            return ("block_id", id(block))

    def _same_varnode_identity(self, left, right) -> bool:
        if left is None or right is None:
            return False
        if left is right:
            return True
        left_key = self._varnode_cache_key(left)
        right_key = self._varnode_cache_key(right)
        return left_key is not None and right_key is not None and left_key == right_key

    def _varnode_input_multiplicity(self, op, varnode) -> int:
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

    def _iter_varnode_descendant_ops(self, varnode):
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

    def _has_vector_countdown_loop(
        self,
        all_ops: Sequence[object],
        rounded_vn,
        *,
        lane_count: int,
    ) -> bool:
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            phi_output = getattr(op, "getOutput", lambda: None)()
            if phi_output is None:
                continue
            has_init = False
            input_count = int(getattr(op, "getNumInputs", lambda: 0)() or 0)
            for index in range(input_count):
                if self._same_varnode_value(self._follow_passthrough_varnode(op.getInput(index)), rounded_vn):
                    has_init = True
                    break
            if not has_init:
                continue
            if self._index_phi_has_step(all_ops, phi_output, -int(lane_count)):
                return True
        return False

    def _index_phi_has_step(
        self,
        all_ops: Sequence[object],
        phi_output,
        step: int,
    ) -> bool:
        for op in all_ops:
            mnemonic = getattr(op, "getMnemonic", lambda: None)()
            if mnemonic not in {"INT_ADD", "INT_SUB"}:
                continue
            if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
                continue
            left = self._follow_passthrough_varnode(op.getInput(0))
            right = self._follow_passthrough_varnode(op.getInput(1))
            constant = self._signed_varnode_constant_value(right)
            if self._same_varnode_value(left, phi_output) and constant is not None:
                actual = int(constant) if mnemonic == "INT_ADD" else -int(constant)
                if actual == int(step):
                    return True
            constant = self._signed_varnode_constant_value(left)
            if mnemonic == "INT_ADD" and self._same_varnode_value(right, phi_output) and constant is not None:
                if int(constant) == int(step):
                    return True
        return False

    def _has_vector_loop_bound_to_rounded_count(
        self,
        all_ops: Sequence[object],
        pointer_phi,
        pointer_param: dict,
        rounded_vn,
        *,
        element_size: int,
        base_offset: int,
        vector_stride: int,
    ) -> bool:
        """Prove a vector cursor stops at ``base + rounded_count * elem``.

        Clang/LLVM often emits a pointer-induction vector loop instead of a
        separate countdown induction.  This keeps the recognition object-centric:
        the proof is over Ghidra varnodes and P-code def-use links, not textual
        decompiler output.
        """

        compare_ops = {
            "INT_EQUAL",
            "INT_NOTEQUAL",
            "INT_LESS",
            "INT_LESSEQUAL",
            "INT_SLESS",
            "INT_SLESSEQUAL",
        }
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() not in compare_ops:
                continue
            if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
                continue
            left = self._follow_passthrough_varnode(op.getInput(0))
            right = self._follow_passthrough_varnode(op.getInput(1))
            if self._vector_cursor_matches_end_bound(
                left,
                right,
                pointer_phi,
                pointer_param,
                rounded_vn,
                element_size=element_size,
                base_offset=base_offset,
                vector_stride=vector_stride,
            ):
                return True
            if self._vector_cursor_matches_end_bound(
                right,
                left,
                pointer_phi,
                pointer_param,
                rounded_vn,
                element_size=element_size,
                base_offset=base_offset,
                vector_stride=vector_stride,
            ):
                return True
        return False

    def _vector_cursor_matches_end_bound(
        self,
        cursor_vn,
        end_vn,
        pointer_phi,
        pointer_param: dict,
        rounded_vn,
        *,
        element_size: int,
        base_offset: int,
        vector_stride: int,
    ) -> bool:
        cursor_offset = self._byte_offset_from_pointer_like(cursor_vn, pointer_phi)
        if cursor_offset is None:
            return False
        if int(cursor_offset) not in {0, int(vector_stride)}:
            return False
        return self._varnode_is_base_plus_scaled_counter(
            end_vn,
            pointer_param,
            rounded_vn,
            element_size=element_size,
            byte_offset=int(base_offset) + int(cursor_offset),
        )

    def _has_scalar_tail_from_rounded_count(
        self,
        all_ops: Sequence[object],
        pointer_param: dict,
        count_param: dict,
        rounded_vn,
        *,
        element_size: int,
        start_offset: int = 0,
        start_index: int = 0,
        max_unrolled_terms: int = 0,
        tail_index_source_varnode=None,
        lane_count: Optional[int] = None,
    ) -> bool:
        tail_starts = self._tail_start_varnodes_from_rounded_count(
            all_ops,
            pointer_param,
            rounded_vn,
            element_size=element_size,
            start_offset=start_offset,
            tail_index_source_varnode=tail_index_source_varnode,
            lane_count=lane_count,
        )
        if not tail_starts:
            self._debug(
                "Declined vectorized readonly prefix-sum tail: "
                f"no tail-start varnode for start_offset={start_offset}"
            )
            return False

        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            phi_output = getattr(op, "getOutput", lambda: None)()
            if phi_output is None:
                continue
            input_count = int(getattr(op, "getNumInputs", lambda: 0)() or 0)
            if not any(
                any(
                    self._same_varnode_value(self._follow_passthrough_varnode(op.getInput(index)), tail_start)
                    for tail_start in tail_starts
                )
                for index in range(input_count)
            ):
                continue
            if not self._phi_has_pointer_step(all_ops, phi_output, step_bytes=int(element_size)):
                self._debug(
                    "Declined vectorized readonly prefix-sum tail PHI: "
                    f"no +{element_size} pointer step for phi={self._varnode_cache_key(phi_output)}"
                )
                continue
            if not self._tail_load_contributes_additively_to_return(
                all_ops,
                phi_output,
                element_size=element_size,
            ):
                self._debug(
                    "Declined vectorized readonly prefix-sum tail PHI: "
                    f"tail load does not flow additively for phi={self._varnode_cache_key(phi_output)}"
                )
                continue
            if not (
                self._has_scalar_tail_bound_to_count(
                    all_ops,
                    phi_output,
                    pointer_param,
                    count_param,
                    element_size=element_size,
                )
                or self._has_scalar_tail_countdown_from_count_minus_rounded(
                    all_ops,
                    rounded_vn,
                    count_param,
                    start_index=start_index,
                )
            ):
                self._debug(
                    "Declined vectorized readonly prefix-sum tail PHI: "
                    f"tail bound not tied to count for phi={self._varnode_cache_key(phi_output)}"
                )
                continue
            return True
        if self._has_unrolled_scalar_tail_from_rounded_count(
            all_ops,
            tail_starts,
            count_param,
            element_size=element_size,
            max_terms=max_unrolled_terms,
            tail_index_source_varnode=tail_index_source_varnode,
            lane_count=lane_count,
        ):
            return True
        return False

    def _tail_load_contributes_additively_to_return(
        self,
        all_ops: Sequence[object],
        tail_phi,
        *,
        element_size: int,
    ) -> bool:
        for load_op in all_ops:
            if getattr(load_op, "getMnemonic", lambda: None)() != "LOAD":
                continue
            if int(getattr(load_op, "getNumInputs", lambda: 0)() or 0) < 2:
                continue
            address = self._follow_passthrough_varnode(load_op.getInput(1))
            if not self._same_varnode_value(address, tail_phi):
                continue
            output = getattr(load_op, "getOutput", lambda: None)()
            if output is None:
                continue
            load_size = max(1, int(getattr(output, "getSize", lambda: element_size)() or element_size))
            if load_size != int(element_size):
                continue
            if self._load_lanes_flow_additively_to_return(
                output,
                load_size=load_size,
                element_size=element_size,
            ):
                return True
        return False

    def _has_unrolled_scalar_tail_from_rounded_count(
        self,
        all_ops: Sequence[object],
        tail_starts: Sequence[object],
        count_param: dict,
        *,
        element_size: int,
        max_terms: int,
        tail_index_source_varnode=None,
        lane_count: Optional[int] = None,
    ) -> bool:
        """Recognize a finite scalar tail emitted as guarded straight-line loads."""

        if int(max_terms) <= 0 or not tail_starts:
            return False
        if not self._unrolled_tail_count_guards_are_object_linked(
            all_ops,
            tail_starts,
            count_param,
            max_terms=int(max_terms),
            tail_index_source_varnode=tail_index_source_varnode,
            lane_count=lane_count,
        ):
            self._debug("Declined vectorized readonly prefix-sum tail: unrolled tail guards are incomplete")
            return False

        covered_offsets = set()
        for load_op in all_ops:
            if getattr(load_op, "getMnemonic", lambda: None)() != "LOAD":
                continue
            if int(getattr(load_op, "getNumInputs", lambda: 0)() or 0) < 2:
                continue
            output = getattr(load_op, "getOutput", lambda: None)()
            if output is None:
                continue
            load_size = max(1, int(getattr(output, "getSize", lambda: element_size)() or element_size))
            if load_size != int(element_size):
                continue
            address = self._follow_passthrough_varnode(load_op.getInput(1))
            term_index = None
            for tail_start in tail_starts:
                byte_offset = self._byte_offset_from_pointer_like(address, tail_start)
                if byte_offset is None:
                    continue
                if int(byte_offset) % int(element_size) != 0:
                    continue
                candidate_index = int(byte_offset) // int(element_size)
                if 0 <= candidate_index < int(max_terms):
                    term_index = candidate_index
                    break
            if term_index is None:
                continue
            if not self._load_lanes_flow_additively_to_any_return(
                output,
                load_size=load_size,
                element_size=element_size,
            ):
                continue
            covered_offsets.add(int(term_index))
        expected_offsets = set(range(int(max_terms)))
        if covered_offsets != expected_offsets:
            self._debug(
                "Declined vectorized readonly prefix-sum tail: "
                f"unrolled tail load coverage={tuple(sorted(covered_offsets))} "
                f"expected={tuple(sorted(expected_offsets))}"
            )
            return False
        return True

    def _unrolled_tail_count_guards_are_object_linked(
        self,
        all_ops: Sequence[object],
        tail_starts: Sequence[object],
        count_param: dict,
        *,
        max_terms: int,
        tail_index_source_varnode=None,
        lane_count: Optional[int] = None,
    ) -> bool:
        if int(max_terms) <= 0:
            return False
        if tail_index_source_varnode is not None and lane_count is not None:
            if not self._has_zero_tail_residue_guard(all_ops, tail_index_source_varnode, lane_count):
                return False
        tail_index_vns = self._tail_index_varnodes_from_tail_starts(tail_starts)
        if not tail_index_vns:
            return False
        required_cutoffs = set(range(1, int(max_terms)))
        if not required_cutoffs:
            return True
        proven_cutoffs = set()
        compare_ops = {
            "INT_EQUAL",
            "INT_NOTEQUAL",
            "INT_LESS",
            "INT_LESSEQUAL",
            "INT_SLESS",
            "INT_SLESSEQUAL",
        }
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() not in compare_ops:
                continue
            if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
                continue
            left = self._follow_passthrough_varnode(op.getInput(0))
            right = self._follow_passthrough_varnode(op.getInput(1))
            if self._varnode_matches_parameter(left, count_param):
                cutoff = self._tail_index_plus_constant_delta(right, tail_index_vns)
                if cutoff in required_cutoffs:
                    proven_cutoffs.add(int(cutoff))
            if self._varnode_matches_parameter(right, count_param):
                cutoff = self._tail_index_plus_constant_delta(left, tail_index_vns)
                if cutoff in required_cutoffs:
                    proven_cutoffs.add(int(cutoff))
        return proven_cutoffs == required_cutoffs

    def _tail_index_varnodes_from_tail_starts(self, tail_starts: Sequence[object]) -> Tuple[object, ...]:
        indices: List[object] = []
        for tail_start in tail_starts or ():
            candidate = self._follow_passthrough_varnode(tail_start)
            def_op = getattr(candidate, "getDef", lambda: None)()
            if def_op is None:
                continue
            mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
            if mnemonic == "PTRADD" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 3:
                indices.append(self._follow_passthrough_varnode(def_op.getInput(1)))
        unique: List[object] = []
        seen = set()
        for index_vn in indices:
            key = self._varnode_cache_key(index_vn)
            if key in seen:
                continue
            seen.add(key)
            unique.append(index_vn)
        return tuple(unique)

    def _tail_index_plus_constant_delta(
        self,
        candidate_vn,
        tail_index_vns: Sequence[object],
    ) -> Optional[int]:
        candidate_vn = self._follow_passthrough_varnode(candidate_vn)
        for tail_index in tail_index_vns or ():
            if self._same_varnode_value(candidate_vn, tail_index):
                return 0
            delta = self._counter_plus_constant_delta(candidate_vn, tail_index)
            if delta is not None:
                return int(delta)
        return None

    def _has_zero_tail_residue_guard(
        self,
        all_ops: Sequence[object],
        tail_index_source_varnode,
        lane_count: int,
    ) -> bool:
        mask = int(lane_count) - 1
        if mask <= 0:
            return False
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() not in {"INT_EQUAL", "INT_NOTEQUAL"}:
                continue
            if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
                continue
            left = self._follow_passthrough_varnode(op.getInput(0))
            right = self._follow_passthrough_varnode(op.getInput(1))
            if self._signed_varnode_constant_value(left) == 0 and self._varnode_is_tail_source_mask(
                right,
                tail_index_source_varnode,
                mask,
            ):
                return True
            if self._signed_varnode_constant_value(right) == 0 and self._varnode_is_tail_source_mask(
                left,
                tail_index_source_varnode,
                mask,
            ):
                return True
        return False

    def _varnode_is_tail_source_mask(self, candidate_vn, source_vn, mask: int) -> bool:
        if source_vn is None:
            return False
        candidate_vn = self._follow_passthrough_varnode(candidate_vn)
        def_op = getattr(candidate_vn, "getDef", lambda: None)()
        if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "INT_AND":
            return False
        if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
            return False
        left = self._follow_passthrough_varnode(def_op.getInput(0))
        right = self._follow_passthrough_varnode(def_op.getInput(1))
        if self._same_varnode_value(left, source_vn) and self._varnode_unsigned_constant_value(right) == int(mask):
            return True
        return self._same_varnode_value(right, source_vn) and self._varnode_unsigned_constant_value(left) == int(mask)

    def _tail_start_varnodes_from_rounded_count(
        self,
        all_ops: Sequence[object],
        pointer_param: dict,
        rounded_vn,
        *,
        element_size: int,
        start_offset: int = 0,
        tail_index_source_varnode=None,
        lane_count: Optional[int] = None,
    ) -> Tuple[object, ...]:
        starts: List[object] = []
        for op in all_ops:
            output = getattr(op, "getOutput", lambda: None)()
            if output is None:
                continue
            if self._varnode_is_base_plus_scaled_counter(
                output,
                pointer_param,
                rounded_vn,
                element_size=element_size,
                byte_offset=int(start_offset),
            ) or self._varnode_is_base_plus_scaled_tail_source_index(
                output,
                pointer_param,
                tail_index_source_varnode,
                lane_count=lane_count,
                element_size=element_size,
            ):
                starts.append(output)
        changed = True
        while changed:
            changed = False
            for op in all_ops:
                if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                    continue
                output = getattr(op, "getOutput", lambda: None)()
                if output is None or any(self._same_varnode_identity(output, start) for start in starts):
                    continue
                input_count = int(getattr(op, "getNumInputs", lambda: 0)() or 0)
                if any(
                    any(
                        self._same_varnode_value(self._follow_passthrough_varnode(op.getInput(index)), start)
                        for start in starts
                    )
                    for index in range(input_count)
                ):
                    starts.append(output)
                    changed = True
        unique: List[object] = []
        seen = set()
        for start in starts:
            key = self._varnode_cache_key(start)
            if key in seen:
                continue
            seen.add(key)
            unique.append(start)
        return tuple(unique)

    def _has_scalar_tail_bound_to_count(
        self,
        all_ops: Sequence[object],
        tail_phi,
        pointer_param: dict,
        count_param: dict,
        *,
        element_size: int,
    ) -> bool:
        compare_ops = {
            "INT_EQUAL",
            "INT_NOTEQUAL",
            "INT_LESS",
            "INT_LESSEQUAL",
            "INT_SLESS",
            "INT_SLESSEQUAL",
        }
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() not in compare_ops:
                continue
            if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
                continue
            left = self._follow_passthrough_varnode(op.getInput(0))
            right = self._follow_passthrough_varnode(op.getInput(1))
            if self._scalar_tail_cursor_matches_count_bound(
                left,
                right,
                tail_phi,
                pointer_param,
                count_param,
                element_size=element_size,
            ):
                return True
            if self._scalar_tail_cursor_matches_count_bound(
                right,
                left,
                tail_phi,
                pointer_param,
                count_param,
                element_size=element_size,
            ):
                return True
        return False

    def _has_scalar_tail_countdown_from_count_minus_rounded(
        self,
        all_ops: Sequence[object],
        rounded_vn,
        count_param: dict,
        *,
        start_index: int = 0,
    ) -> bool:
        """Recognize tail loops controlled by ``remaining = count - rounded - start``."""

        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            phi_output = getattr(op, "getOutput", lambda: None)()
            if phi_output is None:
                continue
            input_count = int(getattr(op, "getNumInputs", lambda: 0)() or 0)
            has_count_minus_rounded_init = any(
                self._varnode_is_count_minus_rounded(
                    self._follow_passthrough_varnode(op.getInput(index)),
                    count_param,
                    rounded_vn,
                    start_index=start_index,
                )
                for index in range(input_count)
            )
            if not has_count_minus_rounded_init:
                continue
            if self._index_phi_has_step(all_ops, phi_output, -1):
                return True
        return False

    def _varnode_is_count_minus_rounded(
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

    def _varnode_is_count_minus_rounded_plus_start(
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

    def _scalar_tail_cursor_matches_count_bound(
        self,
        cursor_vn,
        end_vn,
        tail_phi,
        pointer_param: dict,
        count_param: dict,
        *,
        element_size: int,
    ) -> bool:
        cursor_offset = self._byte_offset_from_pointer_like(cursor_vn, tail_phi)
        if cursor_offset is None:
            return False
        if int(cursor_offset) not in {0, int(element_size)}:
            return False
        return self._varnode_is_base_plus_scaled_parameter(
            end_vn,
            pointer_param,
            count_param,
            element_size=element_size,
            byte_offset=int(cursor_offset),
        )

    def _byte_offset_from_pointer_like(self, candidate_vn, base_vn) -> Optional[int]:
        candidate_vn = self._follow_passthrough_varnode(candidate_vn)
        offset = self._byte_offset_from_pointer(candidate_vn, base_vn)
        if offset is not None:
            return int(offset)
        def_op = getattr(candidate_vn, "getDef", lambda: None)()
        if def_op is not None:
            mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
            if mnemonic in {"INT_ADD", "PTRSUB"} and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
                left = self._follow_passthrough_varnode(def_op.getInput(0))
                right = self._follow_passthrough_varnode(def_op.getInput(1))
                if self._same_varnode_value(left, base_vn):
                    return self._signed_varnode_constant_value(right)
                if mnemonic == "INT_ADD" and self._same_varnode_value(right, base_vn):
                    return self._signed_varnode_constant_value(left)
        if self._same_varnode_value(candidate_vn, base_vn):
            return 0
        return None

    def _varnode_is_base_plus_scaled_parameter(
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

    def _varnode_is_base_plus_scaled_counter(
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

    def _varnode_is_base_plus_scaled_tail_source_index(
        self,
        candidate_vn,
        pointer_param: dict,
        tail_index_source_varnode,
        *,
        lane_count: Optional[int],
        element_size: int,
    ) -> bool:
        if tail_index_source_varnode is None or lane_count is None:
            return False
        candidate_vn = self._follow_passthrough_varnode(candidate_vn)
        def_op = getattr(candidate_vn, "getDef", lambda: None)()
        if def_op is None:
            return False
        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        if mnemonic == "PTRADD" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 3:
            base = self._follow_passthrough_varnode(def_op.getInput(0))
            index = self._follow_passthrough_varnode(def_op.getInput(1))
            elem = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(2)))
            return (
                elem == int(element_size)
                and self._varnode_matches_parameter(base, pointer_param)
                and self._varnode_matches_tail_index_source_or(index, tail_index_source_varnode, lane_count)
            )
        if mnemonic in {"INT_ADD", "PTRSUB"} and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._follow_passthrough_varnode(def_op.getInput(0))
            right = self._follow_passthrough_varnode(def_op.getInput(1))
            if self._varnode_matches_parameter(left, pointer_param):
                return self._varnode_is_scaled_tail_source_index(
                    right,
                    tail_index_source_varnode,
                    lane_count=lane_count,
                    element_size=element_size,
                )
            if mnemonic == "INT_ADD" and self._varnode_matches_parameter(right, pointer_param):
                return self._varnode_is_scaled_tail_source_index(
                    left,
                    tail_index_source_varnode,
                    lane_count=lane_count,
                    element_size=element_size,
                )
        return False

    def _varnode_is_scaled_tail_source_index(
        self,
        candidate_vn,
        tail_index_source_varnode,
        *,
        lane_count: int,
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
            if self._varnode_unsigned_constant_value(right) == int(element_size):
                return self._varnode_matches_tail_index_source_or(left, tail_index_source_varnode, lane_count)
            if self._varnode_unsigned_constant_value(left) == int(element_size):
                return self._varnode_matches_tail_index_source_or(right, tail_index_source_varnode, lane_count)
            return False
        if mnemonic == "INT_LEFT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            shifted = self._follow_passthrough_varnode(def_op.getInput(0))
            shift_bits = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(1)))
            return (
                shift_bits is not None
                and (1 << int(shift_bits)) == int(element_size)
                and self._varnode_matches_tail_index_source_or(shifted, tail_index_source_varnode, lane_count)
            )
        if mnemonic == "INT_OR" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._follow_passthrough_varnode(def_op.getInput(0))
            right = self._follow_passthrough_varnode(def_op.getInput(1))
            low_bits = max(0, (int(element_size) - 1).bit_length())
            return (
                self._varnode_is_scaled_tail_source_index(
                    left,
                    tail_index_source_varnode,
                    lane_count=lane_count,
                    element_size=element_size,
                )
                and self._varnode_low_bits_clear(right, low_bits)
            ) or (
                self._varnode_is_scaled_tail_source_index(
                    right,
                    tail_index_source_varnode,
                    lane_count=lane_count,
                    element_size=element_size,
                )
                and self._varnode_low_bits_clear(left, low_bits)
            )
        return False

    def _varnode_matches_tail_index_source_or(
        self,
        candidate_vn,
        tail_index_source_varnode,
        lane_count: int,
    ) -> bool:
        if tail_index_source_varnode is None:
            return False
        candidate_vn = self._follow_passthrough_varnode(candidate_vn)
        if self._same_varnode_value(candidate_vn, tail_index_source_varnode):
            return int(lane_count) == 1
        def_op = getattr(candidate_vn, "getDef", lambda: None)()
        if def_op is not None and getattr(def_op, "getMnemonic", lambda: None)() == "INT_OR":
            if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
                left = self._follow_passthrough_varnode(def_op.getInput(0))
                right = self._follow_passthrough_varnode(def_op.getInput(1))
                mask = int(lane_count) - 1
                if self._same_varnode_value(left, tail_index_source_varnode) and self._signed_varnode_constant_value(right) == mask:
                    return True
                if self._same_varnode_value(right, tail_index_source_varnode) and self._signed_varnode_constant_value(left) == mask:
                    return True
        if def_op is not None and getattr(def_op, "getMnemonic", lambda: None)() == "MULTIEQUAL":
            input_count = int(getattr(def_op, "getNumInputs", lambda: 0)() or 0)
            for index in range(input_count):
                try:
                    input_vn = self._phi_input_value_varnode(def_op, index)
                except Exception:
                    input_vn = None
                if input_vn is None:
                    try:
                        input_vn = def_op.getInput(index)
                    except Exception:
                        continue
                if self._varnode_matches_tail_index_source_or(input_vn, tail_index_source_varnode, lane_count):
                    return True
        return False

    def _varnode_low_bits_clear(self, candidate_vn, bit_count: int) -> bool:
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

    def _counter_plus_constant_delta(
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

    def _rounded_tail_index_varnode_matches(
        self,
        candidate_vn,
        counter_vn,
        *,
        start_index: int,
    ) -> bool:
        candidate_vn = self._follow_passthrough_varnode(candidate_vn)
        direct_delta = self._counter_plus_constant_delta(candidate_vn, counter_vn)
        if direct_delta == int(start_index):
            return True
        def_op = getattr(candidate_vn, "getDef", lambda: None)()
        if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
            return False
        input_count = int(getattr(def_op, "getNumInputs", lambda: 0)() or 0)
        if input_count <= 0:
            return False
        saw_seed = False
        saw_rounded = False
        for index in range(input_count):
            input_vn = self._follow_passthrough_varnode(def_op.getInput(index))
            if self._signed_varnode_constant_value(input_vn) == int(start_index):
                saw_seed = True
                continue
            if self._counter_plus_constant_delta(input_vn, counter_vn) == int(start_index):
                saw_rounded = True
                continue
        return saw_seed and saw_rounded

    def _counter_low_bits_clear_for_or_delta(
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

    def _parameter_names_from_expr(self, expr) -> Tuple[str, ...]:
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

    def _varnode_is_scaled_parameter_plus_constant(
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

    def _varnode_is_scaled_counter_plus_constant(
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

    def _scaled_counter_delta_bytes(
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

    def _scaled_parameter_varnode(
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

    def _varnode_is_scaled_counter(
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

    def _analysis_mentions_parameter_in_conditions(
        self,
        analysis,
        param_name: str,
    ) -> bool:
        if not param_name:
            return False
        for ret in analysis.returns or []:
            for condition in ret.conditions or []:
                relation = self._condition_relation(condition, param_name)
                if relation is not None:
                    return True
                relation = self._parameter_comparison_relation(condition)
                if relation is not None and param_name in relation[:3:2]:
                    return True
        return False

    def _build_readonly_reduction_semantic_witnesses(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        positive_returns: Sequence[ReturnInfo],
        accumulator_proof: ReductionAccumulatorProof,
        *,
        result_size: int,
        exact_witnesses: Optional[Tuple[ReadonlyReductionWitness, ...]] = None,
    ) -> Tuple[ReadonlyReductionWitness, ...]:
        if exact_witnesses is None:
            exact_witnesses = self._extract_readonly_reduction_exact_witnesses(
                analysis,
                pointer_param,
                count_param,
                positive_returns,
                accumulator_proof,
            )
        witness_proof = accumulator_proof.with_runtime_evidence(
            limit_expr=accumulator_proof.limit_expr,
            result_size=result_size,
            loop_body_witnesses=tuple(exact_witnesses),
            exact_return_witnesses=tuple(exact_witnesses),
            guard_constraints=tuple(accumulator_proof.guard_constraints or ()),
            signed_counter=bool(accumulator_proof.signed_counter),
        )
        loop_body_exact_witnesses = []
        for witness in exact_witnesses:
            expected_terms = witness_proof.loop_body_terms_for_count_value(int(witness.exact_count))
            if expected_terms is None:
                continue
            if tuple(term.stable_key() for term in witness.terms) == tuple(
                term.stable_key() for term in expected_terms
            ):
                loop_body_exact_witnesses.append(witness)
        synthesized_witnesses = self._synthesize_linear_readonly_reduction_witnesses(
            pointer_param,
            witness_proof,
            result_size=result_size,
        )
        if not loop_body_exact_witnesses:
            return synthesized_witnesses
        if not synthesized_witnesses:
            return tuple(loop_body_exact_witnesses)

        exact_by_count = {
            int(witness.exact_count): witness
            for witness in loop_body_exact_witnesses
        }
        synthesized_by_count = {
            int(witness.exact_count): witness
            for witness in synthesized_witnesses
        }
        overlap = set(exact_by_count) & set(synthesized_by_count)
        for exact_count in sorted(overlap):
            if exact_by_count[exact_count].stable_key() != synthesized_by_count[exact_count].stable_key():
                return exact_witnesses

        merged = dict(synthesized_by_count)
        merged.update(exact_by_count)
        return tuple(merged[count] for count in sorted(merged))

    def _extract_readonly_reduction_exact_witnesses(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        positive_returns: Sequence[ReturnInfo],
        accumulator_proof: Optional[ReductionAccumulatorProof] = None,
    ) -> Tuple[ReadonlyReductionWitness, ...]:
        count_name = str(count_param.get("name") or "")
        witness_by_count: Dict[int, ReadonlyReductionWitness] = {}
        for ret in positive_returns or []:
            exact_count = self._exact_counter_value_from_conditions(ret.conditions or [], count_name)
            extracted = self._extract_readonly_return_terms_and_bias(
                analysis,
                pointer_param,
                ret,
                accumulator_proof,
            )
            terms = None
            constant_bias = 0
            if extracted is not None:
                terms, constant_bias = extracted
            if terms is not None and (exact_count is None or exact_count <= 0):
                exact_count = self._infer_exact_count_from_readonly_terms(
                    ret.conditions or [],
                    terms,
                    count_param,
                    accumulator_proof,
                )
            if exact_count is None or exact_count <= 0:
                self._debug("Skipped readonly exact-return witness: no exact positive counter value")
                continue
            expected_terms = (
                accumulator_proof.full_terms_for_count_value(int(exact_count))
                if accumulator_proof is not None
                else None
            )
            if expected_terms is None:
                expected_trip_count = self._readonly_loop_trip_count_for_count_value(accumulator_proof, int(exact_count))
                if expected_trip_count is None:
                    self._debug(
                        "Skipped readonly exact-return witness: "
                        f"no expected term model for count={exact_count}"
                    )
                    continue
            else:
                expected_trip_count = len(expected_terms)
            if expected_trip_count is None:
                continue
            witness_terms = self._resolve_readonly_exact_witness_terms(
                analysis,
                pointer_param,
                ret,
                accumulator_proof,
                exact_count=int(exact_count),
                expected_trip_count=int(expected_trip_count),
                expected_terms=expected_terms,
                extracted_terms=terms,
                constant_bias=int(constant_bias),
            )
            if witness_terms is None:
                self._debug(
                    "Skipped readonly exact-return witness: "
                    f"term extraction/count mismatch for count={exact_count}"
                )
                continue
            witness = ReadonlyReductionWitness(
                exact_count=int(exact_count),
                terms=tuple(witness_terms),
            )
            existing = witness_by_count.get(int(exact_count))
            if existing is None or existing.stable_key() == witness.stable_key():
                witness_by_count[int(exact_count)] = witness
        if not witness_by_count:
            return ()
        return tuple(witness_by_count[count] for count in sorted(witness_by_count))

    def _resolve_readonly_exact_witness_terms(
        self,
        analysis,
        pointer_param: dict,
        ret: ReturnInfo,
        accumulator_proof: Optional[ReductionAccumulatorProof],
        *,
        exact_count: int,
        expected_trip_count: int,
        expected_terms: Optional[Sequence[ReadonlyReductionTermRef]],
        extracted_terms: Optional[Sequence[ReadonlyReductionTermRef]],
        constant_bias: int,
    ) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        if extracted_terms is not None and len(extracted_terms) == int(expected_trip_count):
            if expected_terms is None or tuple(term.stable_key() for term in extracted_terms) == tuple(
                term.stable_key() for term in expected_terms
            ):
                return tuple(extracted_terms)
            if expected_terms is not None and self._readonly_term_multiset_key(extracted_terms) == self._readonly_term_multiset_key(
                expected_terms
            ):
                return tuple(expected_terms)
        canonical_terms = self._canonicalize_readonly_exact_witness_terms(
            analysis,
            pointer_param,
            ret,
            accumulator_proof,
            exact_count=int(exact_count),
            extracted_terms=extracted_terms,
            constant_bias=int(constant_bias),
        )
        if canonical_terms is not None:
            return canonical_terms
        return self._self_consistent_readonly_exact_witness_terms(
            ret,
            accumulator_proof,
            exact_count=int(exact_count),
            extracted_terms=extracted_terms,
            constant_bias=int(constant_bias),
        )

    def _self_consistent_readonly_exact_witness_terms(
        self,
        ret: ReturnInfo,
        accumulator_proof: Optional[ReductionAccumulatorProof],
        *,
        exact_count: int,
        extracted_terms: Optional[Sequence[ReadonlyReductionTermRef]],
        constant_bias: int,
    ) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        if extracted_terms is None or exact_count <= 0 or len(extracted_terms) != int(exact_count):
            return None
        result_size = max(
            1,
            int(getattr(accumulator_proof, "result_size", 0) or getattr(ret.value, "size", 0) or 0),
        )
        expected_bias = 0
        if accumulator_proof is not None:
            expected_bias = int(getattr(accumulator_proof, "constant_bias", 0) or 0)
        if self._normalize_readonly_constant_bias(int(constant_bias), result_size) != self._normalize_readonly_constant_bias(
            expected_bias,
            result_size,
        ):
            return None
        sorted_terms = tuple(sorted(extracted_terms, key=lambda term: (int(term.byte_offset), int(term.access_size))))
        expected_offsets = [index * result_size for index in range(int(exact_count))]
        actual_offsets = [int(term.byte_offset) for term in sorted_terms]
        actual_sizes = [max(1, int(term.access_size or 0)) for term in sorted_terms]
        if actual_offsets != expected_offsets:
            return None
        if any(size != result_size for size in actual_sizes):
            return None
        return sorted_terms

    def _readonly_exact_positive_return_is_absorbable(
        self,
        analysis,
        pointer_param: dict,
        ret: ReturnInfo,
        accumulator_proof: Optional[ReductionAccumulatorProof],
        *,
        exact_count: int,
    ) -> bool:
        extracted = self._extract_readonly_return_terms_and_bias(
            analysis,
            pointer_param,
            ret,
            accumulator_proof,
        )
        terms = None
        constant_bias = 0
        if extracted is not None:
            terms, constant_bias = extracted
        expected_terms = (
            accumulator_proof.full_terms_for_count_value(int(exact_count))
            if accumulator_proof is not None
            else None
        )
        if expected_terms is None:
            expected_trip_count = int(exact_count)
        else:
            expected_trip_count = len(expected_terms)
        witness_terms = self._resolve_readonly_exact_witness_terms(
            analysis,
            pointer_param,
            ret,
            accumulator_proof,
            exact_count=int(exact_count),
            expected_trip_count=int(expected_trip_count),
            expected_terms=expected_terms,
            extracted_terms=terms,
            constant_bias=int(constant_bias),
        )
        return witness_terms is not None

    def _order_readonly_exact_positive_returns(
        self,
        returns: Sequence[ReturnInfo],
        analysis,
        pointer_param: dict,
        count_param: dict,
        accumulator_proof: Optional[ReductionAccumulatorProof],
    ) -> List[ReturnInfo]:
        return [
            ret
            for _index, ret in sorted(
                enumerate(returns or ()),
                key=lambda item: self._readonly_exact_positive_return_selection_key(
                    item[1],
                    item[0],
                    analysis,
                    pointer_param,
                    count_param,
                    accumulator_proof,
                ),
            )
        ]

    def _readonly_exact_positive_return_selection_key(
        self,
        ret: ReturnInfo,
        original_index: int,
        analysis,
        pointer_param: dict,
        count_param: dict,
        accumulator_proof: Optional[ReductionAccumulatorProof],
    ) -> Tuple[int, int, int, int, int]:
        exact_count = self._exact_counter_value_from_conditions(
            ret.conditions or [],
            str(count_param.get("name") or ""),
        )
        if exact_count is None or int(exact_count) <= 0:
            return (1, 0, 0, 0, int(original_index))
        prefix_score = self._readonly_exact_positive_return_prefix_score(
            analysis,
            pointer_param,
            ret,
            accumulator_proof,
            exact_count=int(exact_count),
        )
        unresolved_score = 1 if self._expression_tree_contains_type(ret.value, ExpressionType.UNKNOWN) else 0
        phi_score = 1 if self._expression_tree_contains_type(ret.value, ExpressionType.PHI) else 0
        return (0, -int(prefix_score), unresolved_score, phi_score, int(original_index))

    def _readonly_exact_positive_return_prefix_score(
        self,
        analysis,
        pointer_param: dict,
        ret: ReturnInfo,
        accumulator_proof: Optional[ReductionAccumulatorProof],
        *,
        exact_count: int,
    ) -> int:
        extracted = self._extract_readonly_return_terms_and_bias(
            analysis,
            pointer_param,
            ret,
            accumulator_proof,
        )
        if extracted is None:
            return 0
        terms, constant_bias = extracted
        if self._self_consistent_readonly_exact_witness_terms(
            ret,
            accumulator_proof,
            exact_count=int(exact_count),
            extracted_terms=terms,
            constant_bias=int(constant_bias),
        ) is not None:
            return 30 + int(exact_count)

        expected_terms = (
            accumulator_proof.full_terms_for_count_value(int(exact_count))
            if accumulator_proof is not None
            else None
        )
        if expected_terms is not None and (
            tuple(term.stable_key() for term in terms) == tuple(term.stable_key() for term in expected_terms)
            or self._readonly_term_multiset_key(terms) == self._readonly_term_multiset_key(expected_terms)
        ):
            return 20 + int(exact_count)
        if len(tuple(terms or ())) == int(exact_count):
            return 10 + int(exact_count)
        return 0

    def _expression_tree_contains_type(
        self,
        expr: Optional[Expression],
        expr_type: ExpressionType,
    ) -> bool:
        if expr is None:
            return False
        if expr.expr_type == expr_type:
            return True
        if expr.expr_type == ExpressionType.PHI and expr.value:
            return any(
                (condition is not None and self._expression_tree_contains_type(condition.expression, expr_type))
                or self._expression_tree_contains_type(value, expr_type)
                for condition, value in expr.value
            )
        return any(
            self._expression_tree_contains_type(operand, expr_type)
            for operand in (expr.operands or [])
        )

    def _canonicalize_readonly_exact_witness_terms(
        self,
        analysis,
        pointer_param: dict,
        ret: ReturnInfo,
        accumulator_proof: Optional[ReductionAccumulatorProof],
        *,
        exact_count: int,
        extracted_terms: Optional[Sequence[ReadonlyReductionTermRef]],
        constant_bias: int,
    ) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        if accumulator_proof is None or exact_count <= 0:
            return None
        expected_terms = accumulator_proof.full_terms_for_count_value(int(exact_count))
        if not expected_terms:
            return None
        result_size = max(
            1,
            int(getattr(accumulator_proof, "result_size", 0) or getattr(ret.value, "size", 0) or 0),
        )
        canonical_value = self._build_readonly_reduction_expression_from_terms(
            pointer_param,
            expected_terms,
            constant_bias=constant_bias,
            result_size=result_size,
        )
        if canonical_value is None:
            return None
        candidate_values = [ret.value]
        reduced_value = _reduce_expression_under_conditions(ret.value, ret.conditions or [])
        if reduced_value is not ret.value:
            candidate_values.insert(0, reduced_value)
        for candidate in candidate_values:
            if _expressions_equivalent_under_conditions(
                candidate,
                canonical_value,
                ret.conditions or [],
                analysis.parameters or [],
            ):
                return tuple(expected_terms)
            if self._prove_expression_equivalence_under_conditions(
                candidate,
                canonical_value,
                ret.conditions or [],
                analysis.parameters or [],
            ):
                return tuple(expected_terms)
        if extracted_terms is not None and (
            tuple(term.stable_key() for term in extracted_terms) == tuple(
                term.stable_key() for term in expected_terms
            )
            or self._readonly_term_multiset_key(extracted_terms) == self._readonly_term_multiset_key(expected_terms)
        ):
            return tuple(expected_terms)
        return None

    def _readonly_term_multiset_key(
        self,
        terms: Sequence[ReadonlyReductionTermRef],
    ) -> Tuple[object, ...]:
        return tuple(sorted((term.stable_key() for term in terms or ()), key=repr))

    def _build_readonly_reduction_expression_from_terms(
        self,
        pointer_param: dict,
        terms: Sequence[ReadonlyReductionTermRef],
        *,
        constant_bias: int,
        result_size: int,
    ) -> Optional[Expression]:
        access_terms = [self._readonly_reduction_term_expression(pointer_param, term) for term in terms or ()]
        if any(term is None for term in access_terms):
            return None
        components: List[Optional[Expression]] = list(access_terms)
        normalized_bias = self._normalize_readonly_constant_bias(int(constant_bias), max(1, int(result_size or 0)))
        if normalized_bias != 0:
            components.append(Expression.constant(normalized_bias, size=max(1, int(result_size or 0))))
        expr = self._sum_expression_terms(components)
        if expr is not None:
            expr.size = max(1, int(result_size or 0))
        return expr

    def _readonly_reduction_term_expression(
        self,
        pointer_param: dict,
        term: ReadonlyReductionTermRef,
    ) -> Optional[Expression]:
        pointer_expr = self._parameter_expression(pointer_param)
        pointer_size = max(1, int(getattr(pointer_expr, "size", 0) or pointer_param.get("size", 0) or 8))
        byte_offset = int(term.byte_offset)
        access_size = max(1, int(term.access_size))

        if byte_offset == 0:
            address_expr = pointer_expr
        else:
            address_expr = Expression.binary_op(
                "INT_ADD",
                pointer_expr,
                Expression.constant(byte_offset, size=pointer_size),
            )
            address_expr.size = pointer_size

        load_expr = Expression.memory(address_expr, size=access_size)
        load_expr.size = access_size
        return load_expr

    def _infer_exact_count_from_readonly_terms(
        self,
        conditions: Sequence[Condition],
        terms: Sequence[ReadonlyReductionTermRef],
        count_param: dict,
        accumulator_proof: Optional[ReductionAccumulatorProof],
    ) -> Optional[int]:
        if accumulator_proof is None or not terms:
            return None
        term_key = tuple(term.stable_key() for term in terms)
        max_count = max(
            int(accumulator_proof.start_index),
            len(tuple(accumulator_proof.seed_terms or ())),
            1,
        )
        for count_value in range(1, max_count + 1):
            expected_terms = accumulator_proof.full_terms_for_count_value(count_value)
            if expected_terms is None:
                continue
            if term_key != tuple(term.stable_key() for term in expected_terms):
                continue
            if self._conditions_imply_counter_value(conditions, count_param, count_value):
                return count_value
        return None

    def _conditions_imply_counter_value(
        self,
        conditions: Sequence[Condition],
        count_param: dict,
        count_value: int,
    ) -> bool:
        equality = self._counter_equality_condition(count_param, count_value)
        constraint_set = ConditionConstraintSet.from_conditions(conditions or [])
        if constraint_set.implies_condition(equality):
            return True
        solver_unsat = ConditionSMTOracle.conjunction_is_unsat(
            list(conditions or []) + [equality.negate()]
        )
        return bool(solver_unsat) if solver_unsat is not None else False

    def _conditions_allow_counter_value(
        self,
        conditions: Sequence[Condition],
        count_param: dict,
        count_value: int,
    ) -> bool:
        equality = self._counter_equality_condition(count_param, count_value)
        constraint_set = ConditionConstraintSet.from_conditions(conditions or [])
        if not constraint_set.overlaps_with([equality]):
            solver_unsat = ConditionSMTOracle.conjunction_is_unsat(
                list(conditions or []) + [equality]
            )
            return bool(solver_unsat is False)
        return True

    def _counter_equality_condition(
        self,
        count_param: dict,
        count_value: int,
    ) -> Condition:
        count_expr = self._parameter_expression(count_param)
        return Condition(
            Expression.binary_op(
                "INT_EQUAL",
                count_expr,
                Expression.constant(int(count_value), count_expr.size or 4),
            ),
            False,
        )

    def _readonly_loop_trip_count_for_count_value(
        self,
        accumulator_proof: Optional[ReductionAccumulatorProof],
        count_value: int,
    ) -> Optional[int]:
        if count_value <= 0:
            return None
        if accumulator_proof is None:
            return int(count_value)
        return accumulator_proof.trip_count_for_count_value(count_value)

    def _synthesize_linear_readonly_reduction_witnesses(
        self,
        pointer_param: dict,
        accumulator_proof: Optional[ReductionAccumulatorProof],
        *,
        result_size: int,
    ) -> Tuple[ReadonlyReductionWitness, ...]:
        if accumulator_proof is None:
            return ()
        stride = int(accumulator_proof.stride)
        element_size = int(accumulator_proof.element_size)
        start_index = int(accumulator_proof.start_index)
        index_step = int(accumulator_proof.index_step)
        access_size = max(1, int(result_size or 0))
        if stride <= 0 or element_size <= 0 or element_size != access_size or index_step <= 0:
            return ()
        witnesses: List[ReadonlyReductionWitness] = []
        max_count = max(4, start_index + min(index_step * 2, 32) + 1)
        for exact_count in range(1, max_count + 1):
            terms = accumulator_proof.loop_body_terms_for_count_value(exact_count)
            if terms is None:
                continue
            witnesses.append(
                ReadonlyReductionWitness(
                    exact_count=exact_count,
                    terms=terms,
                )
            )
        return tuple(witnesses)

    def _extract_readonly_reduction_terms(
        self,
        expr: Optional[Expression],
        parameters: Sequence[dict],
        pointer_param: dict,
    ) -> Optional[List[ReadonlyReductionTermRef]]:
        extracted = self._extract_readonly_reduction_terms_and_bias(
            expr,
            parameters,
            pointer_param,
        )
        if extracted is None:
            return None
        terms, constant_bias = extracted
        if int(constant_bias) != 0:
            return None
        return list(terms)

    def _extract_readonly_reduction_terms_and_bias(
        self,
        expr: Optional[Expression],
        parameters: Sequence[dict],
        pointer_param: dict,
    ) -> Optional[Tuple[Tuple[ReadonlyReductionTermRef, ...], int]]:
        if expr is None:
            return None
        big_endian = self._program_is_big_endian()
        extracted: List[ReadonlyReductionTermRef] = []
        constant_bias = 0
        for sign, term in self._flatten_add_terms(expr):
            if term.expr_type == ExpressionType.CONSTANT:
                value = self._raw_constant_value(term)
                if value is None:
                    return None
                constant_bias += int(sign) * int(value)
                continue
            if sign != 1:
                return None
            descriptor = self._extract_readonly_reduction_term_descriptor(
                term,
                parameters,
                pointer_param,
                big_endian=big_endian,
            )
            if descriptor is None:
                return None
            extracted.append(descriptor)
        if not extracted:
            return None
        extracted.sort(key=lambda item: (int(item.byte_offset), int(item.access_size)))
        return tuple(extracted), int(constant_bias)

    def _normalize_readonly_constant_bias(self, value: int, result_size: int) -> int:
        bits = max(1, int(result_size or 0)) * 8
        return int(value) % (1 << bits)

    def _extract_readonly_reduction_term_descriptor(
        self,
        expr: Optional[Expression],
        parameters: Sequence[dict],
        pointer_param: dict,
        *,
        big_endian: bool,
        lsb_byte_offset: int = 0,
        narrowed_size: Optional[int] = None,
    ) -> Optional[ReadonlyReductionTermRef]:
        if expr is None:
            return None

        if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
            if expr.operator == "INT_SEXT":
                return None
            if expr.operator in {"INT_ZEXT", "CAST", "COPY"}:
                return self._extract_readonly_reduction_term_descriptor(
                    expr.operands[0],
                    parameters,
                    pointer_param,
                    big_endian=big_endian,
                    lsb_byte_offset=lsb_byte_offset,
                    narrowed_size=narrowed_size,
                )

        if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
            if expr.operator == "SUBPIECE":
                byte_offset = self._raw_constant_value(expr.operands[1])
                if byte_offset is None or byte_offset < 0:
                    return None
                return self._extract_readonly_reduction_term_descriptor(
                    expr.operands[0],
                    parameters,
                    pointer_param,
                    big_endian=big_endian,
                    lsb_byte_offset=lsb_byte_offset + int(byte_offset),
                    narrowed_size=max(1, int(expr.size or 0)),
                )
            if expr.operator == "INT_RIGHT":
                shift_bits = self._raw_constant_value(expr.operands[1])
                if shift_bits is None or shift_bits < 0 or (int(shift_bits) % 8) != 0:
                    return None
                return self._extract_readonly_reduction_term_descriptor(
                    expr.operands[0],
                    parameters,
                    pointer_param,
                    big_endian=big_endian,
                    lsb_byte_offset=lsb_byte_offset + (int(shift_bits) // 8),
                    narrowed_size=narrowed_size or max(1, int(expr.size or 0)),
                )
            if expr.operator == "INT_AND":
                mask_width = self._low_mask_width_bytes(expr.operands[0], expr.operands[1])
                if mask_width is None:
                    mask_width = self._low_mask_width_bytes(expr.operands[1], expr.operands[0])
                if mask_width is not None:
                    return self._extract_readonly_reduction_term_descriptor(
                        expr.operands[0] if expr.operands[0].expr_type != ExpressionType.CONSTANT else expr.operands[1],
                        parameters,
                        pointer_param,
                        big_endian=big_endian,
                        lsb_byte_offset=lsb_byte_offset,
                        narrowed_size=narrowed_size or mask_width,
                    )

        if expr.expr_type != ExpressionType.MEMORY or not expr.operands:
            return None

        load_size = max(1, int(expr.size or 0))
        access_size = max(1, int(narrowed_size or load_size))
        if lsb_byte_offset < 0 or access_size > load_size or lsb_byte_offset + access_size > load_size:
            return None
        location = canonicalize_location(expr.operands[0], parameters, size=load_size)
        if location is None or not location.base_ref.matches_parameter(pointer_param):
            return None
        if big_endian:
            byte_offset = int(location.offset) + (load_size - access_size - int(lsb_byte_offset))
        else:
            byte_offset = int(location.offset) + int(lsb_byte_offset)
        return ReadonlyReductionTermRef(
            byte_offset=byte_offset,
            access_size=access_size,
        )

    def _low_mask_width_bytes(
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

    def _program_is_big_endian(self) -> bool:
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

    def _phi_input_value_varnode(self, phi_op, input_index: int):
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

    def _phi_incoming_block(self, phi_parent, input_index: int):
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

    def _same_pcode_block(self, left, right) -> bool:
        if left is None or right is None:
            return False
        if left is right:
            return True
        try:
            equals = getattr(left, "equals", None)
            if callable(equals) and bool(equals(right)):
                return True
        except Exception:
            pass
        try:
            equals = getattr(right, "equals", None)
            if callable(equals) and bool(equals(left)):
                return True
        except Exception:
            pass
        left_ref = self._make_pcode_block_ref(left)
        right_ref = self._make_pcode_block_ref(right)
        return (
            left_ref is not None
            and right_ref is not None
            and left_ref.stable_key() == right_ref.stable_key()
        )

    def _same_storage_varnode(self, left, right) -> bool:
        if left is None or right is None:
            return False
        if left is right:
            return True
        try:
            left_addr = left.getAddress()
            right_addr = right.getAddress()
            if left_addr is None or right_addr is None:
                return False
            return (
                left_addr.getAddressSpace().getName() == right_addr.getAddressSpace().getName()
                and int(left.getOffset()) == int(right.getOffset())
                and int(left.getSize()) == int(right.getSize())
            )
        except Exception:
            return False

    def _same_high_variable(self, left, right) -> bool:
        if left is None or right is None:
            return False
        try:
            left_high = left.getHigh()
            right_high = right.getHigh()
        except Exception:
            return False
        if left_high is None or right_high is None:
            return False
        if left_high is right_high:
            return True
        try:
            if left_high == right_high:
                return True
        except Exception:
            pass
        try:
            left_symbol = left_high.getSymbol()
            right_symbol = right_high.getSymbol()
            if left_symbol is not None and right_symbol is not None and left_symbol is right_symbol:
                return True
        except Exception:
            pass
        return False

    def _match_pointer_progression_phi(
        self,
        phi_op,
        pointer_param: dict,
    ) -> Optional[Dict[str, object]]:
        output = getattr(phi_op, "getOutput", lambda: None)()
        if output is None:
            return None

        input_count = int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0)
        for init_index in range(input_count):
            init_varnode = self._follow_passthrough_varnode(
                self._phi_input_value_varnode(phi_op, init_index)
            )
            init_offset = self._byte_offset_from_parameter_pointer(init_varnode, pointer_param)
            if init_offset is None or int(init_offset) < 0:
                continue
            for back_index in range(input_count):
                if back_index == init_index:
                    continue
                back_varnode = self._follow_passthrough_varnode(
                    self._phi_input_value_varnode(phi_op, back_index)
                )
                step = self._extract_pointer_step(back_varnode, output)
                if step is None or step <= 0:
                    continue
                start_index = 0
                if int(init_offset) > 0 and int(init_offset) % int(step) == 0:
                    start_index = int(init_offset) // int(step)
                return {
                    "phi_op": phi_op,
                    "phi_output": output,
                    "stride": int(step),
                    "start_offset": int(init_offset),
                    "start_index": int(start_index),
                    "index_step": 1,
                    "index_scale": int(step),
                }
        return None

    def _match_index_progression_phi(
        self,
        phi_op,
    ) -> Optional[Dict[str, object]]:
        output = getattr(phi_op, "getOutput", lambda: None)()
        if output is None:
            return None

        input_count = int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0)
        for init_index in range(input_count):
            init_varnode = self._follow_passthrough_varnode(
                self._phi_input_value_varnode(phi_op, init_index)
            )
            init_value = self._varnode_constant_value(init_varnode)
            if init_value is None:
                continue
            for back_index in range(input_count):
                if back_index == init_index:
                    continue
                back_varnode = self._follow_passthrough_varnode(
                    self._phi_input_value_varnode(phi_op, back_index)
                )
                step = self._extract_index_step(back_varnode, output)
                if step is not None and step > 0:
                    return {
                        "phi_op": phi_op,
                        "phi_output": output,
                        "start": int(init_value),
                        "step": int(step),
                    }
        return None

    def _match_accumulator_phi(
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
            pointer_param,
            pointer_phis,
            index_phis,
            result_size=result_size,
        )
        if candidate is None:
            return None
        load_progressions = self._grouped_accumulator_load_progressions(
            candidate,
            pointer_param,
            pointer_phis,
            index_phis,
            result_size=result_size,
        )
        if not load_progressions:
            return None
        first = load_progressions[0]
        if any(
            signature["stride"] != first["stride"]
            or signature.get("start_index", 0) != first.get("start_index", 0)
            or signature.get("index_step", 1) != first.get("index_step", 1)
            or signature.get("index_scale", signature["stride"]) != first.get("index_scale", first["stride"])
            for signature in load_progressions[1:]
        ):
            return None
        expanded_terms = self._readonly_load_progression_term_counter(
            load_progressions,
            result_size=max(1, int(result_size or first["element_size"])),
        )
        if expanded_terms is None or any(count != 1 for count in expanded_terms.values()):
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
        direct_value_refs, direct_return_refs = self._direct_return_value_and_return_refs_from_varnodes(
            (
                getattr(phi_op, "getOutput", lambda: None)(),
                getattr(candidate.back_def, "getOutput", lambda: None)(),
                candidate.back_varnode,
            )
        )
        return_op_refs = self._dedupe_pcode_refs(tuple(direct_return_refs))
        return_value_op_refs = self._dedupe_pcode_refs(tuple(direct_value_refs))
        proof = ReductionAccumulatorProof(
            reduction_kind="memory_sum",
            pointer_base_ref=pointer_base_ref,
            count_parameter_name=count_param.get("name", "count"),
            count_parameter_index=count_param.get("index"),
            count_parameter_storage_identity_key=self._parameter_storage_identity_key(count_param),
            limit_expr=count_expr,
            result_size=max(1, int(result_size or first["element_size"])),
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

    def _match_accumulator_phi_candidate(
        self,
        phi_op,
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
                if back_def is None or getattr(back_def, "getMnemonic", lambda: None)() != "INT_ADD":
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
                    result_size=result_size,
                )
                if load_progressions is None or not load_progressions:
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
                )
        return None

    def _grouped_accumulator_load_progressions(
        self,
        candidate: ReadonlyAccumulatorPhiCandidate,
        pointer_param: dict,
        pointer_phis: Sequence[Dict[str, object]],
        index_phis: Sequence[Dict[str, object]],
        *,
        result_size: Optional[int] = None,
    ) -> List[Dict[str, object]]:
        grouped = list(candidate.load_progressions)
        parent_block = getattr(candidate.phi_op, "getParent", lambda: None)()
        if parent_block is None:
            return grouped
        for sibling_op in self._iter_block_ops(parent_block):
            if sibling_op is candidate.phi_op:
                continue
            if getattr(sibling_op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            sibling = self._match_accumulator_phi_candidate(
                sibling_op,
                pointer_param,
                pointer_phis,
                index_phis,
                result_size=result_size,
            )
            if sibling is None:
                continue
            if not self._accumulator_phi_candidates_can_group(candidate, sibling):
                continue
            grouped.extend(list(sibling.load_progressions))
        unique_grouped: List[Dict[str, object]] = []
        seen_keys = set()
        for signature in grouped:
            load_op_ref = signature.get("load_op_ref")
            if isinstance(load_op_ref, PcodeOpRef):
                load_key = load_op_ref.stable_key()
            else:
                load_key = None
            signature_key = (
                load_key,
                int(signature.get("start_offset", 0) or 0),
                max(1, int(signature.get("element_size", 0) or 0)),
            )
            if signature_key in seen_keys:
                continue
            seen_keys.add(signature_key)
            unique_grouped.append(signature)
        return unique_grouped

    def _accumulator_phi_candidates_can_group(
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
        return self._accumulator_load_group_signature(base.load_progressions) == self._accumulator_load_group_signature(
            sibling.load_progressions
        )

    def _pcode_block_group_key(self, block) -> Optional[Tuple[int, Optional[int]]]:
        if block is None:
            return None
        try:
            index = int(getattr(block, "getIndex", lambda: -1)() or -1)
        except Exception:
            index = -1
        try:
            start = getattr(block, "getStart", lambda: None)()
            start_offset = int(start.getOffset()) if start is not None else None
        except Exception:
            start_offset = None
        return (index, start_offset)

    def _accumulator_load_group_signature(
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

    def _extract_readonly_accumulator_seed_terms(
        self,
        init_varnode,
        pointer_param: dict,
        load_signature: Dict[str, int],
    ) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        if self._varnode_constant_value(init_varnode) == 0:
            return ()

        expected = self._expected_readonly_prefix_seed_terms(load_signature)
        if not expected:
            return None

        init_expr = self._build_pcode_expression(init_varnode, placeholders={})
        if init_expr is None:
            init_expr = self._trace_varnode_expression(init_varnode)
        terms = self._extract_readonly_reduction_terms(
            init_expr,
            [pointer_param],
            pointer_param,
        )
        if terms is None:
            return None
        seed_terms = tuple(terms)
        if tuple(term.stable_key() for term in seed_terms) != tuple(term.stable_key() for term in expected):
            if not self._readonly_seed_terms_are_materialized_pre_loop(
                seed_terms,
                load_signature,
            ):
                return None
        return seed_terms

    def _readonly_seed_terms_are_materialized_pre_loop(
        self,
        seed_terms: Sequence[ReadonlyReductionTermRef],
        load_signature: Dict[str, int],
    ) -> bool:
        """Accept non-prefix accumulator seeds only when their object layout is proven.

        A loop may start at a later logical index with an accumulator initialized
        from selected earlier memory terms.  That is not equivalent to a normal
        prefix unless the selected terms happen to cover the full omitted range,
        so the terms are preserved verbatim in the runtime proof.
        """

        seed_terms = tuple(seed_terms or ())
        if not seed_terms:
            return False
        start_index = int(load_signature.get("start_index", 0) or 0)
        index_step = int(load_signature.get("index_step", 1) or 1)
        index_scale = int(load_signature.get("index_scale", load_signature.get("stride", 0)) or 0)
        element_size = int(load_signature.get("element_size", 0) or 0)
        start_offset = int(load_signature.get("start_offset", 0) or 0)
        if start_index <= 0 or index_step <= 0 or index_scale <= 0 or element_size <= 0:
            return False

        term_start_offset = start_offset - start_index * index_scale
        seen_offsets = set()
        for term in seed_terms:
            try:
                byte_offset = int(term.byte_offset)
                access_size = max(1, int(term.access_size or 0))
            except (TypeError, ValueError):
                return False
            if access_size != element_size:
                return False
            if byte_offset in seen_offsets:
                return False
            seen_offsets.add(byte_offset)
            if byte_offset < term_start_offset or byte_offset >= start_offset:
                return False
            logical_delta = byte_offset - term_start_offset
            if logical_delta < 0 or (logical_delta % index_scale) != 0:
                return False
            logical_index = logical_delta // index_scale
            if logical_index < 0 or logical_index >= start_index:
                return False
            if ((start_index - logical_index) % index_step) != 0:
                return False
        return True

    def _expected_readonly_prefix_seed_terms(
        self,
        load_signature: Dict[str, int],
    ) -> Tuple[ReadonlyReductionTermRef, ...]:
        start_index = int(load_signature.get("start_index", 0) or 0)
        index_step = int(load_signature.get("index_step", 1) or 1)
        index_scale = int(load_signature.get("index_scale", load_signature.get("stride", 0)) or 0)
        element_size = int(load_signature.get("element_size", 0) or 0)
        if start_index <= 0 or index_step <= 0 or index_scale <= 0 or element_size <= 0:
            return ()
        start_offset = int(load_signature.get("start_offset", start_index * index_scale) or 0)
        term_start_offset = start_offset - start_index * index_scale
        first_index = start_index % index_step
        if first_index == start_index:
            return ()
        return tuple(
            ReadonlyReductionTermRef(
                byte_offset=int(term_start_offset + index * index_scale),
                access_size=element_size,
            )
            for index in range(first_index, start_index, index_step)
        )

    def _collect_load_progressions_from_varnode(
        self,
        varnode,
        pointer_param: dict,
        pointer_phis: Sequence[Dict[str, object]],
        index_phis: Sequence[Dict[str, object]],
        depth: int = 0,
        *,
        lsb_byte_offset: int = 0,
        narrowed_size: Optional[int] = None,
        result_size: Optional[int] = None,
    ) -> Optional[List[Dict[str, object]]]:
        if varnode is None or depth > 8:
            return None
        varnode = self._follow_readonly_load_addend_passthrough(varnode)
        if self._varnode_constant_value(varnode) == 0:
            return []
        if self._varnode_constant_value(varnode) is not None:
            return None

        def_op = getattr(varnode, "getDef", lambda: None)()
        if def_op is None:
            return None
        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        if mnemonic == "LOAD":
            signature = self._match_load_progression(
                def_op,
                pointer_param,
                pointer_phis,
                index_phis,
            )
            if signature is None:
                return None
            adjusted = self._adjust_readonly_load_signature_access(
                signature,
                lsb_byte_offset=int(lsb_byte_offset),
                narrowed_size=narrowed_size,
            )
            return [adjusted] if adjusted is not None else None
        if mnemonic == "INT_ADD":
            left = self._collect_load_progressions_from_varnode(
                def_op.getInput(0),
                pointer_param,
                pointer_phis,
                index_phis,
                depth + 1,
                lsb_byte_offset=lsb_byte_offset,
                narrowed_size=narrowed_size,
                result_size=result_size,
            )
            right = self._collect_load_progressions_from_varnode(
                def_op.getInput(1),
                pointer_param,
                pointer_phis,
                index_phis,
                depth + 1,
                lsb_byte_offset=lsb_byte_offset,
                narrowed_size=narrowed_size,
                result_size=result_size,
            )
            if left is None or right is None:
                return None
            return left + right
        if mnemonic == "INT_SEXT":
            input_varnode = self._follow_readonly_load_addend_passthrough(def_op.getInput(0))
            input_size = max(1, int(getattr(input_varnode, "getSize", lambda: 0)() or 0))
            result_bytes = int(result_size or 0)
            if result_bytes <= 0 or result_bytes > input_size:
                return None
            next_narrowed_size = (
                result_bytes
                if narrowed_size is None
                else min(int(narrowed_size), result_bytes)
            )
            return self._collect_load_progressions_from_varnode(
                input_varnode,
                pointer_param,
                pointer_phis,
                index_phis,
                depth + 1,
                lsb_byte_offset=lsb_byte_offset,
                narrowed_size=next_narrowed_size,
                result_size=result_size,
            )
        if mnemonic in {"SUBPIECE", "INT_RIGHT", "INT_ZEXT", "CAST", "COPY"}:
            next_lsb_byte_offset = int(lsb_byte_offset)
            next_narrowed_size = narrowed_size
            if mnemonic == "SUBPIECE":
                byte_offset = self._varnode_constant_value(
                    self._follow_readonly_load_addend_passthrough(def_op.getInput(1))
                )
                if byte_offset is None or int(byte_offset) < 0:
                    return None
                output = getattr(def_op, "getOutput", lambda: None)()
                next_lsb_byte_offset += int(byte_offset)
                output_size = max(1, int(getattr(output, "getSize", lambda: 0)() or 0))
                next_narrowed_size = (
                    output_size
                    if next_narrowed_size is None
                    else min(int(next_narrowed_size), output_size)
                )
            elif mnemonic == "INT_RIGHT":
                shift_bits = self._varnode_constant_value(
                    self._follow_readonly_load_addend_passthrough(def_op.getInput(1))
                )
                if shift_bits is None or int(shift_bits) < 0 or (int(shift_bits) % 8) != 0:
                    return None
                next_lsb_byte_offset += int(shift_bits) // 8
            elif mnemonic != "SUBPIECE" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 1:
                return None
            return self._collect_load_progressions_from_varnode(
                def_op.getInput(0),
                pointer_param,
                pointer_phis,
                index_phis,
                depth + 1,
                lsb_byte_offset=next_lsb_byte_offset,
                narrowed_size=next_narrowed_size,
                result_size=result_size,
            )
        if mnemonic == "INT_AND" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._follow_readonly_load_addend_passthrough(def_op.getInput(0))
            right = self._follow_readonly_load_addend_passthrough(def_op.getInput(1))
            left_const = self._varnode_constant_value(left)
            right_const = self._varnode_constant_value(right)
            if left_const is not None:
                mask_width = self._low_mask_width_bytes_from_value(int(left_const))
                if mask_width is None:
                    return None
                return self._collect_load_progressions_from_varnode(
                    right,
                    pointer_param,
                    pointer_phis,
                    index_phis,
                    depth + 1,
                    lsb_byte_offset=lsb_byte_offset,
                    narrowed_size=narrowed_size or mask_width,
                    result_size=result_size,
                )
            if right_const is not None:
                mask_width = self._low_mask_width_bytes_from_value(int(right_const))
                if mask_width is None:
                    return None
                return self._collect_load_progressions_from_varnode(
                    left,
                    pointer_param,
                    pointer_phis,
                    index_phis,
                    depth + 1,
                    lsb_byte_offset=lsb_byte_offset,
                    narrowed_size=narrowed_size or mask_width,
                    result_size=result_size,
                )
        return None

    def _follow_readonly_load_addend_passthrough(self, varnode):
        current = varnode
        seen = set()
        passthrough = {"COPY", "CAST", "INT_ZEXT"}
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

    def _readonly_load_progression_term_counter(
        self,
        load_progressions: Sequence[Dict[str, object]],
        *,
        result_size: int,
    ) -> Optional[Counter[Tuple[int, int]]]:
        counter: Counter[Tuple[int, int]] = Counter()
        for signature in load_progressions or ():
            lane_offset = int(signature.get("start_offset", 0) or 0)
            lane_size = max(1, int(signature.get("element_size", 0) or 0))
            access_size = min(max(1, int(result_size or lane_size)), lane_size)
            if access_size <= 0 or lane_size % access_size != 0:
                return None
            for byte_delta in range(0, lane_size, access_size):
                counter[(lane_offset + byte_delta, access_size)] += 1
        return counter if counter else None

    def _adjust_readonly_load_signature_access(
        self,
        signature: Dict[str, object],
        *,
        lsb_byte_offset: int,
        narrowed_size: Optional[int],
    ) -> Optional[Dict[str, object]]:
        load_size = max(1, int(signature.get("element_size", 0) or 0))
        access_size = max(1, int(narrowed_size or load_size))
        lsb_byte_offset = int(lsb_byte_offset)
        if lsb_byte_offset < 0 or access_size > load_size or lsb_byte_offset + access_size > load_size:
            return None
        adjusted = dict(signature)
        if self._program_is_big_endian():
            byte_delta = load_size - access_size - lsb_byte_offset
        else:
            byte_delta = lsb_byte_offset
        adjusted["start_offset"] = int(adjusted.get("start_offset", 0) or 0) + int(byte_delta)
        adjusted["element_size"] = access_size
        return adjusted

    def _low_mask_width_bytes_from_value(self, mask: int) -> Optional[int]:
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

    def _match_load_progression(
        self,
        load_op,
        pointer_param: dict,
        pointer_phis: Sequence[Dict[str, object]],
        index_phis: Sequence[Dict[str, object]],
    ) -> Optional[Dict[str, int]]:
        output = getattr(load_op, "getOutput", lambda: None)()
        load_size = max(1, int(getattr(output, "getSize", lambda: 4)() or 4))
        address_varnode = self._follow_passthrough_varnode(load_op.getInput(1))
        address_def = getattr(address_varnode, "getDef", lambda: None)()
        mnemonic = getattr(address_def, "getMnemonic", lambda: None)() if address_def is not None else None
        contextual_pointer_phis = self._pointer_phis_for_load_context(
            pointer_phis,
            load_op,
            address_def,
        )
        contextual_index_phis = self._index_phis_for_load_context(
            index_phis,
            load_op,
            address_def,
        )
        if address_def is not None and mnemonic == "PTRADD" and int(getattr(address_def, "getNumInputs", lambda: 0)() or 0) >= 3:
            base_input = self._follow_passthrough_varnode(address_def.getInput(0))
            index_input = self._follow_passthrough_varnode(address_def.getInput(1))
            elem_size = self._varnode_constant_value(self._follow_passthrough_varnode(address_def.getInput(2)))
            constant_index = self._varnode_constant_value(index_input)
            if elem_size is not None and elem_size > 0 and constant_index is not None:
                for pointer_info in contextual_pointer_phis:
                    if self._same_varnode_value(base_input, pointer_info["phi_output"]):
                        signature = self._load_progression_from_pointer_phi(
                            load_op,
                            pointer_info,
                            load_size=load_size,
                            extra_byte_offset=int(elem_size) * int(constant_index),
                        )
                        if signature is None:
                            return None
                        return {
                            **signature,
                        }
            index_info = self._matched_index_progression(index_input, contextual_index_phis)
            if (
                elem_size is not None
                and elem_size > 0
                and self._varnode_matches_parameter(base_input, pointer_param)
                and index_info is not None
            ):
                return {
                    "load_op_ref": self._make_pcode_op_ref(load_op),
                    "induction_phi_ref": self._make_pcode_op_ref(index_info.get("phi_op")),
                    "stride": int(elem_size) * int(index_info.get("step", 1) or 1),
                    "element_size": load_size,
                    "start_offset": int(elem_size) * int(index_info.get("start", 0) or 0),
                    "start_index": int(index_info.get("start", 0) or 0),
                    "index_step": int(index_info.get("step", 1) or 1),
                    "index_scale": int(elem_size),
                }
        if address_def is not None and mnemonic == "INT_ADD" and int(getattr(address_def, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._follow_passthrough_varnode(address_def.getInput(0))
            right = self._follow_passthrough_varnode(address_def.getInput(1))
            for pointer_info in contextual_pointer_phis:
                if self._same_varnode_value(left, pointer_info["phi_output"]) and self._varnode_constant_value(right) == 0:
                    return self._load_progression_from_pointer_phi(
                        load_op,
                        pointer_info,
                        load_size=load_size,
                    )
                if self._same_varnode_value(right, pointer_info["phi_output"]) and self._varnode_constant_value(left) == 0:
                    return self._load_progression_from_pointer_phi(
                        load_op,
                        pointer_info,
                        load_size=load_size,
                    )
            if self._varnode_matches_parameter(left, pointer_param):
                scaled = self._scaled_index_stride_and_start(right, contextual_index_phis)
                if scaled is not None and scaled[0] > 0:
                    induction_info = self._induction_info_from_scaled_index(right, contextual_index_phis)
                    return {
                        "load_op_ref": self._make_pcode_op_ref(load_op),
                        "induction_phi_ref": self._make_pcode_op_ref(induction_info.get("phi_op") if induction_info else None),
                        "stride": int(scaled[0]),
                        "element_size": load_size,
                        "start_offset": int(scaled[1]),
                        "start_index": int(scaled[2]),
                        "index_step": int(scaled[3]),
                        "index_scale": int(scaled[4]),
                    }
            if self._varnode_matches_parameter(right, pointer_param):
                scaled = self._scaled_index_stride_and_start(left, contextual_index_phis)
                if scaled is not None and scaled[0] > 0:
                    induction_info = self._induction_info_from_scaled_index(left, contextual_index_phis)
                    return {
                        "load_op_ref": self._make_pcode_op_ref(load_op),
                        "induction_phi_ref": self._make_pcode_op_ref(induction_info.get("phi_op") if induction_info else None),
                        "stride": int(scaled[0]),
                        "element_size": load_size,
                        "start_offset": int(scaled[1]),
                        "start_index": int(scaled[2]),
                        "index_step": int(scaled[3]),
                        "index_scale": int(scaled[4]),
                    }
        for pointer_info in contextual_pointer_phis:
            if self._same_varnode_value(address_varnode, pointer_info["phi_output"]):
                return self._load_progression_from_pointer_phi(
                    load_op,
                    pointer_info,
                    load_size=load_size,
                )
        return None

    def _pointer_phis_for_load_context(
        self,
        pointer_phis: Sequence[Dict[str, object]],
        load_op,
        address_def,
    ) -> List[Dict[str, object]]:
        if not pointer_phis:
            return []
        context_blocks = {
            self._pcode_block_group_key(getattr(load_op, "getParent", lambda: None)()),
            self._pcode_block_group_key(getattr(address_def, "getParent", lambda: None)()),
        }
        context_blocks.discard(None)

        def rank(pointer_info: Dict[str, object]) -> Tuple[int, str]:
            phi_block = self._pcode_block_group_key(
                getattr(pointer_info.get("phi_op"), "getParent", lambda: None)()
            )
            same_context = phi_block in context_blocks if phi_block is not None else False
            phi_ref = self._make_pcode_op_ref(pointer_info.get("phi_op"))
            return (0 if same_context else 1, repr(phi_ref.stable_key()) if phi_ref is not None else "")

        return sorted(list(pointer_phis), key=rank)

    def _index_phis_for_load_context(
        self,
        index_phis: Sequence[Dict[str, object]],
        load_op,
        address_def,
    ) -> List[Dict[str, object]]:
        if not index_phis:
            return []
        context_blocks = {
            self._pcode_block_group_key(getattr(load_op, "getParent", lambda: None)()),
            self._pcode_block_group_key(getattr(address_def, "getParent", lambda: None)()),
        }
        context_blocks.discard(None)

        def rank(index_info: Dict[str, object]) -> Tuple[int, str]:
            phi_block = self._pcode_block_group_key(
                getattr(index_info.get("phi_op"), "getParent", lambda: None)()
            )
            same_context = phi_block in context_blocks if phi_block is not None else False
            phi_ref = self._make_pcode_op_ref(index_info.get("phi_op"))
            return (0 if same_context else 1, repr(phi_ref.stable_key()) if phi_ref is not None else "")

        return sorted(list(index_phis), key=rank)

    def _load_progression_from_pointer_phi(
        self,
        load_op,
        pointer_info: Dict[str, object],
        *,
        load_size: int,
        extra_byte_offset: int = 0,
    ) -> Optional[Dict[str, object]]:
        """Build a load progression from a pointer-induction PHI.

        The induction PHI describes the cursor value at loop entry.  A load may
        add a constant element offset on top of that cursor, for example a peeled
        prefix loop whose body loads ``base[i + 1]`` while the cursor PHI starts
        at ``base``.  Keep both the byte offset and the logical element index in
        sync so seed compensation can prove that the materialized prefix covers
        the omitted loop iterations.
        """

        index_scale = int(pointer_info.get("index_scale", pointer_info["stride"]) or pointer_info["stride"])
        if index_scale <= 0:
            return None
        extra_byte_offset = int(extra_byte_offset or 0)
        if extra_byte_offset < 0 or extra_byte_offset % index_scale != 0:
            return None
        return {
            "load_op_ref": self._make_pcode_op_ref(load_op),
            "induction_phi_ref": self._make_pcode_op_ref(pointer_info.get("phi_op")),
            "stride": int(pointer_info["stride"]),
            "element_size": max(1, int(load_size or 0)),
            "start_offset": int(pointer_info.get("start_offset", 0) or 0) + extra_byte_offset,
            "start_index": int(pointer_info.get("start_index", 0) or 0) + (extra_byte_offset // index_scale),
            "index_step": int(pointer_info.get("index_step", 1) or 1),
            "index_scale": index_scale,
        }

    def _matched_index_progression(
        self,
        varnode,
        index_phis: Sequence[Dict[str, object]],
    ) -> Optional[Dict[str, object]]:
        varnode = self._follow_passthrough_varnode(varnode)
        for info in index_phis:
            if self._same_varnode_value(varnode, info["phi_output"]):
                return info
        return None

    def _induction_info_from_scaled_index(
        self,
        varnode,
        index_phis: Sequence[Dict[str, object]],
    ) -> Optional[Dict[str, object]]:
        varnode = self._follow_passthrough_varnode(varnode)
        direct = self._matched_index_progression(varnode, index_phis)
        if direct is not None:
            return direct
        def_op = getattr(varnode, "getDef", lambda: None)()
        if def_op is None:
            return None
        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        if mnemonic in {"INT_MULT", "INT_LEFT"} and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._induction_info_from_scaled_index(def_op.getInput(0), index_phis)
            if left is not None:
                return left
            return self._induction_info_from_scaled_index(def_op.getInput(1), index_phis)
        return None

    def _matches_index_progression(
        self,
        varnode,
        index_phis: Sequence[Dict[str, object]],
    ) -> bool:
        return self._matched_index_progression(varnode, index_phis) is not None

    def _scaled_index_stride(
        self,
        varnode,
        index_phis: Sequence[Dict[str, object]],
    ) -> Optional[int]:
        scaled = self._scaled_index_stride_and_start(varnode, index_phis)
        if scaled is None:
            return None
        return int(scaled[0])

    def _scaled_index_stride_and_start(
        self,
        varnode,
        index_phis: Sequence[Dict[str, object]],
    ) -> Optional[Tuple[int, int, int, int, int]]:
        varnode = self._follow_passthrough_varnode(varnode)
        index_info = self._matched_index_progression(varnode, index_phis)
        if index_info is not None:
            start = int(index_info.get("start", 0) or 0)
            step = int(index_info.get("step", 1) or 1)
            return step, start, start, step, 1
        def_op = getattr(varnode, "getDef", lambda: None)()
        if def_op is None:
            return None
        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        if mnemonic == "INT_MULT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._follow_passthrough_varnode(def_op.getInput(0))
            right = self._follow_passthrough_varnode(def_op.getInput(1))
            left_info = self._matched_index_progression(left, index_phis)
            if left_info is not None:
                scale = self._varnode_constant_value(right)
                if scale is None:
                    return None
                return (
                    int(scale) * int(left_info.get("step", 1) or 1),
                    int(scale) * int(left_info.get("start", 0) or 0),
                    int(left_info.get("start", 0) or 0),
                    int(left_info.get("step", 1) or 1),
                    int(scale),
                )
            right_info = self._matched_index_progression(right, index_phis)
            if right_info is not None:
                scale = self._varnode_constant_value(left)
                if scale is None:
                    return None
                return (
                    int(scale) * int(right_info.get("step", 1) or 1),
                    int(scale) * int(right_info.get("start", 0) or 0),
                    int(right_info.get("start", 0) or 0),
                    int(right_info.get("step", 1) or 1),
                    int(scale),
                )
        if mnemonic == "INT_LEFT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            shifted = self._follow_passthrough_varnode(def_op.getInput(0))
            shift_bits = self._varnode_constant_value(self._follow_passthrough_varnode(def_op.getInput(1)))
            shifted_info = self._matched_index_progression(shifted, index_phis)
            if shifted_info is not None and shift_bits is not None and shift_bits >= 0:
                scale = 1 << int(shift_bits)
                return (
                    scale * int(shifted_info.get("step", 1) or 1),
                    scale * int(shifted_info.get("start", 0) or 0),
                    int(shifted_info.get("start", 0) or 0),
                    int(shifted_info.get("step", 1) or 1),
                    int(scale),
                )
        return None

    def _extract_pointer_step(
        self,
        varnode,
        phi_output,
    ) -> Optional[int]:
        varnode = self._follow_passthrough_varnode(varnode)
        def_op = getattr(varnode, "getDef", lambda: None)()
        if def_op is None:
            return None
        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        if mnemonic == "PTRADD" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 3:
            base = self._follow_passthrough_varnode(def_op.getInput(0))
            index = self._follow_passthrough_varnode(def_op.getInput(1))
            element_size = self._varnode_constant_value(self._follow_passthrough_varnode(def_op.getInput(2)))
            index_value = self._varnode_constant_value(index)
            if (
                self._same_varnode_value(base, phi_output)
                and element_size is not None
                and index_value is not None
            ):
                return int(element_size) * int(index_value)
        if mnemonic in {"INT_ADD", "PTRSUB"} and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._follow_passthrough_varnode(def_op.getInput(0))
            right = self._follow_passthrough_varnode(def_op.getInput(1))
            if self._same_varnode_value(left, phi_output):
                return self._varnode_constant_value(right)
            if self._same_varnode_value(right, phi_output):
                return self._varnode_constant_value(left)
        return None

    def _extract_index_step(
        self,
        varnode,
        phi_output,
    ) -> Optional[int]:
        step_expr = self._extract_index_step_expression(varnode, phi_output)
        if step_expr is None:
            return None
        bit_width = int(getattr(step_expr, "size", 0) or getattr(varnode, "getSize", lambda: 0)() or 4) * 8
        return self._signed_constant_value(step_expr, bit_width_hint=bit_width)

    def _extract_index_step_expression(
        self,
        varnode,
        phi_output,
    ) -> Optional[Expression]:
        varnode = self._follow_passthrough_varnode(varnode)
        def_op = getattr(varnode, "getDef", lambda: None)()
        if def_op is None:
            return None
        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        if mnemonic in {"INT_ADD", "INT_SUB"} and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._follow_passthrough_varnode(def_op.getInput(0))
            right = self._follow_passthrough_varnode(def_op.getInput(1))
            if self._same_varnode_value(left, phi_output):
                step_expr = self._build_pcode_expression(right, placeholders={})
                if step_expr is None or self._expression_is_unresolved(step_expr):
                    return None
                if mnemonic == "INT_ADD":
                    return step_expr
                negated = Expression.unary_op("INT_2COMP", step_expr)
                negated.size = int(getattr(step_expr, "size", 0) or getattr(varnode, "getSize", lambda: 0)() or 4)
                return negated
            if self._same_varnode_value(right, phi_output):
                if mnemonic != "INT_ADD":
                    return None
                step_expr = self._build_pcode_expression(left, placeholders={})
                if step_expr is None or self._expression_is_unresolved(step_expr):
                    return None
                return step_expr
        return None

    def _follow_passthrough_varnode(self, varnode):
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

    def _varnode_cache_key(self, varnode):
        if varnode is None:
            return None
        address_key = None
        try:
            address = varnode.getAddress()
            if address is not None:
                address_key = (
                    address.getAddressSpace().getName(),
                    int(varnode.getOffset()),
                    int(varnode.getSize()),
                )
        except Exception:
            address_key = None

        def_key = None
        def_op = getattr(varnode, "getDef", lambda: None)()
        if def_op is not None:
            seq = getattr(def_op, "getSeqnum", lambda: None)()
            if seq is not None:
                try:
                    target = seq.getTarget()
                    target_key = str(target) if target is not None else None
                except Exception:
                    target_key = None
                try:
                    order_key = int(seq.getOrder())
                except Exception:
                    order_key = None
                try:
                    time_key = int(seq.getTime())
                except Exception:
                    time_key = None
                def_key = (target_key, order_key, time_key, getattr(def_op, "getMnemonic", lambda: None)())
        if address_key is not None or def_key is not None:
            return ("varnode", address_key, def_key)
        return ("varnode_id", id(varnode))

    def _new_loop_variable_binder_scope(self) -> Dict[Tuple[str, Tuple[Any, ...]], int]:
        return {}

    def _loop_variable_binder_ordinal(
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

    def _loop_variable_expression(
        self,
        scope: Optional[Dict[Tuple[str, Tuple[Any, ...]], int]],
        role: str,
        name: str,
        varnode,
        size: object,
    ) -> Expression:
        try:
            normalized_size = max(1, int(size or 4))
        except (TypeError, ValueError):
            normalized_size = 4
        return Expression.variable(
            name,
            size=normalized_size,
            runtime_ref=self._loop_variable_identity_ref(
                role,
                varnode,
                binder_ordinal=self._loop_variable_binder_ordinal(scope, role, varnode),
            ),
        )

    def _loop_variable_identity_ref(
        self,
        role: str,
        varnode,
        *,
        binder_ordinal: int = 0,
    ) -> Optional[LoopVariableIdentityRef]:
        key = self._varnode_cache_key(varnode)
        if key is None:
            return None
        return LoopVariableIdentityRef(
            role=str(role or "loop_variable"),
            binder_ordinal=max(0, int(binder_ordinal)),
            varnode_key=key,
        )

    def _same_varnode_value(self, left, right) -> bool:
        if left is None or right is None:
            return False
        if left is right:
            return True
        try:
            if left == right:
                return True
        except Exception:
            pass
        try:
            left_addr = left.getAddress()
            right_addr = right.getAddress()
            if (
                left_addr is not None
                and right_addr is not None
                and left_addr.getAddressSpace().getName() == right_addr.getAddressSpace().getName()
                and int(left.getOffset()) == int(right.getOffset())
                and int(left.getSize()) == int(right.getSize())
            ):
                return True
        except Exception:
            pass
        left_high = getattr(left, "getHigh", lambda: None)()
        right_high = getattr(right, "getHigh", lambda: None)()
        if left_high is not None and right_high is not None:
            if left_high is right_high:
                return True
            left_rep = getattr(left_high, "getRepresentative", lambda: None)()
            right_rep = getattr(right_high, "getRepresentative", lambda: None)()
            if left_rep is not None and left_rep is right_rep:
                return True
        return False

    def _same_placeholder_varnode(self, left, right) -> bool:
        if left is None or right is None:
            return False
        if left is right:
            return True
        try:
            if left == right:
                return True
        except Exception:
            pass
        left_high = getattr(left, "getHigh", lambda: None)()
        right_high = getattr(right, "getHigh", lambda: None)()
        if left_high is not None and right_high is not None:
            if left_high is right_high:
                return True
            left_rep = getattr(left_high, "getRepresentative", lambda: None)()
            right_rep = getattr(right_high, "getRepresentative", lambda: None)()
            if left_rep is not None and left_rep is right_rep:
                return True
        return False

    def _varnode_matches_parameter(
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

    def _parameter_identity_keys_from_descriptor(
        self,
        parameter: dict,
    ) -> set[Tuple[Any, ...]]:
        identities: set[Tuple[Any, ...]] = set()
        try:
            index = int(parameter.get("index", -1))
        except (TypeError, ValueError):
            index = -1
        if index >= 0:
            identities.add(("parameter_index", index))
        storage_key = self._summary_storage_identity_key(
            parameter.get("storage_info", parameter.get("storage"))
        )
        if storage_key is not None:
            identities.add(("parameter_storage", storage_key))
        return identities

    def _storage_info_from_varnode(self, varnode) -> Optional[StorageInfo]:
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

    def _parameter_index_from_symbol(self, symbol) -> Optional[int]:
        for method_name in ("getCategoryIndex", "getCategory"):
            getter = getattr(symbol, method_name, None)
            if not callable(getter):
                continue
            try:
                index = int(getter())
            except Exception:
                continue
            if index >= 0:
                return index
        return None

    def _varnode_constant_value(
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

    def _varnode_unsigned_constant_value(self, varnode) -> Optional[int]:
        value = self._varnode_constant_value(varnode)
        if value is None:
            return None
        return int(value)

    def _signed_varnode_constant_value(self, varnode) -> Optional[int]:
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

    def _choose_return_reaching_accumulator(
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

    def _varnode_reaches_return(
        self,
        start_varnode,
        *,
        budget: int = 128,
    ) -> bool:
        stack = [start_varnode]
        seen = set()
        while stack and len(seen) < budget:
            current = stack.pop()
            if current is None:
                continue
            current_id = id(current)
            if current_id in seen:
                continue
            seen.add(current_id)
            descendants = getattr(current, "getDescendants", lambda: None)()
            if descendants is None:
                continue
            try:
                iterator = iter(descendants)
            except TypeError:
                iterator = None
            if iterator is not None:
                for op in iterator:
                    mnemonic = getattr(op, "getMnemonic", lambda: None)()
                    if mnemonic == "RETURN":
                        return True
                    output = getattr(op, "getOutput", lambda: None)()
                    if output is not None:
                        stack.append(output)
                continue
            while descendants.hasNext():
                op = descendants.next()
                mnemonic = getattr(op, "getMnemonic", lambda: None)()
                if mnemonic == "RETURN":
                    return True
                output = getattr(op, "getOutput", lambda: None)()
                if output is not None:
                    stack.append(output)
        return False

    def _reachable_return_op_refs_from_varnodes(
        self,
        start_varnodes: Sequence[object],
        *,
        budget: int = 128,
    ) -> Tuple[PcodeOpRef, ...]:
        stack = [varnode for varnode in start_varnodes if varnode is not None]
        seen_varnodes = set()
        refs: Dict[Tuple[Any, ...], PcodeOpRef] = {}
        while stack and len(seen_varnodes) < budget:
            current = stack.pop()
            current_id = id(current)
            if current_id in seen_varnodes:
                continue
            seen_varnodes.add(current_id)
            for equivalent in self._high_varnode_instances(current):
                equivalent_id = id(equivalent)
                if equivalent_id not in seen_varnodes:
                    seen_varnodes.add(equivalent_id)
                for op in self._iter_varnode_descendant_ops(equivalent):
                    mnemonic = getattr(op, "getMnemonic", lambda: None)()
                    if mnemonic == "RETURN":
                        ref = self._make_pcode_op_ref(op)
                        if (
                            ref is not None
                            and (
                                ref.address_offset is not None
                                or ref.seq_time is not None
                                or ref.seq_order is not None
                            )
                        ):
                            refs.setdefault(ref.stable_key(), ref)
                        continue
                    output = getattr(op, "getOutput", lambda: None)()
                    if output is not None:
                        stack.append(output)
        return tuple(sorted(refs.values(), key=lambda ref: repr(ref.stable_key())))

    def _reachable_return_value_op_refs_from_varnodes(
        self,
        start_varnodes: Sequence[object],
        *,
        budget: int = 128,
    ) -> Tuple[PcodeOpRef, ...]:
        value_refs, _return_refs = self._reachable_return_value_and_return_refs_from_varnodes(
            start_varnodes,
            budget=budget,
        )
        return value_refs

    def _direct_return_value_and_return_refs_from_varnodes(
        self,
        start_varnodes: Sequence[object],
        *,
        budget: int = 128,
    ) -> Tuple[Tuple[PcodeOpRef, ...], Tuple[PcodeOpRef, ...]]:
        """Return refs proven to use the tracked value as the whole return.

        Reachability through an arithmetic op only proves contribution.  A
        scalar accumulator summary may replace a return region only when the
        accumulator value itself reaches RETURN, possibly through value-
        preserving width/passthrough ops.  Vectorized summaries have a separate
        lane-contribution proof and intentionally keep using the broader
        reachability collector after that proof succeeds.
        """

        passthrough_mnemonics = {
            "COPY",
            "CAST",
            "INT_ZEXT",
            "INT_SEXT",
            "SUBPIECE",
        }
        stack: List[Tuple[object, Tuple[PcodeOpRef, ...]]] = [
            (varnode, ()) for varnode in (start_varnodes or ()) if varnode is not None
        ]
        seen_states = set()
        value_refs: Dict[Tuple[Any, ...], PcodeOpRef] = {}
        return_refs: Dict[Tuple[Any, ...], PcodeOpRef] = {}
        while stack and len(seen_states) < budget:
            current, path_refs = stack.pop()
            for equivalent in self._high_varnode_instances(current):
                state_key = (
                    id(equivalent),
                    tuple(ref.stable_key() for ref in path_refs),
                )
                if state_key in seen_states:
                    continue
                seen_states.add(state_key)
                for op in self._iter_varnode_descendant_ops(equivalent):
                    mnemonic = getattr(op, "getMnemonic", lambda: None)()
                    if mnemonic == "RETURN":
                        ref = self._make_pcode_op_ref(op)
                        if (
                            ref is not None
                            and (
                                ref.address_offset is not None
                                or ref.seq_time is not None
                                or ref.seq_order is not None
                            )
                        ):
                            return_refs.setdefault(ref.stable_key(), ref)
                            for value_ref in path_refs:
                                value_refs.setdefault(value_ref.stable_key(), value_ref)
                        continue
                    if mnemonic not in passthrough_mnemonics:
                        continue
                    output = getattr(op, "getOutput", lambda: None)()
                    if output is None:
                        continue
                    ref = self._make_pcode_op_ref(op)
                    next_path_refs = path_refs
                    if (
                        ref is not None
                        and (
                            ref.address_offset is not None
                            or ref.seq_time is not None
                            or ref.seq_order is not None
                        )
                    ):
                        next_path_refs = tuple(path_refs) + (ref,)
                    stack.append((output, next_path_refs))
        return (
            tuple(sorted(value_refs.values(), key=lambda ref: repr(ref.stable_key()))),
            tuple(sorted(return_refs.values(), key=lambda ref: repr(ref.stable_key()))),
        )

    def _reachable_return_value_and_return_refs_from_varnodes(
        self,
        start_varnodes: Sequence[object],
        *,
        budget: int = 128,
    ) -> Tuple[Tuple[PcodeOpRef, ...], Tuple[PcodeOpRef, ...]]:
        stack = [varnode for varnode in start_varnodes if varnode is not None]
        seen_varnodes = set()
        value_refs: Dict[Tuple[Any, ...], PcodeOpRef] = {}
        return_refs: Dict[Tuple[Any, ...], PcodeOpRef] = {}
        while stack and len(seen_varnodes) < budget:
            current = stack.pop()
            current_id = id(current)
            if current_id in seen_varnodes:
                continue
            seen_varnodes.add(current_id)
            for equivalent in self._high_varnode_instances(current):
                equivalent_id = id(equivalent)
                if equivalent_id not in seen_varnodes:
                    seen_varnodes.add(equivalent_id)
                for op in self._iter_varnode_descendant_ops(equivalent):
                    output = getattr(op, "getOutput", lambda: None)()
                    if output is not None:
                        stack.append(output)
                    if getattr(op, "getMnemonic", lambda: None)() == "RETURN":
                        ref = self._make_pcode_op_ref(op)
                        if (
                            ref is not None
                            and (
                                ref.address_offset is not None
                                or ref.seq_time is not None
                                or ref.seq_order is not None
                            )
                        ):
                            return_refs.setdefault(ref.stable_key(), ref)
                    elif output is not None:
                        reachable_returns = self._reachable_return_op_refs_from_varnodes((output,))
                        if not reachable_returns:
                            ref = None
                        else:
                            for return_ref in reachable_returns:
                                return_refs.setdefault(return_ref.stable_key(), return_ref)
                            ref = self._make_pcode_op_ref(op)
                    else:
                        ref = None
                    if (
                        ref is not None
                        and (
                            ref.address_offset is not None
                            or ref.seq_time is not None
                            or ref.seq_order is not None
                        )
                    ):
                        value_refs.setdefault(ref.stable_key(), ref)
        return (
            tuple(sorted(value_refs.values(), key=lambda ref: repr(ref.stable_key()))),
            tuple(sorted(return_refs.values(), key=lambda ref: repr(ref.stable_key()))),
        )

    def _high_varnode_instances(self, varnode) -> Tuple[object, ...]:
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

    def _trace_varnode_expression(
        self,
        varnode,
    ) -> Optional[Expression]:
        if varnode is None:
            return None
        try:
            return self.tracer.trace_varnode(varnode, 0, use_cache=False)
        except TypeError:
            try:
                return self.tracer.trace_varnode(varnode, use_cache=False)
            except Exception:
                return None
        except Exception:
            return None

    def _try_summarize_branch_accumulator_loop(
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

    def _infer_pointer_parameter_name(self, analysis) -> Optional[str]:
        for param in analysis.parameters or []:
            name = str(param.get("name") or "")
            if not name:
                continue
            if is_pointer_data_type(
                param.get("data_type_obj"),
                param.get("data_type"),
                program=getattr(self.tracer, "program", None),
            ):
                return name
        return None

    def _infer_loop_parameter_pair(self, analysis) -> Optional[Tuple[str, str]]:
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

    def _match_less_parameter_pair(self, condition: Condition) -> Optional[Tuple[str, str]]:
        relation = self._parameter_comparison_relation(condition)
        if relation is None:
            return None
        left_name, relation_name, right_name = relation
        if relation_name == "<":
            return left_name, right_name
        if relation_name == ">":
            return right_name, left_name
        return None

    def _parameter_name_from_expr(self, expr: Optional[Expression]) -> Optional[str]:
        if expr is None:
            return None
        if expr.expr_type == ExpressionType.PARAMETER and expr.name:
            return expr.name
        normalized = self._normalize_counter_view(expr, getattr(expr, "name", None) or "")
        if normalized is not None and normalized[0].name:
            return normalized[0].name
        return None

    def _param_expr(self, analysis, name: str) -> Expression:
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

    def _find_pointer_null_case(
        self,
        returns: Sequence[ReturnInfo],
        pointer_name: str,
    ) -> Optional[ReturnInfo]:
        for ret in returns:
            if not self._return_is_constant(ret):
                continue
            if any(self._condition_is_pointer_null(cond, pointer_name) for cond in ret.conditions or []):
                return ret
        return None

    def _find_no_loop_base_case(
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

    def _find_one_step_cases(
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

    def _synthesize_one_step_cases_from_effects(
        self,
        analysis,
        base_case: ReturnInfo,
        pointer_name: str,
        start_name: str,
        limit_name: str,
        *,
        require_pointer_nonnull: bool,
    ) -> List[ReturnInfo]:
        effect_summary = getattr(analysis, "effect_summary", None)
        if effect_summary is None:
            return []
        coeffs = self._extract_linear_location_coefficients(base_case.value, analysis.parameters or [])
        if not coeffs:
            return []

        grouped: Dict[Tuple[object, ...], List] = {}
        for effect in effect_summary.effects or []:
            conds = ConditionSimplifier.simplify_conditions_object_centric(effect.conditions or [])
            key = _runtime_conditions_signature(conds)
            grouped.setdefault(key, []).append((conds, effect))

        synthesized: List[ReturnInfo] = []
        for grouped_effects in grouped.values():
            conds = grouped_effects[0][0]
            has_nonnull = any(self._condition_is_pointer_nonnull(cond, pointer_name) for cond in conds)
            if require_pointer_nonnull and not has_nonnull:
                self._debug(
                    "Skipping effect-derived one-step candidate: missing local pointer-nonnull guard "
                    f"for conditions {[cond.to_string() for cond in conds]}"
                )
                continue
            if not any(self._condition_is_less(cond, start_name, limit_name) for cond in conds):
                self._debug(
                    "Skipping effect-derived one-step candidate: missing loop-progress guard "
                    f"for conditions {[cond.to_string() for cond in conds]}"
                )
                continue
            parity = self._extract_counter_parity(conds, start_name)
            if parity is None:
                self._debug(
                    "Skipping effect-derived one-step candidate: could not determine counter parity "
                    f"for conditions {[cond.to_string() for cond in conds]}"
                )
                continue
            step_eq = Condition(
                Expression.binary_op(
                    "INT_EQUAL",
                    self._param_expr(analysis, limit_name),
                    Expression.binary_op(
                        "INT_ADD",
                        self._param_expr(analysis, start_name),
                        Expression.constant(1, self._param_expr(analysis, start_name).size or 4),
                    ),
                ),
                False,
            )
            step_context = ConditionSimplifier.simplify_conditions_object_centric(list(conds) + [step_eq])
            if ConditionSimplifier.object_centric_is_contradiction(step_context):
                self._debug(
                    "Skipping effect-derived one-step candidate: one-step context is contradictory "
                    f"for conditions {[cond.to_string() for cond in conds]}"
                )
                continue

            delta_terms: List[Expression] = []
            for _conds, effect in grouped_effects:
                coeff = coeffs.get(effect.location)
                if coeff in (None, 0):
                    continue
                delta_expr = self._extract_store_delta_expr(
                    effect,
                    analysis.parameters or [],
                    step_context,
                )
                if delta_expr is None:
                    self._debug(
                        "Aborting effect-derived one-step synthesis: could not isolate store delta "
                        f"for location={effect.location} value={effect.value.to_string()} "
                        f"conditions={[cond.to_string() for cond in step_context]}"
                    )
                    return []
                reduced_delta = _reduce_expression_under_conditions(delta_expr, step_context)
                scaled = self._scale_expression(reduced_delta, coeff)
                if scaled is not None:
                    delta_terms.append(scaled)
            if not delta_terms:
                self._debug(
                    "Skipping effect-derived one-step candidate: no additive delta terms matched "
                    f"for conditions {[cond.to_string() for cond in conds]}"
                )
                continue

            delta_sum = self._sum_expression_terms(delta_terms)
            if delta_sum is None:
                continue
            value = Expression.binary_op("INT_ADD", base_case.value, delta_sum)
            value.size = base_case.value.size
            synthesized.append(
                ReturnInfo(
                    address=base_case.address,
                    value=value,
                    conditions=step_context,
                    branch_index=9_000 if parity else 9_001,
                    pcode_identity=base_case.pcode_identity,
                    pcode_order=base_case.pcode_order,
                    pcode_time=base_case.pcode_time,
                    pcode_op_ref=getattr(base_case, "pcode_op_ref", None),
                    return_value_pcode_op_refs=tuple(
                        getattr(base_case, "return_value_pcode_op_refs", ()) or ()
                    ),
                )
            )
        return synthesized

    def _extract_linear_location_coefficients(
        self,
        expr: Expression,
        parameters: Sequence[dict],
    ) -> Dict[CanonicalLocation, int]:
        coeffs: Dict[CanonicalLocation, int] = {}
        for sign, term in self._flatten_add_terms(expr):
            if term.expr_type == ExpressionType.CONSTANT:
                continue
            if term.expr_type != ExpressionType.MEMORY or not term.operands:
                return {}
            location = canonicalize_location(term.operands[0], parameters, size=term.size)
            if location is None:
                return {}
            coeffs[location] = coeffs.get(location, 0) + sign
        return {loc: coeff for loc, coeff in coeffs.items() if coeff != 0}

    def _extract_store_delta_expr(
        self,
        effect,
        parameters: Sequence[dict],
        conditions: Optional[Sequence[Condition]] = None,
    ) -> Optional[Expression]:
        active_conditions = list(conditions or [])
        reduced_value = _reduce_expression_under_conditions(effect.value, active_conditions)
        current_read = Expression.memory(
            self._address_expr_for_location(effect.location, parameters),
            size=effect.location.size,
        )
        reduced_current_read = _reduce_expression_under_conditions(current_read, active_conditions)
        delta = self._extract_additive_delta(reduced_value, reduced_current_read, parameters)
        if delta is not None:
            return delta
        if reduced_value.equals(reduced_current_read):
            return Expression.constant(0, size=effect.location.size)
        return None

    def _address_expr_for_location(
        self,
        location: CanonicalLocation,
        parameters: Sequence[dict],
    ) -> Expression:
        base_param = None
        for param in parameters:
            if location.base_ref.matches_parameter(param):
                base_param = param
                break
        base_expr = Expression.parameter(
            location.base_ref.parameter_name or location.base_param,
            index=int((base_param or {}).get("index", 0)),
            data_type=(base_param or {}).get("data_type"),
            data_type_obj=(base_param or {}).get("data_type_obj"),
            size=int((base_param or {}).get("size", 8) or 8),
        )
        if location.offset == 0:
            return base_expr
        return Expression.binary_op(
            "INT_ADD",
            base_expr,
            Expression.constant(location.offset, size=base_expr.size or 8),
        )

    def _extract_additive_delta(
        self,
        expr: Expression,
        base_expr: Expression,
        parameters: Sequence[dict],
    ) -> Optional[Expression]:
        expr_terms = self._flatten_add_terms(expr)
        base_terms = self._flatten_add_terms(base_expr)
        remaining = list(expr_terms)
        for sign, term in base_terms:
            matched = False
            for index, (cand_sign, cand_term) in enumerate(remaining):
                if cand_sign != sign:
                    continue
                if not self._terms_equivalent(cand_term, term, parameters):
                    continue
                del remaining[index]
                matched = True
                break
            if not matched:
                return None
        return self._sum_expression_terms(
            [self._scale_expression(term, sign) for sign, term in remaining if self._scale_expression(term, sign) is not None]
        )

    def _terms_equivalent(
        self,
        left: Expression,
        right: Expression,
        parameters: Sequence[dict],
    ) -> bool:
        if _expressions_equivalent_under_conditions(left, right, [], parameters):
            return True
        if (
            left.expr_type == ExpressionType.MEMORY
            and right.expr_type == ExpressionType.MEMORY
            and left.operands
            and right.operands
        ):
            left_loc = canonicalize_location(left.operands[0], parameters, size=left.size)
            right_loc = canonicalize_location(right.operands[0], parameters, size=right.size)
            if left_loc is not None and right_loc is not None:
                return left_loc == right_loc
        return _runtime_expression_signature(left) == _runtime_expression_signature(right)

    def _flatten_add_terms(
        self,
        expr: Expression,
        sign: int = 1,
    ) -> List[Tuple[int, Expression]]:
        if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_ADD" and len(expr.operands) == 2:
            return self._flatten_add_terms(expr.operands[0], sign) + self._flatten_add_terms(expr.operands[1], sign)
        if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_SUB" and len(expr.operands) == 2:
            return self._flatten_add_terms(expr.operands[0], sign) + self._flatten_add_terms(expr.operands[1], -sign)
        if expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "INT_2COMP" and expr.operands:
            return self._flatten_add_terms(expr.operands[0], -sign)
        return [(sign, expr)]

    def _scale_expression(self, expr: Expression, factor: int) -> Optional[Expression]:
        if factor == 0:
            return None
        if factor == 1:
            return expr
        if factor == -1:
            negated = Expression.unary_op("INT_2COMP", expr)
            negated.size = expr.size
            return negated
        return Expression.binary_op(
            "INT_MULT",
            Expression.constant(factor, size=expr.size or 4),
            expr,
        )

    def _sum_expression_terms(
        self,
        terms: Sequence[Optional[Expression]],
    ) -> Optional[Expression]:
        normalized = [term for term in terms if term is not None]
        if not normalized:
            return Expression.constant(0, 4)
        total = normalized[0]
        for term in normalized[1:]:
            total = Expression.binary_op("INT_ADD", total, term)
            total.size = max(total.size, term.size)
        return total

    def _build_parity_split_loop_value(
        self,
        base_expr: Expression,
        start_name: str,
        limit_name: str,
        even_affine: Tuple[int, int],
        odd_affine: Tuple[int, int],
        start_is_even: bool,
    ) -> Optional[Expression]:
        start_expr = self._param_expr_placeholder(start_name, base_expr.size or 4)
        limit_expr = self._param_expr_placeholder(limit_name, base_expr.size or 4)
        size = start_expr.size or 4
        n_expr = Expression.binary_op("INT_SUB", limit_expr, start_expr)
        n_expr.size = size
        one = Expression.constant(1, size)
        two = Expression.constant(2, size)

        if start_is_even:
            n_even = Expression.binary_op("INT_SDIV", Expression.binary_op("INT_ADD", n_expr, one), two)
            n_odd = Expression.binary_op("INT_SDIV", n_expr, two)
            first_even = start_expr
            first_odd = Expression.binary_op("INT_ADD", start_expr, one)
        else:
            n_even = Expression.binary_op("INT_SDIV", n_expr, two)
            n_odd = Expression.binary_op("INT_SDIV", Expression.binary_op("INT_ADD", n_expr, one), two)
            first_even = Expression.binary_op("INT_ADD", start_expr, one)
            first_odd = start_expr
        for item in (n_even, n_odd, first_even, first_odd):
            item.size = size

        sum_even = self._build_arithmetic_progression_sum(first_even, n_even, size)
        sum_odd = self._build_arithmetic_progression_sum(first_odd, n_odd, size)
        contrib_terms: List[Expression] = []
        even_sum_term = self._scale_expression(sum_even, even_affine[0])
        odd_sum_term = self._scale_expression(sum_odd, odd_affine[0])
        if even_sum_term is not None:
            contrib_terms.append(even_sum_term)
        if odd_sum_term is not None:
            contrib_terms.append(odd_sum_term)
        even_count_term = self._scale_expression(n_even, even_affine[1])
        odd_count_term = self._scale_expression(n_odd, odd_affine[1])
        if even_count_term is not None:
            contrib_terms.append(even_count_term)
        if odd_count_term is not None:
            contrib_terms.append(odd_count_term)
        contrib = self._sum_expression_terms(contrib_terms)
        if contrib is None:
            return None
        total = Expression.binary_op("INT_ADD", base_expr, contrib)
        total.size = base_expr.size
        return total

    def _param_expr_placeholder(self, name: str, size: int) -> Expression:
        return Expression.parameter(name, size=size)

    def _build_arithmetic_progression_sum(
        self,
        first_term: Expression,
        count: Expression,
        size: int,
    ) -> Expression:
        one = Expression.constant(1, size)
        count_minus_one = Expression.binary_op("INT_SUB", count, one)
        count_minus_one.size = size
        tail = Expression.binary_op("INT_ADD", first_term, count_minus_one)
        tail.size = size
        pair_sum = Expression.binary_op("INT_ADD", first_term, tail)
        pair_sum.size = size
        product = Expression.binary_op("INT_MULT", count, pair_sum)
        product.size = size
        half = Expression.binary_op("INT_SDIV", product, Expression.constant(2, size))
        half.size = size
        return half

    def _condition_is_pointer_null(self, condition: Condition, pointer_name: str) -> bool:
        return self._match_pointer_equality(condition, pointer_name, expect_zero=True)

    def _condition_is_pointer_nonnull(self, condition: Condition, pointer_name: str) -> bool:
        return self._match_pointer_equality(condition, pointer_name, expect_zero=False)

    def _pointer_nonnull_condition(self, pointer_name: str, analysis) -> Condition:
        ptr_expr = self._param_expr(analysis, pointer_name)
        return Condition(
            Expression.binary_op(
                "INT_NOTEQUAL",
                ptr_expr,
                Expression.constant(0, size=ptr_expr.size or 8),
            ),
            False,
        )

    def _match_pointer_equality(self, condition: Condition, pointer_name: str, expect_zero: bool) -> bool:
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return False
        if expr.operator not in {"INT_EQUAL", "INT_NOTEQUAL"}:
            return False
        left_name = self._parameter_name_from_expr(expr.operands[0])
        right_name = self._parameter_name_from_expr(expr.operands[1])
        left_const = self._constant_value(expr.operands[0])
        right_const = self._constant_value(expr.operands[1])
        matches = (
            (left_name == pointer_name and right_const == 0)
            or (right_name == pointer_name and left_const == 0)
        )
        if not matches:
            return False
        is_equal = expr.operator == "INT_EQUAL"
        if condition.negated:
            is_equal = not is_equal
        return is_equal if expect_zero else not is_equal

    def _condition_is_less(self, condition: Condition, start_name: str, limit_name: str) -> bool:
        relation = self._parameter_comparison_relation(condition)
        if relation is None:
            return False
        left_name, relation_name, right_name = relation
        return (
            (left_name == start_name and right_name == limit_name and relation_name == "<")
            or (left_name == limit_name and right_name == start_name and relation_name == ">")
        )

    def _condition_is_not_less(self, condition: Condition, start_name: str, limit_name: str) -> bool:
        relation = self._parameter_comparison_relation(condition)
        if relation is None:
            return False
        left_name, relation_name, right_name = relation
        return (
            (left_name == start_name and right_name == limit_name and relation_name == ">=")
            or (left_name == limit_name and right_name == start_name and relation_name == "<=")
        )

    def _condition_is_step_equality(self, condition: Condition, start_name: str, limit_name: str) -> bool:
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_EQUAL" or len(expr.operands) != 2:
            return False
        left_name = self._parameter_name_from_expr(expr.operands[0])
        right_name = self._parameter_name_from_expr(expr.operands[1])
        if left_name == limit_name and self._expr_is_add_one_of_param(expr.operands[1], start_name):
            return not condition.negated
        if right_name == limit_name and self._expr_is_add_one_of_param(expr.operands[0], start_name):
            return not condition.negated
        return False

    def _expr_is_add_one_of_param(self, expr: Expression, param_name: str) -> bool:
        if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_ADD" or len(expr.operands) != 2:
            return False
        left_name = self._parameter_name_from_expr(expr.operands[0])
        right_name = self._parameter_name_from_expr(expr.operands[1])
        left_const = self._constant_value(expr.operands[0])
        right_const = self._constant_value(expr.operands[1])
        return (
            (left_name == param_name and right_const == 1)
            or (right_name == param_name and left_const == 1)
        )

    def _extract_counter_parity(
        self,
        conditions: Sequence[Condition],
        counter_name: str,
    ) -> Optional[bool]:
        for condition in conditions or []:
            expr = getattr(condition, "expression", None)
            if (
                expr is None
                or expr.expr_type != ExpressionType.BINARY_OP
                or expr.operator not in {"INT_EQUAL", "INT_NOTEQUAL"}
                or len(expr.operands) != 2
            ):
                continue
            bitand = None
            parity_const = None
            if self._constant_value(expr.operands[0]) in {0, 1}:
                bitand = expr.operands[1]
                parity_const = self._constant_value(expr.operands[0])
            elif self._constant_value(expr.operands[1]) in {0, 1}:
                bitand = expr.operands[0]
                parity_const = self._constant_value(expr.operands[1])
            if bitand is None or parity_const is None:
                continue
            if bitand.expr_type != ExpressionType.BINARY_OP or bitand.operator != "INT_AND" or len(bitand.operands) != 2:
                continue
            if self._constant_value(bitand.operands[0]) == 1:
                counter_expr = bitand.operands[1]
            elif self._constant_value(bitand.operands[1]) == 1:
                counter_expr = bitand.operands[0]
            else:
                continue
            if self._parameter_name_from_expr(counter_expr) != counter_name:
                continue
            is_equal = expr.operator == "INT_EQUAL"
            if condition.negated:
                is_equal = not is_equal
            is_even = is_equal if parity_const == 0 else not is_equal
            return is_even
        return None

    def _return_is_constant(self, ret: ReturnInfo) -> bool:
        return ret.value is not None and ret.value.expr_type == ExpressionType.CONSTANT

    def _iter_pcode_ops(self, high_function) -> Iterable:
        for basic_block in high_function.getBasicBlocks():
            pcode_iter = basic_block.getIterator()
            while pcode_iter.hasNext():
                yield pcode_iter.next()

    def _parameter_can_be_counter(self, param_info: dict) -> bool:
        size = int(param_info.get("size") or 0)
        if size not in {1, 2, 4, 8}:
            return False
        data_type_obj = param_info.get("data_type_obj")
        if data_type_obj is None:
            return True
        return is_integral_data_type(
            data_type_obj,
            param_info.get("data_type"),
            program=getattr(self.tracer, "program", None),
        )

    def _parameter_expression(self, param_info: dict) -> Expression:
        size = int(param_info.get("size") or 4)
        storage_info = self._summary_storage_info_from_parameter(param_info)
        try:
            index = int(param_info.get("index")) if param_info.get("index") is not None else -1
        except (TypeError, ValueError):
            index = -1
        return Expression.parameter(
            param_info.get("name", "param_1"),
            index=index,
            data_type=param_info.get("data_type"),
            data_type_obj=param_info.get("data_type_obj"),
            size=size,
            storage_info=storage_info,
        )

    def _is_direct_self_call(self, op, function_name: str) -> bool:
        resolver = getattr(self.tracer, "resolve_call_target_ref", None)
        if not callable(resolver):
            return False
        target_ref = resolver(
            op.getInput(0),
            allow_containing=True,
            allow_code_address=False,
        )
        return bool(target_ref is not None and target_ref.function_name == function_name)

    def _expression_contains_recursive_unknown(self, expr: Optional[Expression], function_name: str) -> bool:
        if expr is None:
            return False
        if expr.expr_type == ExpressionType.UNKNOWN:
            runtime_ref = getattr(expr, "runtime_ref", None)
            if not isinstance(runtime_ref, UnknownValueRef):
                return False
            target_ref = runtime_ref.target_ref
            return bool(
                target_ref is not None
                and target_ref.function_name == function_name
            )
        if expr.expr_type == ExpressionType.PHI and expr.value:
            return any(
                (cond is not None and self._expression_contains_recursive_unknown(cond.expression, function_name))
                or self._expression_contains_recursive_unknown(value, function_name)
                for cond, value in expr.value
            )
        return any(self._expression_contains_recursive_unknown(operand, function_name) for operand in expr.operands or [])

    def _is_constant_expression(self, expr: Optional[Expression]) -> bool:
        return expr is not None and expr.expr_type == ExpressionType.CONSTANT

    def _constant_value(self, expr: Optional[Expression]) -> Optional[int]:
        raw = self._raw_constant_value(expr)
        if raw is None:
            return None
        return raw

    def _raw_constant_value(self, expr: Optional[Expression]) -> Optional[int]:
        if expr is None:
            return None
        if expr.expr_type == ExpressionType.CONSTANT:
            return int(expr.value)
        evaluated = eval_constant_raw(expr)
        if evaluated is None:
            return None
        return int(evaluated[0])

    def _signed_constant_value(
        self,
        expr: Optional[Expression],
        bit_width_hint: Optional[int] = None,
    ) -> Optional[int]:
        raw_value = self._raw_constant_value(expr)
        if raw_value is None:
            return None
        assert expr is not None
        bit_width = int(bit_width_hint or ((expr.size or 0) * 8))
        if bit_width <= 0:
            return raw_value
        modulus = 1 << bit_width
        signed = raw_value % modulus
        if signed >= (1 << (bit_width - 1)):
            signed -= modulus
        return signed

    def _extract_addend_expression(self, expr: Expression, function_name: str) -> Optional[Expression]:
        if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None
        if expr.operator not in {"INT_ADD", "INT_SUB"}:
            return None

        left, right = expr.operands
        if self._expression_contains_recursive_unknown(left, function_name) and not self._expression_contains_recursive_unknown(right, function_name):
            if expr.operator == "INT_ADD":
                return right
            if expr.operator == "INT_SUB":
                return Expression.unary_op("INT_2COMP", right)
        if self._expression_contains_recursive_unknown(right, function_name) and not self._expression_contains_recursive_unknown(left, function_name):
            if expr.operator == "INT_ADD":
                return left
        return None

    def _extract_unit_step_from_call_argument(self, expr: Expression, param_name: str) -> Optional[int]:
        bit_width_hint = self._infer_counter_bit_width(expr, param_name)
        affine = self._extract_affine_term(expr, param_name, bit_width_hint=bit_width_hint)
        if affine is None:
            return None
        coeff, bias = affine
        if coeff != 1:
            return None
        if bias in {-1, 1}:
            return bias
        return None

    def _extract_affine_term(
        self,
        expr: Expression,
        param_name: str,
        bit_width_hint: Optional[int] = None,
    ) -> Optional[Tuple[int, int]]:
        normalized_counter = self._normalize_counter_view(expr, param_name)
        if normalized_counter is not None:
            return 1, 0
        if expr.expr_type == ExpressionType.CONSTANT:
            signed_value = self._signed_constant_value(expr, bit_width_hint=bit_width_hint)
            if signed_value is None:
                return None
            return 0, signed_value
        if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_2COMP", "INT_NEGATE"} and len(expr.operands) == 1:
            operand = self._extract_affine_term(
                expr.operands[0],
                param_name,
                bit_width_hint=bit_width_hint,
            )
            if operand is None:
                return None
            coeff, bias = operand
            return -coeff, -bias
        if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None

        node_bit_width = bit_width_hint or self._infer_counter_bit_width(expr, param_name)
        left = self._extract_affine_term(expr.operands[0], param_name, bit_width_hint=node_bit_width)
        right = self._extract_affine_term(expr.operands[1], param_name, bit_width_hint=node_bit_width)

        if expr.operator == "INT_ADD" and left is not None and right is not None:
            return left[0] + right[0], left[1] + right[1]
        if expr.operator == "INT_SUB" and left is not None and right is not None:
            return left[0] - right[0], left[1] - right[1]
        if expr.operator == "INT_MULT":
            left_const = self._signed_constant_value(expr.operands[0], bit_width_hint=node_bit_width)
            right_const = self._signed_constant_value(expr.operands[1], bit_width_hint=node_bit_width)
            if left_const is not None and right is not None:
                return left_const * right[0], left_const * right[1]
            if right_const is not None and left is not None:
                return right_const * left[0], right_const * left[1]
        return None

    def _extract_affine_placeholder_term(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
        bit_width_hint: Optional[int] = None,
    ) -> Optional[Tuple[int, int]]:
        expr = self._canonicalize_expression(expr)
        if expr is None:
            return None
        if bit_width_hint is None:
            bit_width_hint = max(1, int(getattr(placeholder, "size", 0) or 4)) * 8
        try:
            if expr.structural_key() == placeholder.structural_key():
                return 1, 0
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
        if expr.expr_type == ExpressionType.CONSTANT:
            signed_value = self._signed_constant_value(expr, bit_width_hint=bit_width_hint)
            if signed_value is None:
                return None
            return 0, signed_value
        if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_2COMP", "INT_NEGATE"} and len(expr.operands) == 1:
            operand = self._extract_affine_placeholder_term(
                expr.operands[0],
                placeholder,
                bit_width_hint=bit_width_hint,
            )
            if operand is None:
                return None
            coeff, bias = operand
            return -coeff, -bias
        if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None

        node_bit_width = bit_width_hint or (expr.size * 8 if expr.size else None)
        left = self._extract_affine_placeholder_term(
            expr.operands[0],
            placeholder,
            bit_width_hint=node_bit_width,
        )
        right = self._extract_affine_placeholder_term(
            expr.operands[1],
            placeholder,
            bit_width_hint=node_bit_width,
        )

        if expr.operator == "INT_ADD" and left is not None and right is not None:
            return left[0] + right[0], left[1] + right[1]
        if expr.operator == "INT_SUB" and left is not None and right is not None:
            return left[0] - right[0], left[1] - right[1]
        if expr.operator == "INT_MULT":
            left_const = self._signed_constant_value(expr.operands[0], bit_width_hint=node_bit_width)
            right_const = self._signed_constant_value(expr.operands[1], bit_width_hint=node_bit_width)
            if left_const is not None and right is not None:
                return left_const * right[0], left_const * right[1]
            if right_const is not None and left is not None:
                return right_const * left[0], right_const * left[1]
        return None

    def _normalize_counter_view(
        self,
        expr: Optional[Expression],
        param_name: str,
    ) -> Optional[Tuple[Expression, Optional[int]]]:
        if expr is None:
            return None
        if expr.expr_type == ExpressionType.PARAMETER and expr.name == param_name:
            return expr, (expr.size * 8) if expr.size else None
        if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_ZEXT", "INT_SEXT"} and len(expr.operands) == 1:
            return self._normalize_counter_view(expr.operands[0], param_name)
        if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "SUBPIECE" and len(expr.operands) == 2:
            source, offset = expr.operands
            offset_value = self._raw_constant_value(offset)
            if offset_value == 0:
                source_counter = self._normalize_counter_view(source, param_name)
                if source_counter is not None:
                    expr_bits = (expr.size * 8) if expr.size else None
                    if expr_bits is not None and expr_bits > 0:
                        return source_counter[0], expr_bits
        if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_AND" or len(expr.operands) != 2:
            return None

        left_counter = self._normalize_counter_view(expr.operands[0], param_name)
        right_counter = self._normalize_counter_view(expr.operands[1], param_name)
        left_const = self._raw_constant_value(expr.operands[0])
        right_const = self._raw_constant_value(expr.operands[1])

        if left_counter is not None and right_const is not None:
            mask_bits = self._bit_width_from_low_bit_mask(right_const)
            if mask_bits is not None:
                return left_counter[0], mask_bits
        if right_counter is not None and left_const is not None:
            mask_bits = self._bit_width_from_low_bit_mask(left_const)
            if mask_bits is not None:
                return right_counter[0], mask_bits
        return None

    def _infer_counter_bit_width(self, expr: Optional[Expression], param_name: str) -> Optional[int]:
        normalized = self._normalize_counter_view(expr, param_name)
        if normalized is not None:
            return normalized[1]
        if expr is None:
            return None
        for operand in expr.operands or []:
            operand_bit_width = self._infer_counter_bit_width(operand, param_name)
            if operand_bit_width is not None:
                return operand_bit_width
        return None

    def _bit_width_from_low_bit_mask(self, value: int) -> Optional[int]:
        if value <= 0:
            return None
        if (value & (value + 1)) != 0:
            return None
        bit_width = value.bit_length()
        if bit_width < 8 or bit_width % 8 != 0:
            return None
        return bit_width

    def _infer_lower_bound_from_conditions(self, conditions: Sequence[Condition], param_name: str) -> Optional[int]:
        lower_bounds: List[int] = []
        for condition in conditions or []:
            relation = self._condition_relation(condition, param_name)
            if relation is None:
                continue
            relation_name, constant = relation
            if relation_name == ">":
                lower_bounds.append(constant)
            elif relation_name == ">=":
                lower_bounds.append(constant - 1)
        if not lower_bounds:
            return None
        return max(lower_bounds)

    def _infer_lower_bound_from_base_conditions(self, conditions: Sequence[Condition], param_name: str) -> Optional[int]:
        upper_bounds: List[int] = []
        for condition in conditions or []:
            relation = self._condition_relation(condition, param_name)
            if relation is None:
                continue
            relation_name, constant = relation
            if relation_name == "<=":
                upper_bounds.append(constant)
            elif relation_name == "<":
                upper_bounds.append(constant - 1)
        if not upper_bounds:
            return None
        return min(upper_bounds)

    def _condition_relation(self, condition: Condition, param_name: str) -> Optional[Tuple[str, int]]:
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None
        left, right = expr.operands
        right_const = self._constant_value(right)
        left_const = self._constant_value(left)

        op = expr.operator
        relation: Optional[str] = None

        if self._is_condition_counter_view(left, param_name) and right_const is not None:
            relation = self._comparison_to_relation(op, swapped=False)
            constant = right_const
        elif self._is_condition_counter_view(right, param_name) and left_const is not None:
            relation = self._comparison_to_relation(op, swapped=True)
            constant = left_const
        else:
            return None

        if relation is None:
            return None
        if condition.negated:
            relation = self._negate_relation(relation)
            if relation is None:
                return None
        return relation, constant

    def _exact_counter_value_from_conditions(
        self,
        conditions: Sequence[Condition],
        param_name: str,
    ) -> Optional[int]:
        lower_bounds: List[int] = []
        upper_bounds: List[int] = []
        for condition in conditions or []:
            expr = getattr(condition, "expression", None)
            if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
                relation = self._condition_relation(condition, param_name)
                if relation is None:
                    continue
                relation_name, constant = relation
            else:
                operator = getattr(expr, "operator", None)
                left, right = expr.operands
                right_const = self._constant_value(right)
                left_const = self._constant_value(left)
                if self._is_condition_counter_view(left, param_name) and right_const is not None:
                    if operator == "INT_EQUAL" and not condition.negated:
                        return right_const
                    if operator == "INT_NOTEQUAL" and condition.negated:
                        return right_const
                if self._is_condition_counter_view(right, param_name) and left_const is not None:
                    if operator == "INT_EQUAL" and not condition.negated:
                        return left_const
                    if operator == "INT_NOTEQUAL" and condition.negated:
                        return left_const
                affine_left = self._solve_counter_affine_equality(left, right_const, operator, condition.negated, param_name)
                if affine_left is not None:
                    return affine_left
                affine_right = self._solve_counter_affine_equality(right, left_const, operator, condition.negated, param_name)
                if affine_right is not None:
                    return affine_right
                relation = self._condition_relation(condition, param_name)
                if relation is None:
                    continue
                relation_name, constant = relation

            if relation_name == ">":
                lower_bounds.append(constant + 1)
            elif relation_name == ">=":
                lower_bounds.append(constant)
            elif relation_name == "<":
                upper_bounds.append(constant - 1)
            elif relation_name == "<=":
                upper_bounds.append(constant)
        if not lower_bounds or not upper_bounds:
            return None
        exact_lower = max(lower_bounds)
        exact_upper = min(upper_bounds)
        if exact_lower == exact_upper:
            return exact_lower
        return None

    def _solve_counter_affine_equality(
        self,
        expr: Optional[Expression],
        other_const: Optional[int],
        operator: Optional[str],
        negated: bool,
        param_name: str,
    ) -> Optional[int]:
        if (
            expr is None
            or other_const is None
            or operator not in {"INT_EQUAL", "INT_NOTEQUAL"}
        ):
            return None
        if operator == "INT_EQUAL" and negated:
            return None
        if operator == "INT_NOTEQUAL" and not negated:
            return None

        bit_width_hint = self._infer_counter_bit_width(expr, param_name)
        affine = self._extract_affine_term(expr, param_name, bit_width_hint=bit_width_hint)
        if affine is None:
            return None
        coeff, bias = affine
        if coeff != 1:
            return None
        return other_const - bias

    def _parameter_comparison_relation(self, condition: Condition) -> Optional[Tuple[str, str, str]]:
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None
        relation = self._comparison_to_relation(expr.operator, swapped=False)
        if relation is None:
            return None
        left_name = self._parameter_name_from_expr(expr.operands[0])
        right_name = self._parameter_name_from_expr(expr.operands[1])
        if not left_name or not right_name or left_name == right_name:
            return None
        if condition.negated:
            relation = self._negate_relation(relation)
            if relation is None:
                return None
        return left_name, relation, right_name

    def _is_condition_counter_view(self, expr: Optional[Expression], param_name: str) -> bool:
        if expr is None:
            return False
        if self._normalize_counter_view(expr, param_name) is not None:
            return True
        if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "PIECE" and len(expr.operands) == 2:
            return self._normalize_counter_view(expr.operands[1], param_name) is not None
        if expr.expr_type != ExpressionType.BINARY_OP or expr.operator not in {"INT_OR", "INT_ADD"} or len(expr.operands) != 2:
            return False
        left, right = expr.operands
        return self._matches_shifted_high_reconstruction(left, right, param_name) or self._matches_shifted_high_reconstruction(right, left, param_name)

    def _matches_shifted_high_reconstruction(
        self,
        high_expr: Optional[Expression],
        low_expr: Optional[Expression],
        param_name: str,
    ) -> bool:
        low_counter = self._normalize_counter_view(low_expr, param_name)
        if low_counter is None:
            return False
        if high_expr is None:
            return False
        if high_expr.expr_type != ExpressionType.BINARY_OP or high_expr.operator != "INT_LEFT" or len(high_expr.operands) != 2:
            return False
        shift_bits = self._raw_constant_value(high_expr.operands[1])
        if shift_bits is None:
            return False
        low_bits = low_counter[1]
        if low_bits is None:
            return False
        return shift_bits == low_bits

    def _comparison_to_relation(self, operator: str, swapped: bool) -> Optional[str]:
        mapping = {
            "INT_SLESS": "<",
            "INT_SLESSEQUAL": "<=",
            "INT_LESS": "<",
            "INT_LESSEQUAL": "<=",
        }
        relation = mapping.get(operator)
        if relation is None:
            return None
        if not swapped:
            return relation
        if relation == "<":
            return ">"
        if relation == "<=":
            return ">="
        return None

    def _negate_relation(self, relation: str) -> Optional[str]:
        return {
            "<": ">=",
            "<=": ">",
            ">": "<=",
            ">=": "<",
        }.get(relation)

    def _build_closed_form(
        self,
        param_expr: Expression,
        lower_bound: int,
        coeff: int,
        bias: int,
        base_value: int,
    ) -> Optional[Expression]:
        size = param_expr.size or 4
        wide_size = self._summary_working_size(size)
        lower_const = Expression.constant(lower_bound, size)
        wide_param = self._zero_extend_bitpattern(param_expr, wide_size)
        wide_lower = self._zero_extend_bitpattern(lower_const, wide_size)
        shift_amount = Expression.constant(1, wide_size)

        triangular_n = self._triangular(wide_param, wide_size, shift_amount)
        if lower_bound == 0:
            triangular_delta = triangular_n
        else:
            triangular_lower = self._triangular(wide_lower, wide_size, shift_amount)
            triangular_delta = Expression.binary_op("INT_SUB", triangular_n, triangular_lower)
            triangular_delta.size = wide_size

        term_exprs: List[Expression] = []
        coeff_term = self._scale_term(triangular_delta, coeff, wide_size)
        if coeff_term is not None:
            term_exprs.append(coeff_term)
        if bias != 0:
            distance = Expression.binary_op("INT_SUB", wide_param, wide_lower)
            distance.size = wide_size
            bias_term = self._scale_term(distance, bias, wide_size)
            if bias_term is not None:
                term_exprs.append(bias_term)

        total = self._sum_terms(term_exprs, base_value, size, wide_size)
        return self._truncate_to_width(total, size)

    def _triangular(self, expr: Expression, size: int, shift_amount: Expression) -> Expression:
        one = Expression.constant(1, size)
        incremented = Expression.binary_op("INT_ADD", expr, one)
        incremented.size = size
        product = Expression.binary_op("INT_MULT", expr, incremented)
        product.size = size
        tri = Expression.binary_op("INT_RIGHT", product, shift_amount)
        tri.size = size
        return tri

    def _summary_working_size(self, narrow_size: int) -> int:
        narrow_bits = max(8, narrow_size * 8)
        wide_bits = max(64, narrow_bits * 2)
        return max(narrow_size, (wide_bits + 7) // 8)

    def _zero_extend_bitpattern(self, expr: Expression, target_size: int) -> Expression:
        source_size = expr.size or 0
        if source_size <= 0 or source_size >= target_size:
            copied = expr
            copied.size = max(source_size, target_size)
            if source_size > target_size:
                return self._truncate_to_width(copied, target_size)
            return copied
        widened = Expression.unary_op("INT_ZEXT", expr)
        widened.size = target_size
        return widened

    def _truncate_to_width(self, expr: Expression, target_size: int) -> Expression:
        if (expr.size or 0) <= target_size:
            expr.size = target_size
            return expr
        truncated = Expression.binary_op("SUBPIECE", expr, Expression.constant(0, 4))
        truncated.size = target_size
        return truncated

    def _scale_term(
        self,
        expr: Expression,
        factor: int,
        wide_size: int,
    ) -> Optional[Expression]:
        if factor == 0:
            return None
        if factor == 1:
            expr.size = wide_size
            return expr
        if factor == -1:
            negated = Expression.unary_op("INT_2COMP", expr)
            negated.size = wide_size
            return negated
        factor_const = self._zero_extend_bitpattern(Expression.constant(factor, expr.size or wide_size), wide_size)
        scaled = Expression.binary_op("INT_MULT", factor_const, expr)
        scaled.size = wide_size
        return scaled

    def _sum_terms(
        self,
        term_exprs: Sequence[Expression],
        base_value: int,
        size: int,
        wide_size: int,
    ) -> Expression:
        total: Optional[Expression] = None
        if base_value != 0:
            total = self._zero_extend_bitpattern(Expression.constant(base_value, size), wide_size)
        for term in term_exprs:
            if total is None:
                total = term
                continue
            total = Expression.binary_op("INT_ADD", total, term)
            total.size = wide_size
        if total is None:
            total = self._zero_extend_bitpattern(Expression.constant(0, size), wide_size)
        total.size = wide_size
        return total

    def _build_recursive_conditions(self, param_expr: Expression, lower_bound: int) -> Optional[List[Condition]]:
        size = param_expr.size or 4
        lower_const = Expression.constant(lower_bound, size)
        cond_expr = Expression.binary_op("INT_SLESS", lower_const, param_expr)
        return [Condition(cond_expr, False)]

    def _build_base_conditions(self, param_expr: Expression, lower_bound: int) -> Optional[List[Condition]]:
        size = param_expr.size or 4
        lower_const = Expression.constant(lower_bound, size)
        cond_expr = Expression.binary_op("INT_SLESSEQUAL", param_expr, lower_const)
        return [Condition(cond_expr, False)]
