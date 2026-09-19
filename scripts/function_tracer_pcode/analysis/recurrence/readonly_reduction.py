"""Read-only memory reduction summaries and their return-region proofs."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Sequence, Tuple
from collections import Counter
from dataclasses import replace
from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
    LocationBaseRef,
    READONLY_SUM_OPCODE,
    ReadonlyReductionRef,
    ReadonlyReductionTermRef,
    ReadonlyReductionWitness,
    ReductionAccumulatorProof,
    ReturnInfo,
)
from scripts.function_tracer_pcode.core.render_smt import expression_smt_bit_width
from scripts.function_tracer_pcode.core.signature import get_declared_type_signedness, is_pointer_data_type
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    ConditionConstraintSet,
    ConditionSMTOracle,
    ConditionSimplifier,
    ReadonlyAffineProgressionLiteral,
    ResidueLoopCase,
    StateTransitionLoopModel,
    _runtime_conditions_signature,
    _runtime_expression_signature,
)
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    ReadonlyRoundedCountCandidate,
    _expressions_equivalent_under_conditions,
    _reduce_expression_under_conditions,
    canonicalize_location,
)
from scripts.function_tracer_pcode.analysis.debug import (
    bounded_items,
    summarize_conditions,
    summarize_values,
)


def _impl__has_readonly_pointer_reduction_candidate(
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


def _impl__readonly_affine_progression_literal(self, analysis) -> Optional[ReadonlyAffineProgressionLiteral]:
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
            step = lanes[1] - lanes[0]
            if step <= 0:
                continue
            if all((lanes[index] - lanes[index - 1]) == step for index in range(1, len(lanes))):
                return ReadonlyAffineProgressionLiteral(step=int(step), lane_base=int(lanes[0]))
    return None


def _impl__readonly_affine_progression_literal_step(self, analysis) -> Optional[int]:
    literal = self._readonly_affine_progression_literal(analysis)
    if literal is None:
        return None
    return int(literal.step)


def _impl__read_readonly_int32_lanes(self, address_value: int, lane_count: int) -> Optional[Tuple[int, ...]]:
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


def _impl__residue_cases_contain_readonly_affine_literal_address(
    self,
    residue_cases: Sequence[ResidueLoopCase],
    *,
    function_body_ranges: Sequence[Tuple[int, int]] = (),
) -> bool:
    for case in residue_cases or ():
        # Once extraction has proven that a SUBPIECE/PIECE/shift term came
        # from readonly literal data, keep the scalar counted-loop path
        # conservative.  The readonly literal may be carried by bias_expr
        # rather than by the integer affine tuple, and treating it as an
        # ordinary scalar affine term can hide the vector-lane contract.
        if bool(getattr(case, "affine_from_readonly_literal", False)):
            return True
        if bool(getattr(case, "affine_from_address_literal", False)):
            return True
        # Some optimized vector loops have already collapsed the readonly
        # lane literal to a bare constant by this point.  Keep this
        # fallback specific to readonly int32 progressions.  A bare
        # executable/function-body-looking bias is rejected only for the
        # constant-iteration shape; address-like affine offsets still need
        # extraction provenance before they block scalar summaries.
        affine = tuple(getattr(case, "affine", ()) or ())
        if len(affine) >= 2:
            coeff_value = affine[0]
            bias_value = affine[1]
            if self._readonly_int32_progression_literal_at_value(bias_value):
                return True
            try:
                integer_coeff = int(coeff_value)
                integer_bias = int(bias_value)
            except (TypeError, ValueError):
                integer_coeff = None
                integer_bias = None
            if integer_coeff == 0 and integer_bias is not None and (
                self._constant_resolves_to_function_body_address(integer_bias, function_body_ranges)
                or self._constant_resolves_to_executable_address(integer_bias)
            ):
                return True
    return False


def _impl__readonly_int32_progression_literal_at_value(self, value: Any) -> bool:
    try:
        integer_value = int(value)
    except (TypeError, ValueError):
        return False
    lanes = self._read_readonly_int32_lanes(integer_value, 4)
    if lanes is None or len(lanes) < 4:
        return False
    step = lanes[1] - lanes[0]
    if step <= 0:
        return False
    return all(
        (lanes[index] - lanes[index - 1]) == step
        for index in range(1, len(lanes))
    )


def _impl__address_points_to_readonly_data(self, address_value: int) -> bool:
    if address_value < 0:
        return False
    program = getattr(self.tracer, "program", None)
    if program is None:
        return False
    try:
        memory = program.getMemory()
        address_factory = program.getAddressFactory()
        default_space = address_factory.getDefaultAddressSpace()
        address = default_space.getAddress(int(address_value))
    except Exception:
        return False
    if memory is None or address is None:
        return False
    try:
        block = memory.getBlock(address)
    except Exception:
        return False
    if block is None:
        return False
    try:
        return bool(block.isRead()) and not bool(block.isWrite()) and not bool(block.isExecute())
    except Exception:
        return False


def _impl__base_witnesses_exactly_cover_region(
    self,
    witnesses: Sequence[ReturnInfo],
    base_conditions: Sequence[Condition],
) -> bool:
    if not witnesses:
        return False
    for ret in witnesses or ():
        ret_conditions = tuple(getattr(ret, "conditions", None) or ())
        if not ret_conditions:
            return False
        try:
            base_implies_ret = ConditionSMTOracle.conjunction_is_unsat(
                list(base_conditions or [])
                + [condition.negate() for condition in ret_conditions]
            )
            ret_implies_base = ConditionSMTOracle.conjunction_is_unsat(
                list(ret_conditions)
                + [condition.negate() for condition in base_conditions or ()]
            )
        except Exception:
            return False
        if base_implies_ret is True and ret_implies_base is True:
            return True
    return False


def _impl__zero_base_return_witnesses_for_region(
    self,
    *,
    returns: Sequence[ReturnInfo],
    base_conditions: Sequence[Condition],
    result_size: int,
) -> Tuple[ReturnInfo, ...]:
    """Find exact returns proving the synthesized nonpositive base value.

    The multiplicative PHI region summary may emit a normalized
    ``n <= 0 -> 0`` return, but only when existing exact returns already
    prove that value over the whole base region.
    """

    zero = Expression.constant(0, size=max(1, int(result_size or 4)))
    witnesses: List[ReturnInfo] = []
    for ret in returns or ():
        ret_conditions = tuple(getattr(ret, "conditions", None) or ())
        if not self._conditions_overlap_conditions(ret_conditions, base_conditions):
            continue
        value = getattr(ret, "value", None)
        if not self._return_value_equals_under_conditions(
            value,
            zero,
            tuple(base_conditions or ()) + ret_conditions,
        ):
            continue
        witnesses.append(ret)
    if not witnesses:
        return ()
    if any(not tuple(getattr(ret, "conditions", None) or ()) for ret in witnesses):
        return tuple(witnesses)
    if any(
        ConditionConstraintSet.from_conditions(base_conditions or []).implies_all(
            tuple(getattr(ret, "conditions", None) or ())
        )
        for ret in witnesses
    ):
        return tuple(witnesses)
    coverage_key = self._prove_return_conditions_cover_region(
        region_conditions=base_conditions,
        returns=witnesses,
    )
    if coverage_key is None:
        return ()
    return tuple(witnesses)


def _impl__prove_return_region_summary_witnesses(
    self,
    *,
    analysis,
    summary_value: Expression,
    summary_conditions: Sequence[Condition],
    exact_returns: Sequence[ReturnInfo],
    allow_summary_region_coverage: bool = False,
) -> Optional[Tuple[Tuple[Any, ...], Tuple[Any, ...], str]]:
    overlapping: List[ReturnInfo] = []
    witness_entries: List[Tuple[Any, ...]] = []
    for ret in exact_returns or ():
        conditions = list(getattr(ret, "conditions", None) or [])
        if not self._return_overlaps_conditions(ret, summary_conditions):
            continue
        self._debug(
            "Return-region summary witness candidate: "
            f"branch={getattr(ret, 'branch_index', None)}, "
            f"conditions={len(conditions)}, value={self._safe_expr_text(getattr(ret, 'value', None))}"
        )
        if any(
            self._expression_is_unresolved(getattr(condition, "expression", None))
            for condition in conditions
        ):
            self._debug(
                "Declined return-region summary proof: overlapping exact return has unresolved condition "
                f"(branch={getattr(ret, 'branch_index', None)})"
            )
            return None
        parameters = self._collect_summary_parameter_specs(
            getattr(ret, "value", None),
            summary_value,
            *(condition.expression for condition in conditions + list(summary_conditions or ()) if condition is not None),
        )
        if parameters is None:
            self._debug(
                "Declined return-region summary proof: parameter collection failed "
                f"(branch={getattr(ret, 'branch_index', None)})"
            )
            return None
        if not self._prove_expression_equivalence_under_conditions(
            getattr(ret, "value", None),
            summary_value,
            conditions + list(summary_conditions or ()),
            parameters,
        ):
            self._debug(
                "Declined return-region summary proof: value equivalence failed "
                f"(branch={getattr(ret, 'branch_index', None)})"
            )
            return None
        overlapping.append(ret)
        witness_entries.append(
            (
                "exact_return_value_witness",
                _runtime_conditions_signature(tuple(conditions)),
                _runtime_expression_signature(getattr(ret, "value", None)),
                getattr(ret, "pcode_identity", None),
                getattr(ret, "branch_index", None),
            )
        )
    if not overlapping:
        self._debug("Declined return-region summary proof: no overlapping exact positive returns")
        return None
    coverage_key = self._prove_return_conditions_cover_region(
        region_conditions=summary_conditions,
        returns=overlapping,
    )
    coverage_status = "proved"
    if coverage_key is None:
        if allow_summary_region_coverage:
            coverage_key = self._prove_summary_conditions_plus_exact_returns_cover_active_precondition(
                active_preconditions=self._analysis_active_preconditions(analysis),
                summary_conditions=summary_conditions,
                exact_returns=exact_returns,
            )
            if coverage_key is not None:
                self._debug(
                    "Proved return-region summary coverage with summary conditions plus disjoint exact returns "
                    f"(witnesses={len(overlapping)})"
                )
        if coverage_key is None:
            self._debug(
                "Declined return-region summary proof: exact witnesses do not cover summary region "
                f"(witnesses={len(overlapping)})"
            )
            return None
    return ("exact_return_witnesses", tuple(witness_entries)), coverage_key, coverage_status


def _impl__expression_contains_readonly_literal_access(
    self,
    expr: Optional[Expression],
) -> bool:
    for node in self._iter_expression_nodes(expr):
        if getattr(node, "expr_type", None) != ExpressionType.BINARY_OP:
            continue
        if getattr(node, "operator", None) not in {"SUBPIECE", "PIECE", "INT_RIGHT"}:
            continue
        operands = tuple(getattr(node, "operands", ()) or ())
        if not operands:
            continue
        for operand in operands:
            if self._expression_contains_readonly_address_constant(operand):
                return True
    return False


def _impl__expression_contains_readonly_address_constant(
    self,
    expr: Optional[Expression],
) -> bool:
    for node in self._iter_expression_nodes(expr):
        if getattr(node, "expr_type", None) != ExpressionType.CONSTANT:
            continue
        value = self._raw_constant_value(node)
        if value is None:
            continue
        integer_value = int(value)
        if self._address_points_to_readonly_data(integer_value):
            return True
        lanes = self._read_readonly_int32_lanes(integer_value, 4)
        if lanes is None or len(lanes) < 4:
            continue
        step = lanes[1] - lanes[0]
        if step > 0 and all(
            (lanes[index] - lanes[index - 1]) == step
            for index in range(1, len(lanes))
        ):
            return True
    return False


def _impl__find_latch_exit_decrement_sum_witness_returns(
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


def _impl__try_summarize_readonly_pointer_reduction(
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
    self._debug(
        "Readonly reduction parameter candidates: "
        f"pointer={pointer_param.get('name')}[{pointer_param.get('index')}], "
        f"count={count_param.get('name')}[{count_param.get('index')}]"
    )

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
        self._debug("Declined readonly reduction summary: candidate normalization failed")
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
    count_positive_param_key = _runtime_expression_signature(self._parameter_expression(count_param))
    overlapping_positive_returns = [
        ret
        for ret in overlapping_positive_returns
        if not self._return_covers_nonpositive_parameter_region(
            ret,
            count_positive_param_key,
        )
    ]
    if not overlapping_positive_returns:
        self._debug(
            "Declined readonly reduction summary: replaceable returns only cover nonpositive counter region"
        )
        return None
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
        if self._debug_available():
            self._debug(
                "Readonly overlapping positive return classification: "
                f"exact_count={exact_count}, "
                f"conditions={summarize_conditions(ret.conditions or ())}"
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
        self._debug(
            "Readonly exact positive return proof status: "
            f"exact_count={exact_count}, absorbable={absorbable}, prefix_score={prefix_score}"
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
        if self._debug_available():
            self._debug(
                "Readonly analysis positive return classification: "
                f"exact_count={exact_count}, "
                f"conditions={summarize_conditions(ret.conditions or ())}"
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
        self._debug(
            "Readonly analysis exact return proof status: "
            f"exact_count={exact_count}, absorbable={absorbable}, prefix_score={prefix_score}"
        )
        if prefix_score <= 0 and absorbable:
            continue
        if not self._readonly_exact_count_region_is_fully_covered_by_return(
            ret,
            positive_conditions,
            count_param,
            int(exact_count),
        ):
            self._debug(
                "Declined readonly reduction summary: exact analysis return "
                f"does not fully cover singleton count={exact_count}"
            )
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
        self._debug("Declined readonly reduction summary: no overlapping positive returns after exact preservation")
        return None
    preserved_returns = [
        ret for ret in (analysis.returns or [])
        if ret not in overlapping_positive_returns and ret not in preserved_exact_positive_returns
    ]
    if not preserved_returns and not overlapping_positive_returns:
        self._debug("Declined readonly reduction summary: no preserved or overlapping returns remain")
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
    self._debug(
        "Readonly reduction summary lowering succeeded: "
        f"preserved_returns={len(preserved_returns)}, "
        f"overlapping_positive_returns={len(overlapping_positive_returns)}, "
        f"preserved_exact_positive_returns={len(preserved_exact_positive_returns)}, "
        f"exact_witnesses={len(exact_return_witnesses)}, "
        f"semantic_witnesses={len(semantic_witnesses)}"
    )
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
    summary_expr = self._readonly_reduction_summary_expression(
        summary_pointer_expr,
        summary_count_expr,
        reduction_ref,
        result_size=result_size,
    )
    if summary_expr is None:
        self._debug("Declined readonly reduction summary: could not build summary expression")
        return None
    positive_anchor = overlapping_positive_returns[0]
    superseded_returns = [
        ret
        for ret in (analysis.returns or [])
        if self._readonly_return_is_superseded_by_summary_region(
            ret,
            summary_positive_conditions,
            overlapping_positive_returns,
        )
    ]
    retained_original_returns = [
        ret
        for ret in (analysis.returns or [])
        if ret not in superseded_returns
    ]
    proof_ref = self._record_readonly_reduction_return_region_proof(
        analysis=analysis,
        summary_value=summary_expr,
        summary_conditions=summary_positive_conditions,
        retained_exact_returns=retained_original_returns,
        superseded_returns=superseded_returns,
        accumulator_proof=accumulator_proof,
        exact_return_witnesses=exact_return_witnesses,
        semantic_witnesses=semantic_witnesses,
    )
    if proof_ref is None:
        self._debug("Readonly reduction summary has no completed proof evidence; candidate gate must validate it")
    source_key = self._summary_value_source_key(summary_expr)
    if source_key is None:
        source_key = (
            "readonly_pointer_reduction_summary",
            _runtime_expression_signature(summary_expr),
        )
    preserved_returns = [
        self._readonly_preserved_return_as_exact_seed(ret)
        for ret in preserved_returns
    ]
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
        return_kind="summary_derived",
        summary_candidate_source_key=source_key,
        summary_transition_evidence_key=proof_ref,
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


def _impl__readonly_preserved_return_as_exact_seed(self, ret: ReturnInfo) -> ReturnInfo:
    """Expose resolved preserved returns as exact seeds to the summary gate."""
    if str(getattr(ret, "return_kind", "exact") or "exact") == "exact":
        return ret
    if getattr(ret, "summary_candidate_source_key", None) is not None:
        return ret
    if getattr(ret, "summary_transition_evidence_key", None) is not None:
        return ret
    if self._expression_tree_contains_type(getattr(ret, "value", None), ExpressionType.UNKNOWN):
        return ret
    if self._readonly_reduction_ref_from_return(ret) is not None:
        return ret
    return replace(
        ret,
        return_kind="exact",
        summary_candidate_id=None,
        summary_candidate_source_key=None,
        summary_transition_evidence_key=None,
        validation_blockers=(),
    )


def _impl__readonly_return_is_superseded_by_summary_region(
    self,
    ret: ReturnInfo,
    summary_conditions: Sequence[Condition],
    overlapping_positive_returns: Sequence[ReturnInfo],
) -> bool:
    if ret in (overlapping_positive_returns or ()):
        return True
    return self._conditions_imply_with_smt(
        getattr(ret, "conditions", None) or (),
        summary_conditions or (),
    )


def _impl__record_readonly_reduction_return_region_proof(
    self,
    *,
    analysis,
    summary_value: Expression,
    summary_conditions: Sequence[Condition],
    retained_exact_returns: Sequence[ReturnInfo],
    superseded_returns: Sequence[ReturnInfo],
    accumulator_proof: ReductionAccumulatorProof,
    exact_return_witnesses: Sequence[ReadonlyReductionWitness],
    semantic_witnesses: Sequence[ReadonlyReductionWitness],
) -> Optional[Tuple[Any, ...]]:
    if not self.enable_completed_recovery_proofs:
        return None
    proof_key = accumulator_proof.stable_key()
    contract_key = accumulator_proof.readonly_term_sequence_contract_key(
        result_size=max(1, int(getattr(summary_value, "size", 0) or accumulator_proof.result_size))
    )
    if proof_key is None or contract_key is None:
        self._debug(
            "Declined readonly reduction proof: unstable proof/contract key "
            f"(proof_key={'ok' if proof_key is not None else 'missing'}, "
            f"contract_key={'ok' if contract_key is not None else 'missing'})"
        )
        return None
    coverage_key = self._prove_summary_conditions_plus_exact_returns_cover_active_precondition(
        active_preconditions=self._analysis_active_preconditions(analysis),
        summary_conditions=summary_conditions,
        exact_returns=retained_exact_returns,
        parameters=getattr(analysis, "parameters", None),
    )
    if coverage_key is None:
        if self._debug_available():
            # 評価するのは要約に載る先頭数件だけ。件数の上限は
            # ``bounded_items`` でここに書く（消費側の遅延評価に頼らない）。
            retained_condition_ops = [
                summarize_conditions(getattr(ret, "conditions", None) or ())
                for ret in bounded_items(retained_exact_returns or ())
            ]
            summary_ops = [
                getattr(getattr(cond, "expression", None), "operator", None)
                for cond in bounded_items(summary_conditions or ())
            ]
            self._debug(
                "Declined readonly reduction proof: coverage proof unavailable "
                f"(summary_conditions={summarize_conditions(summary_conditions or ())}, "
                f"summary_ops={summarize_values(summary_ops)}, "
                f"retained_exact_returns={len(retained_exact_returns or ())}, "
                f"retained_condition_ops={summarize_values(retained_condition_ops)})"
            )
        return None
    source_key = self._summary_value_source_key(summary_value)
    if source_key is None:
        source_key = ("summary_value", _runtime_expression_signature(summary_value))
    witness_key = (
        "readonly_reduction_accumulator_witness",
        proof_key,
        contract_key,
        tuple(witness.stable_key() for witness in exact_return_witnesses or ()),
        tuple(witness.stable_key() for witness in semantic_witnesses or ()),
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
        "proof_source": "readonly_pointer_reduction_summary",
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
                ("readonly_accumulator_contract", "proved"),
                ("readonly_memory_reads", "modeled"),
            ),
        },
    }
    analysis.completed_recovery_proof_evidence = existing + (evidence,)
    return proof_ref


def _impl__select_readonly_reduction_candidate(
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
                observed_signedness=None,
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
    if (
        len(tied_counter_signedness) > 1
        and declared_signedness is None
    ):
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
    if self._readonly_tied_candidates_have_same_pairwise_contract(tied):
        return min(tied, key=lambda item: item[1])[2]
    return None


def _impl__readonly_tied_candidates_have_same_pairwise_contract(
    self,
    tied_candidates: Sequence[
        Tuple[
            Tuple[int, ...],
            int,
            Tuple[bool, List[Condition], ReductionAccumulatorProof, List[Condition], List[ReturnInfo]],
        ]
    ],
) -> bool:
    if not tied_candidates:
        return False
    first_candidate = tied_candidates[0][2]
    first_counter_signed = bool(first_candidate[0])
    first_conditions = first_candidate[3]
    first_contract = self._readonly_candidate_pairwise_contract_key(first_candidate)
    if first_contract is None:
        return False
    for _score, _index, candidate in tied_candidates[1:]:
        if bool(candidate[0]) != first_counter_signed:
            return False
        if not self._conditions_equivalent_object_centric(first_conditions, candidate[3]):
            return False
        if self._readonly_candidate_pairwise_contract_key(candidate) != first_contract:
            return False
    return True


def _impl__readonly_candidate_pairwise_contract_key(
    self,
    candidate: Tuple[bool, List[Condition], ReductionAccumulatorProof, List[Condition], List[ReturnInfo]],
) -> Optional[Tuple[Any, ...]]:
    proof = candidate[2]
    readonly_ref = proof.lower_to_readonly_reduction_ref()
    if readonly_ref is None:
        return None
    contract_key = readonly_ref.readonly_term_sequence_contract_key(
        result_size=max(1, int(getattr(readonly_ref, "result_size", 0) or 0))
    )
    if contract_key is None:
        return None
    return (
        "readonly_candidate_pairwise_contract",
        contract_key,
        bool(candidate[0]),
    )


def _impl__readonly_reduction_candidate_score(
    self,
    analysis,
    pointer_param: dict,
    count_param: dict,
    candidate: Tuple[bool, List[Condition], ReductionAccumulatorProof, List[Condition], List[ReturnInfo]],
    *,
    declared_signedness: Optional[bool],
    observed_signedness: Optional[bool],
) -> Tuple[int, int, int, int, int, int, int, int]:
    counter_signed, _broad_conditions, proof, positive_conditions, overlapping_returns = candidate
    retained_for_coverage = [
        ret
        for ret in (getattr(analysis, "returns", ()) or ())
        if not self._conditions_overlap_for_analysis_parameters(
            getattr(ret, "conditions", None) or (),
            positive_conditions,
            getattr(analysis, "parameters", None),
        )
    ]
    coverage_score = (
        50
        if self._prove_summary_conditions_plus_exact_returns_cover_active_precondition(
            active_preconditions=self._analysis_active_preconditions(analysis),
            summary_conditions=positive_conditions,
            exact_returns=retained_for_coverage,
            parameters=getattr(analysis, "parameters", None),
        )
        is not None
        else 0
    )
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
    observed_score = 0
    return (
        int(coverage_score),
        int(region_site_score),
        int(return_site_evidence_score),
        int(seed_score),
        int(anchor_score),
        int(contract_score),
        int(observed_score),
        int(declared_score),
    )


def _impl__synthesize_exact_returns_from_readonly_witnesses(
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


def _impl__readonly_witness_terms_form_scalar_prefix(
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


def _impl__readonly_synthetic_positive_return_from_proof(
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


def _impl__readonly_bounded_counter_region_is_covered_by_exact_returns(
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


def _impl__collect_readonly_prefix_accumulator_proofs(
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


def _impl__readonly_reduction_condition_signature(
    self,
    conditions: Sequence[Condition],
) -> tuple:
    return tuple(condition.structural_key() for condition in (conditions or ()))


def _impl__readonly_reduction_return_signature(
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


def _impl__readonly_reduction_normalization_state_key(
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


def _impl__normalize_readonly_reduction_candidate(
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


def _impl__readonly_reduction_summary_expression(
    self,
    pointer_expr: Expression,
    count_expr: Expression,
    reduction_ref: ReadonlyReductionRef,
    *,
    result_size: int,
) -> Optional[Expression]:
    readonly_sum = Expression.intrinsic(
        "READONLY_SUM",
        [pointer_expr, count_expr],
        size=max(1, int(result_size or 0)),
        runtime_ref=reduction_ref,
        opcode=READONLY_SUM_OPCODE,
    )
    reduction_kind = str(getattr(reduction_ref, "reduction_kind", "") or "")
    if reduction_kind != "fp_int2float_sum_average":
        return readonly_sum

    denominator = Expression.unary_op("INT2FLOAT", count_expr)
    denominator.size = max(1, int(result_size or getattr(count_expr, "size", 0) or 0))
    average = Expression.binary_op("FLOAT_DIV", readonly_sum, denominator)
    average.size = max(1, int(result_size or getattr(readonly_sum, "size", 0) or 0))
    return average


def _impl__infer_readonly_pointer_reduction_parameters(
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


def _impl__readonly_pointer_candidate_score(
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


def _impl__readonly_counter_candidate_score(
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


def _impl__readonly_reduction_positive_conditions(
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
    conditions: List[Condition] = []
    if analysis is None or self._parameter_has_pointer_guards(analysis, pointer_param):
        conditions.append(
            Condition(
                Expression.binary_op(
                    "INT_NOTEQUAL",
                    pointer_expr,
                    Expression.constant(0, pointer_expr.size or 8),
                ),
                False,
            )
        )
    conditions.append(
        Condition(
            Expression.binary_op(
                compare_op,
                Expression.constant(lower_bound, count_expr.size or 4),
                count_expr,
            ),
            False,
        ),
    )
    return conditions


def _impl__readonly_reduction_region_returns_with_signedness(
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


def _impl__readonly_reduction_region_returns(
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


def _impl__readonly_region_returns_are_subsumable_by_proof(
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


def _impl__readonly_proof_return_sites_cover_returns(
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


def _impl__readonly_reduction_replaceable_positive_returns(
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


def _impl__readonly_exact_materialized_returns_conflict_with_accumulator_proof(
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


def _impl__readonly_preserved_summary_is_subsumed_by_replacement(
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


def _impl__readonly_unresolved_preserved_return_is_subsumed_by_replacement(
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


def _impl__readonly_reduction_ref_specificity(
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


def _impl__readonly_reduction_ref_from_return(
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


def _impl__readonly_summary_return_should_precede_preserved_return(
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


def _impl__readonly_vectorized_return_region_sequence_is_proven(
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


def _impl__readonly_positive_prefix_is_exactly_covered(
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


def _impl__readonly_positive_return_proves_count_value(
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


def _impl__readonly_region_value_proof_allows_broadened_positive_coverage(
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


def _impl__readonly_positive_return_materializes_count_value(
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


def _impl__readonly_positive_return_matches_accumulator_proof(
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


def _impl__readonly_positive_return_accumulator_anchor_count(
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


def _impl__readonly_materialized_positive_return_matches_accumulator_contract(
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


def _impl__readonly_candidate_counts_from_term_contract(
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


def _impl__readonly_loop_anchor_covers_return_region(
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


def _impl__readonly_return_region_value_is_proven(
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


def _impl__readonly_positive_return_has_materialized_readonly_terms(
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


def _impl__extract_readonly_return_terms_and_bias(
    self,
    analysis,
    pointer_param: dict,
    ret: ReturnInfo,
    accumulator_proof: Optional[ReductionAccumulatorProof],
) -> Optional[Tuple[Tuple[ReadonlyReductionTermRef, ...], int]]:
    fp_exact = self._extract_fp_readonly_exact_return_terms_and_bias(
        analysis,
        pointer_param,
        ret,
        accumulator_proof,
    )
    if fp_exact is not None:
        return fp_exact
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


def _impl__extract_fp_readonly_exact_return_terms_and_bias(
    self,
    analysis,
    pointer_param: dict,
    ret: ReturnInfo,
    accumulator_proof: Optional[ReductionAccumulatorProof],
) -> Optional[Tuple[Tuple[ReadonlyReductionTermRef, ...], int]]:
    if accumulator_proof is None:
        return None
    if str(getattr(accumulator_proof, "reduction_kind", "") or "") != "fp_int2float_div_count_sum":
        return None
    count_name = str(getattr(accumulator_proof, "count_parameter_name", "") or "")
    if not count_name:
        return None
    exact_count = self._exact_counter_value_from_conditions(
        getattr(ret, "conditions", None) or (),
        count_name,
    )
    if exact_count != 1:
        return None
    big_endian = self._program_is_big_endian()
    terms = self._extract_fp_count_one_readonly_terms(
        getattr(ret, "value", None),
        analysis.parameters or (),
        pointer_param,
        count_name=count_name,
        big_endian=big_endian,
    )
    if not terms:
        return None
    terms = tuple(sorted(terms, key=lambda item: (int(item.byte_offset), int(item.access_size))))
    expected = accumulator_proof.full_terms_for_count_value(1)
    if expected is not None and tuple(term.stable_key() for term in terms) != tuple(
        term.stable_key() for term in expected
    ):
        return None
    return terms, 0


def _impl__extract_fp_count_one_readonly_terms(
    self,
    expr: Optional[Expression],
    parameters: Sequence[dict],
    pointer_param: dict,
    *,
    count_name: str,
    big_endian: bool,
) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
    if expr is None:
        return None
    if expr.expr_type == ExpressionType.CONSTANT:
        return () if self._raw_constant_value(expr) == 0 else None
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        if expr.operator in {"INT2FLOAT", "INT_ZEXT", "INT_SEXT", "CAST", "COPY"}:
            return self._extract_fp_count_one_readonly_terms(
                expr.operands[0],
                parameters,
                pointer_param,
                count_name=count_name,
                big_endian=big_endian,
            )
    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        if expr.operator == "FLOAT_ADD":
            left = self._extract_fp_count_one_readonly_terms(
                expr.operands[0],
                parameters,
                pointer_param,
                count_name=count_name,
                big_endian=big_endian,
            )
            right = self._extract_fp_count_one_readonly_terms(
                expr.operands[1],
                parameters,
                pointer_param,
                count_name=count_name,
                big_endian=big_endian,
            )
            if left is None or right is None:
                return None
            return tuple(left) + tuple(right)
        if expr.operator == "FLOAT_DIV":
            if not self._fp_denominator_is_count_parameter(expr.operands[1], count_name):
                return None
            return self._extract_fp_count_one_readonly_terms(
                expr.operands[0],
                parameters,
                pointer_param,
                count_name=count_name,
                big_endian=big_endian,
            )
    descriptor = self._extract_readonly_reduction_term_descriptor(
        expr,
        parameters,
        pointer_param,
        big_endian=big_endian,
    )
    if descriptor is None:
        return None
    return (descriptor,)


def _impl__readonly_exact_count_region_is_fully_covered_by_return(
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
    if full_region.implies_all(ret.conditions or []):
        return True
    residual_conditions = self._readonly_exact_count_return_residual_conditions(
        ret.conditions or [],
        positive_conditions or [],
    )
    return self._counter_singleton_region_covers_return_conditions(
        residual_conditions,
        count_param,
        int(exact_count),
    )


def _impl__readonly_exact_count_return_residual_conditions(
    self,
    return_conditions: Sequence[Condition],
    positive_conditions: Sequence[Condition],
) -> List[Condition]:
    positive_constraint_set = ConditionConstraintSet.from_conditions(positive_conditions or [])
    residual: List[Condition] = []
    for condition in return_conditions or []:
        if positive_constraint_set.implies_condition(condition):
            continue
        solver_unsat = ConditionSMTOracle.conjunction_is_unsat(
            list(positive_conditions or []) + [condition.negate()]
        )
        if solver_unsat is True:
            continue
        residual.append(condition)
    return residual


def _impl__readonly_residual_conditions_are_counter_only(
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


def _impl__readonly_region_is_covered_by_returns(
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


def _impl__readonly_subtract_condition_regions(
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


def _impl__readonly_subtract_condition_region(
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


def _impl__readonly_return_has_only_counter_guards_beyond_conditions(
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


def _impl__readonly_reduction_count_compare_op(
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


def _impl__readonly_reduction_counter_is_signed(
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


def _impl__readonly_reduction_counter_signedness_evidence(
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


def _impl__readonly_reduction_condition_signedness(
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


def _impl__readonly_reduction_condition_references_only_counter(
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


def _impl__detect_readonly_sum_accumulator_proof(
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


def _impl__collect_readonly_sum_accumulator_proofs(
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
    elif not matches:
        self._debug(
            "Declined readonly reduction summary: no accumulator PHI matched "
            f"(pointer_phis={len(pointer_phis)}, index_phis={len(index_phis)})"
        )
    return matches


def _impl__detect_vectorized_readonly_prefix_sum_accumulator_proof(
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


def _impl__readonly_reduction_result_size(
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


def _impl__readonly_round_down_candidates(
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


def _impl__readonly_round_down_candidate_from_op(
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


def _impl__readonly_round_down_mask_candidate(
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


def _impl__readonly_round_down_multiply_candidate(
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


def _impl__readonly_round_down_shift_candidate(
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


def _impl__build_readonly_reduction_semantic_witnesses(
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


def _impl__extract_readonly_reduction_exact_witnesses(
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


def _impl__resolve_readonly_exact_witness_terms(
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


def _impl__self_consistent_readonly_exact_witness_terms(
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


def _impl__readonly_exact_positive_return_is_absorbable(
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


def _impl__order_readonly_exact_positive_returns(
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


def _impl__readonly_exact_positive_return_selection_key(
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


def _impl__readonly_exact_positive_return_prefix_score(
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


def _impl__canonicalize_readonly_exact_witness_terms(
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


def _impl__readonly_term_multiset_key(
    self,
    terms: Sequence[ReadonlyReductionTermRef],
) -> Tuple[object, ...]:
    return tuple(sorted((term.stable_key() for term in terms or ()), key=repr))


def _impl__build_readonly_reduction_expression_from_terms(
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


def _impl__readonly_reduction_term_expression(
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


def _impl__infer_exact_count_from_readonly_terms(
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


def _impl__readonly_loop_trip_count_for_count_value(
    self,
    accumulator_proof: Optional[ReductionAccumulatorProof],
    count_value: int,
) -> Optional[int]:
    if count_value <= 0:
        return None
    if accumulator_proof is None:
        return int(count_value)
    return accumulator_proof.trip_count_for_count_value(count_value)


def _impl__synthesize_linear_readonly_reduction_witnesses(
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


def _impl__extract_readonly_reduction_terms(
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


def _impl__extract_readonly_reduction_terms_and_bias(
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


def _impl__normalize_readonly_constant_bias(self, value: int, result_size: int) -> int:
    bits = max(1, int(result_size or 0)) * 8
    return int(value) % (1 << bits)


def _impl__extract_readonly_reduction_term_descriptor(
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


def _impl__extract_readonly_accumulator_seed_terms(
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


def _impl__varnode_is_int_to_float_readonly_load(self, varnode) -> bool:
    varnode = self._follow_readonly_load_addend_passthrough(varnode)
    def_op = getattr(varnode, "getDef", lambda: None)()
    if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "INT2FLOAT":
        return False
    if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 1:
        return False
    current = def_op.getInput(0)
    seen = set()
    passthrough = {"COPY", "CAST", "INT_ZEXT", "INT_SEXT", "SUBPIECE"}
    while current is not None:
        current_key = self._varnode_cache_key(current)
        if current_key in seen:
            return False
        seen.add(current_key)
        input_def = getattr(current, "getDef", lambda: None)()
        mnemonic = getattr(input_def, "getMnemonic", lambda: None)() if input_def is not None else None
        if mnemonic == "LOAD":
            return True
        if mnemonic not in passthrough or int(getattr(input_def, "getNumInputs", lambda: 0)() or 0) < 1:
            return False
        current = input_def.getInput(0)
    return False


def _impl__readonly_float_addend_reduction_kind(
    self,
    varnode,
    count_param: Optional[dict],
) -> Optional[str]:
    current = self._follow_readonly_load_addend_passthrough(varnode)
    def_op = getattr(current, "getDef", lambda: None)()
    mnemonic = getattr(def_op, "getMnemonic", lambda: None)() if def_op is not None else None
    if mnemonic == "INT2FLOAT" and self._varnode_is_int_to_float_readonly_load(current):
        return "fp_int2float_sum"
    if mnemonic == "FLOAT_DIV":
        if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
            return None
        numerator = def_op.getInput(0)
        denominator = def_op.getInput(1)
        if not self._varnode_is_int_to_float_readonly_load(numerator):
            return None
        if not self._varnode_is_int_to_float_parameter(denominator, count_param):
            return None
        return "fp_int2float_div_count_sum"
    return None


def _impl__readonly_seed_terms_are_materialized_pre_loop(
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


def _impl__expected_readonly_prefix_seed_terms(
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


def _impl__follow_readonly_load_addend_passthrough(self, varnode):
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


def _impl__readonly_load_progression_term_counter(
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


def _impl__adjust_readonly_load_signature_access(
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
