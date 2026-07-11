"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.recurrence_summary``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    Condition,
    ConditionConstraintSet,
    ConditionSMTOracle,
    ConditionSimplifier,
    Counter,
    Expression,
    ExpressionType,
    ReadonlyReductionTermRef,
    ReadonlyReductionWitness,
    ReadonlyRoundedCountCandidate,
    ReductionAccumulatorProof,
    _expressions_equivalent_under_conditions,
    _reduce_expression_under_conditions,
    canonicalize_location,
    expression_smt_bit_width,
    get_declared_type_signedness,
)

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

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
