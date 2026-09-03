"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.equivalence.strategies.pairwise``."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Sequence, Tuple
from ._shared import (
    Condition,
    ConditionSMTOracle,
    ConditionSimplifier,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    Mapping,
    ParameterInfo,
    ReadonlyReductionRef,
    ReadonlyReductionTermRef,
    ReturnCase,
    UnknownReasonId,
    _ExactReadonlyReductionProof,
    _ReadonlyLoopSummaryProofAdapter,
    _RuntimeShortcutDecision,
    build_unknown_recovery_actions,
    expression_smt_bit_width,
    parameter_identity_key_from_expression,
)

def _impl__cases_have_equivalent_runtime_reductions(
    self,
    case1: ReturnCase,
    case2: ReturnCase,
    *,
    semantic_parameter_sources: Sequence[ParameterInfo] = (),
) -> bool:
    if self._intrinsic_runtime_values_equivalent(
        case1.value_expr,
        case2.value_expr,
        left_case=case1,
        right_case=case2,
        semantic_parameter_sources=semantic_parameter_sources,
    ):
        return True
    return self._cases_have_equivalent_readonly_reduction_proof(case1, case2)

def _impl__cases_have_equivalent_readonly_reduction_proof(
    self,
    case1: ReturnCase,
    case2: ReturnCase,
) -> bool:
    return (
        self._exact_value_matches_readonly_reduction_proof(case1, case2)
        or self._exact_value_matches_readonly_reduction_proof(case2, case1)
    )

def _impl__exact_value_matches_readonly_reduction_proof(
    self,
    exact_case: ReturnCase,
    summary_case: ReturnCase,
) -> bool:
    return self._prove_exact_load_sum_matches_readonly_reduction(exact_case, summary_case) is not None

def _impl__prove_exact_load_sum_matches_readonly_reduction(
    self,
    exact_case: ReturnCase,
    summary_case: ReturnCase,
) -> Optional[_ExactReadonlyReductionProof]:
    summary_expr = summary_case.value_expr
    summary_ref = getattr(summary_expr, "runtime_ref", None)
    if not isinstance(summary_ref, ReadonlyReductionRef):
        return None
    accumulator_proof = getattr(summary_ref, "accumulator_proof", None)
    if accumulator_proof is None:
        return self._prove_exact_load_sum_matches_readonly_loop_summary(
            exact_case,
            summary_case,
            summary_ref,
        )
    proof_result_size = max(1, int(getattr(accumulator_proof, "result_size", 0) or 0))
    if max(1, int(getattr(summary_ref, "result_size", 0) or 0)) != proof_result_size:
        return None
    if self._normalize_constant_bias(
        int(getattr(summary_ref, "constant_bias", 0) or 0),
        proof_result_size,
    ) != self._normalize_constant_bias(
        int(getattr(accumulator_proof, "constant_bias", 0) or 0),
        proof_result_size,
    ):
        return None
    exact_bits = int(expression_smt_bit_width(exact_case.value_expr) or 0)
    if exact_bits <= 0 or exact_bits % 8 != 0:
        return None
    result_size = exact_bits // 8
    if result_size > proof_result_size:
        return None
    contract_key_fn = getattr(accumulator_proof, "readonly_term_sequence_contract_key", None)
    if not callable(contract_key_fn):
        return None
    try:
        contract_key = contract_key_fn(result_size=result_size)
    except (AttributeError, TypeError, ValueError):
        contract_key = None
    if contract_key is None:
        return None
    extracted = self._extract_readonly_reduction_terms_and_bias_from_expression(
        exact_case.value_expr,
        exact_case.parameters,
        getattr(accumulator_proof, "pointer_base_ref", None),
        program_is_big_endian=getattr(exact_case, "program_is_big_endian", None),
    )
    if extracted is None and str(getattr(accumulator_proof, "reduction_kind", "") or "") == "fp_int2float_div_count_sum":
        extracted = self._extract_fp_count_one_readonly_terms_and_bias_from_expression(
            exact_case.value_expr,
            exact_case.parameters,
            getattr(accumulator_proof, "pointer_base_ref", None),
            accumulator_proof=accumulator_proof,
            program_is_big_endian=getattr(exact_case, "program_is_big_endian", None),
        )
    if extracted is None:
        return None
    extracted_terms, extracted_bias = extracted
    if self._normalize_constant_bias(extracted_bias, result_size) != self._normalize_constant_bias(
        int(getattr(accumulator_proof, "constant_bias", 0) or 0),
        result_size,
    ):
        return None
    extracted_key = tuple(term.stable_key() for term in extracted_terms)
    exact_witnesses = tuple(getattr(accumulator_proof, "exact_return_witnesses", ()) or ())
    for witness in exact_witnesses:
        if extracted_key != tuple(term.stable_key() for term in getattr(witness, "terms", ()) or ()):
            continue
        if self._cases_admit_reduction_count(
            exact_case,
            summary_case,
            accumulator_proof,
            int(getattr(witness, "exact_count", 0) or 0),
        ):
            count_value = int(getattr(witness, "exact_count", 0) or 0)
            return _ExactReadonlyReductionProof(
                exact_terms=tuple(extracted_terms),
                constant_bias=self._normalize_constant_bias(extracted_bias, result_size),
                result_size=result_size,
                count_value=count_value,
                expected_terms=tuple(getattr(witness, "terms", ()) or ()),
                evidence="exact_return_witness",
                count_values=(count_value,),
            )
    return self._exact_terms_match_reduction_proof_under_case_conditions(
        exact_case,
        summary_case,
        accumulator_proof,
        extracted_key,
        exact_terms=tuple(extracted_terms),
        constant_bias=self._normalize_constant_bias(extracted_bias, result_size),
        result_size=result_size,
    )

def _impl__extract_fp_count_one_readonly_terms_and_bias_from_expression(
    self,
    expr: Optional[Expression],
    parameters: Sequence[Dict[str, Any]],
    pointer_base_ref,
    *,
    accumulator_proof,
    program_is_big_endian: Optional[bool] = None,
) -> Optional[tuple[tuple[ReadonlyReductionTermRef, ...], int]]:
    if expr is None or pointer_base_ref is None or accumulator_proof is None:
        return None
    terms = self._extract_fp_count_one_readonly_terms_from_expression(
        expr,
        parameters,
        pointer_base_ref,
        accumulator_proof=accumulator_proof,
        program_is_big_endian=program_is_big_endian,
    )
    if terms is None:
        return None
    normalized_terms = tuple(sorted(terms, key=lambda item: (int(item.byte_offset), int(item.access_size))))
    if not normalized_terms:
        return None
    return normalized_terms, 0

def _impl__extract_fp_count_one_readonly_terms_from_expression(
    self,
    expr: Optional[Expression],
    parameters: Sequence[Dict[str, Any]],
    pointer_base_ref,
    *,
    accumulator_proof,
    program_is_big_endian: Optional[bool] = None,
) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
    if expr is None:
        return None
    if getattr(expr, "expr_type", None) == ExpressionType.CONSTANT:
        return () if self._raw_constant_value(expr) == 0 else None
    if getattr(expr, "expr_type", None) == ExpressionType.UNARY_OP and getattr(expr, "operands", None):
        if getattr(expr, "operator", None) in {"INT2FLOAT", "INT_ZEXT", "INT_SEXT", "CAST", "COPY"}:
            return self._extract_fp_count_one_readonly_terms_from_expression(
                expr.operands[0],
                parameters,
                pointer_base_ref,
                accumulator_proof=accumulator_proof,
                program_is_big_endian=program_is_big_endian,
            )
    if getattr(expr, "expr_type", None) == ExpressionType.BINARY_OP and len(getattr(expr, "operands", ()) or ()) == 2:
        if getattr(expr, "operator", None) == "FLOAT_ADD":
            left = self._extract_fp_count_one_readonly_terms_from_expression(
                expr.operands[0],
                parameters,
                pointer_base_ref,
                accumulator_proof=accumulator_proof,
                program_is_big_endian=program_is_big_endian,
            )
            right = self._extract_fp_count_one_readonly_terms_from_expression(
                expr.operands[1],
                parameters,
                pointer_base_ref,
                accumulator_proof=accumulator_proof,
                program_is_big_endian=program_is_big_endian,
            )
            if left is None or right is None:
                return None
            return tuple(left) + tuple(right)
        if getattr(expr, "operator", None) == "FLOAT_DIV":
            if not self._fp_denominator_matches_reduction_count(
                expr.operands[1],
                parameters,
                accumulator_proof,
            ):
                return None
            return self._extract_fp_count_one_readonly_terms_from_expression(
                expr.operands[0],
                parameters,
                pointer_base_ref,
                accumulator_proof=accumulator_proof,
                program_is_big_endian=program_is_big_endian,
            )
    descriptor = self._extract_readonly_reduction_term_descriptor(
        expr,
        parameters,
        pointer_base_ref,
        program_is_big_endian=program_is_big_endian,
    )
    if descriptor is None:
        return None
    return (descriptor,)

def _impl__fp_denominator_matches_reduction_count(
    self,
    expr: Optional[Expression],
    parameters: Sequence[Dict[str, Any]],
    accumulator_proof,
) -> bool:
    if expr is None or accumulator_proof is None:
        return False
    if getattr(expr, "expr_type", None) == ExpressionType.UNARY_OP and getattr(expr, "operands", None):
        if getattr(expr, "operator", None) in {"INT2FLOAT", "INT_ZEXT", "INT_SEXT", "CAST", "COPY"}:
            return self._fp_denominator_matches_reduction_count(
                expr.operands[0],
                parameters,
                accumulator_proof,
            )
    if getattr(expr, "expr_type", None) == ExpressionType.BINARY_OP and len(getattr(expr, "operands", ()) or ()) == 2:
        if getattr(expr, "operator", None) == "SUBPIECE":
            return self._fp_denominator_matches_reduction_count(
                expr.operands[0],
                parameters,
                accumulator_proof,
            )
    if getattr(expr, "expr_type", None) != ExpressionType.PARAMETER:
        return False
    expr_storage = self._parameter_expression_storage_identity_key(expr)
    expr_index = self._parameter_expression_index_identity_key(expr)
    proof_storage = self._reduction_count_storage_identity_key(accumulator_proof)
    proof_index = self._reduction_count_index_identity_key(accumulator_proof)
    expr_identity = parameter_identity_key_from_expression(expr)
    proof_identities = self._reduction_count_identity_keys(accumulator_proof)
    if self._fp_denominator_count_identity_matches(
        expr_storage,
        expr_index,
        proof_storage,
        proof_index,
    ):
        return True
    if expr_identity is not None and proof_identities:
        return expr_identity is not None and tuple(expr_identity) in proof_identities
    expr_has_identity = expr_storage is not None or expr_index is not None or expr_identity is not None
    if expr_has_identity:
        return False
    return self._fp_denominator_name_fallback_matches_unique_count(
        expr,
        parameters,
        accumulator_proof,
    )

def _impl__prove_exact_load_sum_matches_readonly_loop_summary(
    self,
    exact_case: ReturnCase,
    summary_case: ReturnCase,
    summary_ref: ReadonlyReductionRef,
) -> Optional[_ExactReadonlyReductionProof]:
    loop_summary = getattr(summary_ref, "loop_summary", None)
    if loop_summary is None:
        return None
    requires_effect_proof = getattr(loop_summary, "requires_effect_proof", None)
    if callable(requires_effect_proof) and requires_effect_proof():
        return None
    requires_path_proof = getattr(loop_summary, "requires_path_proof", None)
    if callable(requires_path_proof) and requires_path_proof():
        return None
    result_size = max(1, int(getattr(summary_ref, "result_size", 0) or 0))
    term_descriptor = getattr(loop_summary, "term_descriptor", None)
    if term_descriptor is None:
        return None
    if max(1, int(getattr(term_descriptor, "result_size", 0) or result_size)) != result_size:
        return None
    if self._normalize_constant_bias(
        int(getattr(summary_ref, "constant_bias", 0) or 0),
        result_size,
    ) != self._normalize_constant_bias(
        int(getattr(loop_summary, "constant_bias", 0) or 0),
        result_size,
    ):
        return None
    extracted = self._extract_readonly_reduction_terms_and_bias_from_expression(
        exact_case.value_expr,
        exact_case.parameters,
        getattr(summary_ref, "pointer_base_ref", None),
        program_is_big_endian=getattr(exact_case, "program_is_big_endian", None),
    )
    if extracted is None:
        return None
    extracted_terms, extracted_bias = extracted
    exact_bits = int(expression_smt_bit_width(exact_case.value_expr) or 0)
    if exact_bits != result_size * 8:
        return None
    if self._normalize_constant_bias(extracted_bias, result_size) != self._normalize_constant_bias(
        int(getattr(loop_summary, "constant_bias", 0) or 0),
        result_size,
    ):
        return None
    adapter = _ReadonlyLoopSummaryProofAdapter(
        pointer_base_ref=getattr(summary_ref, "pointer_base_ref", None),
        count_parameter_name=str(getattr(summary_ref, "count_parameter_name", None) or "count"),
        count_parameter_index=getattr(summary_ref, "count_parameter_index", None),
        count_parameter_storage_identity_key=getattr(
            summary_ref,
            "count_parameter_storage_identity_key",
            None,
        ),
        limit_expr=getattr(loop_summary, "limit_expr", None),
        result_size=result_size,
        loop_summary=loop_summary,
    )
    extracted_key = tuple(term.stable_key() for term in extracted_terms)
    max_count = self._exact_reduction_count_search_bound(adapter, len(extracted_terms))
    for count_value in range(1, max_count + 1):
        expected_terms = adapter.full_terms_for_count_value(count_value)
        if expected_terms is None:
            continue
        if extracted_key != tuple(term.stable_key() for term in expected_terms):
            continue
        if self._cases_admit_reduction_count(
            exact_case,
            summary_case,
            adapter,
            count_value,
        ):
            return _ExactReadonlyReductionProof(
                exact_terms=tuple(extracted_terms),
                constant_bias=self._normalize_constant_bias(extracted_bias, result_size),
                result_size=result_size,
                count_value=int(count_value),
                expected_terms=tuple(expected_terms),
                evidence="loop_summary_materialized_terms",
                count_values=(int(count_value),),
            )
    return None

def _impl__prove_exact_load_sum_covers_readonly_loop_summary(
    self,
    exact_case: ReturnCase,
    summary_case: ReturnCase,
    summary_ref: ReadonlyReductionRef,
) -> Optional[Tuple[_ExactReadonlyReductionProof, _ReadonlyLoopSummaryProofAdapter]]:
    loop_summary = getattr(summary_ref, "loop_summary", None)
    if loop_summary is None:
        return None
    requires_effect_proof = getattr(loop_summary, "requires_effect_proof", None)
    if callable(requires_effect_proof) and requires_effect_proof():
        return None
    requires_path_proof = getattr(loop_summary, "requires_path_proof", None)
    if callable(requires_path_proof) and requires_path_proof():
        return None
    result_size = max(1, int(getattr(summary_ref, "result_size", 0) or 0))
    term_descriptor = getattr(loop_summary, "term_descriptor", None)
    if term_descriptor is None:
        return None
    if max(1, int(getattr(term_descriptor, "result_size", 0) or result_size)) != result_size:
        return None
    if self._normalize_constant_bias(
        int(getattr(summary_ref, "constant_bias", 0) or 0),
        result_size,
    ) != self._normalize_constant_bias(
        int(getattr(loop_summary, "constant_bias", 0) or 0),
        result_size,
    ):
        return None
    extracted = self._extract_readonly_reduction_terms_and_bias_from_expression(
        exact_case.value_expr,
        exact_case.parameters,
        getattr(summary_ref, "pointer_base_ref", None),
        program_is_big_endian=getattr(exact_case, "program_is_big_endian", None),
    )
    if extracted is None:
        return None
    extracted_terms, extracted_bias = extracted
    exact_bits = int(expression_smt_bit_width(exact_case.value_expr) or 0)
    if exact_bits != result_size * 8:
        return None
    if self._normalize_constant_bias(extracted_bias, result_size) != self._normalize_constant_bias(
        int(getattr(loop_summary, "constant_bias", 0) or 0),
        result_size,
    ):
        return None
    adapter = _ReadonlyLoopSummaryProofAdapter(
        pointer_base_ref=getattr(summary_ref, "pointer_base_ref", None),
        count_parameter_name=str(getattr(summary_ref, "count_parameter_name", None) or "count"),
        count_parameter_index=getattr(summary_ref, "count_parameter_index", None),
        count_parameter_storage_identity_key=getattr(
            summary_ref,
            "count_parameter_storage_identity_key",
            None,
        ),
        limit_expr=getattr(loop_summary, "limit_expr", None),
        result_size=result_size,
        loop_summary=loop_summary,
    )
    extracted_key = tuple(term.stable_key() for term in extracted_terms)
    max_count = self._exact_reduction_count_search_bound(adapter, len(extracted_terms))
    matching_count_values: List[int] = []
    first_expected_terms: Optional[Tuple[ReadonlyReductionTermRef, ...]] = None
    for count_value in range(1, max_count + 1):
        expected_terms = adapter.full_terms_for_count_value(count_value)
        if expected_terms is None:
            continue
        if extracted_key != tuple(term.stable_key() for term in expected_terms):
            continue
        matching_count_values.append(int(count_value))
        if first_expected_terms is None:
            first_expected_terms = tuple(expected_terms)
    if matching_count_values and first_expected_terms is not None:
        return (
            _ExactReadonlyReductionProof(
                exact_terms=tuple(extracted_terms),
                constant_bias=self._normalize_constant_bias(extracted_bias, result_size),
                result_size=result_size,
                count_value=int(matching_count_values[0]),
                expected_terms=first_expected_terms,
                evidence="method_b_covering_materialized_terms",
                count_values=tuple(matching_count_values),
            ),
            adapter,
        )
    return None

def _impl__exact_terms_match_reduction_proof_under_case_conditions(
    self,
    exact_case: ReturnCase,
    summary_case: ReturnCase,
    accumulator_proof,
    extracted_key: tuple,
    *,
    exact_terms: tuple[ReadonlyReductionTermRef, ...],
    constant_bias: int,
    result_size: int,
) -> Optional[_ExactReadonlyReductionProof]:
    max_count = self._exact_reduction_count_search_bound(accumulator_proof, len(exact_terms))
    for count_value in range(1, max_count + 1):
        expected_terms_fn = getattr(accumulator_proof, "full_terms_for_count_value", None)
        if not callable(expected_terms_fn):
            return None
        expected_terms = expected_terms_fn(count_value)
        if expected_terms is None:
            continue
        if extracted_key != tuple(term.stable_key() for term in expected_terms):
            continue
        if self._cases_admit_reduction_count(
            exact_case,
            summary_case,
            accumulator_proof,
            count_value,
        ):
            return _ExactReadonlyReductionProof(
                exact_terms=tuple(exact_terms),
                constant_bias=int(constant_bias),
                result_size=int(result_size),
                count_value=int(count_value),
                expected_terms=tuple(expected_terms),
                evidence="materialized_full_terms",
                count_values=(int(count_value),),
            )
    return None

def _impl__exact_reduction_count_search_bound(self, accumulator_proof, exact_term_count: int) -> int:
    witness_counts = [
        int(getattr(witness, "exact_count", 0) or 0)
        for witness in tuple(getattr(accumulator_proof, "loop_body_witnesses", ()) or ())
    ] + [
        int(getattr(witness, "exact_count", 0) or 0)
        for witness in tuple(getattr(accumulator_proof, "exact_return_witnesses", ()) or ())
    ]
    start_index = max(0, int(getattr(accumulator_proof, "start_index", 0) or 0))
    index_step = max(1, int(getattr(accumulator_proof, "index_step", 1) or 1))
    seed_count = max(
        len(tuple(getattr(accumulator_proof, "seed_terms", ()) or ())),
        max(0, int(getattr(accumulator_proof, "seed_term_count", 0) or 0)),
    )
    term_budget = max(1, int(exact_term_count or 0) + seed_count + 1)
    materialization_bound = start_index + term_budget * index_step + 1
    return max(1, materialization_bound, *witness_counts)

def _impl__case_pair_readonly_contract_result_size(
    self,
    left_case: Optional[ReturnCase],
    right_case: Optional[ReturnCase],
) -> Optional[int]:
    common_size = self._case_pair_comparison_result_size(left_case, right_case)
    if common_size is not None:
        return common_size
    left_bits = self._case_comparison_bit_width(left_case)
    right_bits = self._case_comparison_bit_width(right_case)
    if (
        left_bits is None
        or right_bits is None
        or left_bits <= 0
        or right_bits <= 0
        or left_bits % 8 != 0
        or right_bits % 8 != 0
    ):
        return None
    left_ref = getattr(getattr(left_case, "value_expr", None), "runtime_ref", None)
    right_ref = getattr(getattr(right_case, "value_expr", None), "runtime_ref", None)
    if not isinstance(left_ref, ReadonlyReductionRef) or not isinstance(right_ref, ReadonlyReductionRef):
        return None
    narrow_size = min(int(left_bits), int(right_bits)) // 8
    if narrow_size <= 0:
        return None
    if (
        self._readonly_reduction_term_sequence_contract_key(left_ref, result_size=narrow_size) is None
        or self._readonly_reduction_term_sequence_contract_key(right_ref, result_size=narrow_size) is None
    ):
        return None
    return narrow_size

def _impl__readonly_contract_pairwise_extra_assertions(
    self,
    left_case: ReturnCase,
    right_case: ReturnCase,
    left_param_replace_fn,
    right_param_replace_fn,
) -> Tuple[str, ...]:
    result_size = self._case_pair_readonly_contract_result_size(left_case, right_case)
    if result_size is None:
        return ()
    left_ref = getattr(getattr(left_case, "value_expr", None), "runtime_ref", None)
    right_ref = getattr(getattr(right_case, "value_expr", None), "runtime_ref", None)
    if not isinstance(left_ref, ReadonlyReductionRef) or not isinstance(right_ref, ReadonlyReductionRef):
        return ()
    decision = self._runtime_loop_contract_shortcut_decision(
        left_ref,
        right_ref,
        result_size=result_size,
    )
    if not decision.equivalent:
        return ()
    if decision.requires_guard_equivalence and not self._case_pair_has_runtime_guard_coverage_or_equivalence(
        left_case,
        right_case,
    ):
        return ()
    target_bits = int(result_size) * 8
    left_value = left_case.get_value_smt(
        left_param_replace_fn,
        target_bits=target_bits,
        use_sign_extension=left_case.should_sign_extend_value(),
    )
    right_value = right_case.get_value_smt(
        right_param_replace_fn,
        target_bits=target_bits,
        use_sign_extension=right_case.should_sign_extend_value(),
    )
    if not left_value or not right_value:
        return ()
    return (
        "; readonly reduction contract equality at proven narrow return surface",
        f"(assert (= {left_value} {right_value}))",
    )

def _impl__readonly_reduction_contract_shortcut_decision(
    self,
    left_ref,
    right_ref,
    *,
    requires_guard_equivalence: bool,
    result_size: Optional[int] = None,
) -> _RuntimeShortcutDecision:
    if not isinstance(left_ref, ReadonlyReductionRef) or not isinstance(right_ref, ReadonlyReductionRef):
        return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="readonly_contract_type_mismatch")
    if getattr(left_ref, "loop_summary", None) is None or getattr(right_ref, "loop_summary", None) is None:
        return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="readonly_contract_missing_loop")
    left_loop_summary = getattr(left_ref, "loop_summary", None)
    right_loop_summary = getattr(right_ref, "loop_summary", None)
    left_profile = getattr(left_loop_summary, "side_effect_profile", None)
    right_profile = getattr(right_loop_summary, "side_effect_profile", None)
    if left_profile is None or right_profile is None:
        return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="readonly_contract_missing_effect_profile")
    if bool(getattr(left_loop_summary, "requires_effect_proof", lambda: True)()) or bool(
        getattr(right_loop_summary, "requires_effect_proof", lambda: True)()
    ):
        return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="readonly_contract_effects_unproven")

    left_base_key = getattr(getattr(left_ref, "pointer_base_ref", None), "semantic_key", lambda: None)()
    right_base_key = getattr(getattr(right_ref, "pointer_base_ref", None), "semantic_key", lambda: None)()
    effective_result_size = self._readonly_contract_effective_result_size(
        left_ref,
        right_ref,
        result_size=result_size,
    )
    if effective_result_size is None:
        return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="readonly_contract_result_width_mismatch")
    if (
        getattr(left_ref, "reduction_kind", None) != getattr(right_ref, "reduction_kind", None)
        or left_base_key is None
        or right_base_key is None
        or left_base_key != right_base_key
        or not self._readonly_contract_count_identities_compatible(left_ref, right_ref)
        or self._normalize_constant_bias(int(getattr(left_ref, "constant_bias", 0) or 0), effective_result_size)
        != self._normalize_constant_bias(int(getattr(right_ref, "constant_bias", 0) or 0), effective_result_size)
    ):
        if self.debug:
            print(
                "[PairwiseStrategy] readonly contract surface mismatch: "
                f"left_kind={getattr(left_ref, 'reduction_kind', None)}, "
                f"right_kind={getattr(right_ref, 'reduction_kind', None)}, "
                f"left_base={left_base_key}, right_base={right_base_key}, "
                f"left_count_identities={tuple(sorted(self._readonly_count_identity_keys(left_ref), key=repr))}, "
                f"right_count_identities={tuple(sorted(self._readonly_count_identity_keys(right_ref), key=repr))}, "
                f"count_compatible={self._readonly_contract_count_identities_compatible(left_ref, right_ref)}, "
                f"left_bias={self._normalize_constant_bias(int(getattr(left_ref, 'constant_bias', 0) or 0), effective_result_size)}, "
                f"right_bias={self._normalize_constant_bias(int(getattr(right_ref, 'constant_bias', 0) or 0), effective_result_size)}"
            )
        return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="readonly_contract_mismatch")
    left_semantic_key = self._readonly_reduction_term_sequence_contract_key(
        left_ref,
        result_size=effective_result_size,
    )
    right_semantic_key = self._readonly_reduction_term_sequence_contract_key(
        right_ref,
        result_size=effective_result_size,
    )
    if left_semantic_key is None or right_semantic_key is None:
        return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="readonly_contract_missing_term_sequence")
    if not self._readonly_reduction_contract_keys_compatible(
        left_semantic_key,
        right_semantic_key,
        left_ref,
        right_ref,
    ):
        return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="readonly_contract_term_sequence_mismatch")
    return _RuntimeShortcutDecision(True, requires_guard_equivalence, reason="readonly_reduction_contract")

def _impl__readonly_contract_effective_result_size(
    self,
    left_ref: ReadonlyReductionRef,
    right_ref: ReadonlyReductionRef,
    *,
    result_size: Optional[int],
) -> Optional[int]:
    try:
        left_result_size = max(1, int(getattr(left_ref, "result_size", 0) or 0))
        right_result_size = max(1, int(getattr(right_ref, "result_size", 0) or 0))
    except (TypeError, ValueError):
        return None
    if result_size is None:
        return left_result_size if left_result_size == right_result_size else None
    try:
        target_result_size = max(1, int(result_size))
    except (TypeError, ValueError):
        return None
    if target_result_size > left_result_size or target_result_size > right_result_size:
        return None
    return target_result_size

def _impl__readonly_reduction_term_sequence_contract_key(
    self,
    readonly_ref: ReadonlyReductionRef,
    *,
    result_size: Optional[int] = None,
) -> Optional[tuple]:
    contract_key_fn = getattr(readonly_ref, "readonly_term_sequence_contract_key", None)
    if callable(contract_key_fn):
        try:
            contract_key = contract_key_fn(result_size=result_size)
        except (AttributeError, TypeError, ValueError):
            contract_key = None
        if contract_key is not None:
            return contract_key
    accumulator_proof = getattr(readonly_ref, "accumulator_proof", None)
    if accumulator_proof is not None:
        proof_key_fn = getattr(accumulator_proof, "readonly_term_sequence_contract_key", None)
        if callable(proof_key_fn):
            try:
                proof_key = proof_key_fn(result_size=result_size)
            except (AttributeError, TypeError, ValueError):
                proof_key = None
            if proof_key is not None:
                return proof_key
    if result_size is not None:
        try:
            if max(1, int(result_size)) != max(1, int(getattr(readonly_ref, "result_size", 0) or 0)):
                return None
        except (TypeError, ValueError):
            return None
    loop_summary = getattr(readonly_ref, "loop_summary", None)
    loop_key_fn = getattr(loop_summary, "pairwise_semantic_key", None)
    if callable(loop_key_fn):
        try:
            loop_key = loop_key_fn()
        except (AttributeError, TypeError, ValueError):
            loop_key = None
        if loop_key is not None:
            return loop_key
    semantic_key_fn = getattr(readonly_ref, "semantic_key", None)
    if callable(semantic_key_fn):
        try:
            return semantic_key_fn()
        except (AttributeError, TypeError, ValueError):
            return None
    return None

def _impl__readonly_reduction_contract_keys_compatible(
    self,
    left_key: tuple,
    right_key: tuple,
    left_ref: ReadonlyReductionRef,
    right_ref: ReadonlyReductionRef,
) -> bool:
    if left_key == right_key:
        return True
    if (
        not isinstance(left_key, tuple)
        or not isinstance(right_key, tuple)
        or len(left_key) != len(right_key)
        or len(left_key) < 5
        or left_key[0] != "readonly_reduction_term_sequence_contract"
        or right_key[0] != "readonly_reduction_term_sequence_contract"
    ):
        return False
    if left_key[:3] != right_key[:3] or left_key[5:] != right_key[5:]:
        return False
    if not self._readonly_contract_count_identities_compatible(left_ref, right_ref):
        return False
    if not self._readonly_contract_limit_keys_compatible(left_key[4], right_key[4], left_ref, right_ref):
        return False
    return tuple(left_key[3]) in self._readonly_count_identity_keys(left_ref) and tuple(
        right_key[3]
    ) in self._readonly_count_identity_keys(right_ref)

def _impl__readonly_contract_limit_keys_compatible(
    self,
    left_limit_key: tuple,
    right_limit_key: tuple,
    left_ref: ReadonlyReductionRef,
    right_ref: ReadonlyReductionRef,
) -> bool:
    if left_limit_key == right_limit_key:
        return True
    left_limit = tuple(left_limit_key or ())
    right_limit = tuple(right_limit_key or ())
    if self._loop_limit_storage_key_is_legacy_index_compatible(left_limit, right_limit, left_ref, right_ref):
        return True
    if self._loop_limit_storage_key_is_legacy_index_compatible(right_limit, left_limit, right_ref, left_ref):
        return True
    return False

def _impl__readonly_projection_contract_limit_keys_compatible(
    self,
    left_limit_key: tuple,
    right_limit_key: tuple,
    left_ref: ReadonlyReductionRef,
    right_ref: ReadonlyReductionRef,
) -> bool:
    if self._readonly_contract_limit_keys_compatible(left_limit_key, right_limit_key, left_ref, right_ref):
        return True
    left_limit = tuple(left_limit_key or ())
    right_limit = tuple(right_limit_key or ())
    left_storage = self._loop_limit_storage_identity_key(left_limit)
    right_storage = self._loop_limit_storage_identity_key(right_limit)
    if left_storage is None or right_storage is None:
        return False
    if left_storage != self._readonly_count_storage_identity_key(left_ref):
        return False
    if right_storage != self._readonly_count_storage_identity_key(right_ref):
        return False
    return self._readonly_contract_count_projection_compatible(left_ref, right_ref)

def _impl__readonly_contract_count_identities_compatible(
    self,
    left_ref: ReadonlyReductionRef,
    right_ref: ReadonlyReductionRef,
) -> bool:
    return self._readonly_count_identities_compatible(left_ref, right_ref)

def _impl__readonly_projection_contract_count_identities_compatible(
    self,
    left_ref: ReadonlyReductionRef,
    right_ref: ReadonlyReductionRef,
) -> bool:
    if self._readonly_count_identities_compatible(left_ref, right_ref):
        return True
    return self._readonly_contract_count_projection_compatible(left_ref, right_ref)

def _impl__readonly_contract_count_projection_compatible(
    self,
    left_ref: ReadonlyReductionRef,
    right_ref: ReadonlyReductionRef,
) -> bool:
    left_storage = self._readonly_count_storage_identity_key(left_ref)
    right_storage = self._readonly_count_storage_identity_key(right_ref)
    left_index = self._readonly_count_index_identity_key(left_ref)
    right_index = self._readonly_count_index_identity_key(right_ref)
    if (
        left_storage is None
        or right_storage is None
        or left_index is None
        or right_index is None
        or left_index != right_index
    ):
        return False
    left_register = self._register_storage_identity_components(left_storage)
    right_register = self._register_storage_identity_components(right_storage)
    if left_register is None or right_register is None:
        return False
    if left_register[:3] != right_register[:3]:
        return False
    left_low, left_size = int(left_register[3]), int(left_register[4])
    right_low, right_size = int(right_register[3]), int(right_register[4])
    if left_size == right_size:
        return False
    left_high = left_low + left_size
    right_high = right_low + right_size
    return (
        left_low <= right_low and right_high <= left_high
    ) or (
        right_low <= left_low and left_high <= right_high
    )

def _impl__readonly_count_identity_key(self, readonly_ref: ReadonlyReductionRef) -> Optional[tuple]:
    identity_fn = getattr(readonly_ref, "count_parameter_semantic_identity", None)
    if callable(identity_fn):
        try:
            identity = identity_fn()
        except (AttributeError, TypeError, ValueError):
            identity = None
        if identity is not None:
            return identity
    storage_key = getattr(readonly_ref, "count_parameter_storage_identity_key", None)
    if storage_key is not None:
        return ("parameter_storage", tuple(storage_key))
    try:
        index = getattr(readonly_ref, "count_parameter_index", None)
        if index is not None and int(index) >= 0:
            return ("parameter", int(index))
    except (TypeError, ValueError):
        pass
    return None

def _impl__readonly_count_identity_keys(self, readonly_ref: ReadonlyReductionRef) -> set[tuple]:
    identities: set[tuple] = set()
    identities_fn = getattr(readonly_ref, "count_parameter_semantic_identities", None)
    if callable(identities_fn):
        try:
            identities.update(tuple(identity) for identity in identities_fn() if identity is not None)
        except (AttributeError, TypeError, ValueError):
            pass
    identity = self._readonly_count_identity_key(readonly_ref)
    if identity is not None:
        identities.add(tuple(identity))
    storage_key = getattr(readonly_ref, "count_parameter_storage_identity_key", None)
    if storage_key is not None:
        identities.add(("parameter_storage", tuple(storage_key)))
    index = getattr(readonly_ref, "count_parameter_index", None)
    try:
        if index is not None and int(index) >= 0:
            identities.add(("parameter", int(index)))
            identities.add(("parameter_index", int(index)))
    except (TypeError, ValueError):
        pass
    return identities

def _impl__readonly_count_storage_identity_key(self, readonly_ref: ReadonlyReductionRef) -> Optional[tuple]:
    storage_key = getattr(readonly_ref, "count_parameter_storage_identity_key", None)
    if storage_key is None:
        return None
    return ("parameter_storage", tuple(storage_key))

def _impl__readonly_count_index_identity_key(self, readonly_ref: ReadonlyReductionRef) -> Optional[tuple]:
    index = getattr(readonly_ref, "count_parameter_index", None)
    try:
        if index is not None and int(index) >= 0:
            return ("parameter", int(index))
    except (TypeError, ValueError):
        return None
    return None

def _impl__readonly_count_identities_compatible(
    self,
    left_ref: ReadonlyReductionRef,
    right_ref: ReadonlyReductionRef,
) -> bool:
    left_storage = self._readonly_count_storage_identity_key(left_ref)
    right_storage = self._readonly_count_storage_identity_key(right_ref)
    left_index = self._readonly_count_index_identity_key(left_ref)
    right_index = self._readonly_count_index_identity_key(right_ref)
    if left_storage is not None and right_storage is not None:
        if left_storage == right_storage:
            return True
        return self._count_identity_components_compatible(
            left_storage,
            left_index,
            right_storage,
            right_index,
        )
    return self._count_identity_components_compatible(
        left_storage,
        left_index,
        right_storage,
        right_index,
    )

def _impl__record_completed_readonly_identity_projection_proof_if_safe(
    self,
    reason_record,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    case1: ReturnCase,
    case2: ReturnCase,
) -> None:
    if not self.enable_completed_recovery_proofs:
        return
    if reason_record.reason_id != UnknownReasonId.READONLY_IDENTITY_MISSING.value:
        return
    object_target_key = self._normalize_nested_tuple(reason_record.object_target_key)
    if not self._readonly_identity_target_is_specific(object_target_key):
        return
    left_ref = getattr(getattr(case1, "value_expr", None), "runtime_ref", None)
    right_ref = getattr(getattr(case2, "value_expr", None), "runtime_ref", None)
    if not isinstance(left_ref, ReadonlyReductionRef) or not isinstance(right_ref, ReadonlyReductionRef):
        return
    relation = self._readonly_identity_storage_relation_from_target(object_target_key)
    if not isinstance(relation, tuple) or not relation or relation[0] != "same_register_base_projection":
        return
    if not self._readonly_projection_term_contracts_match(left_ref, right_ref):
        return
    if not self._readonly_projection_semantic_witnesses_match(left_ref, right_ref):
        return
    if not self._case_pair_has_runtime_guard_coverage_or_equivalence(case1, case2):
        return
    extension_evidence = self._readonly_projection_parameter_extension_evidence(
        analysis1,
        analysis2,
        left_ref,
        right_ref,
        relation,
    )
    if extension_evidence is None:
        return

    actions = tuple(build_unknown_recovery_actions([reason_record]))
    if len(actions) != 1:
        return
    action = actions[0]
    proof_id = self._normalize_nested_tuple(action.proof_obligation_id)
    if proof_id is None:
        return
    records: List[Dict[str, Any]] = [
        dict(item)
        for item in getattr(analysis1, "completed_recovery_proof_evidence", ()) or ()
        if isinstance(item, Mapping)
    ]
    existing_ids = {
        self._normalize_nested_tuple(item.get("proof_obligation_id"))
        for item in records
    }
    if proof_id in existing_ids:
        return
    proof_content = {
        "object_derived": True,
        "object_target_key": object_target_key,
        "left_side": object_target_key[2],
        "right_side": object_target_key[3],
        "object_storage_identity": "matched",
        "count_identity": "matched",
        "guard_implication": "proven",
        "finite_witness": "checked",
        "storage_relation": relation,
        "term_contract_relation": {
            "object_derived": True,
            "status": "matched",
            "relation": "same_except_count_storage_projection",
            "left_term_contract": self._readonly_reduction_term_sequence_contract_key(
                left_ref,
                result_size=getattr(left_ref, "result_size", None),
            ),
            "right_term_contract": self._readonly_reduction_term_sequence_contract_key(
                right_ref,
                result_size=getattr(right_ref, "result_size", None),
            ),
        },
        "parameter_extension": extension_evidence,
    }
    records.append(
        {
            "object_derived": True,
            "status": "complete",
            "reason_id": UnknownReasonId.READONLY_IDENTITY_MISSING.value,
            "proof_kind": action.proof_kind,
            "recovery_proof_kind": action.proof_kind,
            "proof_stage": action.proof_stage,
            "evidence_kind": action.evidence_kind,
            "required_evidence": tuple(action.required_evidence),
            "object_target_key": object_target_key,
            "proof_obligation_id": proof_id,
            "proof_source": "readonly_same_register_projection_semantic_extension",
            "proof_content": proof_content,
        }
    )
    analysis1.completed_recovery_proof_evidence = tuple(records)

def _impl__readonly_projection_term_contracts_match(
    self,
    left_ref: ReadonlyReductionRef,
    right_ref: ReadonlyReductionRef,
) -> bool:
    left_key = self._readonly_reduction_term_sequence_contract_key(
        left_ref,
        result_size=getattr(left_ref, "result_size", None),
    )
    right_key = self._readonly_reduction_term_sequence_contract_key(
        right_ref,
        result_size=getattr(right_ref, "result_size", None),
    )
    if not isinstance(left_key, tuple) or not isinstance(right_key, tuple):
        return False
    if left_key == right_key:
        return True
    if (
        len(left_key) != len(right_key)
        or len(left_key) < 5
        or left_key[0] != "readonly_reduction_term_sequence_contract"
        or right_key[0] != "readonly_reduction_term_sequence_contract"
    ):
        return False
    return (
        left_key[:3] == right_key[:3]
        and left_key[5:] == right_key[5:]
        and self._readonly_projection_contract_count_identities_compatible(left_ref, right_ref)
        and self._readonly_projection_contract_limit_keys_compatible(left_key[4], right_key[4], left_ref, right_ref)
    )

def _impl__readonly_projection_semantic_witnesses_match(
    self,
    left_ref: ReadonlyReductionRef,
    right_ref: ReadonlyReductionRef,
) -> bool:
    left_witnesses = self._readonly_semantic_witness_keys(left_ref)
    right_witnesses = self._readonly_semantic_witness_keys(right_ref)
    return bool(left_witnesses) and left_witnesses == right_witnesses

def _impl__readonly_semantic_witness_keys(self, readonly_ref: ReadonlyReductionRef) -> Tuple[Any, ...]:
    witnesses = getattr(readonly_ref, "semantic_witnesses", None)
    if witnesses is None:
        proof = getattr(readonly_ref, "accumulator_proof", None)
        witnesses = getattr(proof, "semantic_witnesses", None)
    keys: List[Any] = []
    for witness in witnesses or ():
        if hasattr(witness, "stable_key"):
            keys.append(witness.stable_key())
            continue
        try:
            keys.append(tuple(witness))
        except TypeError:
            return ()
    return tuple(keys)

def _impl__readonly_projection_parameter_extension_evidence(
    self,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    left_ref: ReadonlyReductionRef,
    right_ref: ReadonlyReductionRef,
    relation: Tuple[Any, ...],
) -> Optional[Dict[str, Any]]:
    try:
        left_bits = self._readonly_projection_span(relation, "left_bits")
        right_bits = self._readonly_projection_span(relation, "right_bits")
    except (TypeError, ValueError):
        return None
    if left_bits is None or right_bits is None:
        return None
    left_low, left_size = left_bits
    right_low, right_size = right_bits
    if left_size == right_size:
        return None
    if left_size > right_size:
        wide_side, narrow_side = "left", "right"
        wide_bits, narrow_bits = left_size, right_size
        wide_low, narrow_low = left_low, right_low
        wide_analysis, narrow_analysis = analysis1, analysis2
        wide_ref, narrow_ref = left_ref, right_ref
    else:
        wide_side, narrow_side = "right", "left"
        wide_bits, narrow_bits = right_size, left_size
        wide_low, narrow_low = right_low, left_low
        wide_analysis, narrow_analysis = analysis2, analysis1
        wide_ref, narrow_ref = right_ref, left_ref
    shared_index = self._readonly_shared_parameter_index(left_ref, right_ref)
    if shared_index is None:
        return None
    signedness = self._readonly_declared_narrow_parameter_signedness(
        wide_analysis,
        shared_index,
        narrow_bits,
        wide_bits,
    )
    source = (
        "declared_parameter_narrow_type_on_wide_storage"
        if signedness is not None
        else None
    )
    if signedness is None:
        return None
    if self._readonly_declared_parameter_bits(narrow_analysis, shared_index) != narrow_bits:
        return None
    if not self._readonly_projection_ref_storage_matches(
        wide_ref,
        wide_bits=wide_bits,
        low_bit=wide_low,
    ):
        return None
    if not self._readonly_projection_ref_storage_matches(
        narrow_ref,
        wide_bits=wide_bits,
        low_bit=narrow_low,
        size_bits=narrow_bits,
    ):
        return None
    return {
        "object_derived": True,
        "status": "proven",
        "relation": "same_register_base_projection_semantic_extension",
        "projection_relation": relation,
        "wide_side": wide_side,
        "narrow_side": narrow_side,
        "parameter_index": shared_index,
        "signedness": signedness,
        "narrow_bits": narrow_bits,
        "wide_bits": wide_bits,
        "extension": "sign_extend" if signedness == "signed" else "zero_extend",
        "proof_source": source,
    }

def _impl__readonly_projection_span(relation: Tuple[Any, ...], tag: str) -> Optional[Tuple[int, int]]:
    for item in relation:
        if isinstance(item, tuple) and len(item) == 3 and item[0] == tag:
            return int(item[1]), int(item[2])
    return None

def _impl__readonly_shared_parameter_index(
    self,
    left_ref: ReadonlyReductionRef,
    right_ref: ReadonlyReductionRef,
) -> Optional[int]:
    left_index = self._readonly_count_index_identity_key(left_ref)
    right_index = self._readonly_count_index_identity_key(right_ref)
    if (
        isinstance(left_index, tuple)
        and isinstance(right_index, tuple)
        and len(left_index) == 2
        and len(right_index) == 2
        and left_index[0] == "parameter"
        and right_index[0] == "parameter"
        and left_index[1] == right_index[1]
    ):
        return int(left_index[1])
    return None

def _impl__readonly_declared_parameter_bits(
    analysis: FunctionReturnAnalysis,
    index: int,
) -> Optional[int]:
    for param in getattr(analysis, "parameters", ()) or ():
        try:
            if int(param.get("index", -1)) != int(index):
                continue
            return int(param.get("size", 0)) * 8
        except (TypeError, ValueError):
            return None
    return None

def _impl__readonly_declared_narrow_parameter_signedness(
    self,
    analysis: FunctionReturnAnalysis,
    index: int,
    narrow_bits: int,
    wide_bits: int,
) -> Optional[str]:
    for param in getattr(analysis, "parameters", ()) or ():
        try:
            if int(param.get("index", -1)) != int(index):
                continue
            size_bits = int(param.get("size", 0)) * 8
        except (TypeError, ValueError):
            return None
        storage_info = param.get("storage_info") or param.get("storage")
        storage_key_fn = getattr(storage_info, "storage_identity_key", None)
        storage_key = storage_key_fn() if callable(storage_key_fn) else None
        if size_bits != int(narrow_bits):
            continue
        if storage_key is None:
            continue
        components = self._register_storage_identity_components(("parameter_storage", tuple(storage_key)))
        if components is None or components[2] != int(wide_bits):
            continue
        signedness = self._readonly_parameter_declared_signedness(param)
        if signedness is None:
            return None
        return signedness
    return None

def _impl__readonly_parameter_declared_signedness(param: Mapping[str, Any]) -> Optional[str]:
    if "is_signed" in param:
        explicit_signedness = param.get("is_signed")
        if explicit_signedness is True:
            return "signed"
        if explicit_signedness is False:
            return "unsigned"
        return None
    data_type_obj = param.get("data_type_obj")
    if data_type_obj is None:
        return None
    is_signed = getattr(data_type_obj, "isSigned", None)
    if not callable(is_signed):
        return None
    try:
        signed_value = is_signed()
    except Exception:
        return None
    if signed_value is True:
        return "signed"
    if signed_value is False:
        return "unsigned"
    return None

def _impl__readonly_projection_ref_storage_matches(
    self,
    readonly_ref: ReadonlyReductionRef,
    *,
    wide_bits: int,
    low_bit: int,
    size_bits: Optional[int] = None,
) -> bool:
    storage = self._readonly_count_storage_identity_key(readonly_ref)
    components = self._register_storage_identity_components(storage)
    if components is None:
        return False
    _, _, base_bits, ref_low, ref_size = components
    expected_size = int(size_bits) if size_bits is not None else int(wide_bits)
    return base_bits == int(wide_bits) and ref_low == int(low_bit) and ref_size == expected_size

def _impl__readonly_identity_object_target_key(
    self,
    *,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    pair_id: str,
) -> Tuple[Any, ...]:
    """Object-derived target key for readonly operand identity proof backlog."""

    return (
        "readonly_identity",
        ("pair", pair_id),
        self._readonly_identity_side_object_key(
            "left",
            base_ctx.get("analysis1"),
            case1,
        ),
        self._readonly_identity_side_object_key(
            "right",
            base_ctx.get("analysis2"),
            case2,
        ),
        self._readonly_identity_relation_object_key(case1, case2),
    )

def _impl__readonly_identity_relation_object_key(
    self,
    case1: ReturnCase,
    case2: ReturnCase,
) -> Tuple[Any, ...]:
    left_ref = getattr(getattr(case1, "value_expr", None), "runtime_ref", None)
    right_ref = getattr(getattr(case2, "value_expr", None), "runtime_ref", None)
    if not isinstance(left_ref, ReadonlyReductionRef) or not isinstance(right_ref, ReadonlyReductionRef):
        return ("readonly_identity_relation", ("kind", "missing_readonly_ref"))
    left_identities = self._readonly_count_identity_keys(left_ref)
    right_identities = self._readonly_count_identity_keys(right_ref)
    shared_identities = tuple(sorted(left_identities & right_identities, key=repr))
    return (
        "readonly_identity_relation",
        ("shared_count_identities", shared_identities),
        (
            "count_storage_relation",
            self._readonly_count_storage_relation_key(left_ref, right_ref),
        ),
    )

def _impl__readonly_count_storage_relation_key(
    self,
    left_ref: ReadonlyReductionRef,
    right_ref: ReadonlyReductionRef,
) -> Tuple[Any, ...]:
    left_storage = self._readonly_count_storage_identity_key(left_ref)
    right_storage = self._readonly_count_storage_identity_key(right_ref)
    if left_storage is None or right_storage is None:
        return ("missing_storage_identity", left_storage, right_storage)
    if left_storage == right_storage:
        return ("same_storage_identity", left_storage)
    left_register = self._register_storage_identity_components(left_storage)
    right_register = self._register_storage_identity_components(right_storage)
    if left_register is None or right_register is None:
        return ("different_storage_identity", left_storage, right_storage)
    if left_register[:3] != right_register[:3]:
        return ("different_register_base", left_storage, right_storage)
    left_low, left_size = left_register[3], left_register[4]
    right_low, right_size = right_register[3], right_register[4]
    left_high = left_low + left_size
    right_high = right_low + right_size
    contains = None
    if left_low <= right_low and right_high <= left_high:
        contains = "left_contains_right"
    elif right_low <= left_low and left_high <= right_high:
        contains = "right_contains_left"
    return (
        "same_register_base_projection",
        ("base", left_register[:3]),
        ("left_bits", left_low, left_size),
        ("right_bits", right_low, right_size),
        ("projection", contains or "overlap_or_disjoint"),
    )

def _impl__method_b_readonly_summary_ref(self, expr: Optional[Expression]) -> Optional[ReadonlyReductionRef]:
    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, ReadonlyReductionRef) and getattr(runtime_ref, "loop_summary", None) is not None:
        return runtime_ref
    return None

def _impl__value_contains_readonly_ref(cls, value: Any) -> bool:
    normalized = cls._normalize_nested_tuple(value)
    if isinstance(normalized, tuple):
        if normalized and isinstance(normalized[0], str) and normalized[0].startswith("readonly"):
            return True
        if "observed_memory_read" in normalized:
            return True
        return any(cls._value_contains_readonly_ref(item) for item in normalized)
    if isinstance(normalized, list):
        return any(cls._value_contains_readonly_ref(item) for item in normalized)
    if isinstance(normalized, dict):
        return any(
            cls._value_contains_readonly_ref(key)
            or cls._value_contains_readonly_ref(item)
            for key, item in normalized.items()
        )
    return False

def _impl__readonly_identity_side_object_key(
    self,
    side_label: str,
    analysis: Optional[FunctionReturnAnalysis],
    case: ReturnCase,
) -> Tuple[Any, ...]:
    value_expr = getattr(case, "value_expr", None)
    readonly_ref = getattr(value_expr, "runtime_ref", None)
    return (
        "readonly_identity_side",
        side_label,
        self._analysis_entry_key(analysis) if analysis is not None else None,
        self._readonly_return_case_partition_member_object_key(case),
        self._readonly_reduction_ref_object_key(readonly_ref),
        (
            "guards",
            tuple(
                self._return_condition_object_key(condition)
                for condition in (getattr(case, "conditions", None) or ())
            ),
        ),
        ("value", self._readonly_value_object_key(value_expr)),
    )

def _impl__readonly_return_case_partition_member_object_key(self, case: ReturnCase) -> Tuple[Any, ...]:
    return_info = getattr(case, "return_info", None)
    case_index = getattr(case, "index", None)
    try:
        normalized_case_index = int(case_index)
    except (TypeError, ValueError):
        normalized_case_index = None
    source_indices = []
    for source_index in getattr(case, "source_indices", ()) or ():
        try:
            source_indices.append(int(source_index))
        except (TypeError, ValueError):
            continue
    surface = getattr(case, "comparison_surface", None)
    return (
        "readonly_return_case_partition_member",
        normalized_case_index,
        tuple(source_indices),
        (
            "return_case",
            normalized_case_index,
            getattr(return_info, "address", None),
            self._stable_key_or_none(getattr(return_info, "pcode_op_ref", None)),
            getattr(return_info, "pcode_identity", None),
            getattr(return_info, "pcode_order", None),
        ),
        (
            "comparison_surface",
            getattr(surface, "kind", None),
            getattr(surface, "explicit_bit_width", None),
            getattr(surface, "use_sign_extension", None),
        ),
        ("value", self._readonly_value_object_key(getattr(case, "value_expr", None))),
        (
            "guards",
            tuple(
                self._return_condition_object_key(condition)
                for condition in (getattr(case, "conditions", None) or ())
            ),
        ),
    )

def _impl__readonly_value_object_key(self, expr: Any) -> Tuple[Any, ...]:
    readonly_ref = getattr(expr, "runtime_ref", None)
    if isinstance(readonly_ref, ReadonlyReductionRef):
        return ("readonly_value", self._readonly_reduction_ref_object_key(readonly_ref))
    return ("expression", self._expression_runtime_object_key(expr))

def _impl__readonly_reduction_ref_object_key(self, readonly_ref: Any) -> Tuple[Any, ...]:
    if not isinstance(readonly_ref, ReadonlyReductionRef):
        return ("readonly_reduction_ref", None)
    semantic_key = None
    semantic_key_fn = getattr(readonly_ref, "semantic_key", None)
    if callable(semantic_key_fn):
        try:
            semantic_key = semantic_key_fn()
        except (AttributeError, TypeError, ValueError, RecursionError):
            semantic_key = None
    pointer_base_identity = None
    pointer_semantic_key_fn = getattr(getattr(readonly_ref, "pointer_base_ref", None), "semantic_key", None)
    if callable(pointer_semantic_key_fn):
        try:
            pointer_base_identity = pointer_semantic_key_fn()
        except (AttributeError, TypeError, ValueError, RecursionError):
            pointer_base_identity = None
    witness_keys = []
    for witness in getattr(readonly_ref, "semantic_witnesses", ()) or ():
        witness_key_fn = getattr(witness, "stable_key", None)
        if not callable(witness_key_fn):
            continue
        try:
            witness_keys.append(witness_key_fn())
        except (AttributeError, TypeError, ValueError, RecursionError):
            continue
    return (
        "readonly_reduction_ref",
        getattr(readonly_ref, "reduction_kind", None),
        ("semantic_key", semantic_key),
        ("pointer_base_identity", pointer_base_identity),
        ("count_identities", tuple(sorted(self._readonly_count_identity_keys(readonly_ref), key=repr))),
        (
            "term_contract",
            self._readonly_reduction_term_sequence_contract_key(
                readonly_ref,
                result_size=getattr(readonly_ref, "result_size", None),
            ),
        ),
        ("result_size", getattr(readonly_ref, "result_size", None)),
        ("stride", getattr(readonly_ref, "stride", None)),
        ("element_size", getattr(readonly_ref, "element_size", None)),
        ("start_offset", getattr(readonly_ref, "start_offset", None)),
        ("constant_bias", getattr(readonly_ref, "constant_bias", None)),
        ("semantic_witnesses", tuple(witness_keys)),
    )

def _impl__combined_conditions_imply_reduction_count(
    self,
    exact_case: ReturnCase,
    summary_case: ReturnCase,
    accumulator_proof,
    exact_count: int,
) -> bool:
    if exact_count <= 0:
        return False
    count_bits = max(
        self._case_reduction_count_bit_width(exact_case, accumulator_proof),
        self._case_reduction_count_bit_width(summary_case, accumulator_proof),
    )
    count_expr = self._reduction_count_parameter_expression(
        list(getattr(exact_case, "parameters", None) or [])
        + list(getattr(summary_case, "parameters", None) or []),
        accumulator_proof,
        int(count_bits),
    )
    if count_expr is None:
        return False
    equality = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            count_expr,
            Expression.constant(int(exact_count), size=max(1, (int(count_bits) + 7) // 8)),
        ),
        False,
    )
    conditions = self._combined_summary_conditions(exact_case, summary_case)
    implication_conditions = list(conditions or []) + [equality.negate()]
    identity_conditions = self._conditions_with_object_identity_parameter_symbols(
        implication_conditions,
        list(getattr(exact_case, "parameters", None) or [])
        + list(getattr(summary_case, "parameters", None) or []),
    )
    solver_result = ConditionSMTOracle.conjunction_is_unsat(identity_conditions)
    if solver_result is not None:
        return solver_result
    return ConditionSimplifier.object_centric_is_contradiction(identity_conditions)

def _impl__cases_admit_reduction_count(
    self,
    exact_case: ReturnCase,
    summary_case: ReturnCase,
    accumulator_proof,
    exact_count: int,
) -> bool:
    if self._combined_conditions_imply_reduction_count(
        exact_case,
        summary_case,
        accumulator_proof,
        exact_count,
    ):
        return True
    return self._case_implies_reduction_count(exact_case, accumulator_proof, exact_count) and (
        self._case_allows_reduction_count(summary_case, accumulator_proof, exact_count)
    )

def _impl__cases_admit_reduction_count_values(
    self,
    exact_case: ReturnCase,
    summary_case: ReturnCase,
    accumulator_proof,
    exact_counts: Sequence[int],
) -> bool:
    count_values = tuple(sorted({int(value) for value in exact_counts if int(value) > 0}))
    if not count_values:
        return False
    if len(count_values) == 1:
        return self._cases_admit_reduction_count(
            exact_case,
            summary_case,
            accumulator_proof,
            count_values[0],
        )
    return self._combined_conditions_imply_reduction_count_values(
        exact_case,
        summary_case,
        accumulator_proof,
        count_values,
    )

def _impl__combined_conditions_imply_reduction_count_values(
    self,
    exact_case: ReturnCase,
    summary_case: ReturnCase,
    accumulator_proof,
    exact_counts: Sequence[int],
) -> bool:
    count_values = tuple(sorted({int(value) for value in exact_counts if int(value) > 0}))
    if not count_values:
        return False
    if len(count_values) == 1:
        return self._combined_conditions_imply_reduction_count(
            exact_case,
            summary_case,
            accumulator_proof,
            count_values[0],
        )
    count_bits = max(
        self._case_reduction_count_bit_width(exact_case, accumulator_proof),
        self._case_reduction_count_bit_width(summary_case, accumulator_proof),
    )
    parameters = (
        list(getattr(exact_case, "parameters", None) or [])
        + list(getattr(summary_case, "parameters", None) or [])
    )
    count_expr = self._reduction_count_parameter_expression(
        parameters,
        accumulator_proof,
        int(count_bits),
    )
    if count_expr is None:
        return False
    membership = self._reduction_count_membership_condition(
        count_expr,
        count_values,
        int(count_bits),
    )
    if membership is None:
        return False
    implication_conditions = list(self._combined_summary_conditions(exact_case, summary_case) or [])
    implication_conditions.append(membership.negate())
    identity_conditions = self._conditions_with_object_identity_parameter_symbols(
        implication_conditions,
        parameters,
    )
    solver_result = ConditionSMTOracle.conjunction_is_unsat(identity_conditions)
    if solver_result is not None:
        return solver_result
    return ConditionSimplifier.object_centric_is_contradiction(identity_conditions)

def _impl__reduction_count_membership_condition(
    self,
    count_expr: Expression,
    count_values: Sequence[int],
    count_bits: int,
) -> Optional[Condition]:
    values = tuple(sorted({int(value) for value in count_values if int(value) > 0}))
    if not values:
        return None
    count_size = max(1, (max(1, int(count_bits)) + 7) // 8)
    equalities = [
        Expression.binary_op(
            "INT_EQUAL",
            count_expr,
            Expression.constant(value, size=count_size),
        )
        for value in values
    ]
    membership_expr = equalities[0]
    for equality in equalities[1:]:
        membership_expr = Expression.binary_op("BOOL_OR", membership_expr, equality)
    return Condition(membership_expr, False)

def _impl__case_implies_reduction_count(
    self,
    case: ReturnCase,
    accumulator_proof,
    exact_count: int,
) -> bool:
    if self._case_has_direct_reduction_count_equality(
        case,
        accumulator_proof,
        exact_count,
    ):
        return True
    equality = self._reduction_count_equality_condition(case, accumulator_proof, exact_count)
    if equality is None:
        return False
    identity_conditions = self._conditions_with_object_identity_parameter_symbols(
        list(getattr(case, "conditions", None) or []) + [equality.negate()],
        list(getattr(case, "parameters", None) or []),
    )
    solver_result = ConditionSMTOracle.conjunction_is_unsat(identity_conditions)
    if solver_result is not None:
        return solver_result
    if ConditionSimplifier.object_centric_is_contradiction(identity_conditions):
        return True
    return False

def _impl__case_allows_reduction_count(
    self,
    case: ReturnCase,
    accumulator_proof,
    exact_count: int,
) -> bool:
    equality = self._reduction_count_equality_condition(case, accumulator_proof, exact_count)
    if equality is None:
        return False
    identity_conditions = self._conditions_with_object_identity_parameter_symbols(
        list(getattr(case, "conditions", None) or []) + [equality],
        list(getattr(case, "parameters", None) or []),
    )
    solver_result = ConditionSMTOracle.conjunction_is_unsat(identity_conditions)
    if solver_result is not None:
        return not solver_result
    return not ConditionSimplifier.object_centric_is_contradiction(identity_conditions)

def _impl__reduction_count_equality_condition(
    self,
    case: ReturnCase,
    accumulator_proof,
    exact_count: int,
) -> Optional[Condition]:
    if exact_count <= 0:
        return None
    count_bits = self._case_reduction_count_bit_width(case, accumulator_proof)
    count_expr = self._reduction_count_parameter_expression(
        getattr(case, "parameters", None) or [],
        accumulator_proof,
        int(count_bits),
    )
    if count_expr is None:
        return None
    return Condition(
        Expression.binary_op(
            "INT_EQUAL",
            count_expr,
            Expression.constant(int(exact_count), size=max(1, (int(count_bits) + 7) // 8)),
        ),
        False,
    )

def _impl__reduction_count_parameter_expression(
    self,
    parameters: Sequence[Dict[str, Any]],
    accumulator_proof,
    count_bits: int,
) -> Optional[Expression]:
    count_size = max(1, (max(1, int(count_bits)) + 7) // 8)
    descriptor = self._reduction_count_parameter_descriptor(parameters, accumulator_proof)
    proof_index = getattr(accumulator_proof, "count_parameter_index", None)
    count_name = str(getattr(accumulator_proof, "count_parameter_name", None) or "")
    storage_info = None
    if descriptor is None and self._parameters_have_conflicting_reduction_count_storage(
        parameters,
        accumulator_proof,
    ):
        return None
    if descriptor is not None:
        count_name = str(descriptor.get("name") or count_name or "count")
        storage_info = self._storage_info_from_parameter_descriptor(descriptor)
        if proof_index is None:
            proof_index = descriptor.get("index")
    try:
        index = int(proof_index) if proof_index is not None else -1
    except (TypeError, ValueError):
        index = -1
    if index < 0 and storage_info is None:
        return None
    return Expression.parameter(
        count_name or "count",
        index=index,
        size=count_size,
        data_type=descriptor.get("data_type") if descriptor is not None else None,
        data_type_obj=descriptor.get("data_type_obj") if descriptor is not None else None,
        storage_info=storage_info,
    )

def _impl__reduction_count_parameter_descriptor(
    self,
    parameters: Sequence[Dict[str, Any]],
    accumulator_proof,
) -> Optional[Dict[str, Any]]:
    proof_storage = self._reduction_count_storage_identity_key(accumulator_proof)
    proof_index = self._reduction_count_index_identity_key(accumulator_proof)
    if proof_storage is None and proof_index is None:
        return None
    for parameter in parameters or []:
        if self._count_identity_components_compatible(
            proof_storage,
            proof_index,
            self._parameter_descriptor_storage_identity_key(parameter),
            self._parameter_descriptor_index_identity_key(parameter),
        ):
            return parameter
    projected_candidates = []
    if proof_storage is not None and proof_index is not None:
        for parameter in parameters or []:
            parameter_index = self._parameter_descriptor_index_identity_key(parameter)
            parameter_storage = self._parameter_descriptor_storage_identity_key(parameter)
            if (
                parameter_index == proof_index
                and parameter_storage is not None
                and self._count_storage_low_projection_compatible(
                    proof_storage,
                    parameter_storage,
                )
            ):
                projected_candidates.append(parameter)
    if len(projected_candidates) == 1:
        return projected_candidates[0]
    return None

def _impl__parameters_have_conflicting_reduction_count_storage(
    self,
    parameters: Sequence[Dict[str, Any]],
    accumulator_proof,
) -> bool:
    proof_storage = self._reduction_count_storage_identity_key(accumulator_proof)
    proof_index = self._reduction_count_index_identity_key(accumulator_proof)
    if proof_storage is None or proof_index is None:
        return False
    for parameter in parameters or []:
        parameter_index = self._parameter_descriptor_index_identity_key(parameter)
        parameter_storage = self._parameter_descriptor_storage_identity_key(parameter)
        if parameter_index == proof_index and parameter_storage is not None and parameter_storage != proof_storage:
            return True
    return False

def _impl__reduction_count_storage_identity_key(self, accumulator_proof) -> Optional[tuple]:
    storage_key = getattr(accumulator_proof, "count_parameter_storage_identity_key", None)
    if storage_key is None:
        return None
    return ("parameter_storage", tuple(storage_key))

def _impl__reduction_count_index_identity_key(self, accumulator_proof) -> Optional[tuple]:
    index = getattr(accumulator_proof, "count_parameter_index", None)
    try:
        if index is not None and int(index) >= 0:
            return ("parameter", int(index))
    except (TypeError, ValueError):
        return None
    return None

def _impl__reduction_count_identity_keys(self, accumulator_proof) -> set[tuple]:
    identities: set[tuple] = set()
    identities_fn = getattr(accumulator_proof, "count_parameter_semantic_identities", None)
    if callable(identities_fn):
        try:
            identities.update(tuple(identity) for identity in identities_fn() if identity is not None)
        except (AttributeError, TypeError, ValueError):
            pass
    identity_fn = getattr(accumulator_proof, "count_parameter_semantic_identity", None)
    if callable(identity_fn):
        try:
            identity = identity_fn()
        except (AttributeError, TypeError, ValueError):
            identity = None
        if identity is not None:
            identities.add(tuple(identity))
    storage_key = getattr(accumulator_proof, "count_parameter_storage_identity_key", None)
    if storage_key is not None:
        identities.add(("parameter_storage", tuple(storage_key)))
    index = getattr(accumulator_proof, "count_parameter_index", None)
    try:
        if index is not None and int(index) >= 0:
            identities.add(("parameter", int(index)))
            identities.add(("parameter_index", int(index)))
    except (TypeError, ValueError):
        pass
    return identities

def _impl__case_has_direct_reduction_count_equality(
    self,
    case: ReturnCase,
    accumulator_proof,
    exact_count: int,
) -> bool:
    for condition in list(getattr(case, "conditions", None) or []):
        expr = getattr(condition, "expression", None)
        if (
            expr is None
            or getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP
            or len(getattr(expr, "operands", None) or []) != 2
        ):
            continue
        operator = getattr(expr, "operator", None)
        condition_true = not bool(getattr(condition, "negated", False))
        if operator == "INT_EQUAL" and not condition_true:
            continue
        if operator == "INT_NOTEQUAL" and condition_true:
            continue
        if operator not in {"INT_EQUAL", "INT_NOTEQUAL"}:
            continue
        left, right = expr.operands
        if self._expression_is_full_reduction_count_view(left, case, accumulator_proof):
            const_value = self._exact_reduction_count_constant(right)
        elif self._expression_is_full_reduction_count_view(right, case, accumulator_proof):
            const_value = self._exact_reduction_count_constant(left)
        else:
            const_value = self._solve_reduction_count_affine_equality(
                left,
                self._exact_reduction_count_constant(right),
                operator,
                not condition_true,
                case,
                accumulator_proof,
            )
            if const_value is None:
                const_value = self._solve_reduction_count_affine_equality(
                    right,
                    self._exact_reduction_count_constant(left),
                    operator,
                    not condition_true,
                    case,
                    accumulator_proof,
                )
            if const_value is None:
                const_value = self._solve_reduction_count_affine_equality_between_expressions(
                    left,
                    right,
                    operator,
                    not condition_true,
                    case,
                    accumulator_proof,
                )
            if const_value is None:
                const_value = self._solve_reduction_count_masked_equality(
                    left,
                    self._exact_reduction_count_constant(right),
                    operator,
                    not condition_true,
                    case,
                    accumulator_proof,
                )
            if const_value is None:
                const_value = self._solve_reduction_count_masked_equality(
                    right,
                    self._exact_reduction_count_constant(left),
                    operator,
                    not condition_true,
                    case,
                    accumulator_proof,
                )
            if const_value is None:
                continue
        if const_value == int(exact_count):
            return True
    return False

def _impl__solve_reduction_count_affine_equality(
    self,
    expr: Optional[Expression],
    other_const: Optional[int],
    operator: Optional[str],
    negated: bool,
    case: ReturnCase,
    accumulator_proof,
) -> Optional[int]:
    if expr is None or other_const is None or operator not in {"INT_EQUAL", "INT_NOTEQUAL"}:
        return None
    if operator == "INT_EQUAL" and negated:
        return None
    if operator == "INT_NOTEQUAL" and not negated:
        return None
    affine = self._extract_reduction_count_affine(expr, case, accumulator_proof)
    if affine is None:
        return None
    coeff, bias = affine
    if int(coeff) != 1:
        return None
    return int(other_const) - int(bias)

def _impl__solve_reduction_count_affine_equality_between_expressions(
    self,
    left: Optional[Expression],
    right: Optional[Expression],
    operator: Optional[str],
    negated: bool,
    case: ReturnCase,
    accumulator_proof,
) -> Optional[int]:
    """Solve object-level equalities whose operands are affine in the reduction count.

    Ghidra often emits exact finite tail guards as pointer equalities, for
    example PTRADD(PTRADD(base, 3, 4), 1, 4) == PTRADD(base, count, 4).
    Treating those as strings is brittle; instead we lower both sides to a
    base-preserving byte-affine form derived from Expression/PTRADD objects.
    """

    if left is None or right is None or operator not in {"INT_EQUAL", "INT_NOTEQUAL"}:
        return None
    if operator == "INT_EQUAL" and negated:
        return None
    if operator == "INT_NOTEQUAL" and not negated:
        return None

    left_count_affine = self._extract_reduction_count_affine(left, case, accumulator_proof)
    right_count_affine = self._extract_reduction_count_affine(right, case, accumulator_proof)
    if left_count_affine is not None and right_count_affine is not None:
        solved = self._solve_affine_equality(left_count_affine, right_count_affine)
        if solved is not None:
            return solved

    left_addr_affine = self._extract_readonly_address_affine(left, case, accumulator_proof)
    right_addr_affine = self._extract_readonly_address_affine(right, case, accumulator_proof)
    if left_addr_affine is None or right_addr_affine is None:
        return None
    left_base, left_coeff, left_bias = left_addr_affine
    right_base, right_coeff, right_bias = right_addr_affine
    if left_base is None or right_base is None or left_base != right_base:
        return None
    return self._solve_affine_equality(
        (int(left_coeff), int(left_bias)),
        (int(right_coeff), int(right_bias)),
    )

def _impl__solve_reduction_count_masked_equality(
    self,
    expr: Optional[Expression],
    other_const: Optional[int],
    operator: Optional[str],
    negated: bool,
    case: ReturnCase,
    accumulator_proof,
) -> Optional[int]:
    if expr is None or other_const is None or operator not in {"INT_EQUAL", "INT_NOTEQUAL"}:
        return None
    if operator == "INT_EQUAL" and negated:
        return None
    if operator == "INT_NOTEQUAL" and not negated:
        return None
    affine = self._extract_full_width_masked_reduction_count_affine(
        expr,
        case,
        accumulator_proof,
    )
    if affine is None:
        return None
    coeff, bias = affine
    if int(coeff) != 1:
        return None
    solved = int(other_const) - int(bias)
    return int(solved) if solved > 0 else None

def _impl__extract_full_width_masked_reduction_count_affine(
    self,
    expr: Optional[Expression],
    case: ReturnCase,
    accumulator_proof,
) -> Optional[tuple[int, int]]:
    if expr is None:
        return None
    masked = self._extract_full_width_masked_reduction_count_view(expr, case, accumulator_proof)
    if masked is not None:
        return 1, 0
    if getattr(expr, "expr_type", None) == ExpressionType.CONSTANT:
        value = self._exact_reduction_count_constant(expr)
        return (0, int(value)) if value is not None else None
    if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP or len(getattr(expr, "operands", None) or []) != 2:
        return None
    left = self._extract_full_width_masked_reduction_count_affine(expr.operands[0], case, accumulator_proof)
    right = self._extract_full_width_masked_reduction_count_affine(expr.operands[1], case, accumulator_proof)
    operator = getattr(expr, "operator", None)
    if operator == "INT_ADD" and left is not None and right is not None:
        return int(left[0]) + int(right[0]), int(left[1]) + int(right[1])
    if operator == "INT_SUB" and left is not None and right is not None:
        return int(left[0]) - int(right[0]), int(left[1]) - int(right[1])
    return None

def _impl__extract_full_width_masked_reduction_count_view(
    self,
    expr: Optional[Expression],
    case: ReturnCase,
    accumulator_proof,
) -> Optional[Expression]:
    if (
        expr is None
        or getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP
        or getattr(expr, "operator", None) != "INT_AND"
        or len(getattr(expr, "operands", None) or []) != 2
    ):
        return None
    left, right = expr.operands
    candidates = ((left, right), (right, left))
    for source, mask_expr in candidates:
        mask = self._exact_reduction_count_constant(mask_expr)
        if mask is None:
            continue
        if not self._expression_is_full_reduction_count_view(source, case, accumulator_proof):
            if self._expression_is_projected_reduction_count_mask_view(
                source,
                int(mask),
                case,
                accumulator_proof,
            ):
                return source
            continue
        source_bits = max(1, int(expression_smt_bit_width(source) or 0))
        expr_bits = max(1, int(expression_smt_bit_width(expr) or source_bits))
        if expr_bits != source_bits:
            continue
        if int(mask) != (1 << int(source_bits)) - 1:
            if self._expression_is_projected_reduction_count_mask_view(
                source,
                int(mask),
                case,
                accumulator_proof,
            ):
                return source
            continue
        return source
    return None

def _impl__expression_is_projected_reduction_count_mask_view(
    self,
    source: Optional[Expression],
    mask: int,
    case: ReturnCase,
    accumulator_proof,
) -> bool:
    if source is None or getattr(source, "expr_type", None) != ExpressionType.PARAMETER:
        return False
    descriptor = self._reduction_count_parameter_descriptor(
        getattr(case, "parameters", None) or [],
        accumulator_proof,
    )
    if descriptor is None:
        return False
    descriptor_storage = self._parameter_descriptor_storage_identity_key(descriptor)
    proof_storage = self._reduction_count_storage_identity_key(accumulator_proof)
    if descriptor_storage is None or proof_storage is None:
        return False
    if not self._count_storage_low_projection_compatible(descriptor_storage, proof_storage):
        return False
    source_storage = self._parameter_expression_storage_identity_key(source)
    if source_storage is not None and not self._count_storage_low_projection_compatible(
        descriptor_storage,
        source_storage,
    ):
        return False
    descriptor_index = self._parameter_descriptor_index_identity_key(descriptor)
    source_index = self._parameter_expression_index_identity_key(source)
    proof_index = self._reduction_count_index_identity_key(accumulator_proof)
    if descriptor_index is None or source_index is None or proof_index is None:
        return False
    if descriptor_index != source_index or descriptor_index != proof_index:
        return False
    try:
        descriptor_bits = int(descriptor.get("size", 0) or 0) * 8
    except (TypeError, ValueError):
        descriptor_bits = 0
    if descriptor_bits <= 0:
        return False
    source_bits = max(1, int(expression_smt_bit_width(source) or 0))
    if source_bits < descriptor_bits:
        return False
    if int(mask) != (1 << int(descriptor_bits)) - 1:
        return False
    return True

def _impl__extract_readonly_address_affine(
    self,
    expr: Optional[Expression],
    case: ReturnCase,
    accumulator_proof,
) -> Optional[tuple[Optional[tuple], int, int]]:
    """Return (base_identity, count_coeff_bytes, byte_bias) for address expressions."""

    if expr is None:
        return None
    base_key = self._readonly_pointer_base_identity_key(expr, case, accumulator_proof)
    if base_key is not None:
        return base_key, 0, 0
    if getattr(expr, "expr_type", None) == ExpressionType.CONSTANT:
        const_value = self._exact_reduction_count_constant(expr)
        return (None, 0, int(const_value)) if const_value is not None else None
    if getattr(expr, "expr_type", None) == ExpressionType.INTRINSIC and getattr(expr, "name", None) == "PTRADD":
        operands = list(getattr(expr, "operands", None) or [])
        if len(operands) < 3:
            return None
        base_affine = self._extract_readonly_address_affine(operands[0], case, accumulator_proof)
        index_affine = self._extract_reduction_count_affine(operands[1], case, accumulator_proof)
        scale = self._exact_reduction_count_constant(operands[2])
        if base_affine is None or index_affine is None or scale is None:
            return None
        base, base_coeff, base_bias = base_affine
        index_coeff, index_bias = index_affine
        return (
            base,
            int(base_coeff) + int(index_coeff) * int(scale),
            int(base_bias) + int(index_bias) * int(scale),
        )
    if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP or len(getattr(expr, "operands", None) or []) != 2:
        return None
    operator = getattr(expr, "operator", None)
    left = self._extract_readonly_address_affine(expr.operands[0], case, accumulator_proof)
    right = self._extract_readonly_address_affine(expr.operands[1], case, accumulator_proof)
    if operator == "INT_ADD" and left is not None and right is not None:
        return self._combine_readonly_address_affine(left, right, subtract=False)
    if operator == "INT_SUB" and left is not None and right is not None:
        return self._combine_readonly_address_affine(left, right, subtract=True)
    return None

def _impl__combine_readonly_address_affine(
    self,
    left: tuple[Optional[tuple], int, int],
    right: tuple[Optional[tuple], int, int],
    *,
    subtract: bool,
) -> Optional[tuple[Optional[tuple], int, int]]:
    left_base, left_coeff, left_bias = left
    right_base, right_coeff, right_bias = right
    if left_base is not None and right_base is not None:
        if subtract and left_base == right_base:
            base = None
        else:
            return None
    else:
        base = left_base if left_base is not None else right_base
    sign = -1 if subtract else 1
    return (
        base,
        int(left_coeff) + sign * int(right_coeff),
        int(left_bias) + sign * int(right_bias),
    )

def _impl__readonly_pointer_base_identity_key(
    self,
    expr: Optional[Expression],
    case: ReturnCase,
    accumulator_proof,
) -> Optional[tuple]:
    if expr is None or getattr(expr, "expr_type", None) != ExpressionType.PARAMETER:
        return None
    pointer_ref = getattr(accumulator_proof, "pointer_base_ref", None)
    proof_key = getattr(pointer_ref, "semantic_key", lambda: None)()
    if proof_key is None:
        return None
    expr_keys = set()
    try:
        expr_index = getattr(expr, "value", None)
        if expr_index is not None and int(expr_index) >= 0:
            expr_keys.add(("parameter", int(expr_index)))
    except (TypeError, ValueError):
        pass
    storage_info = getattr(expr, "storage_info", None)
    storage_key_fn = getattr(storage_info, "storage_identity_key", None)
    if callable(storage_key_fn):
        try:
            storage_key = storage_key_fn()
        except (AttributeError, TypeError, ValueError):
            storage_key = None
        if storage_key is not None:
            expr_keys.add(("storage_identity", tuple(storage_key)))
    if proof_key in expr_keys:
        return proof_key
    return None

def _impl__extract_reduction_count_affine(
    self,
    expr: Optional[Expression],
    case: ReturnCase,
    accumulator_proof,
) -> Optional[tuple[int, int]]:
    if expr is None:
        return None
    if self._expression_is_full_reduction_count_view(expr, case, accumulator_proof):
        return 1, 0
    if getattr(expr, "expr_type", None) == ExpressionType.CONSTANT:
        value = self._exact_reduction_count_constant(expr)
        return (0, int(value)) if value is not None else None
    if getattr(expr, "expr_type", None) == ExpressionType.UNARY_OP and len(getattr(expr, "operands", None) or []) == 1:
        operator = getattr(expr, "operator", None)
        if operator in {"INT_ZEXT", "INT_SEXT"}:
            operand = expr.operands[0]
            operand_bits = max(1, int(expression_smt_bit_width(operand) or 0))
            if operand_bits != self._case_reduction_count_bit_width(case, accumulator_proof):
                return None
            return self._extract_reduction_count_affine(operand, case, accumulator_proof)
        if operator in {"CAST", "COPY"}:
            operand = expr.operands[0]
            expr_bits = max(1, int(expression_smt_bit_width(expr) or 0))
            operand_bits = max(1, int(expression_smt_bit_width(operand) or 0))
            proof_bits = self._case_reduction_count_bit_width(case, accumulator_proof)
            if expr_bits != operand_bits or expr_bits != proof_bits:
                return None
            return self._extract_reduction_count_affine(expr.operands[0], case, accumulator_proof)
        if operator in {"INT_2COMP", "INT_NEGATE"}:
            operand = self._extract_reduction_count_affine(expr.operands[0], case, accumulator_proof)
            if operand is None:
                return None
            return -int(operand[0]), -int(operand[1])
        return None
    if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP or len(getattr(expr, "operands", None) or []) != 2:
        return None
    left = self._extract_reduction_count_affine(expr.operands[0], case, accumulator_proof)
    right = self._extract_reduction_count_affine(expr.operands[1], case, accumulator_proof)
    operator = getattr(expr, "operator", None)
    if operator == "INT_ADD" and left is not None and right is not None:
        return int(left[0]) + int(right[0]), int(left[1]) + int(right[1])
    if operator == "INT_SUB" and left is not None and right is not None:
        return int(left[0]) - int(right[0]), int(left[1]) - int(right[1])
    if operator == "INT_MULT":
        left_const = self._exact_reduction_count_constant(expr.operands[0])
        right_const = self._exact_reduction_count_constant(expr.operands[1])
        if left_const is not None and right is not None:
            return int(left_const) * int(right[0]), int(left_const) * int(right[1])
        if right_const is not None and left is not None:
            return int(right_const) * int(left[0]), int(right_const) * int(left[1])
    return None

def _impl__expression_is_full_reduction_count_view(
    self,
    expr: Optional[Expression],
    case: ReturnCase,
    accumulator_proof,
) -> bool:
    if expr is None:
        return False
    if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER:
        expr_bits = max(1, int(expression_smt_bit_width(expr) or 0))
        proof_bits = self._case_reduction_count_bit_width(case, accumulator_proof)
        if expr_bits != proof_bits:
            return False
        return self._parameter_matches_reduction_count_identity(expr, case, accumulator_proof)
    if (
        getattr(expr, "expr_type", None) == ExpressionType.BINARY_OP
        and getattr(expr, "operator", None) == "SUBPIECE"
        and len(getattr(expr, "operands", None) or []) == 2
    ):
        source, offset = expr.operands
        if getattr(offset, "expr_type", None) != ExpressionType.CONSTANT:
            return False
        try:
            if int(getattr(offset, "value", 0) or 0) != 0:
                return False
        except (TypeError, ValueError):
            return False
        expr_bits = max(1, int(expression_smt_bit_width(expr) or 0))
        proof_bits = self._case_reduction_count_bit_width(case, accumulator_proof)
        if expr_bits != proof_bits:
            return False
        return self._parameter_matches_reduction_count_identity(source, case, accumulator_proof)
    if getattr(expr, "expr_type", None) == ExpressionType.UNARY_OP and len(getattr(expr, "operands", None) or []) == 1:
        operator = getattr(expr, "operator", None)
        if operator in {"CAST", "COPY"}:
            operand = expr.operands[0]
            expr_bits = max(1, int(expression_smt_bit_width(expr) or 0))
            operand_bits = max(1, int(expression_smt_bit_width(operand) or 0))
            proof_bits = self._case_reduction_count_bit_width(case, accumulator_proof)
            if expr_bits != operand_bits or expr_bits != proof_bits:
                return False
            return self._expression_is_full_reduction_count_view(operand, case, accumulator_proof)
        return False
    return False

def _impl__parameter_matches_reduction_count_identity(
    self,
    expr: Optional[Expression],
    case: ReturnCase,
    accumulator_proof,
) -> bool:
    if expr is None or getattr(expr, "expr_type", None) != ExpressionType.PARAMETER:
        return False
    return self._count_identity_components_compatible(
        self._parameter_expression_storage_identity_key(expr),
        self._parameter_expression_index_identity_key(expr),
        self._reduction_count_storage_identity_key(accumulator_proof),
        self._reduction_count_index_identity_key(accumulator_proof),
    )

def _impl__case_reduction_count_bit_width(
    self,
    case: ReturnCase,
    accumulator_proof,
) -> int:
    proof_bits = self._reduction_count_bit_width(accumulator_proof)
    proof_storage = self._reduction_count_storage_identity_key(accumulator_proof)
    proof_index = self._reduction_count_index_identity_key(accumulator_proof)
    for parameter in getattr(case, "parameters", None) or []:
        if not self._count_identity_components_compatible(
            self._parameter_descriptor_storage_identity_key(parameter),
            self._parameter_descriptor_index_identity_key(parameter),
            proof_storage,
            proof_index,
        ):
            continue
        try:
            size = int(parameter.get("size", 0) or 0)
        except (TypeError, ValueError):
            size = 0
        if size <= 0:
            continue
        candidate_bits = max(1, size * 8)
        if candidate_bits == proof_bits or self._accumulator_proof_supports_count_bit_width(
            case,
            accumulator_proof,
            candidate_bits,
        ):
            return candidate_bits
    return proof_bits

def _impl__reduction_count_bit_width(self, accumulator_proof) -> int:
    limit_expr = getattr(accumulator_proof, "limit_expr", None)
    return max(1, int(expression_smt_bit_width(limit_expr) or 0))
