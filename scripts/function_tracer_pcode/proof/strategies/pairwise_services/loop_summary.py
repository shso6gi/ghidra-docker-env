"""Loop-summary case handling: counted loops, phi-circular states and auxiliary refs."""

from __future__ import annotations

from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple
import hashlib
import json
from dataclasses import replace
from scripts.function_tracer_pcode.core import (
    COUNTED_LOOP_SUM_OPCODE,
    COUNTED_STATE_TRANSITION_VALUE_OPCODE,
    Condition,
    CountedLoopSummaryRef,
    CountedStateTransitionLoopSummaryRef,
    Expression,
    ExpressionType,
    LoopSummaryComparisonResult,
    LoopSummaryRef,
    LoopTermDescriptorRef,
    ReadonlyReductionRef,
    compare_loop_summaries,
)
from scripts.function_tracer_pcode.core.render_smt import _counted_loop_sum_has_exact_lowering, expression_smt_bit_width
from scripts.function_tracer_pcode.proof.strategies.pairwise_services._shared import (
    ConditionNormalizer,
    ParameterInfo,
    ReturnCase,
    UnknownReasonId,
    _RuntimeShortcutDecision,
    parameter_identity_key_from_expression,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_services._shared import (
    _PendingLoopSummaryPair,
)
from scripts.function_tracer_pcode.analysis.debug import summarize_conditions


def _impl__unknown_reason_id_for_loop_fallback(self, reason: Optional[str]):
    reason_text = str(reason or "")
    if reason_text.startswith("readonly_contract_"):
        return UnknownReasonId.READONLY_IDENTITY_MISSING
    if reason_text in {
        "semantic_key_missing",
        "semantic_key_unavailable",
        "semantic_key_none",
        "semantic_key_mismatch",
    }:
        return UnknownReasonId.READONLY_IDENTITY_MISSING
    if reason_text in {
        "loop_summary_guard_mismatch",
        "loop_summary_shape_mismatch",
        "loop_summary_unproven",
        "loop_summary_unknown",
        "loop_summary_operand_mismatch",
        "loop_summary_intrinsic_mismatch",
    }:
        from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
            classify_loop_fallback,
        )

        classification = classify_loop_fallback(reason_text)
        if len(classification.reason_ids) != 1:
            raise ValueError("loop fallback lacks one typed semantic reason")
        return classification.reason_ids[0]
    from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
        classify_loop_fallback,
    )

    classification = classify_loop_fallback(reason_text)
    if len(classification.reason_ids) != 1:
        raise ValueError("loop fallback lacks one typed semantic reason")
    return classification.reason_ids[0]


def _impl__case_pair_loop_summaries_solver_equivalent(
    self,
    left_ref,
    right_ref,
    *,
    left_case: Optional[ReturnCase],
    right_case: Optional[ReturnCase],
    semantic_parameter_sources: Sequence[ParameterInfo] = (),
) -> bool:
    if left_case is None or right_case is None:
        return False
    left_summary = getattr(left_ref, "loop_summary", None)
    right_summary = getattr(right_ref, "loop_summary", None)
    if left_summary is None or right_summary is None:
        return False
    if (
        isinstance(left_ref, CountedLoopSummaryRef)
        and isinstance(right_ref, CountedLoopSummaryRef)
        and not self._counted_loop_summary_wrapper_semantics_match(left_ref, right_ref)
    ):
        return self._case_pair_loop_summaries_solver_equivalent_core(
            left_ref,
            right_ref,
            left_case=left_case,
            right_case=right_case,
            semantic_parameter_sources=semantic_parameter_sources,
        )
    def solver_prover(obligation) -> LoopSummaryComparisonResult:
        if getattr(obligation, "proof_kind", None) != "case_aware_loop_summary_solver_equality":
            return LoopSummaryComparisonResult("unknown", "unsupported loop-summary proof obligation")
        if self._case_pair_loop_summaries_solver_equivalent_core(
            left_ref,
            right_ref,
            left_case=left_case,
            right_case=right_case,
            semantic_parameter_sources=semantic_parameter_sources,
        ):
            return LoopSummaryComparisonResult(
                "equivalent",
                "loop summaries proved by case-aware solver",
                proof_obligation=obligation,
            )
        return LoopSummaryComparisonResult(
            "unknown",
            "case-aware loop-summary solver proof failed",
            proof_obligation=obligation,
        )

    result = compare_loop_summaries(
        left_summary,
        right_summary,
        solver_prover=solver_prover,
    )
    return result.is_equivalent() is True and self._case_pair_has_runtime_guard_coverage_or_equivalence(
        left_case,
        right_case,
    )


def _impl__case_pair_loop_summaries_solver_equivalent_core(
    self,
    left_ref,
    right_ref,
    *,
    left_case: ReturnCase,
    right_case: ReturnCase,
    semantic_parameter_sources: Sequence[ParameterInfo] = (),
) -> bool:
    left_summary = getattr(left_ref, "loop_summary", None)
    right_summary = getattr(right_ref, "loop_summary", None)
    if left_summary is None or right_summary is None:
        return False
    for summary in (left_summary, right_summary):
        requires_effect_proof = getattr(summary, "requires_effect_proof", None)
        if callable(requires_effect_proof) and requires_effect_proof():
            return False
        requires_path_proof = getattr(summary, "requires_path_proof", None)
        if callable(requires_path_proof) and requires_path_proof():
            return False
    if self._loop_summary_surface_blocks_solver_equality(left_summary, right_summary):
        return False
    if self._loop_summary_constant_bias(left_summary) != self._loop_summary_constant_bias(right_summary):
        return False
    if not self._counted_loop_summary_wrapper_semantics_match(left_ref, right_ref):
        return self._case_pair_counted_loop_summaries_closed_values_equivalent(
            left_ref,
            right_ref,
            left_case=left_case,
            right_case=right_case,
            semantic_parameter_sources=semantic_parameter_sources,
        )
    left_term_key = self._loop_term_descriptor_semantic_key(left_summary)
    right_term_key = self._loop_term_descriptor_semantic_key(right_summary)
    if left_term_key is None or right_term_key is None or left_term_key != right_term_key:
        return False
    left_seed = tuple(getattr(left_summary, "seed_terms", ()) or ())
    right_seed = tuple(getattr(right_summary, "seed_terms", ()) or ())
    if len(left_seed) != len(right_seed):
        return False
    if getattr(left_summary, "seed_term_count", None) != getattr(right_summary, "seed_term_count", None):
        return False
    conditions = self._combined_summary_conditions(left_case, right_case)
    expr_pairs = (
        (getattr(left_summary, "start_expr", None), getattr(right_summary, "start_expr", None)),
        (getattr(left_summary, "limit_expr", None), getattr(right_summary, "limit_expr", None)),
        (getattr(left_summary, "step_expr", None), getattr(right_summary, "step_expr", None)),
    )
    seed_expr_pairs: List[Tuple[Expression, Expression]] = []
    for left_term, right_term in zip(left_seed, right_seed):
        if isinstance(left_term, Expression) and isinstance(right_term, Expression):
            seed_expr_pairs.append((left_term, right_term))
            continue
        if left_term != right_term:
            return False
    exprs = [expr for pair in expr_pairs for expr in pair if expr is not None]
    exprs.extend(expr for pair in seed_expr_pairs for expr in pair)
    exprs.extend(condition.expression for condition in conditions or [] if condition is not None)
    parameters = self._collect_intrinsic_parameter_specs(
        left_case,
        right_case,
        *exprs,
        semantic_parameter_sources=semantic_parameter_sources,
    )
    if parameters is None:
        return False
    if self._condition_set_is_unsat(conditions, parameters):
        return True
    for left_expr, right_expr in expr_pairs:
        if left_expr is None or right_expr is None:
            return False
        if not self._prove_intrinsic_equivalence_under_conditions(
            left_expr,
            right_expr,
            conditions,
            parameters,
        ):
            return False
    for left_expr, right_expr in seed_expr_pairs:
        if not self._prove_intrinsic_equivalence_under_conditions(
            left_expr,
            right_expr,
            conditions,
            parameters,
        ):
            return False
    if not self._case_pair_has_runtime_guard_coverage_or_equivalence(left_case, right_case):
        return False
    return True


def _impl__case_pair_counted_loop_summaries_closed_values_equivalent(
    self,
    left_ref,
    right_ref,
    *,
    left_case: ReturnCase,
    right_case: ReturnCase,
    semantic_parameter_sources: Sequence[ParameterInfo] = (),
) -> bool:
    left_expr = getattr(left_case, "value_expr", None)
    right_expr = getattr(right_case, "value_expr", None)
    if getattr(left_expr, "runtime_ref", None) is not left_ref:
        return False
    if getattr(right_expr, "runtime_ref", None) is not right_ref:
        return False
    if not isinstance(left_ref, CountedLoopSummaryRef) or not isinstance(right_ref, CountedLoopSummaryRef):
        return False
    result_size = self._case_pair_comparison_result_size(left_case, right_case)
    if result_size is None:
        return False
    if not self._counted_loop_refs_allow_affine_value_proof(left_ref, right_ref):
        return False
    conditions = self._combined_summary_conditions(left_case, right_case)
    left_guards, left_guards_complete = self._runtime_summary_guard_conditions_from_expression(left_expr)
    right_guards, right_guards_complete = self._runtime_summary_guard_conditions_from_expression(right_expr)
    if not left_guards_complete or not right_guards_complete:
        return False
    for guard in tuple(left_guards) + tuple(right_guards):
        if guard not in conditions:
            conditions.append(guard)
    exprs = [left_expr, right_expr]
    exprs.extend(condition.expression for condition in conditions or [] if condition is not None)
    parameters = self._collect_intrinsic_parameter_specs(
        left_case,
        right_case,
        *exprs,
        semantic_parameter_sources=semantic_parameter_sources,
    )
    if parameters is None:
        return False
    if not self._counted_loop_affine_widths_are_safe(left_expr, right_expr, result_size, parameters):
        return False
    left_closed = self._counted_loop_affine_closed_expression(
        left_expr,
        result_size=result_size,
        conditions=conditions,
        parameters=parameters,
    )
    right_closed = self._counted_loop_affine_closed_expression(
        right_expr,
        result_size=result_size,
        conditions=conditions,
        parameters=parameters,
    )
    if left_closed is None or right_closed is None:
        return False
    if not self._case_pair_has_runtime_guard_coverage_or_equivalence(left_case, right_case):
        return False
    return self._prove_intrinsic_equivalence_under_conditions(
        left_closed,
        right_closed,
        conditions,
        parameters,
    )


def _impl__loop_summary_constant_bias(self, summary) -> int:
    result_size = int(getattr(summary, "result_size", 0) or 0)
    if result_size <= 0:
        descriptor = getattr(summary, "term_descriptor", None)
        result_size = int(getattr(descriptor, "result_size", 0) or 0)
    result_size = max(1, result_size or 4)
    bits = max(1, result_size * 8)
    mask = (1 << bits) - 1
    try:
        return int(getattr(summary, "constant_bias", 0) or 0) & mask
    except (TypeError, ValueError):
        return 0


def _impl__counted_loop_summary_wrapper_semantics_match(self, left_ref, right_ref) -> bool:
    if not isinstance(left_ref, CountedLoopSummaryRef) or not isinstance(right_ref, CountedLoopSummaryRef):
        return True
    left_bias = self._counted_loop_ref_constant_bias(left_ref)
    right_bias = self._counted_loop_ref_constant_bias(right_ref)
    return (
        int(getattr(left_ref, "induction_step", 0) or 0)
        == int(getattr(right_ref, "induction_step", 0) or 0)
        and max(1, int(getattr(left_ref, "result_size", 0) or 0))
        == max(1, int(getattr(right_ref, "result_size", 0) or 0))
        and bool(getattr(left_ref, "signed_loop", False)) == bool(getattr(right_ref, "signed_loop", False))
        and tuple(getattr(left_ref, "residue_cases", ()) or ())
        == tuple(getattr(right_ref, "residue_cases", ()) or ())
        and tuple(getattr(left_ref, "residue_bias_terms", ()) or ())
        == tuple(getattr(right_ref, "residue_bias_terms", ()) or ())
        and left_bias == right_bias
    )


def _impl__counted_loop_ref_constant_bias(self, ref) -> int:
    result_size = max(1, int(getattr(ref, "result_size", 0) or 4))
    bits = max(1, result_size * 8)
    mask = (1 << bits) - 1
    try:
        return int(getattr(ref, "constant_bias", 0) or 0) & mask
    except (TypeError, ValueError):
        return 0


def _impl__loop_summary_surface_blocks_solver_equality(self, left_summary, right_summary) -> bool:
    if getattr(left_summary, "loop_var_unit", None) != getattr(right_summary, "loop_var_unit", None):
        return True
    left_profile = getattr(left_summary, "side_effect_profile", None)
    right_profile = getattr(right_summary, "side_effect_profile", None)
    if left_profile is None or right_profile is None:
        return True
    left_profile_key = left_profile.stable_key()
    right_profile_key = right_profile.stable_key()
    if left_profile_key is None or right_profile_key is None or left_profile_key != right_profile_key:
        return True
    left_cases = tuple(getattr(left_summary, "cases", ()) or ())
    right_cases = tuple(getattr(right_summary, "cases", ()) or ())
    if len(left_cases) != len(right_cases):
        return True
    left_case_keys = tuple(case.stable_key() for case in left_cases)
    right_case_keys = tuple(case.stable_key() for case in right_cases)
    if any(key is None for key in left_case_keys + right_case_keys):
        return True
    return left_case_keys != right_case_keys


def _impl__loop_term_descriptor_semantic_key(self, summary) -> Optional[Tuple[Any, ...]]:
    descriptor = getattr(summary, "term_descriptor", None)
    semantic_key = getattr(descriptor, "semantic_key", None)
    if callable(semantic_key):
        try:
            key = semantic_key()
        except Exception:
            return None
        return key
    return None


def _impl__runtime_loop_contract_shortcut_decision(
    self,
    left_ref,
    right_ref,
    *,
    result_size: Optional[int] = None,
) -> _RuntimeShortcutDecision:
    left_loop_summary = getattr(left_ref, "loop_summary", None)
    right_loop_summary = getattr(right_ref, "loop_summary", None)
    if left_loop_summary is None and right_loop_summary is None:
        return _RuntimeShortcutDecision(False, False, reason="not_loop_contract")
    return self._runtime_refs_shortcut_decision(left_ref, right_ref, result_size=result_size)


def _impl__loop_limit_storage_identity_key(self, limit_key: tuple) -> Optional[tuple]:
    normalized = tuple(limit_key or ())
    if len(normalized) != 2:
        return None
    tag, value = normalized
    if tag == "loop_limit_parameter_storage":
        value_tuple = tuple(value or ())
        if len(value_tuple) == 2 and value_tuple[0] == "storage_identity":
            return ("parameter_storage", tuple(value_tuple[1]))
        return ("parameter_storage", value_tuple)
    if tag == "loop_limit_count_storage_identity":
        return ("parameter_storage", tuple(value or ()))
    return None


def _impl__loop_limit_storage_key_is_legacy_index_compatible(
    self,
    storage_limit_key: tuple,
    index_limit_key: tuple,
    storage_ref: ReadonlyReductionRef,
    index_ref: ReadonlyReductionRef,
) -> bool:
    if not storage_limit_key or storage_limit_key[0] not in {
        "loop_limit_parameter_storage",
        "loop_limit_count_storage_identity",
    }:
        return False
    if len(index_limit_key) != 2 or index_limit_key[0] != "loop_limit_parameter":
        return False
    if self._readonly_count_storage_identity_key(index_ref) is not None:
        return False
    storage_index = self._readonly_count_index_identity_key(storage_ref)
    index_identity = self._readonly_count_index_identity_key(index_ref)
    try:
        limit_index_identity = ("parameter", int(index_limit_key[1]))
    except (TypeError, ValueError):
        return False
    return (
        storage_index is not None
        and index_identity is not None
        and storage_index == index_identity
        and storage_index == limit_index_identity
    )


def _impl__counted_loop_summary_runtime_profile_key(self, counted_ref: CountedLoopSummaryRef) -> Tuple[Any, ...]:
    return (
        "counted_loop_summary_profile_ref",
        max(1, int(getattr(counted_ref, "result_size", 0) or 0)),
        int(getattr(counted_ref, "induction_step", 0) or 0),
        bool(getattr(counted_ref, "signed_loop", False)),
        tuple(getattr(counted_ref, "residue_cases", ()) or ()),
        tuple(
            (
                int(modulus),
                int(residue),
                self._method_b_value_key_or_none(bias_expr),
            )
            for modulus, residue, bias_expr in tuple(getattr(counted_ref, "residue_bias_terms", ()) or ())
        ),
        self._counted_loop_ref_constant_bias(counted_ref),
    )


def _impl__counted_loop_summary_loop_profile_key(self, loop_summary: Optional[LoopSummaryRef]) -> Optional[Tuple[Any, ...]]:
    if loop_summary is None:
        return None
    descriptor = getattr(loop_summary, "term_descriptor", None)
    descriptor_key = self._method_b_key_with_explicit_optional_none(
        self._semantic_key_or_stable_key_or_none(descriptor)
    )
    side_effect_key = self._method_b_key_with_explicit_optional_none(
        self._semantic_key_or_stable_key_or_none(getattr(loop_summary, "side_effect_profile", None))
    )
    if descriptor_key is None or side_effect_key is None:
        return None
    return (
        "counted_loop_summary_loop_profile",
        getattr(loop_summary, "loop_var_unit", None) or "unknown_loop_var_unit",
        self._method_b_value_key_or_none(getattr(loop_summary, "start_expr", None)),
        self._method_b_value_key_or_none(getattr(loop_summary, "limit_expr", None)),
        self._method_b_value_key_or_none(getattr(loop_summary, "step_expr", None)),
        descriptor_key,
        side_effect_key,
        tuple(
            self._method_b_key_with_explicit_optional_none(
                getattr(case, "stable_key", lambda: None)()
            )
            for case in tuple(getattr(loop_summary, "cases", ()) or ())
        ),
    )


def _impl__counted_loop_summary_contract_key(self, counted_ref: CountedLoopSummaryRef) -> Optional[Tuple[Any, ...]]:
    runtime_key = self._counted_loop_summary_runtime_profile_key(counted_ref)
    loop_summary = getattr(counted_ref, "loop_summary", None)
    loop_key = self._counted_loop_summary_loop_profile_key(loop_summary)
    if runtime_key is None or loop_key is None:
        return None
    residue_bias_terms = tuple(
        (
            int(modulus),
            int(residue),
            self._method_b_value_key_or_none(bias_expr),
        )
        for modulus, residue, bias_expr in tuple(getattr(counted_ref, "residue_bias_terms", ()) or ())
    )
    if any(term[2] is None for term in residue_bias_terms):
        return None
    return (
        "counted_loop_summary_contract",
        runtime_key,
        loop_key,
        max(1, int(getattr(counted_ref, "result_size", 0) or 0)),
        int(getattr(counted_ref, "induction_step", 0) or 0),
        bool(getattr(counted_ref, "signed_loop", False)),
        tuple(getattr(counted_ref, "residue_cases", ()) or ()),
        residue_bias_terms,
        self._counted_loop_ref_constant_bias(counted_ref),
        tuple(case.stable_key() for case in tuple(getattr(loop_summary, "cases", ()) or ())),
    )


def _impl__counted_loop_summary_count_identities(self, counted_ref: CountedLoopSummaryRef) -> Tuple[Tuple[Any, ...], ...]:
    identities: List[Tuple[Any, ...]] = []
    for value in (
        getattr(counted_ref, "start_expr", None),
        getattr(counted_ref, "limit_expr", None),
        getattr(counted_ref, "step_expr", None),
    ):
        key = self._method_b_value_key_or_none(value)
        if key is not None:
            identities.append(("expression", key))
    loop_summary = getattr(counted_ref, "loop_summary", None)
    for value in (
        getattr(loop_summary, "start_expr", None),
        getattr(loop_summary, "limit_expr", None),
        getattr(loop_summary, "step_expr", None),
    ):
        key = self._method_b_value_key_or_none(value)
        if key is not None:
            identities.append(("loop_expression", key))
    return tuple(dict.fromkeys(identities))


def _impl__phi_circular_semantic_recurrence_stage_evidence(
    self,
    *,
    object_target_key: Tuple[Any, ...],
    diagnostic: Tuple[Any, ...],
    diagnostic_fields: Dict[str, Any],
) -> Tuple[Any, ...]:
    origin_relation = diagnostic_fields.get("phi_origin_shape_relation")
    guard_pair = (
        "guard_condition_pair",
        ("left_guard_literals", diagnostic_fields.get("left_guard_literals")),
        ("right_guard_literals", diagnostic_fields.get("right_guard_literals")),
        ("relation", "exact_match"),
    )
    summary_binding = (
        "summary_parameter_binding",
        ("left_value_shape", diagnostic_fields.get("left_value_shape")),
        ("right_value_shape", diagnostic_fields.get("right_value_shape")),
        ("value_shape_relation", diagnostic_fields.get("value_shape_relation")),
        ("binding_status", "object_evidence_collected"),
    )
    phi_origin_pair = (
        "phi_origin_pair",
        ("relation", "exact_match"),
        ("phi_origin_shape_relation", origin_relation),
    )
    guard_transition = (
        "guard_transition_relation",
        ("relation", "exact_match"),
        ("transition_status", "object_evidence_collected"),
        ("phi_origin_pair", phi_origin_pair),
        ("guard_condition_pair", guard_pair),
        ("left_value_shape", diagnostic_fields.get("left_value_shape")),
        ("right_value_shape", diagnostic_fields.get("right_value_shape")),
        ("value_shape_relation", diagnostic_fields.get("value_shape_relation")),
    )
    recurrence_relation = (
        "recurrence_relation",
        ("relation", "exact_match"),
        ("recurrence_status", "object_evidence_collected"),
        ("summary_parameter_binding", summary_binding),
        ("guard_transition_relation", guard_transition),
        ("left_value_shape", diagnostic_fields.get("left_value_shape")),
        ("right_value_shape", diagnostic_fields.get("right_value_shape")),
        ("value_shape_relation", diagnostic_fields.get("value_shape_relation")),
    )
    guard_query = self._semantic_recurrence_query_plan(
        query_id="phi_circular_guard_transition",
        query_stage="phi_circular_guard_condition_lowering",
        assertion_kind="guard_transition_equivalence",
        object_target_key=object_target_key,
        object_content=(
            ("guard_transition_relation", guard_transition),
        ),
    )
    recurrence_query = self._semantic_recurrence_query_plan(
        query_id="recursive_summary_recurrence",
        query_stage="recursive_summary_guard_equivalence",
        assertion_kind="summary_recurrence_equivalence",
        object_target_key=object_target_key,
        object_content=(
            ("summary_parameter_binding", summary_binding),
            ("recurrence_relation", recurrence_relation),
        ),
    )
    return (
        (
            "unresolved_expression_stage_evidence",
            ("proof_stage", "phi_circular_guard_condition_lowering"),
            ("status", "object_evidence_collected"),
            ("object_target_key", object_target_key),
            ("pair_lowering_diagnostic", diagnostic),
            ("phi_origin_pair", phi_origin_pair),
            ("guard_condition_pair", guard_pair),
            ("guard_transition_relation", guard_transition),
            ("typed_lowering_rule", "phi_circular_guard_shape_preserving"),
            (
                "proof_query_plan",
                (guard_query,),
            ),
            (
                "required_semantic_proof",
                (
                    "phi_incoming_values",
                    "guard_transition_relation",
                ),
            ),
        ),
        (
            "unresolved_expression_stage_evidence",
            ("proof_stage", "recursive_summary_guard_equivalence"),
            ("status", "object_evidence_collected"),
            ("object_target_key", object_target_key),
            ("pair_lowering_diagnostic", diagnostic),
            ("phi_origin_pair", phi_origin_pair),
            ("guard_condition_pair", guard_pair),
            ("summary_parameter_binding", summary_binding),
            ("recurrence_relation", recurrence_relation),
            (
                "proof_query_plan",
                (recurrence_query,),
            ),
            (
                "required_semantic_proof",
                (
                    "recursive_summary_parameter_binding",
                    "loop_summary_recurrence_semantics",
                ),
            ),
        ),
    )


def _impl__semantic_recurrence_query_plan(
    cls,
    *,
    query_id: str,
    query_stage: str,
    assertion_kind: str,
    object_target_key: Tuple[Any, ...],
    object_content: Tuple[Tuple[str, Any], ...],
) -> Tuple[Any, ...]:
    query_body = (
        ("query_id", query_id),
        ("query_stage", query_stage),
        ("expected_solver_result", "unsat"),
        ("assertion_kind", assertion_kind),
        ("object_target_key", object_target_key),
        ("object_content", object_content),
    )
    query_hash = cls._stable_semantic_recurrence_hash(query_body)
    return (
        "semantic_recurrence_query",
        ("query_id", query_id),
        ("query_stage", query_stage),
        ("query_status", "planned"),
        ("expected_solver_result", "unsat"),
        ("proof_source", "object_derived_query_plan"),
        ("assertion_kind", assertion_kind),
        ("query_hash", query_hash),
        ("object_content", object_content),
        *object_content,
    )


def _impl__stable_semantic_recurrence_hash(value: Any) -> str:
    canonical = json.dumps(
        _impl__semantic_recurrence_jsonable(value),
        sort_keys=True,
        separators=(",", ":"),
    )
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def _impl__semantic_recurrence_jsonable(value: Any) -> Any:
    if isinstance(value, tuple):
        return [_impl__semantic_recurrence_jsonable(item) for item in value]
    if isinstance(value, list):
        return [_impl__semantic_recurrence_jsonable(item) for item in value]
    if isinstance(value, dict):
        return {
            str(key): _impl__semantic_recurrence_jsonable(item)
            for key, item in sorted(value.items(), key=lambda entry: str(entry[0]))
        }
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            return _impl__semantic_recurrence_jsonable(stable_key())
        except Exception:
            pass
    to_dict = getattr(value, "to_dict", None)
    if callable(to_dict):
        try:
            return _impl__semantic_recurrence_jsonable(to_dict())
        except Exception:
            pass
    if isinstance(value, (str, int, float, bool)) or value is None:
        return value
    return repr(value)


def _impl__phi_circular_origin_shape_relation(
    cls,
    left_unknowns: Tuple[Any, ...],
    right_unknowns: Tuple[Any, ...],
) -> Tuple[Any, ...]:
    left_shapes = tuple(
        cls._phi_circular_unknown_origin_shape_key(unknown)
        for unknown in left_unknowns
    )
    right_shapes = tuple(
        cls._phi_circular_unknown_origin_shape_key(unknown)
        for unknown in right_unknowns
    )
    if not left_shapes or not right_shapes:
        relation = "origin_shape_unavailable"
    elif any(shape is None for shape in left_shapes + right_shapes):
        relation = "origin_shape_unavailable"
    elif left_shapes == right_shapes:
        relation = "exact_match"
    else:
        relation = "origin_shape_mismatch"
    return (
        "phi_origin_shape_relation",
        ("relation", relation),
        ("left_origin_shapes", left_shapes),
        ("right_origin_shapes", right_shapes),
    )


def _impl__phi_circular_unknown_origin_shape_key(cls, unknown: Any) -> Optional[Tuple[Any, ...]]:
    if not cls._unknown_expression_is_originated_phi_circular(unknown):
        return None
    runtime_ref = getattr(unknown, "runtime_ref", None)
    origin_key = cls._stable_key_or_none(getattr(runtime_ref, "origin_ref", None))
    return cls._pcode_origin_cross_binary_shape_key(origin_key)


def _impl__find_phi_origin_shape_relation(cls, value: Any) -> Optional[Tuple[Any, ...]]:
    normalized = cls._normalize_nested_tuple(value)
    if isinstance(normalized, tuple):
        if normalized and normalized[0] == "phi_origin_shape_relation":
            if (
                len(normalized) == 2
                and isinstance(normalized[1], tuple)
                and normalized[1]
                and normalized[1][0] == "phi_origin_shape_relation"
            ):
                return normalized[1]
            return normalized
        for item in normalized:
            found = cls._find_phi_origin_shape_relation(item)
            if found is not None:
                return found
    if isinstance(normalized, list):
        for item in normalized:
            found = cls._find_phi_origin_shape_relation(item)
            if found is not None:
                return found
    if isinstance(normalized, dict):
        for item in normalized.values():
            found = cls._find_phi_origin_shape_relation(item)
            if found is not None:
                return found
    return None


def _impl__phi_circular_case_value_shape(
    case_shape: Optional[Tuple[Any, ...]],
) -> Optional[Any]:
    if not case_shape or len(case_shape) < 2:
        return None
    value_item = case_shape[1]
    if isinstance(value_item, tuple) and len(value_item) == 2 and value_item[0] == "value":
        return value_item[1]
    return None


def _impl__phi_circular_unknown_count_relation(
    left_count: int,
    right_count: int,
) -> Tuple[Any, ...]:
    relation = "equal" if int(left_count) == int(right_count) else "count_mismatch"
    return (
        "unknown_count_relation",
        ("relation", relation),
        ("left_count", int(left_count)),
        ("right_count", int(right_count)),
    )


def _impl__phi_circular_value_shape_relation(
    cls,
    left_value: Optional[Any],
    right_value: Optional[Any],
) -> Tuple[Any, ...]:
    left_summary_index = cls._phi_circular_summary_parameter_index(left_value)
    right_summary_index = cls._phi_circular_summary_parameter_index(right_value)
    left_constant = cls._phi_circular_constant_value(left_value)
    right_constant = cls._phi_circular_constant_value(right_value)
    if left_value is None or right_value is None:
        relation = "shape_unavailable"
    elif left_value == right_value:
        relation = "exact_match"
    elif left_summary_index is not None and right_summary_index is not None:
        relation = "summary_parameter_shift"
    elif left_summary_index is not None and right_constant is not None:
        relation = "left_summary_parameter_right_constant"
    elif left_constant is not None and right_summary_index is not None:
        relation = "left_constant_right_summary_parameter"
    else:
        relation = "shape_mismatch"
    return (
        "value_shape_relation",
        ("relation", relation),
        ("left_kind", cls._phi_circular_shape_kind(left_value)),
        ("right_kind", cls._phi_circular_shape_kind(right_value)),
        ("left_summary_parameter_index", left_summary_index),
        ("right_summary_parameter_index", right_summary_index),
        ("left_constant_value", left_constant),
        ("right_constant_value", right_constant),
    )


def _impl__phi_circular_shape_kind(value: Optional[Any]) -> str:
    if isinstance(value, tuple) and value:
        return str(value[0])
    return "unavailable"


def _impl__phi_circular_summary_parameter_index(value: Optional[Any]) -> Optional[int]:
    if not (isinstance(value, tuple) and len(value) == 4 and value[0] == "parameter"):
        return None
    name = str(value[1] or "")
    if not name.startswith("summary_rec_"):
        return None
    try:
        index = int(value[2])
    except (TypeError, ValueError):
        return None
    return index if index >= 0 else None


def _impl__phi_circular_constant_value(value: Optional[Any]) -> Optional[int]:
    if not (isinstance(value, tuple) and len(value) == 3 and value[0] == "const"):
        return None
    try:
        return int(value[1])
    except (TypeError, ValueError):
        return None


def _impl__phi_circular_case_condition_literals(
    self,
    case: ReturnCase,
) -> Tuple[Any, ...]:
    literals: List[Any] = []
    for condition in getattr(case, "conditions", None) or ():
        literals.extend(self._phi_circular_condition_literals(condition))
    return tuple(sorted(literals, key=repr))


def _impl__phi_circular_condition_literals(self, condition: Any) -> Tuple[Any, ...]:
    if condition is None:
        return ()
    unknowns: List[Any] = []
    shape = self._phi_circular_expression_shape_key(
        getattr(condition, "expression", None),
        unknowns,
    )
    if shape is None:
        return ()
    return tuple(
        sorted(
            self._phi_circular_boolean_literals_from_shape(
                shape,
                polarity=not bool(getattr(condition, "negated", False)),
            ),
            key=repr,
        )
    )


def _impl__phi_circular_boolean_literals_from_shape(
    self,
    shape: Any,
    *,
    polarity: bool,
) -> Tuple[Any, ...]:
    if (
        isinstance(shape, tuple)
        and len(shape) == 5
        and shape[0] == "binary"
        and shape[1] == "BOOL_AND"
        and polarity
    ):
        return (
            *self._phi_circular_boolean_literals_from_shape(shape[3], polarity=True),
            *self._phi_circular_boolean_literals_from_shape(shape[4], polarity=True),
        )
    if (
        isinstance(shape, tuple)
        and len(shape) == 4
        and shape[0] == "unary"
        and shape[1] == "BOOL_NEGATE"
    ):
        return self._phi_circular_boolean_literals_from_shape(
            shape[3],
            polarity=not polarity,
        )
    return (("guard_literal", bool(polarity), shape),)


def _impl__phi_circular_opposing_condition_literals(
    left_literals: Tuple[Any, ...],
    right_literals: Tuple[Any, ...],
) -> Tuple[Any, ...]:
    left_by_atom = {
        item[2]: bool(item[1])
        for item in left_literals
        if isinstance(item, tuple) and len(item) == 3 and item[0] == "guard_literal"
    }
    opposing: List[Any] = []
    for item in right_literals:
        if not (isinstance(item, tuple) and len(item) == 3 and item[0] == "guard_literal"):
            continue
        atom = item[2]
        right_polarity = bool(item[1])
        if atom in left_by_atom and left_by_atom[atom] != right_polarity:
            opposing.append(("opposing_guard_literal", atom))
    return tuple(sorted(opposing, key=repr))


def _impl__collect_phi_circular_origin_details(self, expr: Any) -> Tuple[Any, ...]:
    details: List[Tuple[Any, ...]] = []
    seen = set()
    for unknown in self._collect_unknown_expression_nodes(expr):
        runtime_ref = getattr(unknown, "runtime_ref", None)
        if getattr(runtime_ref, "kind", None) != "opaque_unknown":
            continue
        if getattr(runtime_ref, "reason", None) != "phi_circular":
            continue
        if getattr(runtime_ref, "origin_kind", None) != "multiequal_pcode_op":
            continue
        origin_key = self._stable_key_or_none(getattr(runtime_ref, "origin_ref", None))
        if origin_key is None:
            continue
        item = (
            "phi_origin",
            ("runtime_ref", self._diagnostic_key_or_semantic_key_or_stable_key_or_none(runtime_ref)),
            ("origin_kind", "multiequal_pcode_op"),
            ("pcode_op_ref", origin_key),
            ("unknown_expression", self._expression_runtime_object_key(unknown)),
            ("bit_width", int(expression_smt_bit_width(unknown) or 0) or None),
        )
        if item in seen:
            continue
        seen.add(item)
        details.append(item)
    return tuple(sorted(details, key=repr))


def _impl__value_contains_originated_phi_circular(cls, value: Any) -> bool:
    normalized = cls._normalize_nested_tuple(value)
    if isinstance(normalized, tuple):
        if cls._tuple_is_originated_phi_circular_runtime_ref(normalized):
            return True
        return any(cls._value_contains_originated_phi_circular(item) for item in normalized)
    if isinstance(normalized, list):
        return any(cls._value_contains_originated_phi_circular(item) for item in normalized)
    if isinstance(normalized, dict):
        return any(
            cls._value_contains_originated_phi_circular(key)
            or cls._value_contains_originated_phi_circular(item)
            for key, item in normalized.items()
        )
    return False


def _impl__object_target_contains_originated_phi_circular(cls, value: Any) -> bool:
    if isinstance(value, tuple):
        if cls._tuple_is_originated_phi_circular_runtime_ref(value):
            return True
        return any(cls._object_target_contains_originated_phi_circular(item) for item in value)
    if isinstance(value, list):
        return any(cls._object_target_contains_originated_phi_circular(item) for item in value)
    if isinstance(value, dict):
        return any(
            cls._object_target_contains_originated_phi_circular(key)
            or cls._object_target_contains_originated_phi_circular(item)
            for key, item in value.items()
        )
    return False


def _impl__tuple_is_originated_phi_circular_runtime_ref(value: Tuple[Any, ...]) -> bool:
    return (
        len(value) >= 6
        and value[0] == "opaque_unknown"
        and value[1] == "phi_circular"
        and value[4] == "multiequal_pcode_op"
        and value[5] is not None
    )


def _impl__method_b_loop_value_object_key(self, expr: Any) -> Tuple[Any, ...]:
    runtime_ref = getattr(expr, "runtime_ref", None)
    loop_summary = getattr(runtime_ref, "loop_summary", None)
    return (
        "method_b_loop_value",
        self._semantic_key_or_stable_key_or_none(runtime_ref),
        self._semantic_key_or_stable_key_or_none(loop_summary),
        self._method_b_expression_runtime_object_key(expr),
    )


def _impl__case_pair_loop_summary_safe_fallback_reason(
    self,
    case1: ReturnCase,
    case2: ReturnCase,
) -> Optional[str]:
    return self._loop_summary_safe_fallback_reason_for_values(
        case1.value_expr,
        case2.value_expr,
        left_case=case1,
        right_case=case2,
    )


def _impl__loop_summary_safe_fallback_reason_for_values(
    self,
    left: Optional[Expression],
    right: Optional[Expression],
    *,
    left_case: Optional[ReturnCase],
    right_case: Optional[ReturnCase],
) -> Optional[str]:
    if left is None or right is None:
        return None
    left_has_loop = self._expression_contains_loop_summary_runtime(left)
    right_has_loop = self._expression_contains_loop_summary_runtime(right)
    if not left_has_loop and not right_has_loop:
        return None
    if left_case is not None and right_case is not None and self._cases_have_equivalent_readonly_reduction_proof(
        left_case,
        right_case,
    ):
        return None
    if left.expr_type == ExpressionType.INTRINSIC and right.expr_type == ExpressionType.INTRINSIC:
        loop_contract_decision = self._runtime_loop_contract_shortcut_decision(
            getattr(left, "runtime_ref", None),
            getattr(right, "runtime_ref", None),
            result_size=self._case_pair_readonly_contract_result_size(left_case, right_case),
        )
        if self.debug and not loop_contract_decision.equivalent:
            self._debug_print(
                "readonly loop contract shortcut declined: "
                f"{loop_contract_decision.reason}"
            )
        if loop_contract_decision.equivalent:
            if loop_contract_decision.requires_guard_equivalence and (
                left_case is None
                or right_case is None
                or not self._case_pair_has_runtime_guard_coverage_or_equivalence(left_case, right_case)
            ):
                return "loop_summary_guard_mismatch"
            return None
        if left_has_loop and right_has_loop and loop_contract_decision.reason != "not_loop_contract":
            return loop_contract_decision.reason
    if left_has_loop != right_has_loop:
        if (
            left_case is not None
            and right_case is not None
            and self._case_pair_has_one_sided_counted_loop_summary(left, right, left_case, right_case)
        ):
            return "counted_loop_summary_expression_proof_missing"
        return "loop_summary_shape_mismatch"
    if left.expr_type != right.expr_type:
        return "loop_summary_shape_mismatch"

    if left.expr_type == ExpressionType.INTRINSIC:
        left_ref = getattr(left, "runtime_ref", None)
        right_ref = getattr(right, "runtime_ref", None)
        if (
            getattr(left_ref, "loop_summary", None) is not None
            or getattr(right_ref, "loop_summary", None) is not None
        ):
            decision = self._runtime_refs_shortcut_decision(
                left_ref,
                right_ref,
                result_size=self._case_pair_readonly_contract_result_size(left_case, right_case),
            )
            if self.debug and not decision.equivalent:
                self._debug_print(
                    "runtime refs shortcut declined: "
                    f"{decision.reason}"
                )
            if not decision.equivalent:
                return decision.reason
            if decision.requires_guard_equivalence and (
                left_case is None
                or right_case is None
                or not self._case_pair_has_runtime_guard_coverage_or_equivalence(left_case, right_case)
            ):
                return "loop_summary_guard_mismatch"
        if getattr(left, "opcode", None) != getattr(right, "opcode", None):
            return "loop_summary_intrinsic_mismatch"
        if (getattr(left, "name", None) or "") != (getattr(right, "name", None) or ""):
            return "loop_summary_intrinsic_mismatch"
        left_operands = list(getattr(left, "operands", []) or [])
        right_operands = list(getattr(right, "operands", []) or [])
        if len(left_operands) != len(right_operands):
            return "loop_summary_operand_mismatch"
        for left_operand, right_operand in zip(left_operands, right_operands):
            reason = self._loop_summary_safe_fallback_reason_for_values(
                left_operand,
                right_operand,
                left_case=left_case,
                right_case=right_case,
            )
            if reason is not None:
                return reason
        return None

    left_operands = list(getattr(left, "operands", []) or [])
    right_operands = list(getattr(right, "operands", []) or [])
    if len(left_operands) != len(right_operands):
        return "loop_summary_shape_mismatch"
    for left_operand, right_operand in zip(left_operands, right_operands):
        reason = self._loop_summary_safe_fallback_reason_for_values(
            left_operand,
            right_operand,
            left_case=left_case,
            right_case=right_case,
        )
        if reason is not None:
            return reason
    return None


def _impl__expression_contains_loop_summary_runtime(self, expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    runtime_ref = getattr(expr, "runtime_ref", None)
    if getattr(runtime_ref, "loop_summary", None) is not None:
        return True
    if expr.expr_type == ExpressionType.PHI and getattr(expr, "value", None):
        for condition, value in expr.value:
            if condition is not None and self._expression_contains_loop_summary_runtime(condition.expression):
                return True
            if self._expression_contains_loop_summary_runtime(value):
                return True
        return False
    return any(
        self._expression_contains_loop_summary_runtime(operand)
        for operand in getattr(expr, "operands", []) or []
    )


def _impl__case_pair_counted_loop_summary_matches_closed_expression(
    self,
    left_case: ReturnCase,
    right_case: ReturnCase,
    *,
    base_ctx: Optional[Mapping[str, Any]] = None,
) -> bool:
    left = getattr(left_case, "value_expr", None)
    right = getattr(right_case, "value_expr", None)
    left_counted = self._is_provable_counted_loop_summary_value(left, left_case)
    right_counted = self._is_provable_counted_loop_summary_value(right, right_case)
    if left_counted == right_counted:
        if self.debug and (left_counted or right_counted or self._expression_contains_loop_summary_runtime(left) or self._expression_contains_loop_summary_runtime(right)):
            self._debug_print(f"counted-vs-closed proof skipped: left_counted={left_counted}, right_counted={right_counted}")
        return False
    closed_expr = right if left_counted else left
    if self._expression_contains_loop_summary_runtime(closed_expr):
        return False
    comparison_result_size = self._case_pair_comparison_result_size(left_case, right_case)
    if comparison_result_size is None:
        return False

    conditions = self._combined_summary_conditions(left_case, right_case)
    for case in (left_case, right_case):
        for guard in self._runtime_summary_guard_conditions_from_expression(case.value_expr)[0]:
            if guard not in conditions:
                conditions.append(guard)
    parameters = self._collect_intrinsic_parameter_specs(
        left_case,
        right_case,
        left,
        right,
        *(condition.expression for condition in conditions or [] if condition is not None),
        semantic_parameter_sources=self._auxiliary_semantic_parameter_sources(base_ctx),
    )
    if parameters is None:
        if self.debug:
            self._debug_print("counted-vs-closed proof skipped: missing parameter specs")
        return False
    if self._condition_set_is_unsat(conditions, parameters):
        return True
    if self._prove_counted_loop_closed_expression_candidates(
        counted=left if left_counted else right,
        closed=right if left_counted else left,
        counted_case=left_case if left_counted else right_case,
        result_size=comparison_result_size,
        conditions=conditions,
        parameters=parameters,
    ):
        if self.debug:
            self._debug_print("counted-vs-closed proof discharged by SMT candidate")
        return True
    proved = self._prove_intrinsic_equivalence_under_conditions(
        left,
        right,
        conditions,
        parameters,
    )
    if self.debug:
        self._debug_print(f"counted-vs-closed proof SMT result: {proved}")
    return proved


def _impl__case_pair_counted_loop_summaries_match_by_closed_values(
    self,
    left_case: ReturnCase,
    right_case: ReturnCase,
    *,
    base_ctx: Optional[Mapping[str, Any]] = None,
) -> bool:
    left = getattr(left_case, "value_expr", None)
    right = getattr(right_case, "value_expr", None)
    if not self._is_provable_counted_loop_summary_value(left, left_case):
        return False
    if not self._is_provable_counted_loop_summary_value(right, right_case):
        return False
    comparison_result_size = self._case_pair_comparison_result_size(left_case, right_case)
    if comparison_result_size is None:
        return False

    conditions = self._combined_summary_conditions(left_case, right_case)
    any_runtime_guard = False
    for case in (left_case, right_case):
        guards, guards_complete = self._runtime_summary_guard_conditions_from_expression(case.value_expr)
        if not guards_complete:
            return False
        if guards:
            any_runtime_guard = True
        for guard in guards:
            if guard not in conditions:
                conditions.append(guard)
    if not any_runtime_guard:
        if self.debug:
            self._debug_print("counted-vs-counted value proof skipped: no runtime summary guards")
        return False
    parameters = self._collect_intrinsic_parameter_specs(
        left_case,
        right_case,
        left,
        right,
        *(condition.expression for condition in conditions or [] if condition is not None),
        semantic_parameter_sources=self._auxiliary_semantic_parameter_sources(base_ctx),
    )
    if parameters is None:
        if self.debug:
            self._debug_print("counted-vs-counted value proof skipped: missing parameter specs")
        return False
    if self._condition_set_is_unsat(conditions, parameters):
        return True
    if self._composed_counted_state_transition_summaries_match(left, right):
        if self.debug:
            self._debug_print("counted-vs-counted proof discharged by composed state-transition semantic key")
        return True

    left_candidates = self._counted_loop_closed_expression_candidates(
        left,
        counted_case=left_case,
        result_size=comparison_result_size,
        conditions=conditions,
        parameters=parameters,
    )
    right_candidates = self._counted_loop_closed_expression_candidates(
        right,
        counted_case=right_case,
        result_size=comparison_result_size,
        conditions=conditions,
        parameters=parameters,
    )
    if not left_candidates or not right_candidates:
        if self.debug:
            self._debug_print(
                "counted-vs-counted value proof skipped: no closed candidates "
                f"(left={len(left_candidates)}, right={len(right_candidates)})"
            )
        direct_proved = self._prove_intrinsic_equivalence_under_conditions(
            left,
            right,
            conditions,
            parameters,
            timeout=10,
        )
        if self.debug:
            self._debug_print(f"counted-vs-counted direct SMT proof result: {direct_proved}")
        return direct_proved
    for left_candidate in left_candidates:
        for right_candidate in right_candidates:
            if self._prove_intrinsic_equivalence_under_conditions(
                left_candidate,
                right_candidate,
                conditions,
                parameters,
            ):
                if self.debug:
                    self._debug_print("counted-vs-counted proof discharged by SMT candidate pair")
                return True
    if self._prove_intrinsic_equivalence_under_conditions(
        left,
        right,
        conditions,
        parameters,
        timeout=10,
    ):
        if self.debug:
            self._debug_print("counted-vs-counted proof discharged by direct SMT summary equality")
        return True
    if self.debug:
        self._debug_print("counted-vs-counted proof failed for all candidate pairs")
        self._debug_print(
            "counted-vs-counted failed context: "
            f"left_case={getattr(left_case, 'index', None)}:"
            f"{getattr(left_case, 'branch_index', None)} "
            f"right_case={getattr(right_case, 'index', None)}:"
            f"{getattr(right_case, 'branch_index', None)} "
            f"conditions={summarize_conditions(conditions)}"
        )
    return False


def _impl__composed_counted_state_transition_summaries_match(
    self,
    left: Expression,
    right: Expression,
) -> bool:
    left_key = self._composed_counted_state_transition_summary_key(left)
    right_key = self._composed_counted_state_transition_summary_key(right)
    return left_key is not None and left_key == right_key


def _impl__composed_counted_state_transition_summary_key(
    self,
    expr: Expression,
) -> Optional[Tuple[Any, ...]]:
    if getattr(expr, "opcode", None) != COUNTED_LOOP_SUM_OPCODE:
        return None
    operands = list(getattr(expr, "operands", ()) or ())
    if len(operands) != 3:
        return None
    base, start, limit = operands
    if getattr(base, "opcode", None) != COUNTED_STATE_TRANSITION_VALUE_OPCODE:
        return None
    counted_ref = getattr(expr, "runtime_ref", None)
    state_ref = getattr(base, "runtime_ref", None)
    if not isinstance(counted_ref, CountedLoopSummaryRef):
        return None
    if not isinstance(state_ref, CountedStateTransitionLoopSummaryRef):
        return None
    outer_side_effect_key = self._counted_loop_outer_side_effect_key(counted_ref)
    if outer_side_effect_key is None:
        return None
    if not self._counted_state_transition_value_operands_match_ref(
        getattr(base, "operands", None) or (),
        state_ref,
    ):
        return None
    if not self._counted_state_transition_cases_allow_bounded_unroll(state_ref):
        return None
    state_key = self._counted_state_transition_semantic_core_key(state_ref)
    if state_key is None:
        return None
    residue_cases = tuple(
        (
            int(modulus),
            int(residue),
            int(coeff),
            int(bias),
        )
        for modulus, residue, coeff, bias in tuple(getattr(counted_ref, "residue_cases", ()) or ())
    )
    residue_bias_terms = tuple(getattr(counted_ref, "residue_bias_terms", ()) or ())
    if residue_bias_terms:
        return None
    start_key = self._canonical_counted_state_transition_outer_start_key(start, residue_cases)
    if start_key is None:
        return None
    try:
        limit_key = ConditionNormalizer.expression_signature(limit)
    except Exception:
        return None
    return (
        "composed_counted_state_transition_sum",
        state_key,
        int(getattr(counted_ref, "induction_step", 0) or 0),
        max(1, int(getattr(counted_ref, "result_size", 0) or 0)),
        bool(getattr(counted_ref, "signed_loop", False)),
        outer_side_effect_key,
        residue_cases,
        start_key,
        limit_key,
    )


def _impl__counted_loop_outer_side_effect_key(
    self,
    counted_ref: CountedLoopSummaryRef,
) -> Optional[Tuple[Any, ...]]:
    loop_summary = getattr(counted_ref, "loop_summary", None)
    if loop_summary is None:
        return None
    profile = getattr(loop_summary, "side_effect_profile", None)
    if profile is None:
        return None
    if getattr(profile, "requires_effect_proof", lambda: True)():
        return None
    try:
        profile_key = profile.stable_key()
    except Exception:
        return None
    if profile_key is None:
        return None
    return ("outer_loop_side_effect_profile", profile_key)


def _impl__counted_state_transition_semantic_core_key(
    self,
    state_ref: CountedStateTransitionLoopSummaryRef,
) -> Optional[Tuple[Any, ...]]:
    profile = getattr(state_ref, "side_effect_profile", None)
    if profile is None:
        return None
    effectful_flags = (
        "memory_reads",
        "memory_writes",
        "calls",
        "escapes",
        "context_memory_writes",
        "context_calls",
        "context_escapes",
    )
    if any(bool(getattr(profile, flag, False)) for flag in effectful_flags):
        return None
    placeholder = getattr(state_ref, "state_placeholder", None)
    transition_expr = getattr(state_ref, "transition_expr", None)
    if not isinstance(placeholder, Expression) or not isinstance(transition_expr, Expression):
        return None
    canonical_state = Expression.variable(
        "__state",
        size=max(1, int(getattr(placeholder, "size", 0) or getattr(state_ref, "state_size", 0) or 4)),
    )
    normalized_transition = self._replace_expression_node(
        transition_expr,
        placeholder,
        canonical_state,
    )
    try:
        transition_key = ConditionNormalizer.expression_signature(normalized_transition)
        init_key = ConditionNormalizer.expression_signature(getattr(state_ref, "initial_state", None))
        start_key = ConditionNormalizer.expression_signature(getattr(state_ref, "start_expr", None))
        limit_key = ConditionNormalizer.expression_signature(getattr(state_ref, "limit_expr", None))
        step_key = ConditionNormalizer.expression_signature(getattr(state_ref, "step_expr", None))
        guard_keys = tuple(
            ConditionNormalizer.conditions_signature((guard,))
            for guard in tuple(getattr(state_ref, "guard_constraints", ()) or ())
        )
    except Exception:
        return None
    return (
        "counted_state_transition_core",
        init_key,
        start_key,
        limit_key,
        step_key,
        transition_key,
        max(1, int(getattr(state_ref, "state_size", 0) or 0)),
        max(1, int(getattr(state_ref, "result_size", 0) or 0)),
        bool(getattr(state_ref, "signed_loop", False)),
        guard_keys,
    )


def _impl__canonical_counted_state_transition_outer_start_key(
    self,
    start: Expression,
    residue_cases: Tuple[Tuple[int, int, int, int], ...],
) -> Optional[Tuple[Any, ...]]:
    start_value = self._raw_constant_value(start)
    if start_value is None:
        try:
            return ConditionNormalizer.expression_signature(start)
        except Exception:
            return None
    if int(start_value) == 0:
        return ("const", 0)
    if int(start_value) == 1 and self._counted_residue_term_at_zero_is_zero(residue_cases):
        return ("const", 0)
    return ("const", int(start_value))


def _impl__counted_residue_term_at_zero_is_zero(
    residue_cases: Tuple[Tuple[int, int, int, int], ...],
) -> bool:
    if not residue_cases:
        return False
    for modulus, residue, _coeff, bias in residue_cases:
        if int(modulus) <= 0:
            return False
        if 0 % int(modulus) == int(residue) and int(bias) != 0:
            return False
    return True


def _impl__case_pair_has_one_sided_counted_loop_summary(
    self,
    left: Expression,
    right: Expression,
    left_case: ReturnCase,
    right_case: ReturnCase,
) -> bool:
    left_counted = self._is_provable_counted_loop_summary_value(left, left_case)
    right_counted = self._is_provable_counted_loop_summary_value(right, right_case)
    if left_counted == right_counted:
        return False
    closed_expr = right if left_counted else left
    return not self._expression_contains_loop_summary_runtime(closed_expr)


def _impl__is_provable_counted_loop_summary_value(
    self,
    expr: Optional[Expression],
    case: ReturnCase,
) -> bool:
    if expr is None:
        return False
    if getattr(expr, "expr_type", None) != ExpressionType.INTRINSIC:
        return False
    if getattr(expr, "opcode", None) != COUNTED_LOOP_SUM_OPCODE and getattr(expr, "name", None) != "COUNTED_LOOP_SUM":
        return False
    runtime_ref = getattr(expr, "runtime_ref", None)
    if not isinstance(runtime_ref, CountedLoopSummaryRef):
        return False
    loop_summary = getattr(runtime_ref, "loop_summary", None)
    if loop_summary is None:
        return False
    requires_effect_proof = getattr(loop_summary, "requires_effect_proof", None)
    if callable(requires_effect_proof) and requires_effect_proof():
        return False
    requires_path_proof = getattr(loop_summary, "requires_path_proof", None)
    if callable(requires_path_proof) and requires_path_proof():
        return False
    if not _counted_loop_sum_has_exact_lowering(expr):
        if self.debug:
            self._debug_print("counted loop summary not provable: no exact lowering")
        return False
    guards, complete = self._runtime_summary_guard_conditions_from_expression(expr)
    if not complete:
        if self.debug:
            self._debug_print("counted loop summary not provable: incomplete guards")
        return False
    profile = getattr(loop_summary, "side_effect_profile", None)
    has_control_obligation = bool(
        getattr(profile, "conditional_guards", False)
        or getattr(profile, "context_conditional_guards", False)
        or tuple(getattr(loop_summary, "cases", ()) or ())
    )
    if guards:
        covered = self._case_conditions_cover_runtime_summary_guards(case)
        if self.debug and not covered:
            self._debug_print("counted loop summary not provable: guard coverage missing")
        return covered
    if has_control_obligation:
        if self.debug:
            self._debug_print("counted loop summary not provable: control obligation without guards")
        return False
    return True


def _impl__prove_counted_loop_closed_expression_candidates(
    self,
    *,
    counted: Expression,
    closed: Expression,
    counted_case: ReturnCase,
    result_size: int,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
) -> bool:
    candidates = self._counted_loop_closed_expression_candidates(
        counted,
        counted_case=counted_case,
        result_size=result_size,
        conditions=conditions,
        parameters=parameters,
    )
    if not candidates:
        return False
    for candidate in candidates:
        if self._prove_intrinsic_equivalence_under_conditions(
            candidate,
            closed,
            conditions,
            parameters,
        ):
            return True
    return False


def _impl__counted_loop_closed_expression_candidates(
    self,
    counted: Expression,
    *,
    counted_case: ReturnCase,
    result_size: int,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
) -> Tuple[Expression, ...]:
    counted_closed = self._counted_loop_positive_closed_expression(
        counted,
        counted_case=counted_case,
        result_size=result_size,
        conditions=conditions,
        parameters=parameters,
    )
    shifted_closed = self._counted_loop_positive_closed_expression(
        counted,
        counted_case=counted_case,
        result_size=result_size,
        conditions=conditions,
        parameters=parameters,
        shifted_progression=True,
    )
    affine_closed = self._counted_loop_affine_closed_expression_candidate(
        counted,
        result_size=result_size,
        conditions=conditions,
        parameters=parameters,
    )
    bounded_state_closed = self._counted_loop_bounded_state_transition_base_candidate(
        counted,
        result_size=result_size,
        conditions=conditions,
        parameters=parameters,
    )
    candidates = [
        candidate
        for candidate in (counted_closed, shifted_closed, affine_closed, bounded_state_closed)
        if candidate is not None
    ]
    return tuple(candidates)


def _impl__counted_loop_bounded_state_transition_base_candidate(
    self,
    counted: Expression,
    *,
    result_size: int,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
) -> Optional[Expression]:
    operands = getattr(counted, "operands", None) or []
    if len(operands) != 3:
        return None
    base, start, limit = operands
    if getattr(base, "opcode", None) != COUNTED_STATE_TRANSITION_VALUE_OPCODE:
        return None
    runtime_ref = getattr(base, "runtime_ref", None)
    if not isinstance(runtime_ref, CountedStateTransitionLoopSummaryRef):
        return None
    if not self._counted_state_transition_side_effects_allow_bounded_unroll(runtime_ref):
        return None
    if not self._counted_state_transition_value_operands_match_ref(
        getattr(base, "operands", None) or (),
        runtime_ref,
    ):
        return None
    if not self._counted_state_transition_cases_allow_bounded_unroll(runtime_ref):
        return None
    iteration_count = self._bounded_state_transition_iteration_count_from_conditions(
        runtime_ref,
        conditions=conditions,
        parameters=parameters,
        max_iterations=32,
    )
    if iteration_count is None:
        return None
    unrolled_base = self._unroll_counted_state_transition_value(runtime_ref, iteration_count)
    if unrolled_base is None:
        return None
    unrolled_base = self._coerce_expression_to_size(
        unrolled_base,
        max(1, int(getattr(base, "size", 0) or result_size or 0)),
        signed=bool(getattr(runtime_ref, "signed_loop", False)),
    )
    candidate = counted.clone_with(operands=[unrolled_base, start, limit])
    candidate.size = max(1, int(getattr(counted, "size", 0) or result_size or 0))
    return candidate


def _impl__counted_state_transition_side_effects_allow_bounded_unroll(
    self,
    runtime_ref: CountedStateTransitionLoopSummaryRef,
) -> bool:
    profile = getattr(runtime_ref, "side_effect_profile", None)
    if profile is None:
        return False
    requires_effect_proof = getattr(profile, "requires_effect_proof", None)
    if callable(requires_effect_proof):
        try:
            if requires_effect_proof():
                return False
        except Exception:
            return False
    guarded_or_effectful_flags = (
        "memory_reads",
        "memory_writes",
        "calls",
        "escapes",
        "context_memory_writes",
        "context_calls",
        "context_escapes",
        "context_conditional_guards",
    )
    if any(bool(getattr(profile, flag, False)) for flag in guarded_or_effectful_flags):
        return False
    effect_descriptors = tuple(getattr(profile, "effect_descriptors", ()) or ())
    if any(getattr(effect, "kind", None) != "conditional_guard" for effect in effect_descriptors):
        return False
    if int(getattr(profile, "effect_count", 0) or 0) > len(effect_descriptors):
        return False
    if tuple(getattr(profile, "context_descriptors", ()) or ()):
        return False
    return True


def _impl__counted_state_transition_value_operands_match_ref(
    self,
    operands: Sequence[Expression],
    runtime_ref: CountedStateTransitionLoopSummaryRef,
) -> bool:
    if len(operands) != 3:
        return False
    expected = (
        getattr(runtime_ref, "initial_state", None),
        getattr(runtime_ref, "start_expr", None),
        getattr(runtime_ref, "limit_expr", None),
    )
    for actual, expected_expr in zip(operands, expected):
        if not isinstance(actual, Expression) or not isinstance(expected_expr, Expression):
            return False
        try:
            if not actual.equals(expected_expr):
                return False
        except Exception:
            return False
    return True


def _impl__bounded_state_transition_iteration_count_from_conditions(
    self,
    runtime_ref: CountedStateTransitionLoopSummaryRef,
    *,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
    max_iterations: int,
) -> Optional[int]:
    start = getattr(runtime_ref, "start_expr", None)
    limit = getattr(runtime_ref, "limit_expr", None)
    step = getattr(runtime_ref, "step_expr", None)
    if not isinstance(start, Expression) or not isinstance(limit, Expression) or not isinstance(step, Expression):
        return None
    if getattr(step, "expr_type", None) != ExpressionType.CONSTANT:
        return None
    try:
        step_value = int(getattr(step, "value", 0) or 0)
    except (TypeError, ValueError):
        return None
    if step_value <= 0:
        return None
    expr_size = max(
        1,
        int(getattr(start, "size", 0) or 0),
        int(getattr(limit, "size", 0) or 0),
        int(getattr(step, "size", 0) or 0),
    )
    start_sized = self._coerce_expression_to_size(
        start,
        expr_size,
        signed=bool(getattr(runtime_ref, "signed_loop", False)),
    )
    limit_sized = self._coerce_expression_to_size(
        limit,
        expr_size,
        signed=bool(getattr(runtime_ref, "signed_loop", False)),
    )
    for iteration_count in range(0, int(max_iterations) + 1):
        offset = Expression.constant(step_value * iteration_count, size=expr_size)
        expected_limit = Expression.binary_op("INT_ADD", start_sized, offset)
        expected_limit.size = expr_size
        equality = Condition(Expression.binary_op("INT_EQUAL", limit_sized, expected_limit))
        if self._condition_set_implies(conditions, [equality], parameters) and self._bounded_state_transition_trip_count_is_proved(
            runtime_ref,
            iteration_count,
            start_value=self._raw_constant_value(start),
            step_value=step_value,
            limit_sized=limit_sized,
            expr_size=expr_size,
            conditions=conditions,
            parameters=parameters,
        ):
            return iteration_count
    return None


def _impl__bounded_state_transition_trip_count_is_proved(
    self,
    runtime_ref: CountedStateTransitionLoopSummaryRef,
    iteration_count: int,
    *,
    start_value: Optional[int],
    step_value: int,
    limit_sized: Expression,
    expr_size: int,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
) -> bool:
    if start_value is None or step_value <= 0 or iteration_count < 0:
        return False
    bits = max(1, int(expr_size or 0) * 8)
    if bool(getattr(runtime_ref, "signed_loop", False)):
        min_value = 0
        max_value = (1 << (bits - 1)) - 1
        guard_op = "INT_SLESS"
    else:
        min_value = 0
        max_value = (1 << bits) - 1
        guard_op = "INT_LESS"
    concrete_values: List[int] = []
    for index in range(int(iteration_count) + 1):
        value = int(start_value) + int(step_value) * index
        if value < min_value or value > max_value:
            return False
        concrete_values.append(value)
    guard_conclusions: List[Condition] = []
    for value in concrete_values[: int(iteration_count)]:
        current = Expression.constant(value, size=expr_size)
        guard = Expression.binary_op(guard_op, current, limit_sized)
        guard.size = 1
        guard_conclusions.append(Condition(guard))
    exit_value = Expression.constant(concrete_values[int(iteration_count)], size=expr_size)
    exit_equality = Expression.binary_op("INT_EQUAL", exit_value, limit_sized)
    exit_equality.size = 1
    guard_conclusions.append(Condition(exit_equality))
    return self._condition_set_implies(conditions, guard_conclusions, parameters)


def _impl__counted_state_transition_cases_allow_bounded_unroll(
    self,
    runtime_ref: CountedStateTransitionLoopSummaryRef,
) -> bool:
    transition_cases = getattr(runtime_ref, "transition_cases", None)
    if not transition_cases:
        return False
    cases = tuple(transition_cases)
    if len(cases) != 1:
        return False
    only_case = cases[0]
    if not isinstance(only_case, tuple) or len(only_case) != 2:
        return False
    condition_signature, transition_signature = only_case
    if condition_signature is not None and condition_signature != () and condition_signature != (("none",),):
        return False
    transition_expr = getattr(runtime_ref, "transition_expr", None)
    if not isinstance(transition_expr, Expression):
        return False
    try:
        expected_transition_signature = ConditionNormalizer.expression_signature(transition_expr)
    except Exception:
        return False
    if transition_signature != expected_transition_signature:
        return False
    return True


def _impl__unroll_counted_state_transition_value(
    self,
    runtime_ref: CountedStateTransitionLoopSummaryRef,
    iteration_count: int,
) -> Optional[Expression]:
    if iteration_count < 0:
        return None
    state_placeholder = getattr(runtime_ref, "state_placeholder", None)
    transition_expr = getattr(runtime_ref, "transition_expr", None)
    value = getattr(runtime_ref, "initial_state", None)
    if not isinstance(state_placeholder, Expression) or not isinstance(transition_expr, Expression) or not isinstance(value, Expression):
        return None
    for _ in range(int(iteration_count)):
        value = self._replace_expression_node(transition_expr, state_placeholder, value)
        value = value.derive_with(
            size=max(
                1,
                int(
                    getattr(runtime_ref, "result_size", 0)
                    or getattr(value, "size", 0)
                    or 0
                ),
            )
        )
    return value


def _impl__counted_loop_affine_closed_expression_candidate(
    self,
    counted: Expression,
    *,
    result_size: int,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
) -> Optional[Expression]:
    runtime_ref = getattr(counted, "runtime_ref", None)
    if not self._counted_loop_refs_allow_affine_value_proof(runtime_ref, runtime_ref):
        return None
    if not self._counted_loop_affine_widths_are_safe(counted, counted, result_size, parameters):
        return None
    return self._counted_loop_affine_closed_expression(
        counted,
        result_size=result_size,
        conditions=conditions,
        parameters=parameters,
    )


def _impl__counted_loop_positive_closed_expression(
    self,
    counted: Expression,
    *,
    counted_case: ReturnCase,
    result_size: int,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
    shifted_progression: bool = False,
) -> Optional[Expression]:
    runtime_ref = getattr(counted, "runtime_ref", None)
    if not isinstance(runtime_ref, CountedLoopSummaryRef):
        return None
    if int(getattr(runtime_ref, "induction_step", 0) or 0) != 1:
        return None
    residue_cases = tuple(getattr(runtime_ref, "residue_cases", ()) or ())
    if len(residue_cases) != 1:
        return None
    modulus, residue, coeff, bias = residue_cases[0]
    if int(modulus) != 1 or int(residue) != 0:
        return None
    operands = list(getattr(counted, "operands", ()) or ())
    if len(operands) != 3:
        return None
    base, start, limit = operands
    if getattr(start, "expr_type", None) != ExpressionType.CONSTANT:
        return None
    if int(getattr(start, "value", 0) or 0) != 0:
        return None
    guard_operator = "INT_SLESS" if bool(getattr(runtime_ref, "signed_loop", False)) else "INT_LESS"
    positive_span = Condition(Expression.binary_op(guard_operator, start, limit))
    if not self._condition_set_implies(conditions, [positive_span], parameters):
        return None

    target_size = max(1, int(result_size or 0))
    limit_size = max(1, int(getattr(limit, "size", 0) or 0))
    start_size = max(1, int(getattr(start, "size", 0) or 0))
    count_size = max(target_size, limit_size, start_size)
    limit_count = self._coerce_expression_to_size(
        limit,
        count_size,
        signed=bool(getattr(runtime_ref, "signed_loop", False)),
    )
    limit_result = self._coerce_expression_to_size(
        limit,
        target_size,
        signed=bool(getattr(runtime_ref, "signed_loop", False)),
    )
    wide_size = max(8, count_size * 2)
    wide_limit = Expression.unary_op("INT_ZEXT", limit_count)
    wide_limit.size = wide_size
    limit_minus_one_count = Expression.binary_op(
        "INT_SUB",
        limit_count,
        Expression.constant(1, size=count_size),
    )
    limit_minus_one_count.size = count_size
    limit_minus_one_result = self._coerce_expression_to_size(
        limit_minus_one_count,
        target_size,
        signed=False,
    )
    if shifted_progression:
        limit_minus_two_count = Expression.binary_op(
            "INT_SUB",
            limit_count,
            Expression.constant(2, size=count_size),
        )
        limit_minus_two_count.size = count_size
        progression_left = Expression.unary_op("INT_ZEXT", limit_minus_one_count)
        progression_left.size = wide_size
        progression_right = Expression.unary_op("INT_ZEXT", limit_minus_two_count)
        progression_right.size = wide_size
    else:
        progression_left = wide_limit
        progression_right = Expression.binary_op(
            "INT_SUB",
            wide_limit,
            Expression.constant(1, size=wide_size),
        )
        progression_right.size = wide_size
    product = Expression.binary_op("INT_MULT", progression_left, progression_right)
    half = Expression.binary_op("INT_RIGHT", product, Expression.constant(1, size=wide_size))
    triangular = Expression.binary_op("SUBPIECE", half, Expression.constant(0, size=4))
    triangular.size = target_size
    terms: List[Expression] = []
    coeff = int(coeff)
    if coeff != 0:
        if coeff == 1:
            coeff_term = triangular
        else:
            coeff_term = Expression.binary_op(
                "INT_MULT",
                triangular,
                Expression.constant(coeff, size=target_size),
            )
            coeff_term.size = target_size
        terms.append(coeff_term)
        if shifted_progression:
            if coeff == 1:
                shifted_linear = limit_minus_one_result
            else:
                shifted_linear = Expression.binary_op(
                    "INT_MULT",
                    limit_minus_one_result,
                    Expression.constant(coeff, size=target_size),
                )
                shifted_linear.size = target_size
            terms.append(shifted_linear)
    bias = int(bias)
    if bias != 0:
        bias_term = Expression.binary_op(
            "INT_MULT",
            limit_result,
            Expression.constant(bias, size=target_size),
        )
        bias_term.size = target_size
        terms.append(bias_term)
    for bias_modulus, bias_residue, bias_expr in tuple(getattr(runtime_ref, "residue_bias_terms", ()) or ()):
        if int(bias_modulus) != 1 or int(bias_residue) != 0:
            return None
        term_bias = self._coerce_expression_to_size(
            bias_expr,
            target_size,
            signed=self._expression_prefers_signed_extension(bias_expr),
        )
        bias_expr_term = Expression.binary_op("INT_MULT", limit_result, term_bias)
        bias_expr_term.size = target_size
        terms.append(bias_expr_term)
    base_low = base
    if getattr(base, "expr_type", None) == ExpressionType.CONSTANT and int(getattr(base, "value", 0) or 0) == 0:
        base_low = None
    else:
        base_low = self._coerce_expression_to_size(
            base,
            target_size,
            signed=self._expression_prefers_signed_extension(base),
        )
    if base_low is not None:
        terms.insert(0, base_low)
    if not terms:
        return Expression.constant(0, size=target_size)
    total = terms[0]
    for term in terms[1:]:
        total = Expression.binary_op("INT_ADD", total, term)
        total.size = target_size
    total.size = target_size
    return total


def _impl__counted_loop_values_are_provably_equivalent(
    self,
    left: Expression,
    right: Expression,
    *,
    left_case: Optional[ReturnCase],
    right_case: Optional[ReturnCase],
    semantic_parameter_sources: Sequence[ParameterInfo] = (),
) -> bool:
    if left_case is None or right_case is None:
        return False
    if getattr(left, "opcode", None) != COUNTED_LOOP_SUM_OPCODE:
        return False
    if getattr(right, "opcode", None) != COUNTED_LOOP_SUM_OPCODE:
        return False
    if len(getattr(left, "operands", None) or []) != 3 or len(getattr(right, "operands", None) or []) != 3:
        return False

    left_ref = getattr(left, "runtime_ref", None)
    right_ref = getattr(right, "runtime_ref", None)
    if not self._counted_loop_refs_allow_value_proof(left_ref, right_ref):
        if self._counted_loop_affine_values_are_provably_equivalent(
            left,
            right,
            left_case=left_case,
            right_case=right_case,
            semantic_parameter_sources=semantic_parameter_sources,
        ):
            return True
        return False
    if self._counted_loop_affine_values_are_provably_equivalent(
        left,
        right,
        left_case=left_case,
        right_case=right_case,
        semantic_parameter_sources=semantic_parameter_sources,
    ):
        return True
    if (
        getattr(left_ref, "loop_summary", None) is not None
        or getattr(right_ref, "loop_summary", None) is not None
    ) and not self._case_pair_has_runtime_guard_coverage_or_equivalence(left_case, right_case):
        return False
    if not self._counted_loop_refs_match_ignoring_signedness(left_ref, right_ref):
        return False
    if not all(
        self._expressions_share_object_centric_structure(left_operand, right_operand)
        for left_operand, right_operand in zip(left.operands, right.operands)
    ):
        return False
    if bool(getattr(left_ref, "signed_loop", False)) == bool(getattr(right_ref, "signed_loop", False)):
        return True
    conditions = self._combined_summary_conditions(left_case, right_case)
    parameters = self._collect_intrinsic_parameter_specs(
        left_case,
        right_case,
        left,
        right,
        *(condition.expression for condition in conditions or [] if condition is not None),
    )
    if parameters is None:
        return False
    if self._counted_loop_signedness_difference_is_guarded(
        left,
        right,
        conditions,
        parameters,
    ):
        return True
    return self._prove_intrinsic_equivalence_under_conditions(
        left,
        right,
        conditions,
        parameters,
    )


def _impl__counted_loop_affine_values_are_provably_equivalent(
    self,
    left: Expression,
    right: Expression,
    *,
    left_case: ReturnCase,
    right_case: ReturnCase,
    semantic_parameter_sources: Sequence[ParameterInfo] = (),
) -> bool:
    left_ref = getattr(left, "runtime_ref", None)
    right_ref = getattr(right, "runtime_ref", None)
    if not self._counted_loop_refs_allow_affine_value_proof(left_ref, right_ref):
        return False

    left_guards, left_guards_complete = self._runtime_summary_guard_conditions_from_expression(left)
    right_guards, right_guards_complete = self._runtime_summary_guard_conditions_from_expression(right)
    if not left_guards_complete or not right_guards_complete:
        return False
    if not left_guards and not right_guards:
        return False

    conditions = self._combined_summary_conditions(left_case, right_case)
    for guard in tuple(left_guards) + tuple(right_guards):
        if guard not in conditions:
            conditions.append(guard)
    parameters = self._collect_intrinsic_parameter_specs(
        left_case,
        right_case,
        left,
        right,
        *(condition.expression for condition in conditions or [] if condition is not None),
        semantic_parameter_sources=semantic_parameter_sources,
    )
    if parameters is None:
        return False
    if self._condition_set_is_unsat(conditions, parameters):
        return True

    result_size = self._case_pair_comparison_result_size(left_case, right_case)
    if result_size is None:
        return False
    if not self._counted_loop_affine_widths_are_safe(left, right, result_size, parameters):
        return False
    left_closed = self._counted_loop_affine_closed_expression(
        left,
        result_size=result_size,
        conditions=conditions,
        parameters=parameters,
    )
    right_closed = self._counted_loop_affine_closed_expression(
        right,
        result_size=result_size,
        conditions=conditions,
        parameters=parameters,
    )
    if left_closed is None or right_closed is None:
        return False
    return self._prove_intrinsic_equivalence_under_conditions(
        left_closed,
        right_closed,
        conditions,
        parameters,
    )


def _impl__counted_loop_affine_widths_are_safe(
    self,
    left: Expression,
    right: Expression,
    result_size: int,
    parameters: Sequence[Dict[str, Any]],
) -> bool:
    target_bits = max(1, int(result_size or 0) * 8)
    by_identity = {
        tuple(spec.get("identity")): spec
        for spec in parameters or []
        if isinstance(spec.get("identity"), tuple)
    }

    def visit(expr: Optional[Expression]) -> bool:
        if expr is None:
            return True
        if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER:
            expr_bits = max(1, int(getattr(expr, "size", 0) or 4) * 8)
            if expr_bits <= target_bits:
                return True
            identity = parameter_identity_key_from_expression(expr)
            spec = by_identity.get(identity)
            if spec is None:
                return False
            try:
                narrow_bits = int(spec.get("semantic_narrow_bits"))
            except (TypeError, ValueError):
                return False
            if narrow_bits != target_bits:
                return False
            return spec.get("semantic_signedness") in {"signed", "unsigned"}
        if getattr(expr, "expr_type", None) == ExpressionType.PHI:
            for cond, branch_value in getattr(expr, "value", None) or []:
                if cond is not None and not visit(getattr(cond, "expression", None)):
                    return False
                if not visit(branch_value):
                    return False
            return True
        return all(visit(operand) for operand in getattr(expr, "operands", None) or [])

    for counted in (left, right):
        if not visit(counted):
            return False
        runtime_ref = getattr(counted, "runtime_ref", None)
        for _, _, bias_expr in tuple(getattr(runtime_ref, "residue_bias_terms", ()) or ()):
            if not visit(bias_expr):
                return False
    return True


def _impl__counted_loop_refs_allow_affine_value_proof(self, left_ref, right_ref) -> bool:
    if not isinstance(left_ref, CountedLoopSummaryRef) or not isinstance(right_ref, CountedLoopSummaryRef):
        return False
    for loop_summary in (getattr(left_ref, "loop_summary", None), getattr(right_ref, "loop_summary", None)):
        if loop_summary is None:
            return False
        requires_effect_proof = getattr(loop_summary, "requires_effect_proof", None)
        if callable(requires_effect_proof) and requires_effect_proof():
            return False
        requires_path_proof = getattr(loop_summary, "requires_path_proof", None)
        if callable(requires_path_proof) and requires_path_proof():
            return False
    if max(1, int(getattr(left_ref, "result_size", 0) or 0)) != max(
        1, int(getattr(right_ref, "result_size", 0) or 0)
    ):
        return False
    return True


def _impl__counted_loop_affine_closed_expression(
    self,
    counted: Expression,
    *,
    result_size: int,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
) -> Optional[Expression]:
    runtime_ref = getattr(counted, "runtime_ref", None)
    if not isinstance(runtime_ref, CountedLoopSummaryRef):
        return None
    residue_cases = tuple(getattr(runtime_ref, "residue_cases", ()) or ())
    if len(residue_cases) != 1:
        return None
    modulus, residue, coeff, bias = residue_cases[0]
    if int(modulus) != 1 or int(residue) != 0:
        return None
    operands = list(getattr(counted, "operands", ()) or ())
    if len(operands) != 3:
        return None
    base, start, limit = operands
    step = int(getattr(runtime_ref, "induction_step", 0) or 0)
    if step <= 0:
        return None

    trip_count = self._counted_loop_affine_trip_count_expression(
        start,
        limit,
        step,
        conditions=conditions,
        parameters=parameters,
    )
    if trip_count is None:
        return None
    if not self._expression_is_provably_nonnegative_under_conditions(trip_count, conditions, parameters):
        return None

    target_size = max(1, int(result_size or 0))
    count_size = max(
        target_size,
        max(1, int(getattr(start, "size", 0) or 0)),
        max(1, int(getattr(limit, "size", 0) or 0)),
        max(1, int(getattr(trip_count, "size", 0) or 0)),
    )
    count = self._coerce_expression_to_size(
        trip_count,
        count_size,
        signed=bool(getattr(runtime_ref, "signed_loop", False)),
    )
    start_count = self._coerce_expression_to_size(
        start,
        count_size,
        signed=self._expression_prefers_signed_extension(start),
    )
    wide_size = max(8, count_size * 2, target_size * 2)
    wide_count = Expression.unary_op("INT_ZEXT", count)
    wide_count.size = wide_size
    wide_start = Expression.unary_op("INT_ZEXT", start_count)
    wide_start.size = wide_size

    count_minus_one = Expression.binary_op(
        "INT_SUB",
        wide_count,
        Expression.constant(1, size=wide_size),
    )
    count_minus_one.size = wide_size
    triangular_product = Expression.binary_op("INT_MULT", wide_count, count_minus_one)
    triangular_product.size = wide_size
    triangular = Expression.binary_op(
        "INT_RIGHT",
        triangular_product,
        Expression.constant(1, size=wide_size),
    )
    triangular.size = wide_size

    progression_sum = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_MULT", wide_count, wide_start),
        Expression.binary_op("INT_MULT", Expression.constant(step, size=wide_size), triangular),
    )
    progression_sum.size = wide_size

    terms: List[Expression] = []
    coeff = int(coeff)
    if coeff != 0:
        coeff_term = progression_sum
        if coeff != 1:
            coeff_term = Expression.binary_op(
                "INT_MULT",
                progression_sum,
                Expression.constant(coeff, size=wide_size),
            )
            coeff_term.size = wide_size
        terms.append(coeff_term)

    bias = int(bias)
    if bias != 0:
        bias_term = Expression.binary_op(
            "INT_MULT",
            wide_count,
            Expression.constant(bias, size=wide_size),
        )
        bias_term.size = wide_size
        terms.append(bias_term)

    for bias_modulus, bias_residue, bias_expr in tuple(getattr(runtime_ref, "residue_bias_terms", ()) or ()):
        if int(bias_modulus) != 1 or int(bias_residue) != 0:
            return None
        bias_wide = self._coerce_expression_to_size(
            bias_expr,
            wide_size,
            signed=self._expression_prefers_signed_extension(bias_expr),
        )
        bias_expr_term = Expression.binary_op("INT_MULT", wide_count, bias_wide)
        bias_expr_term.size = wide_size
        terms.append(bias_expr_term)

    base_wide = None
    if not (
        getattr(base, "expr_type", None) == ExpressionType.CONSTANT
        and int(getattr(base, "value", 0) or 0) == 0
    ):
        base_wide = self._coerce_expression_to_size(
            base,
            wide_size,
            signed=self._expression_prefers_signed_extension(base),
        )
    if base_wide is not None:
        terms.insert(0, base_wide)
    if not terms:
        return Expression.constant(0, size=target_size)

    total = terms[0]
    for term in terms[1:]:
        total = Expression.binary_op("INT_ADD", total, term)
        total.size = wide_size
    low = Expression.binary_op("SUBPIECE", total, Expression.constant(0, size=4))
    low.size = target_size
    return low


def _impl__counted_loop_affine_trip_count_expression(
    self,
    start: Expression,
    limit: Expression,
    step: int,
    *,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
) -> Optional[Expression]:
    if step <= 0:
        return None
    if step == 1 and self._expression_is_zero(start):
        return limit
    candidate = self._extract_affine_limit_trip_count_candidate(start, limit, step)
    if candidate is None:
        return None
    if not self._counted_loop_limit_matches_start_plus_step_count(
        start,
        limit,
        step,
        candidate,
        conditions,
        parameters,
    ):
        return None
    return candidate


def _impl__counted_loop_limit_matches_start_plus_step_count(
    self,
    start: Expression,
    limit: Expression,
    step: int,
    count: Expression,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
) -> bool:
    size = max(
        1,
        int(getattr(start, "size", 0) or 0),
        int(getattr(limit, "size", 0) or 0),
        int(getattr(count, "size", 0) or 0),
    )
    start_sized = self._coerce_expression_to_size(
        start,
        size,
        signed=self._expression_prefers_signed_extension(start),
    )
    count_sized = self._coerce_expression_to_size(
        count,
        size,
        signed=self._expression_prefers_signed_extension(count),
    )
    limit_sized = self._coerce_expression_to_size(
        limit,
        size,
        signed=self._expression_prefers_signed_extension(limit),
    )
    scaled = Expression.binary_op(
        "INT_MULT",
        Expression.constant(step, size=size),
        count_sized,
    )
    scaled.size = size
    expected_limit = Expression.binary_op("INT_ADD", start_sized, scaled)
    expected_limit.size = size
    if self._expressions_same_shape_ignoring_runtime(expected_limit, limit_sized):
        return True
    equality = Condition(Expression.binary_op("INT_EQUAL", limit_sized, expected_limit))
    return self._condition_set_implies(conditions, [equality], parameters)


def _impl__counted_loop_refs_allow_value_proof(self, left_ref, right_ref) -> bool:
    if left_ref is None or right_ref is None:
        return False
    if not isinstance(left_ref, CountedLoopSummaryRef) or not isinstance(right_ref, CountedLoopSummaryRef):
        return False
    left_loop_summary = getattr(left_ref, "loop_summary", None)
    right_loop_summary = getattr(right_ref, "loop_summary", None)
    if left_loop_summary is None and right_loop_summary is None:
        return True
    for loop_summary in (left_loop_summary, right_loop_summary):
        requires_effect_proof = getattr(loop_summary, "requires_effect_proof", None)
        if callable(requires_effect_proof) and requires_effect_proof():
            return False
        requires_path_proof = getattr(loop_summary, "requires_path_proof", None)
        if callable(requires_path_proof) and requires_path_proof():
            return False
    loop_result = compare_loop_summaries(left_loop_summary, right_loop_summary)
    if loop_result.blocks_shortcut():
        return False
    return loop_result.is_equivalent() is True


def _impl__counted_loop_refs_match_ignoring_signedness(self, left_ref, right_ref) -> bool:
    if left_ref is None or right_ref is None:
        return False
    if not isinstance(left_ref, CountedLoopSummaryRef) or not isinstance(right_ref, CountedLoopSummaryRef):
        return False
    try:
        return (
            int(getattr(left_ref, "induction_step", 0) or 0)
            == int(getattr(right_ref, "induction_step", 0) or 0)
            and max(1, int(getattr(left_ref, "result_size", 0) or 0))
            == max(1, int(getattr(right_ref, "result_size", 0) or 0))
            and tuple(getattr(left_ref, "residue_cases", ()) or ())
            == tuple(getattr(right_ref, "residue_cases", ()) or ())
            and getattr(left_ref, "source", None) == getattr(right_ref, "source", None)
        )
    except Exception:
        return False


def _impl__counted_loop_signedness_difference_is_guarded(
    self,
    left: Expression,
    right: Expression,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
) -> bool:
    left_ref = getattr(left, "runtime_ref", None)
    right_ref = getattr(right, "runtime_ref", None)
    if bool(getattr(left_ref, "signed_loop", False)) == bool(getattr(right_ref, "signed_loop", False)):
        return True
    operands = list(getattr(left, "operands", None) or [])
    if len(operands) != 3:
        return False
    # Signed and unsigned COUNTED_LOOP_SUM lowerings differ in how start/limit
    # are extended to the wide arithmetic domain. If both are non-negative
    # under the current pair guard, the two interpretations coincide.
    return all(
        self._expression_is_provably_nonnegative_under_conditions(expr, conditions, parameters)
        for expr in operands[1:3]
    )


def _impl__clone_auxiliary_counted_loop_summary_ref(
    self,
    runtime_ref: CountedLoopSummaryRef,
    identity_to_spec: Dict[Tuple[object, ...], Dict[str, Any]],
) -> Optional[CountedLoopSummaryRef]:
    cloned_bias_terms = self._clone_auxiliary_residue_bias_terms(
        tuple(getattr(runtime_ref, "residue_bias_terms", ()) or ()),
        identity_to_spec,
    )
    if cloned_bias_terms is None:
        return None
    loop_summary = getattr(runtime_ref, "loop_summary", None)
    cloned_loop_summary = loop_summary
    if isinstance(loop_summary, LoopSummaryRef):
        cloned_loop_summary = self._clone_auxiliary_loop_summary_ref(loop_summary, identity_to_spec)
        if cloned_loop_summary is None:
            return None
    return replace(
        runtime_ref,
        residue_bias_terms=cloned_bias_terms,
        loop_summary=cloned_loop_summary,
    )


def _impl__clone_auxiliary_loop_summary_ref(
    self,
    loop_summary: LoopSummaryRef,
    identity_to_spec: Dict[Tuple[object, ...], Dict[str, Any]],
) -> Optional[LoopSummaryRef]:
    term_descriptor = getattr(loop_summary, "term_descriptor", None)
    if not isinstance(term_descriptor, LoopTermDescriptorRef):
        return loop_summary
    cloned_bias_terms = self._clone_auxiliary_residue_bias_terms(
        tuple(getattr(term_descriptor, "residue_bias_terms", ()) or ()),
        identity_to_spec,
    )
    if cloned_bias_terms is None:
        return None
    return replace(
        loop_summary,
        term_descriptor=replace(term_descriptor, residue_bias_terms=cloned_bias_terms),
    )


def _impl__case_pair_can_defer_loop_summary_proof(
    self,
    left_case: ReturnCase,
    right_case: ReturnCase,
    reason: str,
) -> bool:
    if reason == "loop_summary_guard_mismatch":
        return self._loop_summary_contracts_match_without_guard(
            left_case.value_expr,
            right_case.value_expr,
        )
    return False


def _impl__loop_summary_contracts_match_without_guard(
    self,
    left: Optional[Expression],
    right: Optional[Expression],
) -> bool:
    if left is None or right is None:
        return False
    left_has_loop = self._expression_contains_loop_summary_runtime(left)
    right_has_loop = self._expression_contains_loop_summary_runtime(right)
    if not left_has_loop or not right_has_loop:
        return False
    if left.expr_type == ExpressionType.INTRINSIC and right.expr_type == ExpressionType.INTRINSIC:
        decision = self._runtime_loop_contract_shortcut_decision(
            getattr(left, "runtime_ref", None),
            getattr(right, "runtime_ref", None),
        )
        if decision.equivalent and decision.requires_guard_equivalence:
            return True
    if left.expr_type != right.expr_type:
        return False
    left_operands = list(getattr(left, "operands", []) or [])
    right_operands = list(getattr(right, "operands", []) or [])
    if len(left_operands) != len(right_operands):
        return False
    return any(
        self._loop_summary_contracts_match_without_guard(left_operand, right_operand)
        for left_operand, right_operand in zip(left_operands, right_operands)
    )


def _impl__resolve_pending_loop_summary_pairs_with_partition_proof(
    self,
    pending_pairs: Sequence[_PendingLoopSummaryPair],
    cases1: Sequence[ReturnCase],
    cases2: Sequence[ReturnCase],
    resolved_pairs: set[tuple[int, int]],
) -> set[tuple[int, int]]:
    resolved_pending: set[tuple[int, int]] = set()
    progress = True
    while progress:
        progress = False
        known_resolved = set(resolved_pairs) | resolved_pending
        for pending in pending_pairs:
            pair_key = (pending.i, pending.j)
            if pair_key in resolved_pending:
                continue
            if not self._pending_loop_summary_pair_has_exact_delta_coverage(
                pending,
                cases1,
                cases2,
                known_resolved,
            ):
                continue
            resolved_pending.add(pair_key)
            progress = True
    return resolved_pending


def _impl__pending_loop_summary_pair_has_exact_delta_coverage(
    self,
    pending: _PendingLoopSummaryPair,
    cases1: Sequence[ReturnCase],
    cases2: Sequence[ReturnCase],
    resolved_pairs: set[tuple[int, int]],
) -> bool:
    left_cover_cases = [
        cases1[left_index]
        for left_index, _right_index in sorted(resolved_pairs)
        if _right_index == pending.j
        and left_index != pending.i
        and 0 <= left_index < len(cases1)
        and not self._expression_contains_loop_summary_runtime(cases1[left_index].value_expr)
    ]
    right_cover_cases = [
        cases2[right_index]
        for _left_index, right_index in sorted(resolved_pairs)
        if _left_index == pending.i
        and right_index != pending.j
        and 0 <= right_index < len(cases2)
        and not self._expression_contains_loop_summary_runtime(cases2[right_index].value_expr)
    ]
    return self._condition_delta_region_is_covered_by_cases(
        self._case_summary_condition_basis(pending.left_case),
        self._case_summary_condition_basis(pending.right_case),
        right_cover_cases,
        pending.left_case,
        pending.right_case,
    ) and self._condition_delta_region_is_covered_by_cases(
        self._case_summary_condition_basis(pending.right_case),
        self._case_summary_condition_basis(pending.left_case),
        left_cover_cases,
        pending.right_case,
        pending.left_case,
    )


def _impl__phi_circular_case_shape_and_unknowns(
    self,
    case: ReturnCase,
) -> Tuple[Optional[Tuple[Any, ...]], Tuple[Any, ...]]:
    unknowns: List[Any] = []
    value_shape = self._phi_circular_expression_shape_key(
        getattr(case, "value_expr", None),
        unknowns,
    )
    if value_shape is None:
        return None, ()
    condition_shapes: List[Tuple[Any, ...]] = []
    for condition in getattr(case, "conditions", None) or ():
        expression = getattr(condition, "expression", None)
        condition_shape = self._phi_circular_expression_shape_key(expression, unknowns)
        if condition_shape is None:
            return None, ()
        condition_shapes.append(
            (
                "condition",
                bool(getattr(condition, "negated", False)),
                condition_shape,
            )
        )
    return (
        (
            "phi_circular_case_shape",
            ("value", value_shape),
            ("conditions", tuple(condition_shapes)),
        ),
        tuple(unknowns),
    )


def _impl__phi_circular_expression_shape_key(
    self,
    expr: Any,
    unknowns: List[Any],
) -> Optional[Tuple[Any, ...]]:
    if expr is None or getattr(expr, "expr_type", None) is None:
        return None
    expr_type = expr.expr_type
    if expr_type == ExpressionType.UNKNOWN:
        if not self._unknown_expression_is_originated_phi_circular(expr):
            return None
        bits = int(expression_smt_bit_width(expr) or 0)
        if bits <= 0:
            return None
        unknowns.append(expr)
        return ("unknown", "phi_circular", bits)
    if self._expression_node_is_unsupported_smt_op(expr):
        return None
    bits = int(expression_smt_bit_width(expr) or 0)
    if expr_type == ExpressionType.CONSTANT:
        return ("const", int(getattr(expr, "value", 0) or 0), bits)
    if expr_type == ExpressionType.LITERAL:
        return ("literal", repr(getattr(expr, "value", None)), bits)
    if expr_type == ExpressionType.PARAMETER:
        raw_value = getattr(expr, "value", None)
        return (
            "parameter",
            str(getattr(expr, "name", "") or ""),
            -1 if raw_value is None else int(raw_value),
            bits,
        )
    if expr_type == ExpressionType.VARIABLE:
        return None
    if expr_type == ExpressionType.UNARY_OP:
        operands = getattr(expr, "operands", None) or ()
        if len(operands) != 1:
            return None
        operand = self._phi_circular_expression_shape_key(operands[0], unknowns)
        if operand is None:
            return None
        return ("unary", str(getattr(expr, "operator", "") or ""), bits, operand)
    if expr_type == ExpressionType.BINARY_OP:
        operands = getattr(expr, "operands", None) or ()
        if len(operands) != 2:
            return None
        left = self._phi_circular_expression_shape_key(operands[0], unknowns)
        right = self._phi_circular_expression_shape_key(operands[1], unknowns)
        if left is None or right is None:
            return None
        return (
            "binary",
            str(getattr(expr, "operator", "") or ""),
            bits,
            left,
            right,
        )
    if expr_type == ExpressionType.INTRINSIC:
        operands = []
        for operand_expr in getattr(expr, "operands", None) or ():
            operand = self._phi_circular_expression_shape_key(operand_expr, unknowns)
            if operand is None:
                return None
            operands.append(operand)
        return (
            "intrinsic",
            str(getattr(expr, "name", "") or ""),
            None if getattr(expr, "opcode", None) is None else int(getattr(expr, "opcode")),
            bits,
            tuple(operands),
        )
    return None


def _impl__unknown_expression_is_originated_phi_circular(cls, expr: Any) -> bool:
    if getattr(expr, "expr_type", None) != ExpressionType.UNKNOWN:
        return False
    runtime_ref = getattr(expr, "runtime_ref", None)
    if getattr(runtime_ref, "kind", None) != "opaque_unknown":
        return False
    if getattr(runtime_ref, "reason", None) != "phi_circular":
        return False
    if getattr(runtime_ref, "origin_kind", None) != "multiequal_pcode_op":
        return False
    return cls._stable_key_or_none(getattr(runtime_ref, "origin_ref", None)) is not None
