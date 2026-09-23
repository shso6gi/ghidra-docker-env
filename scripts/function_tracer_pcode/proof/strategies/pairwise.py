# -*- coding: utf-8 -*-
"""Compatibility facade for PairwiseStrategy."""

from scripts.function_tracer_pcode.proof.strategies.pairwise_services import (
    auxiliary_smt as _svc_auxiliary_smt,
    loop_summary as _svc_loop_summary,
    case_conditions as _svc_case_conditions,
    method_b_closure as _svc_method_b_closure,
    opaque_unknowns as _svc_opaque_unknowns,
    orchestration as _svc_orchestration,
    parameter_identity as _svc_parameter_identity,
    pair_cases as _svc_pair_cases,
    readonly_reduction as _svc_readonly_reduction,
    runtime_shortcut as _svc_runtime_shortcut,
    unresolved_lowering as _svc_unresolved_lowering,
)
from typing import Optional
from scripts.function_tracer_pcode.core import FunctionReturnAnalysis
from scripts.function_tracer_pcode.proof.strategies.pairwise_services._shared import (
    CheckStrategy,
    NormalizationSettings,
)
# Re-exported for modules and tests that import these names from here.
from scripts.function_tracer_pcode.proof.strategies.pairwise_services._shared import (
    align_return_value_extension_surfaces,
    build_pair_query,
    canonicalize_location,
)
# Re-exported for modules and tests that import these names from here.
from scripts.function_tracer_pcode.proof.strategies.pairwise_services._shared import (
    QueryResult,
    ReturnCase,
    contains_udiv,
    extract_min_excluded_params,
    extract_sign_facts,
    normalize_analysis_semantic_width,
    normalize_expression,
    validate_counterexample_across_cases,
)

class PairwiseStrategy(CheckStrategy):
    """
    Pairwise戦略（分岐ペア分割方式・二段階チェック）

    各ペア(i,j)に対して：
    1. Stage 1: 条件のみチェック（C1_i ∧ C2_j）
    2. Stage 2: 値不等式を追加してチェック（C1_i ∧ C2_j ∧ V1_i≠V2_j）
    3. Stage 3: 正規化 fallback
    """

    def __init__(
        self,
        formula_builder,
        solver_runner,
        debug: bool = False,
        normalization_settings: Optional[NormalizationSettings] = None,
        enable_completed_recovery_proofs: bool = True,
    ):
        super().__init__(
            formula_builder,
            solver_runner,
            debug,
            enable_completed_recovery_proofs=enable_completed_recovery_proofs,
        )
        self.per_query_timeout = 5
        self.per_query_timeout_hard = 30
        self.save_unknown_queries = False
        self.unknown_query_dir = "/tmp"
        self.normalization_settings = normalization_settings or NormalizationSettings.safe()
        self.solver_proven_rewrite_settings = self.normalization_settings
        self.enable_solver_proven_rewrite_fallback = True
        self.enable_normalization_fallback = False
        self._active_safety_checker = None
        # Process-local obligation attempt cache.  The cache is intentionally
        # owned by the strategy instance so recursive/derived pairwise branches
        # can reuse identical logical queries without changing public dispatch
        # or persisting mutable FunctionReturnAnalysis objects.
        from scripts.function_tracer_pcode.proof.obligations import AttemptCache
        self._exact_query_attempt_cache = AttemptCache(max_entries=4096)
        self._obligation_scheduler_run_id = 0
        # Sound process-local reuse of already proven UNSAT pair obligations.
        # Keys contain the complete pair semantic surface and ABI context;
        # UNKNOWN/SAT outcomes are never reused across views.

    def _solve_query_after_guard(
        self,
        base_ctx,
        case1,
        case2,
        param_replace_fn1,
        param_replace_fn2,
        pair_id,
    ):
        """Explicit value-stage seam; guard execution remains in the prepass."""
        from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
            solve_query_after_guard,
        )
        return solve_query_after_guard(
            self, base_ctx, case1, case2,
            param_replace_fn1, param_replace_fn2, pair_id,
        )

    # ---- service implementations (bound explicitly; see <pkg>/*.py) ----
    # pairwise_services.auxiliary_smt
    _auxiliary_smt_logic = _svc_auxiliary_smt._impl__auxiliary_smt_logic
    _build_condition_only_query = _svc_auxiliary_smt._impl__build_condition_only_query
    _build_intrinsic_equivalence_query = _svc_auxiliary_smt._impl__build_intrinsic_equivalence_query
    _build_nonnegative_query = _svc_auxiliary_smt._impl__build_nonnegative_query
    _build_normalized_inequality_query = _svc_auxiliary_smt._impl__build_normalized_inequality_query
    _build_pair_query = _svc_auxiliary_smt._impl__build_pair_query
    _build_single_case_condition_query = _svc_auxiliary_smt._impl__build_single_case_condition_query
    _case_conditions_have_unsupported_smt_op_excluding_unknowns = _svc_auxiliary_smt._impl__case_conditions_have_unsupported_smt_op_excluding_unknowns
    _clone_auxiliary_expression_for_smt = _svc_auxiliary_smt._impl__clone_auxiliary_expression_for_smt
    _collect_auxiliary_float_declarations = _svc_auxiliary_smt._impl__collect_auxiliary_float_declarations
    _collect_intrinsic_parameter_specs = _svc_auxiliary_smt._impl__collect_intrinsic_parameter_specs
    _expression_has_unsupported_smt_op_excluding_unknowns = _svc_auxiliary_smt._impl__expression_has_unsupported_smt_op_excluding_unknowns
    _expression_node_is_unsupported_smt_op = _svc_auxiliary_smt._impl__expression_node_is_unsupported_smt_op
    _expression_uses_float_or_float_op = staticmethod(_svc_auxiliary_smt._impl__expression_uses_float_or_float_op)
    _merge_completed_recovery_proofs_from_solver_analyses = staticmethod(_svc_auxiliary_smt._impl__merge_completed_recovery_proofs_from_solver_analyses)
    _method_b_dual_summary_solver_proof_content = _svc_auxiliary_smt._impl__method_b_dual_summary_solver_proof_content
    _pair_id_and_side_from_value_query_label = staticmethod(_svc_auxiliary_smt._impl__pair_id_and_side_from_value_query_label)
    _prove_intrinsic_equivalence_under_conditions = _svc_auxiliary_smt._impl__prove_intrinsic_equivalence_under_conditions
    _record_completed_method_b_dual_summary_solver_proof_if_safe = _svc_auxiliary_smt._impl__record_completed_method_b_dual_summary_solver_proof_if_safe
    _render_auxiliary_smt = _svc_auxiliary_smt._impl__render_auxiliary_smt
    _return_cases_have_smt_total_coverage = _svc_auxiliary_smt._impl__return_cases_have_smt_total_coverage
    _save_unknown_query = _svc_auxiliary_smt._impl__save_unknown_query
    _solve_query_internal = _svc_auxiliary_smt._impl__solve_query_internal
    _solve_query_twostage = _svc_auxiliary_smt._impl__solve_query_twostage
    _solver_rewrite_candidate_object_target_key = _svc_auxiliary_smt._impl__solver_rewrite_candidate_object_target_key
    _solver_rewrite_proof_object_target_key = _svc_auxiliary_smt._impl__solver_rewrite_proof_object_target_key
    _solver_rewrite_side_object_key = _svc_auxiliary_smt._impl__solver_rewrite_side_object_key
    _try_solver_proven_rewrite_equivalence = _svc_auxiliary_smt._impl__try_solver_proven_rewrite_equivalence
    _unsupported_smt_op_keys = _svc_auxiliary_smt._impl__unsupported_smt_op_keys
    # pairwise_services.loop_summary
    _bounded_state_transition_iteration_count_from_conditions = _svc_loop_summary._impl__bounded_state_transition_iteration_count_from_conditions
    _bounded_state_transition_trip_count_is_proved = _svc_loop_summary._impl__bounded_state_transition_trip_count_is_proved
    _canonical_counted_state_transition_outer_start_key = _svc_loop_summary._impl__canonical_counted_state_transition_outer_start_key
    _case_pair_counted_loop_summaries_closed_values_equivalent = _svc_loop_summary._impl__case_pair_counted_loop_summaries_closed_values_equivalent
    _case_pair_counted_loop_summaries_match_by_closed_values = _svc_loop_summary._impl__case_pair_counted_loop_summaries_match_by_closed_values
    _case_pair_counted_loop_summary_matches_closed_expression = _svc_loop_summary._impl__case_pair_counted_loop_summary_matches_closed_expression
    _case_pair_has_one_sided_counted_loop_summary = _svc_loop_summary._impl__case_pair_has_one_sided_counted_loop_summary
    _case_pair_loop_summaries_solver_equivalent = _svc_loop_summary._impl__case_pair_loop_summaries_solver_equivalent
    _case_pair_loop_summaries_solver_equivalent_core = _svc_loop_summary._impl__case_pair_loop_summaries_solver_equivalent_core
    _case_pair_loop_summary_safe_fallback_reason = _svc_loop_summary._impl__case_pair_loop_summary_safe_fallback_reason
    _collect_phi_circular_origin_details = _svc_loop_summary._impl__collect_phi_circular_origin_details
    _composed_counted_state_transition_summaries_match = _svc_loop_summary._impl__composed_counted_state_transition_summaries_match
    _composed_counted_state_transition_summary_key = _svc_loop_summary._impl__composed_counted_state_transition_summary_key
    _counted_loop_affine_closed_expression = _svc_loop_summary._impl__counted_loop_affine_closed_expression
    _counted_loop_affine_closed_expression_candidate = _svc_loop_summary._impl__counted_loop_affine_closed_expression_candidate
    _counted_loop_affine_trip_count_expression = _svc_loop_summary._impl__counted_loop_affine_trip_count_expression
    _counted_loop_affine_values_are_provably_equivalent = _svc_loop_summary._impl__counted_loop_affine_values_are_provably_equivalent
    _counted_loop_affine_widths_are_safe = _svc_loop_summary._impl__counted_loop_affine_widths_are_safe
    _counted_loop_bounded_state_transition_base_candidate = _svc_loop_summary._impl__counted_loop_bounded_state_transition_base_candidate
    _counted_loop_closed_expression_candidates = _svc_loop_summary._impl__counted_loop_closed_expression_candidates
    _counted_loop_limit_matches_start_plus_step_count = _svc_loop_summary._impl__counted_loop_limit_matches_start_plus_step_count
    _counted_loop_outer_side_effect_key = _svc_loop_summary._impl__counted_loop_outer_side_effect_key
    _counted_loop_positive_closed_expression = _svc_loop_summary._impl__counted_loop_positive_closed_expression
    _counted_loop_ref_constant_bias = _svc_loop_summary._impl__counted_loop_ref_constant_bias
    _counted_loop_refs_allow_affine_value_proof = _svc_loop_summary._impl__counted_loop_refs_allow_affine_value_proof
    _counted_loop_summary_contract_key = _svc_loop_summary._impl__counted_loop_summary_contract_key
    _counted_loop_summary_count_identities = _svc_loop_summary._impl__counted_loop_summary_count_identities
    _counted_loop_summary_loop_profile_key = _svc_loop_summary._impl__counted_loop_summary_loop_profile_key
    _counted_loop_summary_runtime_profile_key = _svc_loop_summary._impl__counted_loop_summary_runtime_profile_key
    _counted_loop_summary_wrapper_semantics_match = _svc_loop_summary._impl__counted_loop_summary_wrapper_semantics_match
    _counted_loop_values_are_provably_equivalent = _svc_loop_summary._impl__counted_loop_values_are_provably_equivalent
    _counted_residue_term_at_zero_is_zero = staticmethod(_svc_loop_summary._impl__counted_residue_term_at_zero_is_zero)
    _counted_state_transition_cases_allow_bounded_unroll = _svc_loop_summary._impl__counted_state_transition_cases_allow_bounded_unroll
    _counted_state_transition_semantic_core_key = _svc_loop_summary._impl__counted_state_transition_semantic_core_key
    _counted_state_transition_side_effects_allow_bounded_unroll = _svc_loop_summary._impl__counted_state_transition_side_effects_allow_bounded_unroll
    _counted_state_transition_value_operands_match_ref = _svc_loop_summary._impl__counted_state_transition_value_operands_match_ref
    _expression_contains_loop_summary_runtime = _svc_loop_summary._impl__expression_contains_loop_summary_runtime
    _find_phi_origin_shape_relation = classmethod(_svc_loop_summary._impl__find_phi_origin_shape_relation)
    _is_provable_counted_loop_summary_value = _svc_loop_summary._impl__is_provable_counted_loop_summary_value
    _loop_limit_storage_identity_key = _svc_loop_summary._impl__loop_limit_storage_identity_key
    _loop_limit_storage_key_is_legacy_index_compatible = _svc_loop_summary._impl__loop_limit_storage_key_is_legacy_index_compatible
    _loop_summary_constant_bias = _svc_loop_summary._impl__loop_summary_constant_bias
    _loop_summary_safe_fallback_reason_for_values = _svc_loop_summary._impl__loop_summary_safe_fallback_reason_for_values
    _loop_summary_surface_blocks_solver_equality = _svc_loop_summary._impl__loop_summary_surface_blocks_solver_equality
    _loop_term_descriptor_semantic_key = _svc_loop_summary._impl__loop_term_descriptor_semantic_key
    _method_b_loop_value_object_key = _svc_loop_summary._impl__method_b_loop_value_object_key
    _object_target_contains_originated_phi_circular = classmethod(_svc_loop_summary._impl__object_target_contains_originated_phi_circular)
    _phi_circular_boolean_literals_from_shape = _svc_loop_summary._impl__phi_circular_boolean_literals_from_shape
    _phi_circular_case_condition_literals = _svc_loop_summary._impl__phi_circular_case_condition_literals
    _phi_circular_case_value_shape = staticmethod(_svc_loop_summary._impl__phi_circular_case_value_shape)
    _phi_circular_condition_literals = _svc_loop_summary._impl__phi_circular_condition_literals
    _phi_circular_constant_value = staticmethod(_svc_loop_summary._impl__phi_circular_constant_value)
    _phi_circular_opposing_condition_literals = staticmethod(_svc_loop_summary._impl__phi_circular_opposing_condition_literals)
    _phi_circular_origin_shape_relation = classmethod(_svc_loop_summary._impl__phi_circular_origin_shape_relation)
    _phi_circular_semantic_recurrence_stage_evidence = _svc_loop_summary._impl__phi_circular_semantic_recurrence_stage_evidence
    _phi_circular_shape_kind = staticmethod(_svc_loop_summary._impl__phi_circular_shape_kind)
    _phi_circular_summary_parameter_index = staticmethod(_svc_loop_summary._impl__phi_circular_summary_parameter_index)
    _phi_circular_unknown_count_relation = staticmethod(_svc_loop_summary._impl__phi_circular_unknown_count_relation)
    _phi_circular_unknown_origin_shape_key = classmethod(_svc_loop_summary._impl__phi_circular_unknown_origin_shape_key)
    _phi_circular_value_shape_relation = classmethod(_svc_loop_summary._impl__phi_circular_value_shape_relation)
    _prove_counted_loop_closed_expression_candidates = _svc_loop_summary._impl__prove_counted_loop_closed_expression_candidates
    _runtime_loop_contract_shortcut_decision = _svc_loop_summary._impl__runtime_loop_contract_shortcut_decision
    _semantic_recurrence_jsonable = staticmethod(_svc_loop_summary._impl__semantic_recurrence_jsonable)
    _semantic_recurrence_query_plan = classmethod(_svc_loop_summary._impl__semantic_recurrence_query_plan)
    _stable_semantic_recurrence_hash = staticmethod(_svc_loop_summary._impl__stable_semantic_recurrence_hash)
    _tuple_is_originated_phi_circular_runtime_ref = staticmethod(_svc_loop_summary._impl__tuple_is_originated_phi_circular_runtime_ref)
    _unknown_reason_id_for_loop_fallback = _svc_loop_summary._impl__unknown_reason_id_for_loop_fallback
    _unroll_counted_state_transition_value = _svc_loop_summary._impl__unroll_counted_state_transition_value
    _value_contains_originated_phi_circular = classmethod(_svc_loop_summary._impl__value_contains_originated_phi_circular)
    # pairwise_services.loop_summary (continued)
    _case_pair_can_defer_loop_summary_proof = _svc_loop_summary._impl__case_pair_can_defer_loop_summary_proof
    _clone_auxiliary_counted_loop_summary_ref = _svc_loop_summary._impl__clone_auxiliary_counted_loop_summary_ref
    _clone_auxiliary_loop_summary_ref = _svc_loop_summary._impl__clone_auxiliary_loop_summary_ref
    _counted_loop_refs_allow_value_proof = _svc_loop_summary._impl__counted_loop_refs_allow_value_proof
    _counted_loop_refs_match_ignoring_signedness = _svc_loop_summary._impl__counted_loop_refs_match_ignoring_signedness
    _counted_loop_signedness_difference_is_guarded = _svc_loop_summary._impl__counted_loop_signedness_difference_is_guarded
    _loop_summary_contracts_match_without_guard = _svc_loop_summary._impl__loop_summary_contracts_match_without_guard
    _pending_loop_summary_pair_has_exact_delta_coverage = _svc_loop_summary._impl__pending_loop_summary_pair_has_exact_delta_coverage
    _phi_circular_case_shape_and_unknowns = _svc_loop_summary._impl__phi_circular_case_shape_and_unknowns
    _phi_circular_expression_shape_key = _svc_loop_summary._impl__phi_circular_expression_shape_key
    _resolve_pending_loop_summary_pairs_with_partition_proof = _svc_loop_summary._impl__resolve_pending_loop_summary_pairs_with_partition_proof
    _unknown_expression_is_originated_phi_circular = classmethod(_svc_loop_summary._impl__unknown_expression_is_originated_phi_circular)
    # pairwise_services.orchestration
    _accumulator_proof_count_surface_expressions = _svc_method_b_closure._impl__accumulator_proof_count_surface_expressions
    _accumulator_proof_supports_count_bit_width = _svc_method_b_closure._impl__accumulator_proof_supports_count_bit_width
    _append_blocking_unknown_reasons = classmethod(_svc_orchestration._impl__append_blocking_unknown_reasons)
    _append_completed_method_b_covering_case_evidence = _svc_method_b_closure._impl__append_completed_method_b_covering_case_evidence
    _append_completed_method_b_guard_partition_evidence = _svc_method_b_closure._impl__append_completed_method_b_guard_partition_evidence
    _apply_auxiliary_entailed_extension = _svc_parameter_identity._impl__apply_auxiliary_entailed_extension
    _auxiliary_identity_sort_key = _svc_parameter_identity._impl__auxiliary_identity_sort_key
    _auxiliary_entailed_extensions_by_index = _svc_parameter_identity._impl__auxiliary_entailed_extensions_by_index
    _auxiliary_semantic_parameter_sources = _svc_parameter_identity._impl__auxiliary_semantic_parameter_sources
    _blocking_unknown_reasons_should_replace_pair_unknowns = staticmethod(_svc_orchestration._impl__blocking_unknown_reasons_should_replace_pair_unknowns)
    _build_auxiliary_parameter_infos = _svc_parameter_identity._impl__build_auxiliary_parameter_infos
    _case_comparison_bit_width = _svc_case_conditions._impl__case_comparison_bit_width
    _case_pair_comparison_result_size = _svc_case_conditions._impl__case_pair_comparison_result_size
    _case_pair_conditions_unsat_under_shared_inputs = _svc_orchestration._impl__case_pair_conditions_unsat_under_shared_inputs
    _case_summary_condition_basis = _svc_case_conditions._impl__case_summary_condition_basis
    _case_union_condition = _svc_case_conditions._impl__case_union_condition
    _cases_have_equivalent_summary_conditions = _svc_case_conditions._impl__cases_have_equivalent_summary_conditions
    _cases_have_pair_local_summary_guard_compatibility = _svc_case_conditions._impl__cases_have_pair_local_summary_guard_compatibility
    _clone_auxiliary_residue_bias_terms = _svc_parameter_identity._impl__clone_auxiliary_residue_bias_terms
    _coerce_expression_to_size = _svc_case_conditions._impl__coerce_expression_to_size
    _collect_parameter_expression_nodes = _svc_parameter_identity._impl__collect_parameter_expression_nodes
    _collect_parameter_expression_nodes_into = _svc_parameter_identity._impl__collect_parameter_expression_nodes_into
    _collect_summary_parameter_refs = _svc_parameter_identity._impl__collect_summary_parameter_refs
    _combined_summary_conditions = _svc_case_conditions._impl__combined_summary_conditions
    _condition_as_bool_expression = _svc_case_conditions._impl__condition_as_bool_expression
    _condition_delta_region_is_covered_by_cases = _svc_case_conditions._impl__condition_delta_region_is_covered_by_cases
    _condition_implies = _svc_case_conditions._impl__condition_implies
    _condition_positive_equality_operands = _svc_case_conditions._impl__condition_positive_equality_operands
    _condition_region_is_unsat_for_cases = _svc_case_conditions._impl__condition_region_is_unsat_for_cases
    _condition_set_implies = _svc_case_conditions._impl__condition_set_implies
    _condition_set_is_unsat = _svc_case_conditions._impl__condition_set_is_unsat
    _conditions_are_semantically_equivalent = _svc_case_conditions._impl__conditions_are_semantically_equivalent
    _conditions_have_parameter_mask_constant_conflict = _svc_case_conditions._impl__conditions_have_parameter_mask_constant_conflict
    _count_identity_components_compatible = _svc_method_b_closure._impl__count_identity_components_compatible
    _count_storage_low_projection_compatible = _svc_method_b_closure._impl__count_storage_low_projection_compatible
    _diagnostic_key_or_semantic_key_or_stable_key_or_none = staticmethod(_svc_method_b_closure._impl__diagnostic_key_or_semantic_key_or_stable_key_or_none)
    _expression_is_provably_nonnegative_under_conditions = _svc_case_conditions._impl__expression_is_provably_nonnegative_under_conditions
    _expression_is_zero = _svc_case_conditions._impl__expression_is_zero
    _expression_prefers_signed_extension = _svc_case_conditions._impl__expression_prefers_signed_extension
    _extract_affine_limit_trip_count_candidate = _svc_case_conditions._impl__extract_affine_limit_trip_count_candidate
    _extract_constant_scaled_expression = _svc_case_conditions._impl__extract_constant_scaled_expression
    _fp_denominator_count_identity_matches = staticmethod(_svc_orchestration._impl__fp_denominator_count_identity_matches)
    _fp_denominator_name_fallback_matches_unique_count = _svc_orchestration._impl__fp_denominator_name_fallback_matches_unique_count
    _iter_expression_nodes = _svc_case_conditions._impl__iter_expression_nodes
    _method_b_closure_object_target_key = _svc_method_b_closure._impl__method_b_closure_object_target_key
    _method_b_closure_relation_object_key = _svc_method_b_closure._impl__method_b_closure_relation_object_key
    _method_b_closure_side_object_key = _svc_method_b_closure._impl__method_b_closure_side_object_key
    _method_b_covering_case_proof = _svc_method_b_closure._impl__method_b_covering_case_proof
    _method_b_covering_relation_matches_proof = staticmethod(_svc_method_b_closure._impl__method_b_covering_relation_matches_proof)
    _method_b_key_with_explicit_optional_none = _svc_method_b_closure._impl__method_b_key_with_explicit_optional_none
    _method_b_normalized_term_contract_key = _svc_method_b_closure._impl__method_b_normalized_term_contract_key
    _method_b_one_sided_summary_relation = _svc_method_b_closure._impl__method_b_one_sided_summary_relation
    _method_b_recovery_action = staticmethod(_svc_method_b_closure._impl__method_b_recovery_action)
    _method_b_summary_profile_key = _svc_method_b_closure._impl__method_b_summary_profile_key
    _method_b_value_key_or_none = _svc_method_b_closure._impl__method_b_value_key_or_none
    _object_target_contains_void_opaque_unknown = classmethod(_svc_opaque_unknowns._impl__object_target_contains_void_opaque_unknown)
    _opaque_unknown_refs_from_value = classmethod(_svc_opaque_unknowns._impl__opaque_unknown_refs_from_value)
    _opaque_unknown_return_object_evidence_from_target = _svc_opaque_unknowns._impl__opaque_unknown_return_object_evidence_from_target
    _parameter_constant_equality = _svc_case_conditions._impl__parameter_constant_equality
    _parameter_descriptor_identity_keys = _svc_parameter_identity._impl__parameter_descriptor_identity_keys
    _parameter_descriptor_index_identity_key = _svc_parameter_identity._impl__parameter_descriptor_index_identity_key
    _parameter_descriptor_storage_identity_key = _svc_parameter_identity._impl__parameter_descriptor_storage_identity_key
    _parameter_expression_identity_keys = _svc_parameter_identity._impl__parameter_expression_identity_keys
    _parameter_expression_index_identity_key = _svc_parameter_identity._impl__parameter_expression_index_identity_key
    _parameter_expression_key = _svc_case_conditions._impl__parameter_expression_key
    _parameter_expression_storage_identity_key = _svc_parameter_identity._impl__parameter_expression_storage_identity_key
    _parameter_mask_equality = _svc_case_conditions._impl__parameter_mask_equality
    _parameter_plus_constant_affine = _svc_case_conditions._impl__parameter_plus_constant_affine
    _pcode_origin_cross_binary_shape_key = staticmethod(_svc_opaque_unknowns._impl__pcode_origin_cross_binary_shape_key)
    _record_completed_method_b_covering_case_proof_if_safe = _svc_method_b_closure._impl__record_completed_method_b_covering_case_proof_if_safe
    _register_storage_identity_components = _svc_method_b_closure._impl__register_storage_identity_components
    _replace_expression_node = _svc_case_conditions._impl__replace_expression_node
    _semantic_key_or_stable_key_or_none = staticmethod(_svc_method_b_closure._impl__semantic_key_or_stable_key_or_none)
    _solve_affine_equality = _svc_case_conditions._impl__solve_affine_equality
    _storage_info_from_parameter_descriptor = _svc_parameter_identity._impl__storage_info_from_parameter_descriptor
    _unknown_expression_classification_key = _svc_opaque_unknowns._impl__unknown_expression_classification_key
    _unknown_reason_dedup_key = staticmethod(_svc_orchestration._impl__unknown_reason_dedup_key)
    _unsupported_ops_include_memory_or_effect = staticmethod(_svc_opaque_unknowns._impl__unsupported_ops_include_memory_or_effect)
    check = _svc_orchestration._impl_check
    # pairwise_services.orchestration (continued)
    _cases_are_contradictory = _svc_pair_cases._impl__cases_are_contradictory
    _clear_pairwise_extra_assertions = _svc_pair_cases._impl__clear_pairwise_extra_assertions
    _collect_case_unknown_expression_nodes = _svc_pair_cases._impl__collect_case_unknown_expression_nodes
    _collect_unknown_expression_nodes = _svc_pair_cases._impl__collect_unknown_expression_nodes
    _collect_unknown_expression_nodes_into = _svc_pair_cases._impl__collect_unknown_expression_nodes_into
    _conditions_with_object_identity_parameter_symbols = _svc_pair_cases._impl__conditions_with_object_identity_parameter_symbols
    _create_aggregate_result = _svc_pair_cases._impl__create_aggregate_result
    _create_empty_result = _svc_pair_cases._impl__create_empty_result
    _debug_symbol_mapping = _svc_pair_cases._impl__debug_symbol_mapping
    _expressions_share_object_centric_structure = _svc_pair_cases._impl__expressions_share_object_centric_structure
    _extract_return_cases = _svc_pair_cases._impl__extract_return_cases
    _get_expression_safety_checker = _svc_pair_cases._impl__get_expression_safety_checker
    _low_mask_width_bytes = _svc_pair_cases._impl__low_mask_width_bytes
    _normalize_constant_bias = _svc_pair_cases._impl__normalize_constant_bias
    _opaque_parameter_object_identity_key = _svc_pair_cases._impl__opaque_parameter_object_identity_key
    _parameter_object_identity_key = _svc_pair_cases._impl__parameter_object_identity_key
    _prune_unreachable_cases = _svc_pair_cases._impl__prune_unreachable_cases
    _raw_constant_value = _svc_pair_cases._impl__raw_constant_value
    _register_pairwise_extra_assertions = _svc_pair_cases._impl__register_pairwise_extra_assertions
    _solve_canonical_return_observation = _svc_pair_cases._impl__solve_canonical_return_observation
    _try_normalization_equivalence = _svc_pair_cases._impl__try_normalization_equivalence
    # pairwise_services.readonly_reduction
    _case_allows_reduction_count = _svc_readonly_reduction._impl__case_allows_reduction_count
    _case_has_direct_reduction_count_equality = _svc_readonly_reduction._impl__case_has_direct_reduction_count_equality
    _case_implies_reduction_count = _svc_readonly_reduction._impl__case_implies_reduction_count
    _case_pair_readonly_contract_result_size = _svc_readonly_reduction._impl__case_pair_readonly_contract_result_size
    _case_reduction_count_bit_width = _svc_readonly_reduction._impl__case_reduction_count_bit_width
    _cases_admit_reduction_count = _svc_readonly_reduction._impl__cases_admit_reduction_count
    _cases_admit_reduction_count_values = _svc_readonly_reduction._impl__cases_admit_reduction_count_values
    _cases_have_equivalent_readonly_reduction_proof = _svc_readonly_reduction._impl__cases_have_equivalent_readonly_reduction_proof
    _cases_have_equivalent_runtime_reductions = _svc_readonly_reduction._impl__cases_have_equivalent_runtime_reductions
    _combine_readonly_address_affine = _svc_readonly_reduction._impl__combine_readonly_address_affine
    _combined_conditions_imply_reduction_count = _svc_readonly_reduction._impl__combined_conditions_imply_reduction_count
    _combined_conditions_imply_reduction_count_values = _svc_readonly_reduction._impl__combined_conditions_imply_reduction_count_values
    _exact_reduction_count_search_bound = _svc_readonly_reduction._impl__exact_reduction_count_search_bound
    _exact_terms_match_reduction_proof_under_case_conditions = _svc_readonly_reduction._impl__exact_terms_match_reduction_proof_under_case_conditions
    _exact_value_matches_readonly_reduction_proof = _svc_readonly_reduction._impl__exact_value_matches_readonly_reduction_proof
    _expression_is_full_reduction_count_view = _svc_readonly_reduction._impl__expression_is_full_reduction_count_view
    _expression_is_projected_reduction_count_mask_view = _svc_readonly_reduction._impl__expression_is_projected_reduction_count_mask_view
    _extract_fp_count_one_readonly_terms_and_bias_from_expression = _svc_readonly_reduction._impl__extract_fp_count_one_readonly_terms_and_bias_from_expression
    _extract_fp_count_one_readonly_terms_from_expression = _svc_readonly_reduction._impl__extract_fp_count_one_readonly_terms_from_expression
    _extract_full_width_masked_reduction_count_affine = _svc_readonly_reduction._impl__extract_full_width_masked_reduction_count_affine
    _extract_full_width_masked_reduction_count_view = _svc_readonly_reduction._impl__extract_full_width_masked_reduction_count_view
    _extract_readonly_address_affine = _svc_readonly_reduction._impl__extract_readonly_address_affine
    _extract_reduction_count_affine = _svc_readonly_reduction._impl__extract_reduction_count_affine
    _fp_denominator_matches_reduction_count = _svc_readonly_reduction._impl__fp_denominator_matches_reduction_count
    _method_b_readonly_summary_ref = _svc_readonly_reduction._impl__method_b_readonly_summary_ref
    _parameter_matches_reduction_count_identity = _svc_readonly_reduction._impl__parameter_matches_reduction_count_identity
    _parameters_have_conflicting_reduction_count_storage = _svc_readonly_reduction._impl__parameters_have_conflicting_reduction_count_storage
    _prove_exact_load_sum_covers_readonly_loop_summary = _svc_readonly_reduction._impl__prove_exact_load_sum_covers_readonly_loop_summary
    _prove_exact_load_sum_matches_readonly_loop_summary = _svc_readonly_reduction._impl__prove_exact_load_sum_matches_readonly_loop_summary
    _prove_exact_load_sum_matches_readonly_reduction = _svc_readonly_reduction._impl__prove_exact_load_sum_matches_readonly_reduction
    _readonly_contract_count_identities_compatible = _svc_readonly_reduction._impl__readonly_contract_count_identities_compatible
    _readonly_contract_count_projection_compatible = _svc_readonly_reduction._impl__readonly_contract_count_projection_compatible
    _readonly_contract_effective_result_size = _svc_readonly_reduction._impl__readonly_contract_effective_result_size
    _readonly_contract_limit_keys_compatible = _svc_readonly_reduction._impl__readonly_contract_limit_keys_compatible
    _readonly_contract_pairwise_extra_assertions = _svc_readonly_reduction._impl__readonly_contract_pairwise_extra_assertions
    _readonly_count_identities_compatible = _svc_readonly_reduction._impl__readonly_count_identities_compatible
    _readonly_count_identity_key = _svc_readonly_reduction._impl__readonly_count_identity_key
    _readonly_count_identity_keys = _svc_readonly_reduction._impl__readonly_count_identity_keys
    _readonly_count_index_identity_key = _svc_readonly_reduction._impl__readonly_count_index_identity_key
    _readonly_count_storage_identity_key = _svc_readonly_reduction._impl__readonly_count_storage_identity_key
    _readonly_count_storage_relation_key = _svc_readonly_reduction._impl__readonly_count_storage_relation_key
    _readonly_identity_object_target_key = _svc_readonly_reduction._impl__readonly_identity_object_target_key
    _readonly_identity_relation_object_key = _svc_readonly_reduction._impl__readonly_identity_relation_object_key
    _readonly_identity_side_object_key = _svc_readonly_reduction._impl__readonly_identity_side_object_key
    _readonly_pointer_base_identity_key = _svc_readonly_reduction._impl__readonly_pointer_base_identity_key
    _readonly_projection_contract_count_identities_compatible = _svc_readonly_reduction._impl__readonly_projection_contract_count_identities_compatible
    _readonly_projection_contract_limit_keys_compatible = _svc_readonly_reduction._impl__readonly_projection_contract_limit_keys_compatible
    _readonly_projection_parameter_extension_evidence = _svc_readonly_reduction._impl__readonly_projection_parameter_extension_evidence
    _readonly_projection_ref_storage_matches = _svc_readonly_reduction._impl__readonly_projection_ref_storage_matches
    _readonly_projection_semantic_witnesses_match = _svc_readonly_reduction._impl__readonly_projection_semantic_witnesses_match
    _readonly_projection_span = staticmethod(_svc_readonly_reduction._impl__readonly_projection_span)
    _readonly_projection_term_contracts_match = _svc_readonly_reduction._impl__readonly_projection_term_contracts_match
    _readonly_reduction_contract_keys_compatible = _svc_readonly_reduction._impl__readonly_reduction_contract_keys_compatible
    _readonly_reduction_contract_shortcut_decision = _svc_readonly_reduction._impl__readonly_reduction_contract_shortcut_decision
    _readonly_reduction_ref_object_key = _svc_readonly_reduction._impl__readonly_reduction_ref_object_key
    _readonly_reduction_term_sequence_contract_key = _svc_readonly_reduction._impl__readonly_reduction_term_sequence_contract_key
    _readonly_return_case_partition_member_object_key = _svc_readonly_reduction._impl__readonly_return_case_partition_member_object_key
    _readonly_semantic_witness_keys = _svc_readonly_reduction._impl__readonly_semantic_witness_keys
    _readonly_shared_parameter_index = _svc_readonly_reduction._impl__readonly_shared_parameter_index
    _readonly_value_object_key = _svc_readonly_reduction._impl__readonly_value_object_key
    _record_completed_readonly_identity_projection_proof_if_safe = _svc_readonly_reduction._impl__record_completed_readonly_identity_projection_proof_if_safe
    _reduction_count_bit_width = _svc_readonly_reduction._impl__reduction_count_bit_width
    _reduction_count_equality_condition = _svc_readonly_reduction._impl__reduction_count_equality_condition
    _reduction_count_identity_keys = _svc_readonly_reduction._impl__reduction_count_identity_keys
    _reduction_count_index_identity_key = _svc_readonly_reduction._impl__reduction_count_index_identity_key
    _reduction_count_membership_condition = _svc_readonly_reduction._impl__reduction_count_membership_condition
    _reduction_count_parameter_descriptor = _svc_readonly_reduction._impl__reduction_count_parameter_descriptor
    _reduction_count_parameter_expression = _svc_readonly_reduction._impl__reduction_count_parameter_expression
    _reduction_count_storage_identity_key = _svc_readonly_reduction._impl__reduction_count_storage_identity_key
    _solve_reduction_count_affine_equality = _svc_readonly_reduction._impl__solve_reduction_count_affine_equality
    _solve_reduction_count_affine_equality_between_expressions = _svc_readonly_reduction._impl__solve_reduction_count_affine_equality_between_expressions
    _solve_reduction_count_masked_equality = _svc_readonly_reduction._impl__solve_reduction_count_masked_equality
    _value_contains_readonly_ref = classmethod(_svc_readonly_reduction._impl__value_contains_readonly_ref)
    # pairwise_services.readonly_reduction (continued)
    _exact_reduction_count_constant = _svc_readonly_reduction._impl__exact_reduction_count_constant
    _expression_contains_reduction_count_surface_at_width = _svc_readonly_reduction._impl__expression_contains_reduction_count_surface_at_width
    _extract_readonly_reduction_term_descriptor = _svc_readonly_reduction._impl__extract_readonly_reduction_term_descriptor
    _extract_readonly_reduction_terms_and_bias_from_expression = _svc_readonly_reduction._impl__extract_readonly_reduction_terms_and_bias_from_expression
    _extract_readonly_reduction_terms_from_expression = _svc_readonly_reduction._impl__extract_readonly_reduction_terms_from_expression
    _flatten_readonly_add_terms = _svc_readonly_reduction._impl__flatten_readonly_add_terms
    _readonly_reduction_values_equivalent = _svc_readonly_reduction._impl__readonly_reduction_values_equivalent
    # pairwise_services.runtime_shortcut
    _case_conditions_cover_runtime_summary_guards = _svc_runtime_shortcut._impl__case_conditions_cover_runtime_summary_guards
    _case_pair_has_runtime_guard_coverage_or_equivalence = _svc_runtime_shortcut._impl__case_pair_has_runtime_guard_coverage_or_equivalence
    _clone_auxiliary_runtime_ref_for_smt = _svc_runtime_shortcut._impl__clone_auxiliary_runtime_ref_for_smt
    _expressions_same_shape_ignoring_runtime = _svc_runtime_shortcut._impl__expressions_same_shape_ignoring_runtime
    _intrinsic_runtime_values_equivalent = _svc_runtime_shortcut._impl__intrinsic_runtime_values_equivalent
    _method_b_expression_runtime_object_key = _svc_runtime_shortcut._impl__method_b_expression_runtime_object_key
    _method_b_summary_runtime_ref = _svc_runtime_shortcut._impl__method_b_summary_runtime_ref
    _runtime_ref_has_guard_constraints = _svc_runtime_shortcut._impl__runtime_ref_has_guard_constraints
    _runtime_refs_exact_shortcut_decision = _svc_runtime_shortcut._impl__runtime_refs_exact_shortcut_decision
    _runtime_refs_require_guard_equivalence = _svc_runtime_shortcut._impl__runtime_refs_require_guard_equivalence
    _runtime_refs_semantic_shortcut_decision = _svc_runtime_shortcut._impl__runtime_refs_semantic_shortcut_decision
    _runtime_refs_share_shortcut_semantics = _svc_runtime_shortcut._impl__runtime_refs_share_shortcut_semantics
    _runtime_refs_shortcut_decision = _svc_runtime_shortcut._impl__runtime_refs_shortcut_decision
    _runtime_summary_guard_conditions_from_expression = _svc_runtime_shortcut._impl__runtime_summary_guard_conditions_from_expression
    # pairwise_services.unresolved_lowering
    _case_conditions_contain_unresolved = _svc_unresolved_lowering._impl__case_conditions_contain_unresolved
    _case_contains_unresolved_expression = _svc_unresolved_lowering._impl__case_contains_unresolved_expression
    _case_value_contains_unresolved = _svc_unresolved_lowering._impl__case_value_contains_unresolved
    _case_value_unresolved_is_pairwise_lowered = _svc_unresolved_lowering._impl__case_value_unresolved_is_pairwise_lowered
    _collect_unresolved_expression_classification = _svc_unresolved_lowering._impl__collect_unresolved_expression_classification
    _deferred_call_info_for_ref = _svc_unresolved_lowering._impl__deferred_call_info_for_ref
    _deferred_call_object_evidence_from_target = _svc_unresolved_lowering._impl__deferred_call_object_evidence_from_target
    _deferred_call_ref_relation = staticmethod(_svc_unresolved_lowering._impl__deferred_call_ref_relation)
    _deferred_call_runtime_refs_from_value = classmethod(_svc_unresolved_lowering._impl__deferred_call_runtime_refs_from_value)
    _deferred_call_semantic_refs = classmethod(_svc_unresolved_lowering._impl__deferred_call_semantic_refs)
    _deferred_call_unknown_lowering_item = _svc_unresolved_lowering._impl__deferred_call_unknown_lowering_item
    _deferred_call_unresolved_expression_stage_evidence = _svc_unresolved_lowering._impl__deferred_call_unresolved_expression_stage_evidence
    _expression_contains_unresolved = _svc_unresolved_lowering._impl__expression_contains_unresolved
    _find_pair_lowering_diagnostic = classmethod(_svc_unresolved_lowering._impl__find_pair_lowering_diagnostic)
    _generic_unresolved_expression_proof_obligations = _svc_unresolved_lowering._impl__generic_unresolved_expression_proof_obligations
    _generic_unresolved_expression_stage_evidence = _svc_unresolved_lowering._impl__generic_unresolved_expression_stage_evidence
    _object_target_contains_deferred_call_unknown = classmethod(_svc_unresolved_lowering._impl__object_target_contains_deferred_call_unknown)
    _opaque_unknown_unresolved_expression_stage_evidence = _svc_unresolved_lowering._impl__opaque_unknown_unresolved_expression_stage_evidence
    _phi_circular_typed_lowering_evidence = _svc_unresolved_lowering._impl__phi_circular_typed_lowering_evidence
    _try_build_unresolved_deferred_call_lowering = _svc_unresolved_lowering._impl__try_build_unresolved_deferred_call_lowering
    _try_build_unresolved_phi_circular_lowering = _svc_unresolved_lowering._impl__try_build_unresolved_phi_circular_lowering
    _unresolved_expression_action_status = _svc_unresolved_lowering._impl__unresolved_expression_action_status
    _unresolved_expression_cause_taxonomy = _svc_unresolved_lowering._impl__unresolved_expression_cause_taxonomy
    _unresolved_expression_deferred_call_diagnostic_evidence = _svc_unresolved_lowering._impl__unresolved_expression_deferred_call_diagnostic_evidence
    _unresolved_expression_generic_diagnostic_evidence = _svc_unresolved_lowering._impl__unresolved_expression_generic_diagnostic_evidence
    _unresolved_expression_location_classification = _svc_unresolved_lowering._impl__unresolved_expression_location_classification
    _unresolved_expression_location_taxonomy = staticmethod(_svc_unresolved_lowering._impl__unresolved_expression_location_taxonomy)
    _unresolved_expression_locations = _svc_unresolved_lowering._impl__unresolved_expression_locations
    _unresolved_expression_object_target_key = _svc_unresolved_lowering._impl__unresolved_expression_object_target_key
    _unresolved_expression_opaque_unknown_diagnostic_evidence = _svc_unresolved_lowering._impl__unresolved_expression_opaque_unknown_diagnostic_evidence
    _unresolved_expression_pair_lowering_diagnostic = _svc_unresolved_lowering._impl__unresolved_expression_pair_lowering_diagnostic
    _unresolved_expression_phi_circular_full_shape_diagnostic_evidence = _svc_unresolved_lowering._impl__unresolved_expression_phi_circular_full_shape_diagnostic_evidence
    _unresolved_expression_recovery_proof_obligations = _svc_unresolved_lowering._impl__unresolved_expression_recovery_proof_obligations
    _unresolved_expression_side_object_key = _svc_unresolved_lowering._impl__unresolved_expression_side_object_key
    _unresolved_expression_substage = staticmethod(_svc_unresolved_lowering._impl__unresolved_expression_substage)
    _unresolved_expression_target_cause = classmethod(_svc_unresolved_lowering._impl__unresolved_expression_target_cause)
    _unresolved_expression_target_uses_generic_pending_census = classmethod(_svc_unresolved_lowering._impl__unresolved_expression_target_uses_generic_pending_census)
    _unresolved_expression_typed_lowering_evidence = _svc_unresolved_lowering._impl__unresolved_expression_typed_lowering_evidence
    _value_contains_deferred_call_ref = classmethod(_svc_unresolved_lowering._impl__value_contains_deferred_call_ref)

from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
    register_canonical_guard_strategy_type,
)

register_canonical_guard_strategy_type(PairwiseStrategy)
