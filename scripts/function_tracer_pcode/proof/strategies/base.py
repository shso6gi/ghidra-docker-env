# -*- coding: utf-8 -*-
"""Compatibility facade for CheckStrategy."""

from scripts.function_tracer_pcode.proof.strategies.proof_gates import (
    call_effect as _svc_call_effect,
    recovery as _svc_recovery,
    return_coverage as _svc_return_coverage,
    return_metadata as _svc_return_metadata,
    sat_safety as _svc_sat_safety,
    blocking_reasons as _svc_blocking_reasons,
    function_identity as _svc_function_identity,
    object_keys as _svc_object_keys,
    target_specificity as _svc_target_specificity,
)
from scripts.function_tracer_pcode.proof.strategies.proof_gates._shared import (
    ABC,
    FunctionReturnAnalysis,
    StrategyResult,
    UnknownReasonId,
    abstractmethod,
)
# Re-exported for modules and tests that import these names from here.
from scripts.function_tracer_pcode.proof.strategies.proof_gates._shared import (
    ReturnCoverageCheckResult,
)

class CheckStrategy(ABC):
    """等価性判定戦略の基底クラス"""

    _RETURN_COVERAGE_TARGET_SCHEMA_VERSION = 3
    _RETURN_COVERAGE_PROOF_SCHEMA_VERSION = 2
    _RETURN_COVERAGE_NORMALIZATION_AWARE_PROOF_SCHEMA_VERSION = 3
    _RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION = 1
    _RETURN_COVERAGE_NORMALIZATION_POLICY_ID = "return-coverage-proof-scoped-normalization"
    _RETURN_COVERAGE_NORMALIZATION_RULESET_VERSION = 1
    _RETURN_COVERAGE_NORMALIZATION_CANONICAL_ENCODING_VERSION = 1
    _RETURN_COVERAGE_DISCHARGEABLE_INCONCLUSIVE_CAUSES = {
        "solver_timeout",
        "smt_disambiguation_inconclusive",
    }

    _CALL_EFFECT_PROOF_RECOVERABLE_UNSAFETY_REASONS = {
        "unsupported_call_effect_summary",
        "effect_summary_path_coverage_incomplete",
        "effect_call_argument_evidence_incomplete",
        "bounded_call_refinement_argument_alignment_failed",
        "bounded_call_refinement_deferred_target_unresolved",
        "bounded_call_refinement_return_summary_unusable",
    }
    _COMPLETED_PROOF_BLOCKER_FIELDS = (
        "sat_unsafety_reasons",
        "coverage_gap_reasons",
        "unsupported_effect_reasons",
        "active_unsafety_reasons",
        "active_coverage_gaps",
        "active_coverage_gap_reasons",
        "active_unsupported_effects",
        "unsupported_call_effect_reasons",
        "unsupported_memory_effect_reasons",
    )
    _CALL_EFFECT_PROOF_CONTENT_REQUIRED_OBJECT_KINDS = {
        "call_argument_evidence",
        "call_target_resolution_evidence",
        "deferred_call",
        "unsupported_call_effect",
        "call_effect_blocker",
    }
    _UNSUPPORTED_CALL_EFFECT_REASON_COMPATIBILITY_GROUPS = (
        frozenset(
            {
                "target_identity_unavailable",
                "callee_unsupported_call_may_expose_parameter_memory",
            }
        ),
    )
    _UNSUPPORTED_CALL_EFFECT_COMPATIBILITY_REQUIRED_FLAGS = (
        "reason_signature_match",
        "target_expression_match",
        "argument_keys_match",
        "path_guard_match",
        "callee_identity_category_match",
        "callee_identity_reachable",
        "unsupported_fact_evidence_complete",
    )
    _READONLY_IDENTITY_ACTION_REQUIREMENT = (
        "object_storage_identity",
        ("object_storage_identity", "count_identity", "guard_implication", "finite_witness"),
    )
    _METHOD_B_ACTION_REQUIREMENTS = {
        ("proof_backed_covering_case", "method_b_covering_case"): (
            "seed_compensation",
            ("seed_compensation", "term_sequence", "pure_side_effect_profile"),
        ),
        ("guard_partition_completion", "method_b_guard_partition"): (
            "guard_partition",
            ("guard_partition", "partition_coverage_proof"),
        ),
    }
    _RETURN_COVERAGE_COMPLETION_REQUIREMENTS = {
        UnknownReasonId.RETURN_COVERAGE_GAP: (
            ("return_partition_extraction", "missing_return_guard"),
            ("return_guard_coverage", "case_guard_disjunction"),
        ),
        UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE: (
            ("return_coverage_smt_disambiguation", "case_guard_disjunction"),
        ),
    }
    
    def __init__(
        self,
        formula_builder,
        solver_runner,
        debug: bool = False,
        enable_completed_recovery_proofs: bool = True,
    ):
        """
        Args:
            formula_builder: FormulaBuilder インスタンス
            solver_runner: ParallelSolverRunner インスタンス
            debug: デバッグモード
        """
        self.formula_builder = formula_builder
        self.solver_runner = solver_runner
        self.debug = debug
        self.enable_completed_recovery_proofs = enable_completed_recovery_proofs

    @abstractmethod
    def check(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        save_formula: bool = False
    ) -> StrategyResult:
        """
        等価性をチェック
        
        Args:
            analysis1: 関数1の解析結果
            analysis2: 関数2の解析結果
            save_formula: SMT式を保存するか
        
        Returns:
            StrategyResult
        """
        pass

    # ---- service implementations (bound explicitly; see <pkg>/*.py) ----
    # proof_gates.call_effect
    _analysis_for_call_effect_object_target = staticmethod(_svc_call_effect._impl__analysis_for_call_effect_object_target)
    _bounded_call_refinement_content_is_complete = _svc_call_effect._impl__bounded_call_refinement_content_is_complete
    _bounded_call_refinement_evidence_for_call_argument_target = _svc_call_effect._impl__bounded_call_refinement_evidence_for_call_argument_target
    _call_argument_bounded_refinement_section_is_complete = classmethod(_svc_call_effect._impl__call_argument_bounded_refinement_section_is_complete)
    _call_argument_callee_summary_section_is_complete = classmethod(_svc_call_effect._impl__call_argument_callee_summary_section_is_complete)
    _call_argument_dependency_graph_section_is_complete = classmethod(_svc_call_effect._impl__call_argument_dependency_graph_section_is_complete)
    _call_argument_evidence_phase15_proof_content = _svc_call_effect._impl__call_argument_evidence_phase15_proof_content
    _call_argument_evidence_phase15_proof_content_is_complete = classmethod(_svc_call_effect._impl__call_argument_evidence_phase15_proof_content_is_complete)
    _call_argument_phase15_sections_are_consistent = classmethod(_svc_call_effect._impl__call_argument_phase15_sections_are_consistent)
    _call_argument_precondition_section_is_complete = classmethod(_svc_call_effect._impl__call_argument_precondition_section_is_complete)
    _call_argument_value_provenance_section_is_complete = classmethod(_svc_call_effect._impl__call_argument_value_provenance_section_is_complete)
    _call_effect_argument_keys_are_present = classmethod(_svc_call_effect._impl__call_effect_argument_keys_are_present)
    _call_effect_blocker_candidate_priority = classmethod(_svc_call_effect._impl__call_effect_blocker_candidate_priority)
    _call_effect_blocker_candidate_score = classmethod(_svc_call_effect._impl__call_effect_blocker_candidate_score)
    _call_effect_blocker_proof_content = _svc_call_effect._impl__call_effect_blocker_proof_content
    _call_effect_blocker_semantic_tie_break = classmethod(_svc_call_effect._impl__call_effect_blocker_semantic_tie_break)
    _call_effect_blocker_sort_token = classmethod(_svc_call_effect._impl__call_effect_blocker_sort_token)
    _call_effect_blocking_object_evidence = _svc_call_effect._impl__call_effect_blocking_object_evidence
    _call_effect_summary_proof_content_is_complete = classmethod(_svc_call_effect._impl__call_effect_summary_proof_content_is_complete)
    _call_effect_summary_proof_content_is_required = classmethod(_svc_call_effect._impl__call_effect_summary_proof_content_is_required)
    _call_effect_summary_proof_id_from_evidence = classmethod(_svc_call_effect._impl__call_effect_summary_proof_id_from_evidence)
    _call_effect_summary_proof_is_complete = _svc_call_effect._impl__call_effect_summary_proof_is_complete
    _call_effect_summary_section_matches = classmethod(_svc_call_effect._impl__call_effect_summary_section_matches)
    _call_effect_target_expression_key_is_present = classmethod(_svc_call_effect._impl__call_effect_target_expression_key_is_present)
    _call_target_is_analysis_entry = classmethod(_svc_call_effect._impl__call_target_is_analysis_entry)
    _completed_call_effect_summary_proof_ids = classmethod(_svc_call_effect._impl__completed_call_effect_summary_proof_ids)
    _cross_binary_call_effect_component_key = classmethod(_svc_call_effect._impl__cross_binary_call_effect_component_key)
    _deferred_call_argument_keys = classmethod(_svc_call_effect._impl__deferred_call_argument_keys)
    _deferred_call_target_expression_key = classmethod(_svc_call_effect._impl__deferred_call_target_expression_key)
    _deferred_calls_semantically_match = _svc_call_effect._impl__deferred_calls_semantically_match
    _expected_call_effect_proof_content_refs = classmethod(_svc_call_effect._impl__expected_call_effect_proof_content_refs)
    _expected_deferred_call_proof_content_refs = classmethod(_svc_call_effect._impl__expected_deferred_call_proof_content_refs)
    _iter_call_effect_blocker_candidates = classmethod(_svc_call_effect._impl__iter_call_effect_blocker_candidates)
    _matched_deferred_call_argument_proof_content = _svc_call_effect._impl__matched_deferred_call_argument_proof_content
    _matched_unknown_indirect_call_effect_fingerprint = _svc_call_effect._impl__matched_unknown_indirect_call_effect_fingerprint
    _matched_unknown_indirect_call_effect_proof_content = _svc_call_effect._impl__matched_unknown_indirect_call_effect_proof_content
    _matched_unsupported_call_effect_no_store_parameter_exposure_proof_content = _svc_call_effect._impl__matched_unsupported_call_effect_no_store_parameter_exposure_proof_content
    _record_completed_call_effect_summary_proof_if_safe = _svc_call_effect._impl__record_completed_call_effect_summary_proof_if_safe
    _select_call_effect_blocker_candidate = classmethod(_svc_call_effect._impl__select_call_effect_blocker_candidate)
    _self_recursive_no_store_call_effect_proof_content = _svc_call_effect._impl__self_recursive_no_store_call_effect_proof_content
    _unsupported_call_effect_argument_evidence_is_complete = classmethod(_svc_call_effect._impl__unsupported_call_effect_argument_evidence_is_complete)
    _unsupported_call_effect_argument_keys = classmethod(_svc_call_effect._impl__unsupported_call_effect_argument_keys)
    _unsupported_call_effect_callee_identity_category = classmethod(_svc_call_effect._impl__unsupported_call_effect_callee_identity_category)
    _unsupported_call_effect_callee_identity_is_reachable = classmethod(_svc_call_effect._impl__unsupported_call_effect_callee_identity_is_reachable)
    _unsupported_call_effect_callee_identity_is_unknown = classmethod(_svc_call_effect._impl__unsupported_call_effect_callee_identity_is_unknown)
    _unsupported_call_effect_callee_identity_key = classmethod(_svc_call_effect._impl__unsupported_call_effect_callee_identity_key)
    _unsupported_call_effect_compatibility_policy_evidence = classmethod(_svc_call_effect._impl__unsupported_call_effect_compatibility_policy_evidence)
    _unsupported_call_effect_compatibility_policy_is_complete = classmethod(_svc_call_effect._impl__unsupported_call_effect_compatibility_policy_is_complete)
    _unsupported_call_effect_has_no_observed_writes = classmethod(_svc_call_effect._impl__unsupported_call_effect_has_no_observed_writes)
    _unsupported_call_effect_occurrence_fingerprint = _svc_call_effect._impl__unsupported_call_effect_occurrence_fingerprint
    _unsupported_call_effect_path_condition_key = classmethod(_svc_call_effect._impl__unsupported_call_effect_path_condition_key)
    _unsupported_call_effect_pcode_ref_key = classmethod(_svc_call_effect._impl__unsupported_call_effect_pcode_ref_key)
    _unsupported_call_effect_reason_compatibility_group = classmethod(_svc_call_effect._impl__unsupported_call_effect_reason_compatibility_group)
    _unsupported_call_effect_reason_is_compatible = classmethod(_svc_call_effect._impl__unsupported_call_effect_reason_is_compatible)
    _unsupported_call_effect_reason_signature = classmethod(_svc_call_effect._impl__unsupported_call_effect_reason_signature)
    _unsupported_call_effect_requires_exact_target_expression_match = classmethod(_svc_call_effect._impl__unsupported_call_effect_requires_exact_target_expression_match)
    _unsupported_call_effect_target_expression_key = classmethod(_svc_call_effect._impl__unsupported_call_effect_target_expression_key)
    _unsupported_call_effects_semantically_match = _svc_call_effect._impl__unsupported_call_effects_semantically_match
    _unsupported_call_output_use_fingerprint = _svc_call_effect._impl__unsupported_call_output_use_fingerprint
    _validated_call_effect_blocker_selected_candidate = classmethod(_svc_call_effect._impl__validated_call_effect_blocker_selected_candidate)
    # proof_gates.call_effect (continued)
    _analysis_has_active_call_effect_proof_blockers = classmethod(_svc_call_effect._impl__analysis_has_active_call_effect_proof_blockers)
    _call_argument_evidence_object_key = _svc_call_effect._impl__call_argument_evidence_object_key
    _call_effect_blocking_object_target_key = _svc_call_effect._impl__call_effect_blocking_object_target_key
    _call_effect_callee_identity_key = staticmethod(_svc_call_effect._impl__call_effect_callee_identity_key)
    _call_output_use_surface_is_complete = classmethod(_svc_call_effect._impl__call_output_use_surface_is_complete)
    _call_target_key_for_analysis = classmethod(_svc_call_effect._impl__call_target_key_for_analysis)
    _call_target_resolution_evidence_object_key = _svc_call_effect._impl__call_target_resolution_evidence_object_key
    _deferred_call_is_blocking = staticmethod(_svc_call_effect._impl__deferred_call_is_blocking)
    _deferred_call_object_target_key = _svc_call_effect._impl__deferred_call_object_target_key
    _deferred_call_proof_content_is_complete = classmethod(_svc_call_effect._impl__deferred_call_proof_content_is_complete)
    _deferred_call_site_object_key = _svc_call_effect._impl__deferred_call_site_object_key
    _matched_unknown_indirect_call_effect_surface_is_complete = classmethod(_svc_call_effect._impl__matched_unknown_indirect_call_effect_surface_is_complete)
    _readonly_side_effect_profile_is_specific = classmethod(_svc_call_effect._impl__readonly_side_effect_profile_is_specific)
    _unsupported_call_effect_object_key = _svc_call_effect._impl__unsupported_call_effect_object_key
    _unsupported_call_effect_proof_content_is_complete = classmethod(_svc_call_effect._impl__unsupported_call_effect_proof_content_is_complete)
    # proof_gates.recovery
    _all_recovery_actions_have_completed_proofs = _svc_recovery._impl__all_recovery_actions_have_completed_proofs
    _completed_proof_section_is_clean = classmethod(_svc_recovery._impl__completed_proof_section_is_clean)
    _completed_recovery_proof_evidence = classmethod(_svc_recovery._impl__completed_recovery_proof_evidence)
    _completed_recovery_proof_ids = classmethod(_svc_recovery._impl__completed_recovery_proof_ids)
    _method_b_closure_proof_content_is_complete = classmethod(_svc_recovery._impl__method_b_closure_proof_content_is_complete)
    _method_b_closure_proof_id_from_evidence = classmethod(_svc_recovery._impl__method_b_closure_proof_id_from_evidence)
    _method_b_closure_proof_is_complete = _svc_recovery._impl__method_b_closure_proof_is_complete
    _method_b_covering_proof_content_matches_relation = classmethod(_svc_recovery._impl__method_b_covering_proof_content_matches_relation)
    _method_b_dual_summary_proof_content_matches_relation = classmethod(_svc_recovery._impl__method_b_dual_summary_proof_content_matches_relation)
    _method_b_guard_proof_content_matches_relation = classmethod(_svc_recovery._impl__method_b_guard_proof_content_matches_relation)
    _method_b_proof_sides_match_relation = classmethod(_svc_recovery._impl__method_b_proof_sides_match_relation)
    _produced_recovery_proof_ids = classmethod(_svc_recovery._impl__produced_recovery_proof_ids)
    _proof_int_like = classmethod(_svc_recovery._impl__proof_int_like)
    _proof_nonnegative_int_like = classmethod(_svc_recovery._impl__proof_nonnegative_int_like)
    _proof_positive_int_like = classmethod(_svc_recovery._impl__proof_positive_int_like)
    _proof_section_payload_matches = classmethod(_svc_recovery._impl__proof_section_payload_matches)
    _proof_status_value_is_complete = classmethod(_svc_recovery._impl__proof_status_value_is_complete)
    _proof_target_contains_diagnostic_value = classmethod(_svc_recovery._impl__proof_target_contains_diagnostic_value)
    _proof_target_contains_missing_or_diagnostic = classmethod(_svc_recovery._impl__proof_target_contains_missing_or_diagnostic)
    _proof_target_contains_weak_value = classmethod(_svc_recovery._impl__proof_target_contains_weak_value)
    _proof_target_pair_is_specific = classmethod(_svc_recovery._impl__proof_target_pair_is_specific)
    _proof_text_is_specific = classmethod(_svc_recovery._impl__proof_text_is_specific)
    _readonly_identity_proof_content_is_complete = classmethod(_svc_recovery._impl__readonly_identity_proof_content_is_complete)
    _readonly_identity_proof_id_from_evidence = classmethod(_svc_recovery._impl__readonly_identity_proof_id_from_evidence)
    _readonly_identity_proof_is_complete = _svc_recovery._impl__readonly_identity_proof_is_complete
    _readonly_projection_extension_proof_content_is_complete = classmethod(_svc_recovery._impl__readonly_projection_extension_proof_content_is_complete)
    _recovery_proof_is_complete = _svc_recovery._impl__recovery_proof_is_complete
    # proof_gates.return_coverage
    _analysis_has_active_return_coverage_blockers = _svc_return_coverage._impl__analysis_has_active_return_coverage_blockers
    _analysis_has_proved_outcome_partition = _svc_return_coverage._impl__analysis_has_proved_outcome_partition
    _analysis_has_total_outcome_partition = _svc_return_coverage._impl__analysis_has_total_outcome_partition
    _analysis_requires_completed_return_coverage_proof = _svc_return_coverage._impl__analysis_requires_completed_return_coverage_proof
    _base_context_has_return_coverage_domain_assumptions = staticmethod(_svc_return_coverage._impl__base_context_has_return_coverage_domain_assumptions)
    _build_return_case_coverage_query = _svc_return_coverage._impl__build_return_case_coverage_query
    _check_return_case_coverage_gap = _svc_return_coverage._impl__check_return_case_coverage_gap
    _collect_return_coverage_unsafety_reasons = _svc_return_coverage._impl__collect_return_coverage_unsafety_reasons
    _sat_decisive_return_coverage_unsafety_reasons = _svc_return_coverage._impl__sat_decisive_return_coverage_unsafety_reasons
    _make_return_coverage_unknown_reason = _svc_return_coverage._impl__make_return_coverage_unknown_reason
    _outcome_condition_groups_are_unsat = _svc_return_coverage._impl__outcome_condition_groups_are_unsat
    _outcome_condition_smt = _svc_return_coverage._impl__outcome_condition_smt
    _outcome_conditions_smt = _svc_return_coverage._impl__outcome_conditions_smt
    _outcome_cross_kind_disjoint = _svc_return_coverage._impl__outcome_cross_kind_disjoint
    _outcome_expression_smt = _svc_return_coverage._impl__outcome_expression_smt
    _outcome_guard_union_is_total = _svc_return_coverage._impl__outcome_guard_union_is_total
    _outcome_guard_union_smt = _svc_return_coverage._impl__outcome_guard_union_smt
    _outcome_guard_unions_equivalent = _svc_return_coverage._impl__outcome_guard_unions_equivalent
    _outcome_partition_covered_labels = _svc_return_coverage._impl__outcome_partition_covered_labels
    _outcome_partition_identity_key = _svc_return_coverage._impl__outcome_partition_identity_key
    _outcome_partition_inconclusive_labels = _svc_return_coverage._impl__outcome_partition_inconclusive_labels
    _outcome_partition_unknown_object_evidence = _svc_return_coverage._impl__outcome_partition_unknown_object_evidence
    _outcome_partition_unknown_object_target_key = _svc_return_coverage._impl__outcome_partition_unknown_object_target_key
    _outcome_partitions_are_equivalent = _svc_return_coverage._impl__outcome_partitions_are_equivalent
    _outcome_return_values_equal_under_guards = _svc_return_coverage._impl__outcome_return_values_equal_under_guards
    _outcome_smt_assertions_are_unsat = _svc_return_coverage._impl__outcome_smt_assertions_are_unsat
    _record_completed_return_coverage_proof = _svc_return_coverage._impl__record_completed_return_coverage_proof
    _return_case_partition_member_object_key = _svc_return_coverage._impl__return_case_partition_member_object_key
    _return_cases_have_object_centric_total_coverage = _svc_return_coverage._impl__return_cases_have_object_centric_total_coverage
    _return_cases_have_smt_total_coverage = _svc_return_coverage._impl__return_cases_have_smt_total_coverage
    _return_coverage_case_debug_suffix = _svc_return_coverage._impl__return_coverage_case_debug_suffix
    _return_coverage_case_identity_key = _svc_return_coverage._impl__return_coverage_case_identity_key
    _return_coverage_covered_proof_content = _svc_return_coverage._impl__return_coverage_covered_proof_content
    _return_coverage_guard_disjunction_identity_key = _svc_return_coverage._impl__return_coverage_guard_disjunction_identity_key
    _return_coverage_guard_evidence_is_complete = classmethod(_svc_return_coverage._impl__return_coverage_guard_evidence_is_complete)
    _return_coverage_identity_contains_forbidden_atoms = classmethod(_svc_return_coverage._impl__return_coverage_identity_contains_forbidden_atoms)
    _return_coverage_inconclusive_proof_content = _svc_return_coverage._impl__return_coverage_inconclusive_proof_content
    _return_coverage_normalization_policy = classmethod(_svc_return_coverage._impl__return_coverage_normalization_policy)
    _return_coverage_normalization_policy_digest = classmethod(_svc_return_coverage._impl__return_coverage_normalization_policy_digest)
    _return_coverage_normalization_proof_content_is_complete = classmethod(_svc_return_coverage._impl__return_coverage_normalization_proof_content_is_complete)
    _return_coverage_normalization_required = classmethod(_svc_return_coverage._impl__return_coverage_normalization_required)
    _return_coverage_normalized_payload_is_complete = classmethod(_svc_return_coverage._impl__return_coverage_normalized_payload_is_complete)
    _return_coverage_object_target_key = _svc_return_coverage._impl__return_coverage_object_target_key
    _return_coverage_object_target_key_is_valid = classmethod(_svc_return_coverage._impl__return_coverage_object_target_key_is_valid)
    _return_coverage_partition_identity_key = _svc_return_coverage._impl__return_coverage_partition_identity_key
    _return_coverage_proof_content_can_discharge_inconclusive = classmethod(_svc_return_coverage._impl__return_coverage_proof_content_can_discharge_inconclusive)
    _return_coverage_proof_content_is_complete = classmethod(_svc_return_coverage._impl__return_coverage_proof_content_is_complete)
    _return_coverage_proof_id_from_evidence = classmethod(_svc_return_coverage._impl__return_coverage_proof_id_from_evidence)
    _return_coverage_proof_is_complete = _svc_return_coverage._impl__return_coverage_proof_is_complete
    _return_coverage_structural_proof_content = _svc_return_coverage._impl__return_coverage_structural_proof_content
    _return_coverage_structural_proof_content_is_complete = classmethod(_svc_return_coverage._impl__return_coverage_structural_proof_content_is_complete)
    _return_coverage_structural_proof_content_matches_target = classmethod(_svc_return_coverage._impl__return_coverage_structural_proof_content_matches_target)
    _return_coverage_target_partition_cases = staticmethod(_svc_return_coverage._impl__return_coverage_target_partition_cases)
    _return_outcome_values_are_equivalent = _svc_return_coverage._impl__return_outcome_values_are_equivalent
    _return_partition_object_key = _svc_return_coverage._impl__return_partition_object_key
    _unknown_outcome_identity_key = _svc_return_coverage._impl__unknown_outcome_identity_key
    _unknown_outcome_member_identity_key = _svc_return_coverage._impl__unknown_outcome_member_identity_key
    _unresolved_return_coverage_unknown_reasons = _svc_return_coverage._impl__unresolved_return_coverage_unknown_reasons
    # proof_gates.return_metadata
    _coerce_return_width = staticmethod(_svc_return_metadata._impl__coerce_return_width)
    _collect_condition_width_sign_metadata = classmethod(_svc_return_metadata._impl__collect_condition_width_sign_metadata)
    _expression_bit_width_from_object_key = classmethod(_svc_return_metadata._impl__expression_bit_width_from_object_key)
    _expression_smt_bit_width_for_object_key = staticmethod(_svc_return_metadata._impl__expression_smt_bit_width_for_object_key)
    _normalize_zero_constant_widths_for_declared_symbols = classmethod(_svc_return_metadata._impl__normalize_zero_constant_widths_for_declared_symbols)
    _return_pcode_value_input_width_bits = staticmethod(_svc_return_metadata._impl__return_pcode_value_input_width_bits)
    # proof_gates.sat_safety
    _complete_v2_sat_counterexample_ambiguity_if_observed = _svc_sat_safety._impl__complete_v2_sat_counterexample_ambiguity_if_observed
    _supersede_rejected_witness_blocker = _svc_sat_safety._impl__supersede_rejected_witness_blocker
    _observe_v2_sat_counterexample_ambiguity = _svc_sat_safety._impl__observe_v2_sat_counterexample_ambiguity
    _collect_decisive_sat_unsafety_reasons = _svc_sat_safety._impl__collect_decisive_sat_unsafety_reasons
    _collect_equivalence_blocking_unsafety_reasons = _svc_sat_safety._impl__collect_equivalence_blocking_unsafety_reasons
    _counterexample_model_fingerprint = classmethod(_svc_sat_safety._impl__counterexample_model_fingerprint)
    _make_blocking_unsafety_unknown_reason = _svc_sat_safety._impl__make_blocking_unsafety_unknown_reason
    _make_sat_counterexample_ambiguous_unknown_reason = _svc_sat_safety._impl__make_sat_counterexample_ambiguous_unknown_reason
    _make_sat_unsafety_unknown_reason = _svc_sat_safety._impl__make_sat_unsafety_unknown_reason
    _normalize_counterexample_model_value = classmethod(_svc_sat_safety._impl__normalize_counterexample_model_value)
    _record_completed_sat_counterexample_replay_proof = _svc_sat_safety._impl__record_completed_sat_counterexample_replay_proof
    _record_pairwise_counterexample_replay_proof = _svc_sat_safety._impl__record_pairwise_counterexample_replay_proof
    _counterexample_replay_reasons = _svc_sat_safety._impl__counterexample_replay_reasons
    _pair_return_width_unsafety_reasons = _svc_sat_safety._impl__pair_return_width_unsafety_reasons
    _sat_counterexample_ambiguous_object_target_key = _svc_sat_safety._impl__sat_counterexample_ambiguous_object_target_key
    _sat_unsafety_object_evidence = _svc_sat_safety._impl__sat_unsafety_object_evidence
    _sat_unsafety_object_target_key = _svc_sat_safety._impl__sat_unsafety_object_target_key
    _sat_unsafety_reason_object_evidence = _svc_sat_safety._impl__sat_unsafety_reason_object_evidence
    _sat_unsafety_reason_object_target_key = _svc_sat_safety._impl__sat_unsafety_reason_object_target_key
    _sat_unsafety_resolution_proof_id_from_evidence = classmethod(_svc_sat_safety._impl__sat_unsafety_resolution_proof_id_from_evidence)
    _sat_unsafety_resolution_proof_is_complete = _svc_sat_safety._impl__sat_unsafety_resolution_proof_is_complete
    _sat_unsafety_side_object_evidence = _svc_sat_safety._impl__sat_unsafety_side_object_evidence
    _sat_unsafety_side_object_key = _svc_sat_safety._impl__sat_unsafety_side_object_key
    _unknown_reason_id_for_blocking_unsafety = _svc_sat_safety._impl__unknown_reason_id_for_blocking_unsafety
    # proof_gates.solver_timeout
    _analysis_binary_id = staticmethod(_svc_object_keys._impl__analysis_binary_id)
    _analysis_entry_key = staticmethod(_svc_object_keys._impl__analysis_entry_key)
    _analysis_entry_offset = classmethod(_svc_function_identity._impl__analysis_entry_offset)
    _artifact_stable_key_for_analysis = classmethod(_svc_object_keys._impl__artifact_stable_key_for_analysis)
    _atom_program_id_like = classmethod(_svc_object_keys._impl__atom_program_id_like)
    _atom_str_is = staticmethod(_svc_object_keys._impl__atom_str_is)
    _binary_pair_id_from_analyses = classmethod(_svc_object_keys._impl__binary_pair_id_from_analyses)
    _blocking_reason_index = classmethod(_svc_blocking_reasons._impl__blocking_reason_index)
    _blocking_reason_kind = classmethod(_svc_blocking_reasons._impl__blocking_reason_kind)
    _canonical_json_digest = classmethod(_svc_object_keys._impl__canonical_json_digest)
    _canonical_jsonable_for_digest = classmethod(_svc_object_keys._impl__canonical_jsonable_for_digest)
    _canonicalize_key_sequence = staticmethod(_svc_object_keys._impl__canonicalize_key_sequence)
    _case_conditions_contain_unresolved_expression = _svc_blocking_reasons._impl__case_conditions_contain_unresolved_expression
    _case_miss_expression = _svc_blocking_reasons._impl__case_miss_expression
    _coerce_timeout_seconds = staticmethod(_svc_object_keys._impl__coerce_timeout_seconds)
    _conditions_runtime_object_key = _svc_object_keys._impl__conditions_runtime_object_key
    _debug_print = _svc_blocking_reasons._impl__debug_print
    _deterministic_function_identity = classmethod(_svc_function_identity._impl__deterministic_function_identity)
    _evidence_bool = classmethod(_svc_blocking_reasons._impl__evidence_bool)
    _evidence_get = staticmethod(_svc_blocking_reasons._impl__evidence_get)
    _evidence_has_any = classmethod(_svc_blocking_reasons._impl__evidence_has_any)
    _evidence_has_any_recursive = classmethod(_svc_blocking_reasons._impl__evidence_has_any_recursive)
    _evidence_required_evidence_matches = classmethod(_svc_blocking_reasons._impl__evidence_required_evidence_matches)
    _evidence_text = classmethod(_svc_blocking_reasons._impl__evidence_text)
    _expression_contains_runtime_ref = classmethod(_svc_blocking_reasons._impl__expression_contains_runtime_ref)
    _expression_contains_unresolved = _svc_blocking_reasons._impl__expression_contains_unresolved
    _expression_runtime_object_key = classmethod(_svc_object_keys._impl__expression_runtime_object_key)
    _guard_union_miss_condition = _svc_blocking_reasons._impl__guard_union_miss_condition
    _identity_freeze = classmethod(_svc_function_identity._impl__identity_freeze)
    _iter_expression_nodes_for_metadata = classmethod(_svc_blocking_reasons._impl__iter_expression_nodes_for_metadata)
    _method_b_closure_relation_fields = classmethod(_svc_target_specificity._impl__method_b_closure_relation_fields)
    _method_b_closure_relation_is_specific = classmethod(_svc_target_specificity._impl__method_b_closure_relation_is_specific)
    _method_b_closure_side_is_specific = classmethod(_svc_target_specificity._impl__method_b_closure_side_is_specific)
    _method_b_closure_target_is_specific = classmethod(_svc_target_specificity._impl__method_b_closure_target_is_specific)
    _method_b_count_identities_are_specific = classmethod(_svc_target_specificity._impl__method_b_count_identities_are_specific)
    _method_b_dual_summary_relation_payload = classmethod(_svc_target_specificity._impl__method_b_dual_summary_relation_payload)
    _method_b_exact_terms_are_specific = classmethod(_svc_target_specificity._impl__method_b_exact_terms_are_specific)
    _method_b_guard_count_values = classmethod(_svc_target_specificity._impl__method_b_guard_count_values)
    _method_b_loop_summary_key_is_specific = classmethod(_svc_target_specificity._impl__method_b_loop_summary_key_is_specific)
    _method_b_one_sided_relation_payload = classmethod(_svc_target_specificity._impl__method_b_one_sided_relation_payload)
    _method_b_readonly_term_is_specific = classmethod(_svc_target_specificity._impl__method_b_readonly_term_is_specific)
    _method_b_runtime_ref_key_is_specific = classmethod(_svc_target_specificity._impl__method_b_runtime_ref_key_is_specific)
    _method_b_summary_profile_is_specific = classmethod(_svc_target_specificity._impl__method_b_summary_profile_is_specific)
    _negated_condition_expression = _svc_blocking_reasons._impl__negated_condition_expression
    _nested_contains_tag = classmethod(_svc_object_keys._impl__nested_contains_tag)
    _normalization_policy_digest_from_target = classmethod(_svc_object_keys._impl__normalization_policy_digest_from_target)
    _normalize_nested_tuple = classmethod(_svc_object_keys._impl__normalize_nested_tuple)
    _normalize_query = staticmethod(_svc_blocking_reasons._impl__normalize_query)
    _normalized_function_signature_key = classmethod(_svc_function_identity._impl__normalized_function_signature_key)
    _object_leaf_is_specific = classmethod(_svc_object_keys._impl__object_leaf_is_specific)
    _positive_int_like = staticmethod(_svc_object_keys._impl__positive_int_like)
    _program_id_like = staticmethod(_svc_object_keys._impl__program_id_like)
    _query_cases_are_nonempty = classmethod(_svc_blocking_reasons._impl__query_cases_are_nonempty)
    _readonly_bit_span_is_specific = classmethod(_svc_target_specificity._impl__readonly_bit_span_is_specific)
    _readonly_component_key_is_specific = classmethod(_svc_target_specificity._impl__readonly_component_key_is_specific)
    _readonly_identity_relation_is_specific = classmethod(_svc_target_specificity._impl__readonly_identity_relation_is_specific)
    _readonly_identity_side_is_specific = classmethod(_svc_target_specificity._impl__readonly_identity_side_is_specific)
    _readonly_identity_storage_relation_from_target = classmethod(_svc_target_specificity._impl__readonly_identity_storage_relation_from_target)
    _readonly_identity_target_is_specific = classmethod(_svc_target_specificity._impl__readonly_identity_target_is_specific)
    _readonly_projection_key_is_specific = classmethod(_svc_target_specificity._impl__readonly_projection_key_is_specific)
    _readonly_storage_relation_is_specific = classmethod(_svc_target_specificity._impl__readonly_storage_relation_is_specific)
    _readonly_term_contract_is_specific = classmethod(_svc_target_specificity._impl__readonly_term_contract_is_specific)
    _return_case_object_key = _svc_object_keys._impl__return_case_object_key
    _return_case_smt_disjunctions = staticmethod(_svc_blocking_reasons._impl__return_case_smt_disjunctions)
    _return_condition_object_key = _svc_object_keys._impl__return_condition_object_key
    _return_guard_disjunction_object_key = _svc_object_keys._impl__return_guard_disjunction_object_key
    _return_storage_object_key = _svc_object_keys._impl__return_storage_object_key
    _return_storage_static_key = staticmethod(_svc_function_identity._impl__return_storage_static_key)
    _return_value_extension_ops_object_key = _svc_object_keys._impl__return_value_extension_ops_object_key
    _rewrite_atom_encoded_program_identity_key = classmethod(_svc_object_keys._impl__rewrite_atom_encoded_program_identity_key)
    _rewrite_program_identity_keys = classmethod(_svc_object_keys._impl__rewrite_program_identity_keys)
    _solver_names_from_parallel_result = staticmethod(_svc_object_keys._impl__solver_names_from_parallel_result)
    _solver_timeout_object_target_key = _svc_object_keys._impl__solver_timeout_object_target_key
    _solver_timeout_options_object_key = _svc_object_keys._impl__solver_timeout_options_object_key
    _solver_timeout_side_object_key = _svc_object_keys._impl__solver_timeout_side_object_key
    _split_blocking_reason = staticmethod(_svc_blocking_reasons._impl__split_blocking_reason)
    _stable_key_or_none = staticmethod(_svc_object_keys._impl__stable_key_or_none)
    _summary_return_blocker_reason_id = staticmethod(_svc_blocking_reasons._impl__summary_return_blocker_reason_id)
    _summary_return_candidate_blocker_reason_ids = classmethod(_svc_blocking_reasons._impl__summary_return_candidate_blocker_reason_ids)
    _tag_payload_is_specific = classmethod(_svc_object_keys._impl__tag_payload_is_specific)
    _typed_target_expression_key = classmethod(_svc_object_keys._impl__typed_target_expression_key)
    _unresolved_equivalence_blocking_unknown_reasons = _svc_blocking_reasons._impl__unresolved_equivalence_blocking_unknown_reasons
    