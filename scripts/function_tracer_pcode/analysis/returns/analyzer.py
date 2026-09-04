# -*- coding: utf-8 -*-
"""Compatibility facade for ReturnAnalyzer."""
from contextlib import contextmanager

from scripts.function_tracer_pcode.analysis.returns import (
    call_recovery as _svc_call_recovery,
    control_recovery as _svc_control_recovery,
    effect_integration as _svc_effect_integration,
    lifecycle as _svc_lifecycle,
    return_extraction as _svc_return_extraction,
    return_normalization as _svc_return_normalization,
    analyze_function as _svc_analyze_function,
    divergence_proofs as _svc_divergence_proofs,
    parameters as _svc_parameters,
    pcode_sites as _svc_pcode_sites,
    phi_origins as _svc_phi_origins,
    placeholder_algebra as _svc_placeholder_algebra,
    stack_protector as _svc_stack_protector,
)
from typing import Any, Dict, List, Optional, Set, Tuple
from scripts.function_tracer_pcode.config.settings import BOUNDED_CALL_MAX_CASES, BOUNDED_CALL_REFINEMENT_ENABLED, BOUNDED_CALL_UNROLL_LIMIT
from scripts.function_tracer_pcode.core.analysis import DeferredCallInfo, FunctionReturnAnalysis
from scripts.function_tracer_pcode.core.expression import Condition
from scripts.function_tracer_pcode.analysis.returns.local_values import LocalValueResolver
from scripts.function_tracer_pcode.analysis.returns.expression_cases import ExpressionCaseService
from scripts.function_tracer_pcode.analysis.returns.condition_logic import ConditionLogicService
from scripts.function_tracer_pcode.analysis.returns.region_facts import (
    RegionFacts,
    input_is_nondata_operand,
    parameter_index_for_location,
)
from scripts.function_tracer_pcode.analysis.returns._shared import (
    AnalysisFailure,
    AnalysisSession,
    EffectSummary,
)
# Re-exported for modules and tests that import these names from here.
from scripts.function_tracer_pcode.analysis.returns._shared import (
    normalize_post_state_expression,
    rewrite_observed_loads_from_effects,
)
# Re-exported for modules and tests that import these names from here.
from scripts.function_tracer_pcode.analysis.returns._shared import (
    ConditionTracker,
    PcodeTracer,
    StructuralRecurrenceSummarizer,
    accept_summary_return_candidates,
    resolve_call_targets,
)

class ReturnAnalyzer:

    def __init__(self, program, debug: bool=False, binary_id: Optional[str]=None, *, enable_completed_recovery_proofs: bool=True):
        self.program = program
        self._region_facts = RegionFacts(program)
        self._local_values = LocalValueResolver(debug_print=self._debug_print)
        self.debug = debug
        self._binary_id = binary_id
        self.enable_completed_recovery_proofs = bool(enable_completed_recovery_proofs)
        self._decompiler = None
        self._analysis_session = AnalysisSession()
        self._current_parameters: List[Dict] = []
        self._expression_cases = ExpressionCaseService(
            current_parameters=lambda: self._current_parameters,
        )
        self._condition_logic = ConditionLogicService(
            constant_int_value=lambda expr: self._constant_int_value(expr),
            decompose_comparison_condition=lambda condition: self._decompose_comparison_condition(condition),
            fold_constant_expression=lambda expr, **kw: self._fold_constant_expression(expr, **kw),
        )
        self._current_effect_summary: Optional[EffectSummary] = None
        self._effect_summary_cache: Dict[Tuple[Any, ...], Any] = {}
        self._effect_summary_parameter_cache: Dict[Tuple[Any, ...], List[Dict]] = {}
        self._call_analysis_cache: Dict[Tuple[Any, ...], Optional[FunctionReturnAnalysis]] = {}
        self._local_target_cache: Dict[Tuple[object, ...], Optional[List[Any]]] = {}
        self._current_deferred_calls: Dict[Tuple[Any, ...], DeferredCallInfo] = {}
        self._deferred_call_counter: int = 0
        self._analysis_in_progress: Dict[Tuple[Any, ...], FunctionReturnAnalysis] = {}
        self._return_path_entry_cache: Dict[Tuple[Any, ...], Optional[List[Tuple[List[Any], List[Condition]]]]] = {}
        self._current_blocked_return_path_conditions: List[List[Condition]] = []
        self._current_noreturn_terminal_observations: List[Dict[str, Any]] = []
        self._bounded_call_refinement_enabled = bool(BOUNDED_CALL_REFINEMENT_ENABLED)
        self._bounded_call_unroll_limit = int(BOUNDED_CALL_UNROLL_LIMIT)
        self._bounded_call_max_cases = int(BOUNDED_CALL_MAX_CASES)
        self._last_function_lookup_error: Optional[str] = None
        self._last_analysis_failure: Optional[AnalysisFailure] = None
        self._current_function_prototype = None
        self._current_function_entry_address_value = None
        self._direct_call_graph: Dict[Tuple[Any, ...], Set[Tuple[Any, ...]]] = {}
        self._direct_call_graph_complete_nodes: Set[Tuple[Any, ...]] = set()

    def _ensure_analysis_session(self) -> AnalysisSession:
        try:
            return object.__getattribute__(self, '_analysis_session')
        except AttributeError:
            session = AnalysisSession()
            object.__setattr__(self, '_analysis_session', session)
            return session

    @property
    def _current_parameters(self):
        return self._ensure_analysis_session().parameters

    @_current_parameters.setter
    def _current_parameters(self, value):
        self._ensure_analysis_session().parameters = value

    @property
    def _current_effect_summary(self):
        return self._ensure_analysis_session().effect_summary

    @_current_effect_summary.setter
    def _current_effect_summary(self, value):
        self._ensure_analysis_session().effect_summary = value

    @property
    def _current_deferred_calls(self):
        return self._ensure_analysis_session().deferred_calls

    @_current_deferred_calls.setter
    def _current_deferred_calls(self, value):
        self._ensure_analysis_session().deferred_calls = value

    @property
    def _current_function_prototype(self):
        return self._ensure_analysis_session().function_prototype

    @_current_function_prototype.setter
    def _current_function_prototype(self, value):
        self._ensure_analysis_session().function_prototype = value

    @property
    def _current_function_entry_address_value(self):
        return self._ensure_analysis_session().function_entry_address

    @_current_function_entry_address_value.setter
    def _current_function_entry_address_value(self, value):
        self._ensure_analysis_session().function_entry_address = value

    @property
    def _current_blocked_return_path_conditions(self):
        return self._ensure_analysis_session().blocked_return_path_conditions

    @_current_blocked_return_path_conditions.setter
    def _current_blocked_return_path_conditions(self, value):
        self._ensure_analysis_session().blocked_return_path_conditions = value

    @property
    def _current_noreturn_terminal_observations(self):
        return self._ensure_analysis_session().noreturn_terminal_observations

    @_current_noreturn_terminal_observations.setter
    def _current_noreturn_terminal_observations(self, value):
        self._ensure_analysis_session().noreturn_terminal_observations = value

    @property
    def _return_path_entry_cache(self):
        return self._ensure_analysis_session().return_path_entry_cache

    @_return_path_entry_cache.setter
    def _return_path_entry_cache(self, value):
        self._ensure_analysis_session().return_path_entry_cache = value

    @contextmanager
    def _analysis_context(self, parameters: List[Dict], effect_summary: Optional[EffectSummary], function_prototype=None, function_entry_address=None):
        """Temporarily bind per-analysis state and restore the parent context on exit."""
        previous_parameters = self._current_parameters
        previous_effect_summary = self._current_effect_summary
        previous_deferred_calls = self._current_deferred_calls
        previous_function_prototype = self._current_function_prototype
        previous_function_entry_address = self._current_function_entry_address_value
        self._current_parameters = parameters
        self._current_effect_summary = effect_summary
        self._current_deferred_calls = {}
        self._current_function_prototype = function_prototype
        self._current_function_entry_address_value = function_entry_address
        try:
            yield
        finally:
            self._current_parameters = previous_parameters
            self._current_effect_summary = previous_effect_summary
            self._current_deferred_calls = previous_deferred_calls
            self._current_function_prototype = previous_function_prototype
            self._current_function_entry_address_value = previous_function_entry_address

    # ---- service implementations (bound explicitly; see <pkg>/*.py) ----
    # call_recovery
    _align_deferred_call_arguments_for_recording = _svc_call_recovery._impl__align_deferred_call_arguments_for_recording
    _apply_bounded_call_refinement = _svc_call_recovery._impl__apply_bounded_call_refinement
    _apply_effect_call_argument_evidence_to_deferred_calls = _svc_call_recovery._impl__apply_effect_call_argument_evidence_to_deferred_calls
    _block_path_contains_noreturn_call = _svc_call_recovery._impl__block_path_contains_noreturn_call
    _bound_parameter_maps_for_target_args = _svc_call_recovery._impl__bound_parameter_maps_for_target_args
    _bound_parameter_storage_values_from_call_args = _svc_call_recovery._impl__bound_parameter_storage_values_from_call_args
    _bound_parameter_values_from_call_args = _svc_call_recovery._impl__bound_parameter_values_from_call_args
    _build_return_tracking_targets = _svc_call_recovery._impl__build_return_tracking_targets
    _cached_callee_analysis_for_outcome_summary = _svc_call_recovery._impl__cached_callee_analysis_for_outcome_summary
    _call_output_proves_wrapper_return = _svc_call_recovery._impl__call_output_proves_wrapper_return
    _call_summary_is_safe = _svc_call_recovery._impl__call_summary_is_safe
    _call_wrapper_recovery_conflicts_with_existing_returns = _svc_call_recovery._impl__call_wrapper_recovery_conflicts_with_existing_returns
    _caller_return_value_matches_param_on_eq_one = _svc_call_recovery._impl__caller_return_value_matches_param_on_eq_one
    _cbranch_direct_target_keys = _svc_call_recovery._impl__cbranch_direct_target_keys
    _coerce_runtime_target_ref = _svc_call_recovery._impl__coerce_runtime_target_ref
    _direct_call_target_function_key = _svc_call_recovery._impl__direct_call_target_function_key
    _enumerate_switch_branch_targets = _svc_call_recovery._impl__enumerate_switch_branch_targets
    _enumerate_switch_dispatch_targets = _svc_call_recovery._impl__enumerate_switch_dispatch_targets
    _expand_linear_code_target = _svc_call_recovery._impl__expand_linear_code_target
    _expression_contains_unknown_or_call = _svc_call_recovery._impl__expression_contains_unknown_or_call
    _expression_unknowns_are_deferred_call_refs = _svc_call_recovery._impl__expression_unknowns_are_deferred_call_refs
    _find_caller_return_partition_for_param_minus_one_obligation = _svc_call_recovery._impl__find_caller_return_partition_for_param_minus_one_obligation
    _find_indirect_dispatch_op_on_block = _svc_call_recovery._impl__find_indirect_dispatch_op_on_block
    _find_terminal_call_from_linear_ops = _svc_call_recovery._impl__find_terminal_call_from_linear_ops
    _find_terminal_call_on_block_path = _svc_call_recovery._impl__find_terminal_call_on_block_path
    _get_freshest_callee_parameters = _svc_call_recovery._impl__get_freshest_callee_parameters
    _get_implicit_return_target_storages = _svc_call_recovery._impl__get_implicit_return_target_storages
    _get_or_analyze_call_target = _svc_call_recovery._impl__get_or_analyze_call_target
    _invoke_get_or_analyze_call_target = _svc_call_recovery._impl__invoke_get_or_analyze_call_target
    _is_noreturn_call_op = _svc_call_recovery._impl__is_noreturn_call_op
    _is_passthrough_storage_live_in_for_call = _svc_call_recovery._impl__is_passthrough_storage_live_in_for_call
    _is_pcode_call_op = _svc_call_recovery._impl__is_pcode_call_op
    _iter_outcome_call_candidates = _svc_call_recovery._impl__iter_outcome_call_candidates
    _local_target_cache_key = _svc_call_recovery._impl__local_target_cache_key
    _make_call_resolver = _svc_call_recovery._impl__make_call_resolver
    _make_deferred_call_recorder = _svc_call_recovery._impl__make_deferred_call_recorder
    _merge_call_argument_recovery_state = staticmethod(_svc_call_recovery._impl__merge_call_argument_recovery_state)
    _merge_deferred_calls_into_current_analysis = _svc_call_recovery._impl__merge_deferred_calls_into_current_analysis
    _normalize_call_target_expression = _svc_call_recovery._impl__normalize_call_target_expression
    _normalize_callother_userop_expression = _svc_call_recovery._impl__normalize_callother_userop_expression
    _normalize_return_callother_userops = _svc_call_recovery._impl__normalize_return_callother_userops
    _recover_call_wrapper_returns = _svc_call_recovery._impl__recover_call_wrapper_returns
    _recover_call_wrapper_returns_from_pcode = _svc_call_recovery._impl__recover_call_wrapper_returns_from_pcode
    _recover_dispatch_call_arguments = _svc_call_recovery._impl__recover_dispatch_call_arguments
    _recover_uncovered_terminal_call_returns_from_pcode = _svc_call_recovery._impl__recover_uncovered_terminal_call_returns_from_pcode
    _resolve_call_expansions = _svc_call_recovery._impl__resolve_call_expansions
    _resolve_local_branch_target = _svc_call_recovery._impl__resolve_local_branch_target
    _resolve_local_code_target_expansions = _svc_call_recovery._impl__resolve_local_code_target_expansions
    _resolve_object_centric_call_targets = _svc_call_recovery._impl__resolve_object_centric_call_targets
    _resolve_switch_case_target_expansions = _svc_call_recovery._impl__resolve_switch_case_target_expansions
    _resolve_target_function = _svc_call_recovery._impl__resolve_target_function
    _rewrite_deferred_runtime_refs_in_expression = _svc_call_recovery._impl__rewrite_deferred_runtime_refs_in_expression
    _should_synthesize_implicit_passthrough_for_call = _svc_call_recovery._impl__should_synthesize_implicit_passthrough_for_call
    _specialize_call_analysis = _svc_call_recovery._impl__specialize_call_analysis
    _specialize_local_target_expansions = _svc_call_recovery._impl__specialize_local_target_expansions
    _switch_recovery_targets_problematic_region = _svc_call_recovery._impl__switch_recovery_targets_problematic_region
    _target_active_key = _svc_call_recovery._impl__target_active_key
    _tracked_values_match_call_output = _svc_call_recovery._impl__tracked_values_match_call_output
    _try_apply_triangular_mod_caller_outcomes = _svc_call_recovery._impl__try_apply_triangular_mod_caller_outcomes
    # call_recovery (continued)
    _clear_resolved_call_effect_blockers = _svc_call_recovery._impl__clear_resolved_call_effect_blockers
    _expression_contains_deferred_call_value = _svc_call_recovery._impl__expression_contains_deferred_call_value
    _find_terminal_call_before_return = _svc_call_recovery._impl__find_terminal_call_before_return
    _is_semantically_lossless_effect_sensitive_rewrite = _svc_call_recovery._impl__is_semantically_lossless_effect_sensitive_rewrite
    _recover_implicit_return_from_terminal_call = _svc_call_recovery._impl__recover_implicit_return_from_terminal_call
    _resolve_function_from_call_target_ref = _svc_call_recovery._impl__resolve_function_from_call_target_ref
    _resolve_object_centric_transfer_targets = _svc_call_recovery._impl__resolve_object_centric_transfer_targets
    # control_recovery
    _address_offset_for_block_endpoint = _svc_control_recovery._impl__address_offset_for_block_endpoint
    _block_debug_key = _svc_control_recovery._impl__block_debug_key
    _block_has_return_op = _svc_control_recovery._impl__block_has_return_op
    _block_predecessor_count = _svc_control_recovery._impl__block_predecessor_count
    _block_reaches = _svc_control_recovery._impl__block_reaches
    _block_start_address_keys = _svc_control_recovery._impl__block_start_address_keys
    _block_start_address_spaces = _svc_control_recovery._impl__block_start_address_spaces
    _block_successors = _svc_control_recovery._impl__block_successors
    _block_writes_outcome_guard_state = _svc_control_recovery._impl__block_writes_outcome_guard_state
    _branch_guarded_affine_ignored_artifacts_are_shadowed = _svc_control_recovery._impl__branch_guarded_affine_ignored_artifacts_are_shadowed
    _branch_guarded_affine_phi_step = _svc_control_recovery._impl__branch_guarded_affine_phi_step
    _branch_guarded_affine_singleton_base_anchor_matches = _svc_control_recovery._impl__branch_guarded_affine_singleton_base_anchor_matches
    _branch_guarded_artifact_is_imprecise_zero_seed = _svc_control_recovery._impl__branch_guarded_artifact_is_imprecise_zero_seed
    _branch_guarded_artifact_is_structural_accumulator_seed_projection = _svc_control_recovery._impl__branch_guarded_artifact_is_structural_accumulator_seed_projection
    _branch_guarded_expression_is_param_minus_one = _svc_control_recovery._impl__branch_guarded_expression_is_param_minus_one
    _branch_guarded_structural_proof_from_return = _svc_control_recovery._impl__branch_guarded_structural_proof_from_return
    _check_condition_coverage = _svc_control_recovery._impl__check_condition_coverage
    _coerce_block_path_entries = _svc_control_recovery._impl__coerce_block_path_entries
    _collect_switch_impacted_return_sites = _svc_control_recovery._impl__collect_switch_impacted_return_sites
    _control_region_returns_are_safe = _svc_control_recovery._impl__control_region_returns_are_safe
    _direct_cbranch_successor_relation = _svc_control_recovery._impl__direct_cbranch_successor_relation
    _find_branch_guarded_structural_proof_tuple = _svc_control_recovery._impl__find_branch_guarded_structural_proof_tuple
    _find_branch_guarded_while_return_partition = _svc_control_recovery._impl__find_branch_guarded_while_return_partition
    _first_high_block_cbranch = _svc_control_recovery._impl__first_high_block_cbranch
    _get_cached_return_path_entries = _svc_control_recovery._impl__get_cached_return_path_entries
    _high_function_cbranch_count = _svc_control_recovery._impl__high_function_cbranch_count
    _high_function_has_forbidden_control_outcome_ops = _svc_control_recovery._impl__high_function_has_forbidden_control_outcome_ops
    _infer_branch_guarded_while_role_parameters = _svc_control_recovery._impl__infer_branch_guarded_while_role_parameters
    _is_control_outcome_forbidden_fp_mnemonic = _svc_control_recovery._impl__is_control_outcome_forbidden_fp_mnemonic
    _iter_high_basic_blocks = _svc_control_recovery._impl__iter_high_basic_blocks
    _iter_high_block_ops = _svc_control_recovery._impl__iter_high_block_ops
    _mark_incomplete_control_flow = _svc_control_recovery._impl__mark_incomplete_control_flow
    _materialize_direct_path_specific_return_source = _svc_control_recovery._impl__materialize_direct_path_specific_return_source
    _phase1_direct_branch_escapes_function_body = _svc_control_recovery._impl__phase1_direct_branch_escapes_function_body
    _propagate_multiequal_input_for_return_path = _svc_control_recovery._impl__propagate_multiequal_input_for_return_path
    _prove_branch_guarded_affine_unit_count_recurrence = _svc_control_recovery._impl__prove_branch_guarded_affine_unit_count_recurrence
    _prove_branch_guarded_structural_nonprogress_must_diverge = _svc_control_recovery._impl__prove_branch_guarded_structural_nonprogress_must_diverge
    _prove_branch_guarded_while_nonprogress_must_diverge = _svc_control_recovery._impl__prove_branch_guarded_while_nonprogress_must_diverge
    _recover_control_flow_returns_from_block_paths = _svc_control_recovery._impl__recover_control_flow_returns_from_block_paths
    _recover_control_region_returns_early = _svc_control_recovery._impl__recover_control_region_returns_early
    _recover_explicit_return_from_block_paths = _svc_control_recovery._impl__recover_explicit_return_from_block_paths
    _recover_explicit_return_from_path_source = _svc_control_recovery._impl__recover_explicit_return_from_path_source
    _recover_switch_like_returns_from_pcode = _svc_control_recovery._impl__recover_switch_like_returns_from_pcode
    _recover_switch_like_returns_from_placeholder_analysis = _svc_control_recovery._impl__recover_switch_like_returns_from_placeholder_analysis
    _return_path_is_covered_by_existing_return = _svc_control_recovery._impl__return_path_is_covered_by_existing_return
    _same_high_block = _svc_control_recovery._impl__same_high_block
    _should_attempt_switch_recovery = _svc_control_recovery._impl__should_attempt_switch_recovery
    _switch_recovery_conflicts_with_unaffected_returns = _svc_control_recovery._impl__switch_recovery_conflicts_with_unaffected_returns
    _switch_recovery_improves_returns = _svc_control_recovery._impl__switch_recovery_improves_returns
    _synthesize_branch_guarded_affine_initial_count_return = _svc_control_recovery._impl__synthesize_branch_guarded_affine_initial_count_return
    _try_apply_branch_guarded_while_outcomes = _svc_control_recovery._impl__try_apply_branch_guarded_while_outcomes
    _validate_branch_guarded_structural_proof = _svc_control_recovery._impl__validate_branch_guarded_structural_proof
    # control_recovery (continued)
    _blocks_match = _svc_control_recovery._impl__blocks_match
    _filter_noreturn_return_path_entries = _svc_control_recovery._impl__filter_noreturn_return_path_entries
    _find_block_index_on_path = _svc_control_recovery._impl__find_block_index_on_path
    _get_block_start_address = _svc_control_recovery._impl__get_block_start_address
    _is_noreturn_control_transfer_op = _svc_control_recovery._impl__is_noreturn_control_transfer_op
    _matches_blocked_return_path_conditions = _svc_control_recovery._impl__matches_blocked_return_path_conditions
    _min_branch_index = _svc_control_recovery._impl__min_branch_index
    _path_condition_sets_union_condition = _svc_control_recovery._impl__path_condition_sets_union_condition
    _recover_implicit_return_from_block_paths = _svc_control_recovery._impl__recover_implicit_return_from_block_paths
    _score_multiequal_incoming_for_return_path = _svc_control_recovery._impl__score_multiequal_incoming_for_return_path
    _select_multiequal_input_for_return_path = _svc_control_recovery._impl__select_multiequal_input_for_return_path
    _select_path_specific_return_source = _svc_control_recovery._impl__select_path_specific_return_source
    _split_branch_index = _svc_control_recovery._impl__split_branch_index
    # analyzer_services.effect_integration
    _accept_effect_rewrite_without_rank_gain = _svc_effect_integration._impl__accept_effect_rewrite_without_rank_gain
    _accept_effect_sensitive_rewrite = _svc_effect_integration._impl__accept_effect_sensitive_rewrite
    _apply_local_store_effect = _svc_effect_integration._impl__apply_local_store_effect
    _apply_observable_effect_surface = _svc_effect_integration._impl__apply_observable_effect_surface
    _build_effect_summary = _svc_effect_integration._impl__build_effect_summary
    _build_function_control_effect_profile = _svc_effect_integration._impl__build_function_control_effect_profile
    _collapse_effect_sensitive_case_wrapper = _svc_effect_integration._impl__collapse_effect_sensitive_case_wrapper
    _concretize_readonly_loads = _svc_effect_integration._impl__concretize_readonly_loads
    _count_memory_reads = _svc_effect_integration._impl__count_memory_reads
    _count_observed_loads = _svc_effect_integration._impl__count_observed_loads
    _effect_sensitive_rewrite_precision = _svc_effect_integration._impl__effect_sensitive_rewrite_precision
    _effect_sensitive_rewrite_rank = _svc_effect_integration._impl__effect_sensitive_rewrite_rank
    _effect_summary_allows_pre_return_structural_summary = _svc_effect_integration._impl__effect_summary_allows_pre_return_structural_summary
    _expression_contains_stale_effect_value_for_post_state = _svc_effect_integration._impl__expression_contains_stale_effect_value_for_post_state
    _extract_stack_protector_memory_probe = _svc_effect_integration._impl__extract_stack_protector_memory_probe
    _invoke_build_effect_summary = _svc_effect_integration._impl__invoke_build_effect_summary
    _iter_effect_sensitive_rewrite_candidates = _svc_effect_integration._impl__iter_effect_sensitive_rewrite_candidates
    _local_memory_key = _svc_effect_integration._impl__local_memory_key
    _make_empty_effect_summary = _svc_effect_integration._impl__make_empty_effect_summary
    _matched_effect_locations = _svc_effect_integration._impl__matched_effect_locations
    _normalize_return_value_with_effect_summary = _svc_effect_integration._impl__normalize_return_value_with_effect_summary
    _prefer_lossless_materialized_post_state_roundtrip = _svc_effect_integration._impl__prefer_lossless_materialized_post_state_roundtrip
    _propagate_indirect_return_effect = _svc_effect_integration._impl__propagate_indirect_return_effect
    _read_memory_value = _svc_effect_integration._impl__read_memory_value
    _rebuild_effect_sensitive_case_wrapper = _svc_effect_integration._impl__rebuild_effect_sensitive_case_wrapper
    _return_info_effective_region_conditions = _svc_effect_integration._impl__return_info_effective_region_conditions
    _rewrite_effect_sensitive_return_value = _svc_effect_integration._impl__rewrite_effect_sensitive_return_value
    _split_effect_sensitive_return_case = _svc_effect_integration._impl__split_effect_sensitive_return_case
    _symbolic_post_state_roundtrip_rejected = _svc_effect_integration._impl__symbolic_post_state_roundtrip_rejected
    # analyzer_services.lifecycle
    _decompile_function = _svc_lifecycle._impl__decompile_function
    _decompose_comparison_condition = _svc_lifecycle._impl__decompose_comparison_condition
    _find_block_info_for_program_offset = _svc_lifecycle._impl__find_block_info_for_program_offset
    _find_function_by_name = _svc_lifecycle._impl__find_function_by_name
    _get_decompiler = _svc_lifecycle._impl__get_decompiler
    _program_identity = _svc_lifecycle._impl__program_identity
    _program_is_big_endian = _svc_lifecycle._impl__program_is_big_endian
    _program_transaction = contextmanager(_svc_lifecycle._impl__program_transaction)
    _program_userop_name = _svc_lifecycle._impl__program_userop_name
    _resolve_function_from_program_offset = _svc_lifecycle._impl__resolve_function_from_program_offset
    analyze_function_by_name = _svc_lifecycle._impl_analyze_function_by_name
    # return_extraction
    _acc_phi_flows_to_return_origin_phi = _svc_return_extraction._impl__acc_phi_flows_to_return_origin_phi
    _analysis_has_ambiguous_condition_region_returns = _svc_return_extraction._impl__analysis_has_ambiguous_condition_region_returns
    _analysis_has_positive_region_outcome_obligation = _svc_return_extraction._impl__analysis_has_positive_region_outcome_obligation
    _analysis_return_size_bytes = _svc_return_extraction._impl__analysis_return_size_bytes
    _analyze_implicit_return_value = _svc_return_extraction._impl__analyze_implicit_return_value
    _analyze_return_op = _svc_return_extraction._impl__analyze_return_op
    _analyze_return_value = _svc_return_extraction._impl__analyze_return_value
    _append_smt_lowerable_phi_return_fallback_infos = _svc_return_extraction._impl__append_smt_lowerable_phi_return_fallback_infos
    _apply_outcome_partition_summaries = _svc_return_extraction._impl__apply_outcome_partition_summaries
    _build_return_infos_from_expansions = _svc_return_extraction._impl__build_return_infos_from_expansions
    _clear_outcome_partition_summaries = _svc_return_extraction._impl__clear_outcome_partition_summaries
    _collect_linear_ops_to_return = _svc_return_extraction._impl__collect_linear_ops_to_return
    _compare_return_region_order = _svc_return_extraction._impl__compare_return_region_order
    _deduplicate_tracked_return_values = _svc_return_extraction._impl__deduplicate_tracked_return_values
    _dump_return_infos = _svc_return_extraction._impl__dump_return_infos
    _exclusivize_return_regions = _svc_return_extraction._impl__exclusivize_return_regions
    _function_body_has_phase1_pure_return_forbidden_ops = _svc_return_extraction._impl__function_body_has_phase1_pure_return_forbidden_ops
    _function_has_no_return = _svc_return_extraction._impl__function_has_no_return
    _get_current_prototype_return_varnodes = _svc_return_extraction._impl__get_current_prototype_return_varnodes
    _get_function_return_varnodes = _svc_return_extraction._impl__get_function_return_varnodes
    _get_return_type = _svc_return_extraction._impl__get_return_type
    _get_return_type_info = _svc_return_extraction._impl__get_return_type_info
    _high_function_has_nonreturning_region_candidate = _svc_return_extraction._impl__high_function_has_nonreturning_region_candidate
    _high_function_has_phase1_pure_return_forbidden_ops = _svc_return_extraction._impl__high_function_has_phase1_pure_return_forbidden_ops
    _infer_abi_return_storages = _svc_return_extraction._impl__infer_abi_return_storages
    _make_pre_return_summary_anchor = _svc_return_extraction._impl__make_pre_return_summary_anchor
    _make_return_info = _svc_return_extraction._impl__make_return_info
    _make_synthetic_outcome_return = _svc_return_extraction._impl__make_synthetic_outcome_return
    _make_tracked_return_storage_value = _svc_return_extraction._impl__make_tracked_return_storage_value
    _make_tracked_return_value = _svc_return_extraction._impl__make_tracked_return_value
    _make_tracked_return_value_from_affecting_op = _svc_return_extraction._impl__make_tracked_return_value_from_affecting_op
    _materialize_tracked_return_source = _svc_return_extraction._impl__materialize_tracked_return_source
    _merge_equivalent_return_infos = _svc_return_extraction._impl__merge_equivalent_return_infos
    _phase1_pure_return_forbids_mnemonic = staticmethod(_svc_return_extraction._impl__phase1_pure_return_forbids_mnemonic)
    _phase1_return_type_is_float = staticmethod(_svc_return_extraction._impl__phase1_return_type_is_float)
    _phi_origin_keys_from_return_varnode_trace = _svc_return_extraction._impl__phi_origin_keys_from_return_varnode_trace
    _prune_less_precise_return_infos = _svc_return_extraction._impl__prune_less_precise_return_infos
    _recover_return_infos_from_tracked_sources = _svc_return_extraction._impl__recover_return_infos_from_tracked_sources
    _resolve_implicit_return_tracked_values = _svc_return_extraction._impl__resolve_implicit_return_tracked_values
    _resolve_local_return_expression = _svc_return_extraction._impl__resolve_local_return_expression
    _return_conditions_cover_region = _svc_return_extraction._impl__return_conditions_cover_region
    _return_info_candidate_phi_origin_keys = _svc_return_extraction._impl__return_info_candidate_phi_origin_keys
    _return_info_return_phi_origin_keys = _svc_return_extraction._impl__return_info_return_phi_origin_keys
    _return_info_summary_identity_key = _svc_return_extraction._impl__return_info_summary_identity_key
    _return_infos_have_conflicting_overlap = _svc_return_extraction._impl__return_infos_have_conflicting_overlap
    _return_origin_phi_has_acc_output_input = _svc_return_extraction._impl__return_origin_phi_has_acc_output_input
    _return_partition_miss_guard = _svc_return_extraction._impl__return_partition_miss_guard
    _return_phi_origin_keys_from_summary_source_key = _svc_return_extraction._impl__return_phi_origin_keys_from_summary_source_key
    _return_region_can_be_shadowed_by_prior = _svc_return_extraction._impl__return_region_can_be_shadowed_by_prior
    _return_region_conditions_imply = _svc_return_extraction._impl__return_region_conditions_imply
    _return_region_conditions_mutually_imply = _svc_return_extraction._impl__return_region_conditions_mutually_imply
    _return_region_priority_key = _svc_return_extraction._impl__return_region_priority_key
    _return_site_key = _svc_return_extraction._impl__return_site_key
    _return_site_metadata_from_info = staticmethod(_svc_return_extraction._impl__return_site_metadata_from_info)
    _return_value_is_multiplicative_phi_recurrence_candidate = _svc_return_extraction._impl__return_value_is_multiplicative_phi_recurrence_candidate
    _return_value_pcode_op_refs_from_varnode = _svc_return_extraction._impl__return_value_pcode_op_refs_from_varnode
    _return_value_producer_chain = staticmethod(_svc_return_extraction._impl__return_value_producer_chain)
    _site_metadata_with_return_value_pcode_op_refs = _svc_return_extraction._impl__site_metadata_with_return_value_pcode_op_refs
    _split_object_centric_return_case = _svc_return_extraction._impl__split_object_centric_return_case
    _storages_overlap_for_return_recovery = _svc_return_extraction._impl__storages_overlap_for_return_recovery
    _subtract_return_region_conjunction = _svc_return_extraction._impl__subtract_return_region_conjunction
    _tracked_return_value_is_affected_by_op = _svc_return_extraction._impl__tracked_return_value_is_affected_by_op
    _tracked_return_value_key = _svc_return_extraction._impl__tracked_return_value_key
    _try_apply_single_guard_nonprogress_loop_outcomes = _svc_return_extraction._impl__try_apply_single_guard_nonprogress_loop_outcomes
    _try_apply_triangular_mod_optimized_outcomes = _svc_return_extraction._impl__try_apply_triangular_mod_optimized_outcomes
    _try_pre_return_counted_loop_summary = _svc_return_extraction._impl__try_pre_return_counted_loop_summary
    # return_extraction (continued)
    _can_safely_collapse_complementary_return_pair = _svc_return_extraction._impl__can_safely_collapse_complementary_return_pair
    _make_merged_return_info = _svc_return_extraction._impl__make_merged_return_info
    _merge_return_info_pair = _svc_return_extraction._impl__merge_return_info_pair
    _merge_return_info_summary_candidate_source_keys = _svc_return_extraction._impl__merge_return_info_summary_candidate_source_keys
    _partition_return_conditions = _svc_return_extraction._impl__partition_return_conditions
    # analyzer_services.return_normalization
    _normalize_bound_parameter_storage_values = _svc_return_normalization._impl__normalize_bound_parameter_storage_values
    _normalize_bound_parameter_values = _svc_return_normalization._impl__normalize_bound_parameter_values
    _normalize_expanded_return_value = _svc_return_normalization._impl__normalize_expanded_return_value
    _normalize_return_partition = _svc_return_normalization._impl__normalize_return_partition
    _rewrite_drops_composite_location_wrapper = _svc_return_normalization._impl__rewrite_drops_composite_location_wrapper
    _rewrite_expression_signedness = _svc_return_normalization._impl__rewrite_expression_signedness
    _rewrite_single_tracked_return_value_for_op = _svc_return_normalization._impl__rewrite_single_tracked_return_value_for_op
    _rewrite_tracked_return_values_for_op = _svc_return_normalization._impl__rewrite_tracked_return_values_for_op
    _should_replay_canonicalized_return = _svc_return_normalization._impl__should_replay_canonicalized_return
    # lifecycle / analyze_function / condition_logic / ... (session helpers)
    _address_like_keys = _svc_pcode_sites._impl__address_like_keys
    _address_space_name = _svc_pcode_sites._impl__address_space_name
    _apply_structural_recurrence_summary = _svc_analyze_function._impl__apply_structural_recurrence_summary
    _candidate_phi_origin_keys_from_summary_source_key = _svc_phi_origins._impl__candidate_phi_origin_keys_from_summary_source_key
    def _classify_param_condition(self, condition, param_name):
        return self._condition_logic.classify_param_condition(condition, param_name)
    _coerce_optional_int = _svc_pcode_sites._impl__coerce_optional_int
    _collect_guard_dependency_varnodes = _svc_divergence_proofs._impl__collect_guard_dependency_varnodes
    _collect_java_or_python_iterable = staticmethod(_svc_lifecycle._impl__collect_java_or_python_iterable)
    _collect_parameter_descriptors_from_expression = _svc_parameters._impl__collect_parameter_descriptors_from_expression
    _collect_referenced_parameter_descriptors = _svc_parameters._impl__collect_referenced_parameter_descriptors
    _collect_scalar_signedness_profiles = _svc_parameters._impl__collect_scalar_signedness_profiles
    _condition_for_identity_key = _svc_divergence_proofs._impl__condition_for_identity_key
    _condition_identity_key = staticmethod(_svc_divergence_proofs._impl__condition_identity_key)
    _condition_looks_like_stack_protector_guard = _svc_stack_protector._impl__condition_looks_like_stack_protector_guard
    def _condition_mentions_param(self, condition, param_name):
        return self._condition_logic.condition_mentions_param(condition, param_name)
    _conditional_progress_guard_keys_from_structural_proof = _svc_divergence_proofs._impl__conditional_progress_guard_keys_from_structural_proof
    _conditional_progress_guards_contradict_invariant = _svc_divergence_proofs._impl__conditional_progress_guards_contradict_invariant
    _conditions_have_contradictory_pair = _svc_divergence_proofs._impl__conditions_have_contradictory_pair
    @staticmethod
    def _constant_expression_value(expr):
        return ConditionLogicService.constant_expression_value(expr)
    _constant_int_value = _svc_stack_protector._impl__constant_int_value
    _current_function_entry_address = _svc_lifecycle._impl__current_function_entry_address
    _debug_expr_identity_summary = _svc_lifecycle._impl__debug_expr_identity_summary
    _debug_expr_summary = _svc_lifecycle._impl__debug_expr_summary
    _debug_print = _svc_lifecycle._impl__debug_print
    _describe_pcode_site = _svc_pcode_sites._impl__describe_pcode_site
    _edge_condition_for_successor = _svc_divergence_proofs._impl__edge_condition_for_successor
    def _expression_contains_equivalent_subexpr(self, expr, target):
        return self._expression_cases.expression_contains_equivalent_subexpr(expr, target)
    @staticmethod
    def _expression_has_param(expr, param_name):
        return ConditionLogicService.expression_has_param(expr, param_name)
    _expression_is_placeholder_minus_one = _svc_placeholder_algebra._impl__expression_is_placeholder_minus_one
    _expression_is_placeholder_minus_one_under_conditions = _svc_placeholder_algebra._impl__expression_is_placeholder_minus_one_under_conditions
    _expression_is_placeholder_minus_one_unit_condition = _svc_placeholder_algebra._impl__expression_is_placeholder_minus_one_unit_condition
    _expression_is_placeholder_plus_constant = _svc_placeholder_algebra._impl__expression_is_placeholder_plus_constant
    _expression_is_placeholder_plus_one = _svc_placeholder_algebra._impl__expression_is_placeholder_plus_one
    _expression_is_placeholder_plus_one_under_conditions = _svc_placeholder_algebra._impl__expression_is_placeholder_plus_one_under_conditions
    _expression_is_placeholder_plus_unit_condition = _svc_placeholder_algebra._impl__expression_is_placeholder_plus_unit_condition
    _expression_is_placeholder_plus_zero_under_conditions = _svc_placeholder_algebra._impl__expression_is_placeholder_plus_zero_under_conditions
    def _expression_is_zero_constant(self, expr):
        return self._condition_logic.expression_is_zero_constant(expr)
    _expression_is_zero_under_conditions = _svc_placeholder_algebra._impl__expression_is_zero_under_conditions
    _extract_difference_pair = _svc_stack_protector._impl__extract_difference_pair
    _extract_indirect_probe = _svc_stack_protector._impl__extract_indirect_probe
    _extract_stack_protector_compare_pair = _svc_stack_protector._impl__extract_stack_protector_compare_pair
    _field_value_from_structural_proof = staticmethod(_svc_divergence_proofs._impl__field_value_from_structural_proof)
    _find_matching_parameter_descriptor_index = _svc_parameters._impl__find_matching_parameter_descriptor_index
    _function_entry_address = staticmethod(_svc_lifecycle._impl__function_entry_address)
    _high_function_cyclic_sccs = _svc_divergence_proofs._impl__high_function_cyclic_sccs
    _is_zero_constant = _svc_stack_protector._impl__is_zero_constant
    _merge_parameter_descriptors = _svc_parameters._impl__merge_parameter_descriptors
    _negated_unit_condition_key_for_expression = _svc_placeholder_algebra._impl__negated_unit_condition_key_for_expression
    _parameter_descriptor_from_expression = _svc_parameters._impl__parameter_descriptor_from_expression
    _parameter_descriptor_key = _svc_parameters._impl__parameter_descriptor_key
    _pcode_op_identity_key = _svc_pcode_sites._impl__pcode_op_identity_key
    _pcode_op_input_def_reaches_phi = _svc_pcode_sites._impl__pcode_op_input_def_reaches_phi
    _pcode_op_stable_key = _svc_pcode_sites._impl__pcode_op_stable_key
    _pcode_ops_match = _svc_pcode_sites._impl__pcode_ops_match
    _phase1_body_contains_address = staticmethod(_svc_analyze_function._impl__phase1_body_contains_address)
    _phi_circular_origin_stable_keys = _svc_phi_origins._impl__phi_circular_origin_stable_keys
    _placeholder_minus_one_unit_condition_guard_key = _svc_placeholder_algebra._impl__placeholder_minus_one_unit_condition_guard_key
    _placeholder_plus_unit_condition_guard_key = _svc_placeholder_algebra._impl__placeholder_plus_unit_condition_guard_key
    _prove_scc_must_diverge_under_guard = _svc_divergence_proofs._impl__prove_scc_must_diverge_under_guard
    _prove_single_guard_nonprogress_region_must_diverge = _svc_divergence_proofs._impl__prove_single_guard_nonprogress_region_must_diverge
    _reads_share_stack_protector_probe = _svc_stack_protector._impl__reads_share_stack_protector_probe
    _record_scalar_signedness_from_expression = _svc_parameters._impl__record_scalar_signedness_from_expression
    _recursive_scc_certificate = _svc_divergence_proofs._impl__recursive_scc_certificate
    # RegionFacts collaborator (Phase 5): the facade keeps these names as thin
    # delegators for existing callers and tests.
    def _region_address_is_code(self, address) -> bool:
        return self._region_facts.address_is_code(address)

    def _region_live_in_key(self, varnode, *, mnemonic, input_index, parameters):
        return self._region_facts.live_in_key(
            varnode, mnemonic=mnemonic, input_index=input_index, parameters=parameters
        )

    _region_input_is_nondata_operand = staticmethod(input_is_nondata_operand)
    _region_parameter_index_for_location = staticmethod(parameter_index_for_location)
    _repair_mixed_scalar_signedness = _svc_parameters._impl__repair_mixed_scalar_signedness
    _scc_preserves_guard_dependencies = _svc_divergence_proofs._impl__scc_preserves_guard_dependencies
    _single_guard_condition_matches = _svc_divergence_proofs._impl__single_guard_condition_matches
    _single_guard_conditions_are_contradictory = _svc_divergence_proofs._impl__single_guard_conditions_are_contradictory
    _strip_stack_protector_only_conditions = _svc_stack_protector._impl__strip_stack_protector_only_conditions
    _strip_transparent_unary = staticmethod(_svc_placeholder_algebra._impl__strip_transparent_unary)
    _synchronize_parameters_with_referenced_parameter_expressions = _svc_parameters._impl__synchronize_parameters_with_referenced_parameter_expressions
    _tuple_field_from_structural_proof = staticmethod(_svc_divergence_proofs._impl__tuple_field_from_structural_proof)
    _unit_condition_key_for_expression = _svc_placeholder_algebra._impl__unit_condition_key_for_expression
    _varnode_guard_dependency_key = _svc_divergence_proofs._impl__varnode_guard_dependency_key
    _varnodes_same_storage = _svc_pcode_sites._impl__varnodes_same_storage
    analyze_function = _svc_analyze_function._impl_analyze_function
    dispose = _svc_lifecycle._impl_dispose
    # session helpers (continued)
    _analysis_is_fully_argument_specialized = _svc_analyze_function._impl__analysis_is_fully_argument_specialized
    _analysis_needs_wrapper_recovery = _svc_analyze_function._impl__analysis_needs_wrapper_recovery
    _analysis_scope_key = _svc_lifecycle._impl__analysis_scope_key
    _attempt_disassemble_at = _svc_lifecycle._impl__attempt_disassemble_at
    _augment_parameters_with_implicit_passthrough = _svc_parameters._impl__augment_parameters_with_implicit_passthrough
    def _build_condition_signature_set(self, conditions):
        return self._condition_logic.build_condition_signature_set(conditions)
    _choose_richer_parameter_descriptors = _svc_parameters._impl__choose_richer_parameter_descriptors
    def _clone_expression(self, expr):
        return self._expression_cases.clone_expression(expr)
    def _coerce_expression_size(self, expr, size):
        return self._condition_logic.coerce_expression_size(expr, size)
    def _coerce_order_key(self, value):
        return self._condition_logic.coerce_order_key(value)
    _coerce_wrapper_storage_info = _svc_parameters._impl__coerce_wrapper_storage_info
    def _collect_expression_object_keys(self, expr, out):
        return self._expression_cases.collect_expression_object_keys(expr, out)
    _collect_parameters = _svc_parameters._impl__collect_parameters
    def _condition_contradicts_any(self, condition, others):
        return self._condition_logic.condition_contradicts_any(condition, others)
    def _condition_is_constant_equality_guard(self, condition):
        return self._condition_logic.condition_is_constant_equality_guard(condition)
    def _condition_is_param_equal_const(self, condition, param, value):
        return self._condition_logic.condition_is_param_equal_const(condition, param, value)
    _condition_is_param_minus_one_nonpositive = _svc_placeholder_algebra._impl__condition_is_param_minus_one_nonpositive
    def _condition_is_signed_less_than_one_of_param(self, condition, param):
        return self._condition_logic.condition_is_signed_less_than_one_of_param(condition, param)
    def _condition_is_signed_nonpositive_of_param(self, condition, param):
        return self._condition_logic.condition_is_signed_nonpositive_of_param(condition, param)
    def _condition_is_signed_positive_of_param(self, condition, param):
        return self._condition_logic.condition_is_signed_positive_of_param(condition, param)
    def _condition_lists_equivalent(self, left, right):
        return self._expression_cases.condition_lists_equivalent(left, right)
    def _condition_logical_operator(self, condition):
        return self._condition_logic.condition_logical_operator(condition)
    def _condition_set_conjunction_expression(self, conditions):
        return self._condition_logic.condition_set_conjunction_expression(conditions)
    def _condition_sets_are_complementary(self, left_conditions, right_conditions):
        return self._condition_logic.condition_sets_are_complementary(left_conditions, right_conditions)
    def _condition_to_expression(self, condition):
        return self._condition_logic.condition_to_expression(condition)
    def _conditions_are_unsat(self, conditions):
        return self._condition_logic.conditions_are_unsat(conditions)
    def _conditions_equivalent(self, left, right):
        return self._condition_logic.conditions_equivalent(left, right)
    def _conditions_imply(self, left, right):
        return self._condition_logic.conditions_imply(left, right)
    def _conditions_overlap(self, left, right):
        return self._condition_logic.conditions_overlap(left, right)
    def _count_object_centric_unknowns(self, expr):
        return self._expression_cases.count_object_centric_unknowns(expr)
    def _count_opaque_unknowns(self, expr):
        return self._expression_cases.count_opaque_unknowns(expr)
    def _count_phi_nodes(self, expr):
        return self._expression_cases.count_phi_nodes(expr)
    def _count_unresolved_value_nodes(self, expr):
        return self._expression_cases.count_unresolved_value_nodes(expr)
    def _deduplicate_expression_cases(self, cases):
        return self._expression_cases.deduplicate_expression_cases(cases)
    _deduplicate_storage_infos = _svc_parameters._impl__deduplicate_storage_infos
    _detect_signedness = _svc_parameters._impl__detect_signedness
    def _direct_expression_runtime_guard_conditions(self, expr):
        return self._expression_cases.direct_expression_runtime_guard_conditions(expr)
    # LocalValueResolver collaborator (Phase 5): thin delegators for existing
    # callers and tests.
    def _evaluate_local_pcode_expression(self, pcode_op, tracer, local_values, local_storages, local_memory, visiting=None):
        return self._local_values.evaluate_pcode(pcode_op, tracer, local_values, local_storages, local_memory, visiting)

    def _evaluate_local_varnode_expression(self, varnode, tracer, local_values, local_storages, local_memory, visiting=None):
        return self._local_values.evaluate_varnode(varnode, tracer, local_values, local_storages, local_memory, visiting)
    def _expand_boolean_expression_cases(self, expr, base_conditions):
        return self._expression_cases.expand_boolean_expression_cases(expr, base_conditions)
    def _expand_object_centric_expression_cases(self, expr, base_conditions):
        return self._expression_cases.expand_object_centric_expression_cases(expr, base_conditions)
    _expression_contains_phi = _svc_phi_origins._impl__expression_contains_phi
    _expression_contains_phi_circular = _svc_phi_origins._impl__expression_contains_phi_circular
    _expression_contains_phi_circular_marker = _svc_phi_origins._impl__expression_contains_phi_circular_marker
    def _expression_has_nontrivial_location_wrapper(self, expr, location):
        return self._expression_cases.expression_has_nontrivial_location_wrapper(expr, location)
    _expression_is_one_under_conditions = _svc_placeholder_algebra._impl__expression_is_one_under_conditions
    _expression_is_param_minus_one = _svc_placeholder_algebra._impl__expression_is_param_minus_one
    _expression_is_positive_after_unit_progress_guard = _svc_divergence_proofs._impl__expression_is_positive_after_unit_progress_guard
    def _expression_is_same_parameter(self, expr, param):
        return self._condition_logic.expression_is_same_parameter(expr, param)
    def _expression_is_same_parameter_ignoring_subpiece(self, expr, param):
        return self._condition_logic.expression_is_same_parameter_ignoring_subpiece(expr, param)
    def _expression_references_allowed_subtrees(self, expr, allowed_subtrees):
        return self._expression_cases.expression_references_allowed_subtrees(expr, allowed_subtrees)
    def _expression_references_only_allowed_objects(self, expr, args):
        return self._expression_cases.expression_references_only_allowed_objects(expr, args)
    def _expression_runtime_guard_conditions(self, expr):
        return self._expression_cases.expression_runtime_guard_conditions(expr)
    def _expressions_equal_under_conditions_smt(self, left, right, conditions, parameters):
        return self._condition_logic.expressions_equal_under_conditions_smt(left, right, conditions, parameters)
    def _expressions_same_key(self, left, right):
        return self._condition_logic.expressions_same_key(left, right)
    _extend_active_functions = _svc_lifecycle._impl__extend_active_functions
    def _fold_constant_expression(self, expr, *, fallback_expr=None):
        return self._expression_cases.fold_constant_expression(expr, fallback_expr=fallback_expr)
    _function_cache_key = _svc_lifecycle._impl__function_cache_key
    _get_function_manager = _svc_lifecycle._impl__get_function_manager
    _get_instruction_with_fallback = _svc_lifecycle._impl__get_instruction_with_fallback
    _get_pcode_opcode = _svc_pcode_sites._impl__get_pcode_opcode
    _get_storage_info = _svc_parameters._impl__get_storage_info
    _has_non_parameter_symbol_for_storage = _svc_parameters._impl__has_non_parameter_symbol_for_storage
    _high_function_has_cfg_cycle = _svc_divergence_proofs._impl__high_function_has_cfg_cycle
    def _is_boolean_expression(self, expr):
        return self._expression_cases.is_boolean_expression(expr)
    def _is_direct_location_carrier(self, expr):
        return self._expression_cases.is_direct_location_carrier(expr)
    _is_signed_type = _svc_parameters._impl__is_signed_type
    _is_void_type = _svc_parameters._impl__is_void_type
    _is_zero_constant_varnode = _svc_pcode_sites._impl__is_zero_constant_varnode
    def _iter_expression_nodes_for_unconditional_runtime_guards(self, expr):
        return self._expression_cases.iter_expression_nodes_for_unconditional_runtime_guards(expr)
    def _local_varnode_key(self, varnode):
        return self._local_values.varnode_key(varnode)

    def _lookup_local_alias_expression(self, varnode, tracer, local_values, local_storages):
        return self._local_values.lookup_alias(varnode, tracer, local_values, local_storages)

    def _lookup_local_expression_for_storage(self, target_storage, local_values, local_storages):
        return self._local_values.lookup_for_storage(target_storage, local_values, local_storages)
    _make_tracer = _svc_lifecycle._impl__make_tracer
    def _parameter_constant_assignments_from_conditions(self, conditions):
        return self._condition_logic.parameter_constant_assignments_from_conditions(conditions)
    _parameter_descriptor_quality = _svc_parameters._impl__parameter_descriptor_quality
    _parameter_equals_condition = _svc_phi_origins._impl__parameter_equals_condition
    _parameter_expression = _svc_parameters._impl__parameter_expression
    _parameter_storages_match_for_passthrough = _svc_parameters._impl__parameter_storages_match_for_passthrough
    _parameter_storages_overlap_for_passthrough = _svc_parameters._impl__parameter_storages_overlap_for_passthrough
    _pcode_op_affects_tracked_storage = _svc_pcode_sites._impl__pcode_op_affects_tracked_storage
    _pcode_op_debug_name = _svc_pcode_sites._impl__pcode_op_debug_name
    _phi_circular_additive_signature = _svc_phi_origins._impl__phi_circular_additive_signature
    _phi_expression_key_set = _svc_phi_origins._impl__phi_expression_key_set
    _phi_free_finite_fallback_candidates = _svc_phi_origins._impl__phi_free_finite_fallback_candidates
    _phi_origin_keys_from_varnode_defs = _svc_phi_origins._impl__phi_origin_keys_from_varnode_defs
    _propagate_passthrough_input_from_op = _svc_parameters._impl__propagate_passthrough_input_from_op
    def _pruning_conditions_signature(self, conditions):
        return self._condition_logic.pruning_conditions_signature(conditions)
    _reachable_cycle_keys = _svc_divergence_proofs._impl__reachable_cycle_keys
    _readonly_reduction_contract_priority_score = _svc_phi_origins._impl__readonly_reduction_contract_priority_score
    _readonly_reduction_ref_contract_priority_score = _svc_phi_origins._impl__readonly_reduction_ref_contract_priority_score
    _resolve_function_from_address = _svc_lifecycle._impl__resolve_function_from_address
    def _resolve_precise_object_state_value(self, value, conditions, effect_summary):
        return self._expression_cases.resolve_precise_object_state_value(value, conditions, effect_summary)
    def _runtime_ref_guard_conditions(self, runtime_ref):
        return self._expression_cases.runtime_ref_guard_conditions(runtime_ref)
    def _signed_positive_condition(self, expr):
        return self._condition_logic.signed_positive_condition(expr)
    _signed_unit_constant_matches = _svc_placeholder_algebra._impl__signed_unit_constant_matches
    _single_parameter_expression_in_conditions = _svc_phi_origins._impl__single_parameter_expression_in_conditions
    _split_small_finite_parameter_reachability_conditions = _svc_phi_origins._impl__split_small_finite_parameter_reachability_conditions
    _state_phi_feeds_positive_loop_guard = _svc_divergence_proofs._impl__state_phi_feeds_positive_loop_guard
    def _substitute_parameter_constants_under_conditions(self, expr, conditions):
        return self._condition_logic.substitute_parameter_constants_under_conditions(expr, conditions)
    _synthesize_implicit_passthrough_parameter = _svc_parameters._impl__synthesize_implicit_passthrough_parameter
    _varnode_location_key = staticmethod(_svc_pcode_sites._impl__varnode_location_key)
    _varnodes_may_alias = classmethod(_svc_pcode_sites._impl__varnodes_may_alias)
    def _wrapper_preserves_collapsed_operand(self, operator, shared_operand, *, kept_operand_index):
        return self._expression_cases.wrapper_preserves_collapsed_operand(operator, shared_operand, kept_operand_index=kept_operand_index)
    # session helpers (continued)
    def _active_conditions_imply_all(self, active_conditions, conclusions, *, assignments=None):
        return self._condition_logic.active_conditions_imply_all(active_conditions, conclusions, assignments=assignments)
    def _condition_truth_under_parameter_assignments(self, condition, assignments, *, _active_ids=None):
        return self._condition_logic.condition_truth_under_parameter_assignments(condition, assignments, _active_ids=_active_ids)
    def _conditions_conjunction_is_false_under_assignments(self, conditions, assignments):
        return self._condition_logic.conditions_conjunction_is_false_under_assignments(conditions, assignments)
    def _contains_multiequal(self, varnode, depth=0):
        return self._expression_cases.contains_multiequal(varnode, depth)
    def _evaluate_expression_under_parameter_assignments(self, expr, assignments, *, _active_ids=None):
        return self._condition_logic.evaluate_expression_under_parameter_assignments(expr, assignments, _active_ids=_active_ids)
    def _expression_contains_unresolved_value(self, expr):
        return self._expression_cases.expression_contains_unresolved_value(expr)
    def _reduce_phi_expression_under_conditions_with_smt(self, expr, conditions, *, _active_ids=None):
        return self._condition_logic.reduce_phi_expression_under_conditions_with_smt(expr, conditions, _active_ids=_active_ids)
    def _substitute_parameter_constants(self, expr, assignments):
        return self._condition_logic.substitute_parameter_constants(expr, assignments)
    get_last_analysis_failure = _svc_lifecycle._impl_get_last_analysis_failure
    get_last_analysis_failure_status = _svc_lifecycle._impl_get_last_analysis_failure_status
    get_last_function_lookup_error = _svc_lifecycle._impl_get_last_function_lookup_error
    refresh_structural_recurrence_summary = _svc_analyze_function._impl_refresh_structural_recurrence_summary
