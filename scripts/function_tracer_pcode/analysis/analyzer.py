# -*- coding: utf-8 -*-
"""Compatibility facade for ReturnAnalyzer."""
from .analyzer_services._shared import *

class ReturnAnalyzer:

    def __init__(self, program, debug: bool=False, binary_id: Optional[str]=None, *, enable_completed_recovery_proofs: bool=True):
        self.program = program
        self.debug = debug
        self._binary_id = binary_id
        self.enable_completed_recovery_proofs = bool(enable_completed_recovery_proofs)
        self._decompiler = None
        self._analysis_session = AnalysisSession()
        self._current_parameters: List[Dict] = []
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

    def _debug_print(self, msg: str, indent: int=0):
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_debug_print', self, msg, indent)

    def _program_is_big_endian(self) -> Optional[bool]:
        from .analyzer_services.lifecycle import invoke as _invoke
        return _invoke('_program_is_big_endian', self)

    def _program_identity(self) -> Optional[int]:
        from .analyzer_services.lifecycle import invoke as _invoke
        return _invoke('_program_identity', self)

    def _current_function_entry_address(self):
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_current_function_entry_address', self)

    @staticmethod
    def _function_entry_address(function):
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_function_entry_address', function)

    def _debug_expr_summary(self, expr: Optional[Expression], max_depth: int=4) -> str:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_debug_expr_summary', self, expr, max_depth)

    def _debug_expr_identity_summary(self, expr: Optional[Expression], max_depth: int=3) -> str:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_debug_expr_identity_summary', self, expr, max_depth)

    def _coerce_optional_int(self, value: object) -> Optional[int]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_coerce_optional_int', self, value)

    def _describe_pcode_site(self, pcode_op, fallback_address: Optional[str]=None, *, identity_prefix: Optional[str]=None) -> Dict[str, Optional[object]]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_describe_pcode_site', self, pcode_op, fallback_address, identity_prefix=identity_prefix)

    def _pcode_op_identity_key(self, pcode_op) -> Optional[Tuple[Any, ...]]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_pcode_op_identity_key', self, pcode_op)

    def _pcode_ops_match(self, lhs, rhs) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_pcode_ops_match', self, lhs, rhs)

    def _return_site_key(self, ret_info: ReturnInfo) -> str:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_return_site_key', self, ret_info)

    @staticmethod
    def _return_site_metadata_from_info(info: ReturnInfo) -> Dict[str, Optional[object]]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_return_site_metadata_from_info', info)

    def _return_value_pcode_op_refs_from_varnode(self, varnode) -> Tuple[PcodeOpRef, ...]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_return_value_pcode_op_refs_from_varnode', self, varnode)

    @staticmethod
    def _return_value_producer_chain(varnode, *, max_depth: int=4) -> Tuple[Any, ...]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_return_value_producer_chain', varnode, max_depth=max_depth)

    def _site_metadata_with_return_value_pcode_op_refs(self, site_metadata: Optional[Dict[str, Optional[object]]], *, return_varnode=None, producer_op=None, tracer=None) -> Dict[str, Optional[object]]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_site_metadata_with_return_value_pcode_op_refs', self, site_metadata, return_varnode=return_varnode, producer_op=producer_op, tracer=tracer)

    def _make_return_info(self, *, address: str, value: Expression, conditions: List[Condition], branch_index: Optional[int]=None, site_metadata: Optional[Dict[str, Optional[object]]]=None) -> ReturnInfo:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_make_return_info', self, address=address, value=value, conditions=conditions, branch_index=branch_index, site_metadata=site_metadata)

    def _expression_contains_equivalent_subexpr(self, expr: Optional[Expression], target: Optional[Expression]) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_expression_contains_equivalent_subexpr', self, expr, target)

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

    def _get_decompiler(self):
        from .analyzer_services.lifecycle import invoke as _invoke
        return _invoke('_get_decompiler', self)

    @contextmanager
    def _program_transaction(self, description: str):
        from .analyzer_services.lifecycle import invoke as _invoke
        return _invoke('_program_transaction', self, description)

    def dispose(self):
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('dispose', self)

    def _dump_return_infos(self, analysis: FunctionReturnAnalysis):
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_dump_return_infos', self, analysis)

    def _check_condition_coverage(self, analysis: FunctionReturnAnalysis):
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_check_condition_coverage', self, analysis)

    def _condition_mentions_param(self, condition: Condition, param_name: str) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_condition_mentions_param', self, condition, param_name)

    def _expression_is_zero_constant(self, expr: Optional[Expression]) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_expression_is_zero_constant', self, expr)

    @staticmethod
    def _expression_has_param(expr: Optional[Expression], param_name: str) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_expression_has_param', expr, param_name)

    def _decompose_comparison_condition(self, condition: Condition) -> Optional[Tuple[bool, str, Expression, Expression]]:
        from .analyzer_services.lifecycle import invoke as _invoke
        return _invoke('_decompose_comparison_condition', self, condition)

    def _classify_param_condition(self, condition: Condition, param_name: str) -> Tuple[bool, bool, bool]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_classify_param_condition', self, condition, param_name)

    def analyze_function(self, function, timeout: int=60, active_functions: Optional[Set[Tuple[Any, ...]]]=None, bound_parameter_values: Optional[Dict[int, Expression]]=None, bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]]=None) -> Optional[FunctionReturnAnalysis]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('analyze_function', self, function, timeout, active_functions, bound_parameter_values, bound_parameter_storage_values)

    def _apply_structural_recurrence_summary(self, function, high_function, analysis: FunctionReturnAnalysis, tracer: PcodeTracer) -> Optional[FunctionReturnAnalysis]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_apply_structural_recurrence_summary', self, function, high_function, analysis, tracer)

    def _try_pre_return_counted_loop_summary(self, *, function, high_function, tracer: PcodeTracer, parameters: Sequence[Dict], return_ops: Sequence, current_function_ref: CallTargetRef, analysis_scope_key, return_type: Optional[str], return_type_obj, signedness_result: Optional[SignednessResult], effect_summary: EffectSummary) -> Optional[FunctionReturnAnalysis]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_try_pre_return_counted_loop_summary', self, function=function, high_function=high_function, tracer=tracer, parameters=parameters, return_ops=return_ops, current_function_ref=current_function_ref, analysis_scope_key=analysis_scope_key, return_type=return_type, return_type_obj=return_type_obj, signedness_result=signedness_result, effect_summary=effect_summary)

    def _make_pre_return_summary_anchor(self, function, return_ops: Sequence) -> ReturnInfo:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_make_pre_return_summary_anchor', self, function, return_ops)

    def _effect_summary_allows_pre_return_structural_summary(self, effect_summary: Optional[EffectSummary], *, function=None, high_function=None, return_type: Optional[str]=None, return_type_obj=None) -> bool:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_effect_summary_allows_pre_return_structural_summary', self, effect_summary, function=function, high_function=high_function, return_type=return_type, return_type_obj=return_type_obj)

    def _function_body_has_phase1_pure_return_forbidden_ops(self, function) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_function_body_has_phase1_pure_return_forbidden_ops', self, function)

    def _phase1_direct_branch_escapes_function_body(self, instruction, body) -> bool:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_phase1_direct_branch_escapes_function_body', self, instruction, body)

    @staticmethod
    def _phase1_body_contains_address(body, target) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_phase1_body_contains_address', body, target)

    def _high_function_has_phase1_pure_return_forbidden_ops(self, high_function) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_high_function_has_phase1_pure_return_forbidden_ops', self, high_function)

    @staticmethod
    def _region_input_is_nondata_operand(mnemonic: str, input_index: int) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_region_input_is_nondata_operand', mnemonic, input_index)

    def _region_address_is_code(self, address) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_region_address_is_code', self, address)

    @staticmethod
    def _region_parameter_index_for_location(location_key: Tuple[str, int, int], parameters: Sequence[Dict[str, Any]]) -> Optional[int]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_region_parameter_index_for_location', location_key, parameters)

    def _region_live_in_key(self, varnode, *, mnemonic: str, input_index: int, parameters: Sequence[Dict[str, Any]]) -> Tuple[Optional[Tuple[object, ...]], str]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_region_live_in_key', self, varnode, mnemonic=mnemonic, input_index=input_index, parameters=parameters)

    def _build_function_control_effect_profile(self, high_function, function=None, parameters: Optional[Sequence[Dict[str, Any]]]=None) -> FunctionControlEffectProfile:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_build_function_control_effect_profile', self, high_function, function, parameters)

    def _direct_call_target_function_key(self, op) -> Optional[Tuple[object, ...]]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_direct_call_target_function_key', self, op)

    def _recursive_scc_certificate(self, function_key: Optional[Tuple[object, ...]]) -> Tuple[bool, Optional[str], Tuple[Tuple[object, ...], ...]]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_recursive_scc_certificate', self, function_key)

    @staticmethod
    def _phase1_pure_return_forbids_mnemonic(mnemonic: Optional[str]) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_phase1_pure_return_forbids_mnemonic', mnemonic)

    @staticmethod
    def _collect_java_or_python_iterable(value) -> Tuple[Tuple[Any, ...], bool]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_collect_java_or_python_iterable', value)

    @staticmethod
    def _phase1_return_type_is_float(return_type: Optional[str], return_type_obj=None) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_phase1_return_type_is_float', return_type, return_type_obj)

    def _normalize_return_partition(self, analysis: FunctionReturnAnalysis) -> None:
        from .analyzer_services.return_normalization import invoke as _invoke
        return _invoke('_normalize_return_partition', self, analysis)

    def _normalize_return_callother_userops(self, analysis: FunctionReturnAnalysis) -> None:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_normalize_return_callother_userops', self, analysis)

    def _normalize_callother_userop_expression(self, expr: Optional[Expression]) -> Tuple[Optional[Expression], bool]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_normalize_callother_userop_expression', self, expr)

    def _program_userop_name(self, userop_id: Optional[int]) -> Optional[str]:
        from .analyzer_services.lifecycle import invoke as _invoke
        return _invoke('_program_userop_name', self, userop_id)

    @staticmethod
    def _constant_expression_value(expr: Optional[Expression]) -> Optional[int]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_constant_expression_value', expr)

    def _strip_stack_protector_only_conditions(self, return_infos: List[ReturnInfo]) -> List[ReturnInfo]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_strip_stack_protector_only_conditions', self, return_infos)

    def _synchronize_parameters_with_referenced_parameter_expressions(self, analysis: FunctionReturnAnalysis) -> None:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_synchronize_parameters_with_referenced_parameter_expressions', self, analysis)

    def _repair_mixed_scalar_signedness(self, analysis: FunctionReturnAnalysis) -> None:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_repair_mixed_scalar_signedness', self, analysis)

    def _collect_scalar_signedness_profiles(self, return_infos: List[ReturnInfo]) -> Dict[Tuple[StructuralKey, int], Dict[str, int]]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_collect_scalar_signedness_profiles', self, return_infos)

    def _record_scalar_signedness_from_expression(self, expr: Expression, profiles: Dict[Tuple[StructuralKey, int], Dict[str, int]]) -> None:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_record_scalar_signedness_from_expression', self, expr, profiles)

    def _rewrite_expression_signedness(self, expr: Optional[Expression], preferred: Dict[Tuple[StructuralKey, int], str]) -> Tuple[Optional[Expression], bool]:
        from .analyzer_services.return_normalization import invoke as _invoke
        return _invoke('_rewrite_expression_signedness', self, expr, preferred)

    def _collect_referenced_parameter_descriptors(self, return_infos: List[ReturnInfo]) -> List[Dict]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_collect_referenced_parameter_descriptors', self, return_infos)

    def _collect_parameter_descriptors_from_expression(self, expr: Optional[Expression], discovered: Dict[str, Dict]) -> None:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_collect_parameter_descriptors_from_expression', self, expr, discovered)

    def _parameter_descriptor_from_expression(self, expr: Expression) -> Dict:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_parameter_descriptor_from_expression', self, expr)

    def _parameter_descriptor_key(self, descriptor: Dict) -> str:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_parameter_descriptor_key', self, descriptor)

    def _find_matching_parameter_descriptor_index(self, parameters: List[Dict], candidate: Dict) -> Optional[int]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_find_matching_parameter_descriptor_index', self, parameters, candidate)

    def _merge_parameter_descriptors(self, existing: Optional[Dict], candidate: Dict) -> Dict:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_merge_parameter_descriptors', self, existing, candidate)

    def _condition_looks_like_stack_protector_guard(self, condition: Condition) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_condition_looks_like_stack_protector_guard', self, condition)

    def _extract_stack_protector_compare_pair(self, condition: Optional[Condition]) -> Optional[Tuple[Expression, Expression]]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_extract_stack_protector_compare_pair', self, condition)

    def _extract_difference_pair(self, expr: Optional[Expression]) -> Optional[Tuple[Expression, Expression]]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_extract_difference_pair', self, expr)

    def _is_zero_constant(self, expr: Optional[Expression]) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_is_zero_constant', self, expr)

    def _reads_share_stack_protector_probe(self, left: Expression, right: Expression) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_reads_share_stack_protector_probe', self, left, right)

    def _extract_stack_protector_memory_probe(self, expr: Optional[Expression]) -> Optional[Tuple[StructuralKey, int, int, int]]:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_extract_stack_protector_memory_probe', self, expr)

    def _extract_indirect_probe(self, expr: Optional[Expression]) -> Optional[Tuple[StructuralKey, int, int]]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_extract_indirect_probe', self, expr)

    def _constant_int_value(self, expr: Optional[Expression]) -> Optional[int]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_constant_int_value', self, expr)

    def _apply_outcome_partition_summaries(self, function, high_function, analysis: FunctionReturnAnalysis) -> None:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_apply_outcome_partition_summaries', self, function, high_function, analysis)

    def _clear_outcome_partition_summaries(self, analysis: FunctionReturnAnalysis) -> None:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_clear_outcome_partition_summaries', self, analysis)

    def _try_apply_single_guard_nonprogress_loop_outcomes(self, high_function, analysis: FunctionReturnAnalysis) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_try_apply_single_guard_nonprogress_loop_outcomes', self, high_function, analysis)

    def _prove_single_guard_nonprogress_region_must_diverge(self, high_function, analysis: FunctionReturnAnalysis, *, divergence_guard: Condition, param: Expression) -> Optional[Dict[str, Any]]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_prove_single_guard_nonprogress_region_must_diverge', self, high_function, analysis, divergence_guard=divergence_guard, param=param)

    def _prove_scc_must_diverge_under_guard(self, scc: Sequence[Any], *, all_blocks: Sequence[Any], divergence_guard: Condition, param: Expression, tracer: Optional[PcodeTracer]) -> Optional[Dict[str, Any]]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_prove_scc_must_diverge_under_guard', self, scc, all_blocks=all_blocks, divergence_guard=divergence_guard, param=param, tracer=tracer)

    def _high_function_cyclic_sccs(self, blocks: Sequence[Any]) -> List[Tuple[Any, ...]]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_high_function_cyclic_sccs', self, blocks)

    def _block_successors(self, block) -> Tuple[Any, ...]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_block_successors', self, block)

    def _block_predecessor_count(self, block) -> int:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_block_predecessor_count', self, block)

    def _block_has_return_op(self, block) -> bool:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_block_has_return_op', self, block)

    def _block_writes_outcome_guard_state(self, block) -> bool:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_block_writes_outcome_guard_state', self, block)

    def _scc_preserves_guard_dependencies(self, scc_set: Set[Any]) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_scc_preserves_guard_dependencies', self, scc_set)

    def _collect_guard_dependency_varnodes(self, varnode, guard_dependency_keys: Set[Tuple[Any, ...]], *, is_root: bool, seen: Set[Tuple[Any, ...]]) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_collect_guard_dependency_varnodes', self, varnode, guard_dependency_keys, is_root=is_root, seen=seen)

    def _varnode_guard_dependency_key(self, varnode) -> Tuple[Any, ...]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_varnode_guard_dependency_key', self, varnode)

    def _edge_condition_for_successor(self, block, successor, tracer: Optional[PcodeTracer]) -> Optional[Condition]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_edge_condition_for_successor', self, block, successor, tracer)

    def _direct_cbranch_successor_relation(self, cbranch, block, successor) -> Optional[str]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_direct_cbranch_successor_relation', self, cbranch, block, successor)

    def _cbranch_direct_target_keys(self, cbranch, block) -> Set[Tuple[str, int]]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_cbranch_direct_target_keys', self, cbranch, block)

    def _block_start_address_keys(self, block) -> Set[Tuple[str, int]]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_block_start_address_keys', self, block)

    def _block_start_address_spaces(self, block) -> Set[str]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_block_start_address_spaces', self, block)

    def _address_like_keys(self, value, *, default_space: Optional[str]=None) -> Set[Tuple[str, int]]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_address_like_keys', self, value, default_space=default_space)

    def _address_space_name(self, address) -> Optional[str]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_address_space_name', self, address)

    def _first_high_block_cbranch(self, block):
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_first_high_block_cbranch', self, block)

    def _conditions_are_unsat(self, conditions: Sequence[Condition]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_conditions_are_unsat', self, conditions)

    def _single_guard_condition_matches(self, condition: Condition, divergence_guard: Condition, param: Expression) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_single_guard_condition_matches', self, condition, divergence_guard, param)

    def _single_guard_conditions_are_contradictory(self, divergence_guard: Condition, edge_condition: Condition, param: Expression) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_single_guard_conditions_are_contradictory', self, divergence_guard, edge_condition, param)

    def _same_high_block(self, left, right) -> bool:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_same_high_block', self, left, right)

    def _block_debug_key(self, block) -> Any:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_block_debug_key', self, block)

    def _iter_outcome_call_candidates(self, analysis: FunctionReturnAnalysis) -> Iterable[Tuple[Optional[CallTargetRef], Tuple[Expression, ...], str, str]]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_iter_outcome_call_candidates', self, analysis)

    def _try_apply_triangular_mod_caller_outcomes(self, high_function, analysis: FunctionReturnAnalysis) -> bool:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_try_apply_triangular_mod_caller_outcomes', self, high_function, analysis)

    def _find_caller_return_partition_for_param_minus_one_obligation(self, analysis: FunctionReturnAnalysis, *, param: Expression, nonpositive: Condition, eq_one: Condition) -> Tuple[Optional[ReturnInfo], Optional[ReturnInfo]]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_find_caller_return_partition_for_param_minus_one_obligation', self, analysis, param=param, nonpositive=nonpositive, eq_one=eq_one)

    def _caller_return_value_matches_param_on_eq_one(self, value: Optional[Expression], param: Expression) -> bool:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_caller_return_value_matches_param_on_eq_one', self, value, param)

    def _cached_callee_analysis_for_outcome_summary(self, target_ref: Optional[CallTargetRef]) -> Optional[FunctionReturnAnalysis]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_cached_callee_analysis_for_outcome_summary', self, target_ref)

    def _analysis_has_positive_region_outcome_obligation(self, analysis: Optional[FunctionReturnAnalysis]) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_analysis_has_positive_region_outcome_obligation', self, analysis)

    def _try_apply_branch_guarded_while_outcomes(self, high_function, analysis: FunctionReturnAnalysis) -> bool:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_try_apply_branch_guarded_while_outcomes', self, high_function, analysis)

    def _infer_branch_guarded_while_role_parameters(self, analysis: FunctionReturnAnalysis) -> Optional[Tuple[Expression, Expression]]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_infer_branch_guarded_while_role_parameters', self, analysis)

    def _prove_branch_guarded_structural_nonprogress_must_diverge(self, high_function, *, analysis: Optional[FunctionReturnAnalysis]=None, initial_c_ret: ReturnInfo, invariant_conditions: Sequence[Condition]) -> Optional[Dict[str, Any]]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_prove_branch_guarded_structural_nonprogress_must_diverge', self, high_function, analysis=analysis, initial_c_ret=initial_c_ret, invariant_conditions=invariant_conditions)

    def _branch_guarded_structural_proof_from_return(self, ret: ReturnInfo) -> Optional[Tuple[Any, ...]]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_branch_guarded_structural_proof_from_return', self, ret)

    def _find_branch_guarded_structural_proof_tuple(self, value) -> Optional[Tuple[Any, ...]]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_find_branch_guarded_structural_proof_tuple', self, value)

    def _validate_branch_guarded_structural_proof(self, high_function, *, structural_proof: Tuple[Any, ...], analysis: Optional[FunctionReturnAnalysis], initial_c_ret: ReturnInfo, invariant_conditions: Sequence[Condition]) -> bool:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_validate_branch_guarded_structural_proof', self, high_function, structural_proof=structural_proof, analysis=analysis, initial_c_ret=initial_c_ret, invariant_conditions=invariant_conditions)

    @staticmethod
    def _tuple_field_from_structural_proof(proof: Tuple[Any, ...], field_name: str) -> Tuple[Any, ...]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_tuple_field_from_structural_proof', proof, field_name)

    @staticmethod
    def _field_value_from_structural_proof(proof: Tuple[Any, ...], field_name: str) -> Any:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_field_value_from_structural_proof', proof, field_name)

    @staticmethod
    def _condition_identity_key(condition: Condition) -> Tuple[Any, ...]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_condition_identity_key', condition)

    def _conditional_progress_guard_keys_from_structural_proof(self, proof: Tuple[Any, ...]) -> Dict[int, Tuple[Any, ...]]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_conditional_progress_guard_keys_from_structural_proof', self, proof)

    def _condition_for_identity_key(self, key: Tuple[Any, ...], conditions: Sequence[Condition]) -> Optional[Condition]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_condition_for_identity_key', self, key, conditions)

    def _conditional_progress_guards_contradict_invariant(self, guard_keys: Dict[int, Tuple[Any, ...]], *, target_conditions: Sequence[Condition], invariant_conditions: Sequence[Condition]) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_conditional_progress_guards_contradict_invariant', self, guard_keys, target_conditions=target_conditions, invariant_conditions=invariant_conditions)

    def _conditions_have_contradictory_pair(self, left: Sequence[Condition], right: Sequence[Condition]) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_conditions_have_contradictory_pair', self, left, right)

    def _find_branch_guarded_while_return_partition(self, analysis: FunctionReturnAnalysis, *, high_function, c_param: Expression, c_nonpositive: Condition, c_positive: Condition, t_positive: Condition) -> Tuple[Optional[ReturnInfo], Optional[ReturnInfo]]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_find_branch_guarded_while_return_partition', self, analysis, high_function=high_function, c_param=c_param, c_nonpositive=c_nonpositive, c_positive=c_positive, t_positive=t_positive)

    def _synthesize_branch_guarded_affine_initial_count_return(self, high_function, analysis: FunctionReturnAnalysis, *, c_param: Expression, c_positive: Condition, t_positive: Condition, zero_ret: ReturnInfo) -> Optional[ReturnInfo]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_synthesize_branch_guarded_affine_initial_count_return', self, high_function, analysis, c_param=c_param, c_positive=c_positive, t_positive=t_positive, zero_ret=zero_ret)

    def _branch_guarded_artifact_is_imprecise_zero_seed(self, artifact: ReturnInfo, *, zero_ret: ReturnInfo, parameters: Sequence[Dict]) -> bool:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_branch_guarded_artifact_is_imprecise_zero_seed', self, artifact, zero_ret=zero_ret, parameters=parameters)

    def _branch_guarded_artifact_is_structural_accumulator_seed_projection(self, artifact: ReturnInfo, *, recursive_returns: Sequence[ReturnInfo], parameters: Sequence[Dict]) -> bool:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_branch_guarded_artifact_is_structural_accumulator_seed_projection', self, artifact, recursive_returns=recursive_returns, parameters=parameters)

    def _prove_branch_guarded_affine_unit_count_recurrence(self, high_function, *, analysis: FunctionReturnAnalysis, c_param: Expression, target_conditions: Sequence[Condition], recursive_returns: Sequence[ReturnInfo], candidate_phi_origin_keys: Sequence[Tuple[Any, ...]]=(), return_phi_origin_keys: Sequence[Tuple[Any, ...]]=(), nonprogress_conditions: Sequence[Condition]=(), allow_latch_progress_guard: bool=False) -> Optional[Tuple[Any, ...]]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_prove_branch_guarded_affine_unit_count_recurrence', self, high_function, analysis=analysis, c_param=c_param, target_conditions=target_conditions, recursive_returns=recursive_returns, candidate_phi_origin_keys=candidate_phi_origin_keys, return_phi_origin_keys=return_phi_origin_keys, nonprogress_conditions=nonprogress_conditions, allow_latch_progress_guard=allow_latch_progress_guard)

    def _acc_phi_flows_to_return_origin_phi(self, acc_phi, return_origin_keys: Set[Tuple[Any, ...]], *, summarizer: StructuralRecurrenceSummarizer, high_function) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_acc_phi_flows_to_return_origin_phi', self, acc_phi, return_origin_keys, summarizer=summarizer, high_function=high_function)

    def _return_origin_phi_has_acc_output_input(self, return_phi, acc_phi) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_return_origin_phi_has_acc_output_input', self, return_phi, acc_phi)

    def _varnodes_same_storage(self, left, right) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_varnodes_same_storage', self, left, right)

    def _pcode_op_input_def_reaches_phi(self, op, target_phi_key: Tuple[Any, ...], *, max_depth: int) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_pcode_op_input_def_reaches_phi', self, op, target_phi_key, max_depth=max_depth)

    def _pcode_op_stable_key(self, op) -> Optional[Tuple[Any, ...]]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_pcode_op_stable_key', self, op)

    def _phi_circular_origin_stable_keys(self, expr: Optional[Expression]) -> Set[Tuple[Any, ...]]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_phi_circular_origin_stable_keys', self, expr)

    def _return_info_candidate_phi_origin_keys(self, ret: Optional[ReturnInfo]) -> Set[Tuple[Any, ...]]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_return_info_candidate_phi_origin_keys', self, ret)

    def _return_info_return_phi_origin_keys(self, ret: Optional[ReturnInfo]) -> Set[Tuple[Any, ...]]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_return_info_return_phi_origin_keys', self, ret)

    def _candidate_phi_origin_keys_from_summary_source_key(self, value) -> Set[Tuple[Any, ...]]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_candidate_phi_origin_keys_from_summary_source_key', self, value)

    def _return_phi_origin_keys_from_summary_source_key(self, value) -> Set[Tuple[Any, ...]]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_return_phi_origin_keys_from_summary_source_key', self, value)

    def _expression_is_placeholder_plus_one(self, expr: Optional[Expression], placeholder: Expression) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_expression_is_placeholder_plus_one', self, expr, placeholder)

    def _expression_is_placeholder_minus_one(self, expr: Optional[Expression], placeholder: Expression) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_expression_is_placeholder_minus_one', self, expr, placeholder)

    def _expression_is_placeholder_plus_one_under_conditions(self, expr: Optional[Expression], placeholder: Expression, conditions: Sequence[Condition]) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_expression_is_placeholder_plus_one_under_conditions', self, expr, placeholder, conditions)

    def _expression_is_placeholder_minus_one_under_conditions(self, expr: Optional[Expression], placeholder: Expression, conditions: Sequence[Condition]) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_expression_is_placeholder_minus_one_under_conditions', self, expr, placeholder, conditions)

    def _expression_is_placeholder_plus_zero_under_conditions(self, expr: Optional[Expression], placeholder: Expression, conditions: Sequence[Condition]) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_expression_is_placeholder_plus_zero_under_conditions', self, expr, placeholder, conditions)

    def _expression_is_zero_under_conditions(self, expr: Optional[Expression], conditions: Sequence[Condition]) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_expression_is_zero_under_conditions', self, expr, conditions)

    def _expression_is_placeholder_minus_one_unit_condition(self, expr: Optional[Expression], placeholder: Expression, conditions: Sequence[Condition]) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_expression_is_placeholder_minus_one_unit_condition', self, expr, placeholder, conditions)

    def _placeholder_minus_one_unit_condition_guard_key(self, expr: Optional[Expression], placeholder: Expression, conditions: Sequence[Condition]) -> Optional[Tuple[Any, ...]]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_placeholder_minus_one_unit_condition_guard_key', self, expr, placeholder, conditions)

    def _expression_is_placeholder_plus_unit_condition(self, expr: Optional[Expression], placeholder: Expression, conditions: Sequence[Condition]) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_expression_is_placeholder_plus_unit_condition', self, expr, placeholder, conditions)

    def _placeholder_plus_unit_condition_guard_key(self, expr: Optional[Expression], placeholder: Expression, conditions: Sequence[Condition]) -> Optional[Tuple[Any, ...]]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_placeholder_plus_unit_condition_guard_key', self, expr, placeholder, conditions)

    def _unit_condition_key_for_expression(self, expr: Optional[Expression], conditions: Sequence[Condition]) -> Optional[Tuple[Any, ...]]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_unit_condition_key_for_expression', self, expr, conditions)

    def _negated_unit_condition_key_for_expression(self, expr: Optional[Expression], conditions: Sequence[Condition]) -> Optional[Tuple[Any, ...]]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_negated_unit_condition_key_for_expression', self, expr, conditions)

    @staticmethod
    def _strip_transparent_unary(expr: Optional[Expression]) -> Optional[Expression]:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_strip_transparent_unary', expr)

    def _expression_is_placeholder_plus_constant(self, expr: Optional[Expression], placeholder: Expression, constant: int) -> bool:
        from .analyzer_services.session_helpers_1 import invoke as _invoke
        return _invoke('_expression_is_placeholder_plus_constant', self, expr, placeholder, constant)

    def _signed_unit_constant_matches(self, value: int, expected: int, size: Optional[int]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_signed_unit_constant_matches', self, value, expected, size)

    def _expressions_same_key(self, left: Optional[Expression], right: Optional[Expression]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_expressions_same_key', self, left, right)

    def _state_phi_feeds_positive_loop_guard(self, high_function, *, summarizer: StructuralRecurrenceSummarizer, header_block, backedge_indices: Sequence[int], state_phi, state_placeholder: Expression, target_conditions: Sequence[Condition], allow_latch_progress_guard: bool) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_state_phi_feeds_positive_loop_guard', self, high_function, summarizer=summarizer, header_block=header_block, backedge_indices=backedge_indices, state_phi=state_phi, state_placeholder=state_placeholder, target_conditions=target_conditions, allow_latch_progress_guard=allow_latch_progress_guard)

    def _expression_is_positive_after_unit_progress_guard(self, expr: Optional[Expression], state_placeholder: Expression, conditions: Sequence[Condition]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_expression_is_positive_after_unit_progress_guard', self, expr, state_placeholder, conditions)

    def _branch_guarded_affine_ignored_artifacts_are_shadowed(self, ignored_artifacts: Sequence[ReturnInfo], recursive_returns: Sequence[Tuple[ReturnInfo, int]], parameters: Sequence[Dict]) -> bool:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_branch_guarded_affine_ignored_artifacts_are_shadowed', self, ignored_artifacts, recursive_returns, parameters)

    def _branch_guarded_affine_phi_step(self, value: Optional[Expression]) -> Optional[int]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_branch_guarded_affine_phi_step', self, value)

    def _phi_circular_additive_signature(self, expr: Optional[Expression]) -> Optional[Tuple[int, int]]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_phi_circular_additive_signature', self, expr)

    def _branch_guarded_affine_singleton_base_anchor_matches(self, value: Optional[Expression], conditions: Sequence[Condition], c_param: Expression, target_conditions: Sequence[Condition]) -> bool:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_branch_guarded_affine_singleton_base_anchor_matches', self, value, conditions, c_param, target_conditions)

    def _condition_is_param_minus_one_nonpositive(self, condition: Condition, param: Expression, target_conditions: Sequence[Condition]=()) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_condition_is_param_minus_one_nonpositive', self, condition, param, target_conditions)

    def _branch_guarded_expression_is_param_minus_one(self, expr: Optional[Expression], param: Expression, target_conditions: Sequence[Condition]) -> bool:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_branch_guarded_expression_is_param_minus_one', self, expr, param, target_conditions)

    def _expression_is_one_under_conditions(self, expr: Optional[Expression], target_conditions: Sequence[Condition]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_expression_is_one_under_conditions', self, expr, target_conditions)

    def _return_conditions_cover_region(self, region_conditions: Sequence[Condition], returns: Sequence[ReturnInfo]) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_return_conditions_cover_region', self, region_conditions, returns)

    def _conditions_overlap(self, left: Sequence[Condition], right: Sequence[Condition]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_conditions_overlap', self, left, right)

    def _conditions_imply(self, left: Sequence[Condition], right: Sequence[Condition]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_conditions_imply', self, left, right)

    def _expressions_equal_under_conditions_smt(self, left: Optional[Expression], right: Optional[Expression], conditions: Sequence[Condition], parameters: Sequence[Dict]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_expressions_equal_under_conditions_smt', self, left, right, conditions, parameters)

    def _prove_branch_guarded_while_nonprogress_must_diverge(self, high_function, *, invariant_conditions: Sequence[Condition]) -> Optional[Dict[str, Any]]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_prove_branch_guarded_while_nonprogress_must_diverge', self, high_function, invariant_conditions=invariant_conditions)

    def _reachable_cycle_keys(self, reachable: Set[Any], adjacency: Mapping[Any, Sequence[Any]]) -> Set[Any]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_reachable_cycle_keys', self, reachable, adjacency)

    def _condition_contradicts_any(self, condition: Condition, others: Sequence[Condition]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_condition_contradicts_any', self, condition, others)

    def _return_info_summary_identity_key(self, ret: ReturnInfo) -> Tuple[Any, ...]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_return_info_summary_identity_key', self, ret)

    def _try_apply_triangular_mod_optimized_outcomes(self, high_function, analysis: FunctionReturnAnalysis) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_try_apply_triangular_mod_optimized_outcomes', self, high_function, analysis)

    def _return_partition_miss_guard(self, returns: Sequence[ReturnInfo]) -> Condition:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_return_partition_miss_guard', self, returns)

    def _parameter_expression(self, analysis: FunctionReturnAnalysis, index: int) -> Optional[Expression]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_parameter_expression', self, analysis, index)

    def _signed_positive_condition(self, expr: Expression) -> Condition:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_signed_positive_condition', self, expr)

    def _condition_is_signed_nonpositive_of_param(self, condition: Condition, param: Expression) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_condition_is_signed_nonpositive_of_param', self, condition, param)

    def _condition_is_signed_positive_of_param(self, condition: Condition, param: Expression) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_condition_is_signed_positive_of_param', self, condition, param)

    def _condition_is_signed_less_than_one_of_param(self, condition: Condition, param: Expression) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_condition_is_signed_less_than_one_of_param', self, condition, param)

    def _condition_is_param_equal_const(self, condition: Condition, param: Expression, value: int) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_condition_is_param_equal_const', self, condition, param, value)

    def _analysis_return_size_bytes(self, analysis: FunctionReturnAnalysis) -> int:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_analysis_return_size_bytes', self, analysis)

    def _make_synthetic_outcome_return(self, analysis: FunctionReturnAnalysis, *, value: Expression, conditions: Sequence[Condition], branch_index: int, tag: str) -> ReturnInfo:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_make_synthetic_outcome_return', self, analysis, value=value, conditions=conditions, branch_index=branch_index, tag=tag)

    def _coerce_expression_size(self, expr: Expression, size: int) -> Expression:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_coerce_expression_size', self, expr, size)

    def _expression_is_param_minus_one(self, expr: Expression, param: Expression) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_expression_is_param_minus_one', self, expr, param)

    def _expression_is_same_parameter(self, expr: Expression, param: Expression) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_expression_is_same_parameter', self, expr, param)

    def _expression_is_same_parameter_ignoring_subpiece(self, expr: Expression, param: Expression) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_expression_is_same_parameter_ignoring_subpiece', self, expr, param)

    def _expression_contains_phi_circular(self, expr: Optional[Expression]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_expression_contains_phi_circular', self, expr)

    def _conditions_equivalent(self, left: Sequence[Condition], right: Sequence[Condition]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_conditions_equivalent', self, left, right)

    def _high_function_has_forbidden_control_outcome_ops(self, high_function, *, allow_call: bool) -> bool:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_high_function_has_forbidden_control_outcome_ops', self, high_function, allow_call=allow_call)

    def _is_control_outcome_forbidden_fp_mnemonic(self, mnemonic: Optional[str]) -> bool:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_is_control_outcome_forbidden_fp_mnemonic', self, mnemonic)

    def _high_function_has_cfg_cycle(self, high_function) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_high_function_has_cfg_cycle', self, high_function)

    def _high_function_has_nonreturning_region_candidate(self, high_function) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_high_function_has_nonreturning_region_candidate', self, high_function)

    def _block_reaches(self, start, target, allowed: Set[Any]) -> bool:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_block_reaches', self, start, target, allowed)

    def _high_function_cbranch_count(self, high_function) -> int:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_high_function_cbranch_count', self, high_function)

    def _iter_high_basic_blocks(self, high_function):
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_iter_high_basic_blocks', self, high_function)

    def _iter_high_block_ops(self, block):
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_iter_high_block_ops', self, block)

    def _mark_incomplete_control_flow(self, analysis: FunctionReturnAnalysis) -> None:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_mark_incomplete_control_flow', self, analysis)

    def _make_deferred_call_recorder(self, current_function=None):
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_make_deferred_call_recorder', self, current_function)

    def _align_deferred_call_arguments_for_recording(self, target_ref: CallTargetRef, args: Sequence[Expression], caller_parameters: Sequence[Dict]) -> List[Expression]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_align_deferred_call_arguments_for_recording', self, target_ref, args, caller_parameters)

    def _apply_bounded_call_refinement(self, analysis: FunctionReturnAnalysis, active_functions: Set[Tuple[Any, ...]], current_function_ref: Optional[CallTargetRef]) -> None:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_apply_bounded_call_refinement', self, analysis, active_functions, current_function_ref)

    def _apply_effect_call_argument_evidence_to_deferred_calls(self, analysis: FunctionReturnAnalysis) -> None:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_apply_effect_call_argument_evidence_to_deferred_calls', self, analysis)

    def _make_empty_effect_summary(self, parameters: List[Dict]) -> EffectSummary:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_make_empty_effect_summary', self, parameters)

    def _recover_control_region_returns_early(self, current_function, tracer: PcodeTracer, condition_tracker: ConditionTracker, return_ops: List[Any], *, active_functions) -> Tuple[Optional[List[ReturnInfo]], List[str]]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_recover_control_region_returns_early', self, current_function, tracer, condition_tracker, return_ops, active_functions=active_functions)

    def _recover_switch_like_returns_from_placeholder_analysis(self, current_function, tracer: PcodeTracer, condition_tracker: ConditionTracker, return_ops: List[Any], *, active_functions) -> Optional[List[ReturnInfo]]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_recover_switch_like_returns_from_placeholder_analysis', self, current_function, tracer, condition_tracker, return_ops, active_functions=active_functions)

    def _recover_control_flow_returns_from_block_paths(self, current_function, tracer: PcodeTracer, condition_tracker: ConditionTracker, return_ops: List[Any], *, active_functions) -> Optional[List[ReturnInfo]]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_recover_control_flow_returns_from_block_paths', self, current_function, tracer, condition_tracker, return_ops, active_functions=active_functions)

    def _recover_explicit_return_from_block_paths(self, return_op, address: str, tracer: PcodeTracer, condition_tracker: ConditionTracker, return_index: int, path_entries, active_functions: Optional[Set[Tuple[Any, ...]]]=None, current_function=None, site_metadata: Optional[Dict[str, Optional[object]]]=None) -> Optional[List[ReturnInfo]]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_recover_explicit_return_from_block_paths', self, return_op, address, tracer, condition_tracker, return_index, path_entries, active_functions, current_function, site_metadata)

    def _recover_explicit_return_from_path_source(self, return_source, address: str, tracer: PcodeTracer, condition_tracker: ConditionTracker, path_conditions: List[Condition], return_index_base: int, active_functions: Optional[Set[Tuple[Any, ...]]]=None, current_function=None, site_metadata: Optional[Dict[str, Optional[object]]]=None) -> Optional[List[ReturnInfo]]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_recover_explicit_return_from_path_source', self, return_source, address, tracer, condition_tracker, path_conditions, return_index_base, active_functions, current_function, site_metadata)

    def _materialize_direct_path_specific_return_source(self, return_source, address: str, tracer: PcodeTracer, path_conditions: List[Condition], return_index_base: int, site_metadata: Optional[Dict[str, Optional[object]]]=None) -> Optional[List[ReturnInfo]]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_materialize_direct_path_specific_return_source', self, return_source, address, tracer, path_conditions, return_index_base, site_metadata)

    def _get_cached_return_path_entries(self, condition_tracker: ConditionTracker, return_op, *, tracer: Optional[PcodeTracer]=None) -> Optional[List[Tuple[List[Any], List[Condition]]]]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_get_cached_return_path_entries', self, condition_tracker, return_op, tracer=tracer)

    def _control_region_returns_are_safe(self, return_infos: List[ReturnInfo]) -> bool:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_control_region_returns_are_safe', self, return_infos)

    def _return_infos_have_conflicting_overlap(self, return_infos: List[ReturnInfo]) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_return_infos_have_conflicting_overlap', self, return_infos)

    def _recover_call_wrapper_returns(self, decompile_results, analysis: FunctionReturnAnalysis, current_function, tracer: PcodeTracer, condition_tracker: ConditionTracker, return_ops: List[Any], active_functions: Optional[Set[Tuple[Any, ...]]]=None) -> Optional[List[ReturnInfo]]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_recover_call_wrapper_returns', self, decompile_results, analysis, current_function, tracer, condition_tracker, return_ops, active_functions)

    def _recover_uncovered_terminal_call_returns_from_pcode(self, analysis: FunctionReturnAnalysis, tracer: PcodeTracer, condition_tracker: ConditionTracker, return_ops: List[Any], current_function, active_functions: Set[Tuple[Any, ...]]) -> Optional[List[ReturnInfo]]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_recover_uncovered_terminal_call_returns_from_pcode', self, analysis, tracer, condition_tracker, return_ops, current_function, active_functions)

    def _return_path_is_covered_by_existing_return(self, analysis: FunctionReturnAnalysis, path_conditions: Sequence[Condition]) -> bool:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_return_path_is_covered_by_existing_return', self, analysis, path_conditions)

    def _call_wrapper_recovery_conflicts_with_existing_returns(self, existing_returns: List[ReturnInfo], recovered_returns: List[ReturnInfo]) -> bool:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_call_wrapper_recovery_conflicts_with_existing_returns', self, existing_returns, recovered_returns)

    def _recover_call_wrapper_returns_from_pcode(self, analysis: FunctionReturnAnalysis, tracer: PcodeTracer, condition_tracker: ConditionTracker, return_ops: List[Any], current_function, active_functions: Set[Tuple[Any, ...]]) -> Optional[List[ReturnInfo]]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_recover_call_wrapper_returns_from_pcode', self, analysis, tracer, condition_tracker, return_ops, current_function, active_functions)

    def _analysis_needs_wrapper_recovery(self, analysis: Optional[FunctionReturnAnalysis]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_analysis_needs_wrapper_recovery', self, analysis)

    def _should_attempt_switch_recovery(self, analysis: Optional[FunctionReturnAnalysis]) -> bool:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_should_attempt_switch_recovery', self, analysis)

    def _recover_switch_like_returns_from_pcode(self, analysis: FunctionReturnAnalysis, tracer: PcodeTracer, condition_tracker: ConditionTracker, return_ops: Optional[List[Any]]=None, current_function=None, active_functions: Optional[Set[Tuple[Any, ...]]]=None) -> Optional[List[ReturnInfo]]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_recover_switch_like_returns_from_pcode', self, analysis, tracer, condition_tracker, return_ops, current_function, active_functions)

    def _find_indirect_dispatch_op_on_block(self, block_info, mnemonics: Optional[Set[str]]=None) -> Optional[Any]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_find_indirect_dispatch_op_on_block', self, block_info, mnemonics)

    def _enumerate_switch_dispatch_targets(self, dispatch_summary) -> List[Tuple[int, List[Condition]]]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_enumerate_switch_dispatch_targets', self, dispatch_summary)

    def _recover_dispatch_call_arguments(self, dispatch_op, tracer: PcodeTracer) -> List[Expression]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_recover_dispatch_call_arguments', self, dispatch_op, tracer)

    def _resolve_switch_case_target_expansions(self, address_value: int, dispatch_conditions: List[Condition], tracer: PcodeTracer, condition_tracker: ConditionTracker, return_ops: List[Any], *, active_functions: Set[Tuple[Any, ...]], current_function=None):
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_resolve_switch_case_target_expansions', self, address_value, dispatch_conditions, tracer, condition_tracker, return_ops, active_functions=active_functions, current_function=current_function)

    def _find_block_info_for_program_offset(self, condition_tracker: ConditionTracker, address_value: int):
        from .analyzer_services.lifecycle import invoke as _invoke
        return _invoke('_find_block_info_for_program_offset', self, condition_tracker, address_value)

    def _address_offset_for_block_endpoint(self, address) -> Optional[int]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_address_offset_for_block_endpoint', self, address)

    def _enumerate_switch_branch_targets(self, switch_block, indirect_op, tracer: PcodeTracer, condition_tracker: ConditionTracker) -> List[Tuple[int, List[Condition]]]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_enumerate_switch_branch_targets', self, switch_block, indirect_op, tracer, condition_tracker)

    def _collect_switch_impacted_return_sites(self, switch_block, return_ops: List[Any], condition_tracker: ConditionTracker, fallback_address: str) -> Optional[Set[str]]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_collect_switch_impacted_return_sites', self, switch_block, return_ops, condition_tracker, fallback_address)

    def _switch_recovery_targets_problematic_region(self, analysis: FunctionReturnAnalysis, affected_returns: List[ReturnInfo]) -> bool:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_switch_recovery_targets_problematic_region', self, analysis, affected_returns)

    def _switch_recovery_improves_returns(self, analysis: FunctionReturnAnalysis, affected_returns: List[ReturnInfo], recovered: List[ReturnInfo]) -> bool:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_switch_recovery_improves_returns', self, analysis, affected_returns, recovered)

    def _switch_recovery_conflicts_with_unaffected_returns(self, unaffected_returns: List[ReturnInfo], recovered: List[ReturnInfo]) -> bool:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_switch_recovery_conflicts_with_unaffected_returns', self, unaffected_returns, recovered)

    def _find_terminal_call_on_block_path(self, block_path: List[Any], return_op, *, tracer: Optional[PcodeTracer]=None, condition_tracker: Optional[ConditionTracker]=None, current_function=None, path_conditions: Optional[List[Condition]]=None):
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_find_terminal_call_on_block_path', self, block_path, return_op, tracer=tracer, condition_tracker=condition_tracker, current_function=current_function, path_conditions=path_conditions)

    def _collect_linear_ops_to_return(self, block_path: List[Any], return_op) -> Optional[List[Any]]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_collect_linear_ops_to_return', self, block_path, return_op)

    def _find_terminal_call_from_linear_ops(self, linear_ops: List[Any], return_op, *, tracer: Optional[PcodeTracer]=None, condition_tracker: Optional[ConditionTracker]=None, current_function=None, block_path=None, path_conditions: Optional[List[Condition]]=None):
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_find_terminal_call_from_linear_ops', self, linear_ops, return_op, tracer=tracer, condition_tracker=condition_tracker, current_function=current_function, block_path=block_path, path_conditions=path_conditions)

    def _get_pcode_opcode(self, pcode_op) -> Optional[int]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_get_pcode_opcode', self, pcode_op)

    def _pcode_op_debug_name(self, pcode_op) -> str:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_pcode_op_debug_name', self, pcode_op)

    def _is_pcode_call_op(self, pcode_op) -> bool:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_is_pcode_call_op', self, pcode_op)

    def _tracked_return_value_key(self, tracked: _TrackedReturnValue) -> Tuple[Any, ...]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_tracked_return_value_key', self, tracked)

    def _deduplicate_tracked_return_values(self, tracked_values: List[_TrackedReturnValue]) -> List[_TrackedReturnValue]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_deduplicate_tracked_return_values', self, tracked_values)

    def _make_tracked_return_value(self, varnode, tracer: Optional[PcodeTracer], *, storage: Optional[StorageInfo]=None, producer_op=None) -> _TrackedReturnValue:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_make_tracked_return_value', self, varnode, tracer, storage=storage, producer_op=producer_op)

    def _make_tracked_return_storage_value(self, storage: Optional[StorageInfo], *, producer_op=None) -> _TrackedReturnValue:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_make_tracked_return_storage_value', self, storage, producer_op=producer_op)

    def _make_tracked_return_value_from_affecting_op(self, pcode_op, target_storage: Optional[StorageInfo], tracer: Optional[PcodeTracer]) -> Optional[_TrackedReturnValue]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_make_tracked_return_value_from_affecting_op', self, pcode_op, target_storage, tracer)

    def _pcode_op_affects_tracked_storage(self, pcode_op, target_storage: Optional[StorageInfo], tracer: Optional[PcodeTracer], current_function=None) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_pcode_op_affects_tracked_storage', self, pcode_op, target_storage, tracer, current_function)

    def _resolve_implicit_return_tracked_values(self, return_op, tracer: PcodeTracer, condition_tracker: ConditionTracker, current_function=None, block_path=None) -> List[_TrackedReturnValue]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_resolve_implicit_return_tracked_values', self, return_op, tracer, condition_tracker, current_function, block_path)

    def _build_return_tracking_targets(self, return_op, *, tracer: Optional[PcodeTracer], current_function) -> List[_TrackedReturnValue]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_build_return_tracking_targets', self, return_op, tracer=tracer, current_function=current_function)

    def _call_output_proves_wrapper_return(self, linear_ops: List[Any], candidate_index: int, return_op, *, tracer: Optional[PcodeTracer], condition_tracker: Optional[ConditionTracker], current_function, block_path=None, path_conditions: Optional[List[Condition]]=None) -> bool:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_call_output_proves_wrapper_return', self, linear_ops, candidate_index, return_op, tracer=tracer, condition_tracker=condition_tracker, current_function=current_function, block_path=block_path, path_conditions=path_conditions)

    def _rewrite_tracked_return_values_for_op(self, tracked_values: List[_TrackedReturnValue], pcode_op, *, tracer: Optional[PcodeTracer], condition_tracker: Optional[ConditionTracker], path_conditions: Optional[List[Condition]]=None, current_function=None) -> Optional[List[_TrackedReturnValue]]:
        from .analyzer_services.return_normalization import invoke as _invoke
        return _invoke('_rewrite_tracked_return_values_for_op', self, tracked_values, pcode_op, tracer=tracer, condition_tracker=condition_tracker, path_conditions=path_conditions, current_function=current_function)

    def _rewrite_single_tracked_return_value_for_op(self, tracked: _TrackedReturnValue, pcode_op, *, tracer: Optional[PcodeTracer], condition_tracker: Optional[ConditionTracker], path_conditions: Optional[List[Condition]]=None, current_function=None) -> Optional[List[_TrackedReturnValue]]:
        from .analyzer_services.return_normalization import invoke as _invoke
        return _invoke('_rewrite_single_tracked_return_value_for_op', self, tracked, pcode_op, tracer=tracer, condition_tracker=condition_tracker, path_conditions=path_conditions, current_function=current_function)

    def _tracked_return_value_is_affected_by_op(self, tracked: _TrackedReturnValue, pcode_op, *, tracer: Optional[PcodeTracer], current_function=None) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_tracked_return_value_is_affected_by_op', self, tracked, pcode_op, tracer=tracer, current_function=current_function)

    def _propagate_passthrough_input_from_op(self, pcode_op, tracer: Optional[PcodeTracer]) -> List[_TrackedReturnValue]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_propagate_passthrough_input_from_op', self, pcode_op, tracer)

    def _propagate_multiequal_input_for_return_path(self, pcode_op, *, tracer: Optional[PcodeTracer], condition_tracker: Optional[ConditionTracker], path_conditions: Optional[List[Condition]]=None) -> List[_TrackedReturnValue]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_propagate_multiequal_input_for_return_path', self, pcode_op, tracer=tracer, condition_tracker=condition_tracker, path_conditions=path_conditions)

    def _is_zero_constant_varnode(self, varnode) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_is_zero_constant_varnode', self, varnode)

    def _propagate_indirect_return_effect(self, tracked: _TrackedReturnValue, pcode_op, tracer: Optional[PcodeTracer]) -> List[_TrackedReturnValue]:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_propagate_indirect_return_effect', self, tracked, pcode_op, tracer)

    def _tracked_values_match_call_output(self, tracked_values: List[_TrackedReturnValue], call_op, *, tracer: Optional[PcodeTracer], current_function=None) -> bool:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_tracked_values_match_call_output', self, tracked_values, call_op, tracer=tracer, current_function=current_function)

    def _parameter_storages_overlap_for_passthrough(self, caller_storage: Optional[Dict], callee_storage: Optional[Dict]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_parameter_storages_overlap_for_passthrough', self, caller_storage, callee_storage)

    def _parameter_storages_match_for_passthrough(self, caller_storage: Optional[Dict], callee_storage: Optional[Dict]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_parameter_storages_match_for_passthrough', self, caller_storage, callee_storage)

    def _coerce_wrapper_storage_info(self, storage: Optional[object]) -> Optional[StorageInfo]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_coerce_wrapper_storage_info', self, storage)

    def _parameter_descriptor_quality(self, parameters: Optional[List[Dict]]) -> Tuple[int, int, int, int]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_parameter_descriptor_quality', self, parameters)

    def _choose_richer_parameter_descriptors(self, cached_parameters: Optional[List[Dict]], fresh_parameters: Optional[List[Dict]]) -> List[Dict]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_choose_richer_parameter_descriptors', self, cached_parameters, fresh_parameters)

    def _coerce_runtime_target_ref(self, target) -> Optional[CallTargetRef]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_coerce_runtime_target_ref', self, target)

    def _function_cache_key(self, function) -> Optional[Tuple[Any, ...]]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_function_cache_key', self, function)

    def _normalize_bound_parameter_values(self, bound_parameter_values: Optional[Dict[int, Expression]]) -> Dict[int, Expression]:
        from .analyzer_services.return_normalization import invoke as _invoke
        return _invoke('_normalize_bound_parameter_values', self, bound_parameter_values)

    def _normalize_bound_parameter_storage_values(self, bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]]) -> Dict[Tuple[Any, ...], Expression]:
        from .analyzer_services.return_normalization import invoke as _invoke
        return _invoke('_normalize_bound_parameter_storage_values', self, bound_parameter_storage_values)

    def _bound_parameter_values_from_call_args(self, args: Optional[Sequence[Expression]], callee_parameters: Optional[Sequence[Dict]]) -> Dict[int, Expression]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_bound_parameter_values_from_call_args', self, args, callee_parameters)

    def _bound_parameter_storage_values_from_call_args(self, args: Optional[Sequence[Expression]], callee_parameters: Optional[Sequence[Dict]]) -> Dict[Tuple[Any, ...], Expression]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_bound_parameter_storage_values_from_call_args', self, args, callee_parameters)

    def _bound_parameter_maps_for_target_args(self, target, args: Optional[Sequence[Expression]]) -> Tuple[Dict[int, Expression], Dict[Tuple[Any, ...], Expression]]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_bound_parameter_maps_for_target_args', self, target, args)

    def _analysis_scope_key(self, target, bound_parameter_values: Optional[Dict[int, Expression]]=None, bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]]=None) -> Tuple[Any, ...]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_analysis_scope_key', self, target, bound_parameter_values, bound_parameter_storage_values)

    def _target_active_key(self, target_ref: Optional[CallTargetRef]) -> Optional[Tuple[Any, ...]]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_target_active_key', self, target_ref)

    def _extend_active_functions(self, active_functions: Optional[Set[Tuple[Any, ...]]], target_ref: Optional[CallTargetRef]) -> Set[Tuple[Any, ...]]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_extend_active_functions', self, active_functions, target_ref)

    def _resolve_target_function(self, target) -> Optional[Any]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_resolve_target_function', self, target)

    def _get_freshest_callee_parameters(self, target) -> List[Dict]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_get_freshest_callee_parameters', self, target)

    def _augment_parameters_with_implicit_passthrough(self, parameters: List[Dict], tracer: Any, active_functions: Set[Tuple[Any, ...]]) -> List[Dict]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_augment_parameters_with_implicit_passthrough', self, parameters, tracer, active_functions)

    def _should_synthesize_implicit_passthrough_for_call(self, tracer: PcodeTracer, call_op, target_storage: StorageInfo) -> bool:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_should_synthesize_implicit_passthrough_for_call', self, tracer, call_op, target_storage)

    def _is_passthrough_storage_live_in_for_call(self, tracer: PcodeTracer, call_op, target_storage: StorageInfo) -> bool:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_is_passthrough_storage_live_in_for_call', self, tracer, call_op, target_storage)

    def _has_non_parameter_symbol_for_storage(self, tracer: PcodeTracer, target_storage: StorageInfo) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_has_non_parameter_symbol_for_storage', self, tracer, target_storage)

    def _coerce_order_key(self, value: object) -> Optional[int]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_coerce_order_key', self, value)

    def _synthesize_implicit_passthrough_parameter(self, current_parameters: List[Dict], callee_param: Dict, callee_storage: StorageInfo) -> Dict:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_synthesize_implicit_passthrough_parameter', self, current_parameters, callee_param, callee_storage)

    def _clone_expression(self, expr: Expression) -> Expression:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_clone_expression', self, expr)

    def _make_tracer(self, high_function, *, bound_parameter_values: Optional[Dict[int, Expression]]=None, bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]]=None) -> PcodeTracer:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_make_tracer', self, high_function, bound_parameter_values=bound_parameter_values, bound_parameter_storage_values=bound_parameter_storage_values)

    def _invoke_build_effect_summary(self, function, high_function, tracer: PcodeTracer, condition_tracker: ConditionTracker, parameters: List[Dict], active_functions: Set[Tuple[Any, ...]], *, bound_parameter_values: Optional[Dict[int, Expression]]=None, bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]]=None):
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_invoke_build_effect_summary', self, function, high_function, tracer, condition_tracker, parameters, active_functions, bound_parameter_values=bound_parameter_values, bound_parameter_storage_values=bound_parameter_storage_values)

    def _invoke_get_or_analyze_call_target(self, target, active_functions: Set[Tuple[Any, ...]], *, minimum_param_count: int=0, args: Optional[Sequence[Expression]]=None) -> Optional[FunctionReturnAnalysis]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_invoke_get_or_analyze_call_target', self, target, active_functions, minimum_param_count=minimum_param_count, args=args)

    def _build_effect_summary(self, function, high_function, tracer: PcodeTracer, condition_tracker: ConditionTracker, parameters: List[Dict], active_functions: Set[Tuple[Any, ...]], bound_parameter_values: Optional[Dict[int, Expression]]=None, bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]]=None):
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_build_effect_summary', self, function, high_function, tracer, condition_tracker, parameters, active_functions, bound_parameter_values, bound_parameter_storage_values)

    def _make_call_resolver(self, active_functions: Set[Tuple[Any, ...]], current_function=None):
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_make_call_resolver', self, active_functions, current_function)

    def _resolve_call_expansions(self, target, args: List[Expression], active_functions: Set[Tuple[Any, ...]], current_function=None):
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_resolve_call_expansions', self, target, args, active_functions, current_function)

    def _analysis_is_fully_argument_specialized(self, analysis: Optional[FunctionReturnAnalysis]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_analysis_is_fully_argument_specialized', self, analysis)

    def _decompile_function(self, function, timeout: int=60):
        from .analyzer_services.lifecycle import invoke as _invoke
        return _invoke('_decompile_function', self, function, timeout)

    def _resolve_local_code_target_expansions(self, address_value: int, active_functions: Set[Tuple[Any, ...]], current_function=None, args: Optional[List[Expression]]=None):
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_resolve_local_code_target_expansions', self, address_value, active_functions, current_function, args)

    def _local_target_cache_key(self, address_value: int, args: List[Expression]) -> Tuple[object, ...]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_local_target_cache_key', self, address_value, args)

    def _specialize_local_target_expansions(self, expanded: List[Any], tracer: PcodeTracer, args: List[Expression]) -> List[Any]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_specialize_local_target_expansions', self, expanded, tracer, args)

    def _expand_linear_code_target(self, addr, tracer, current_function=None):
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_expand_linear_code_target', self, addr, tracer, current_function)

    def _local_varnode_key(self, varnode) -> Tuple[str, int, int]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_local_varnode_key', self, varnode)

    def _local_memory_key(self, addr_expr: Expression, size: int) -> Tuple[StructuralKey, int]:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_local_memory_key', self, addr_expr, size)

    def _evaluate_local_varnode_expression(self, varnode, tracer, local_values: Dict[Tuple[str, int, int], Expression], local_storages: Dict[Tuple[str, int, int], Any], local_memory: Dict[Tuple[StructuralKey, int], Expression], visiting: Optional[Set[int]]=None) -> Expression:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_evaluate_local_varnode_expression', self, varnode, tracer, local_values, local_storages, local_memory, visiting)

    def _evaluate_local_pcode_expression(self, pcode_op, tracer, local_values: Dict[Tuple[str, int, int], Expression], local_storages: Dict[Tuple[str, int, int], Any], local_memory: Dict[Tuple[StructuralKey, int], Expression], visiting: Optional[Set[int]]=None) -> Optional[Expression]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_evaluate_local_pcode_expression', self, pcode_op, tracer, local_values, local_storages, local_memory, visiting)

    def _apply_local_store_effect(self, pcode_op, tracer, local_values: Dict[Tuple[str, int, int], Expression], local_storages: Dict[Tuple[str, int, int], Any], local_memory: Dict[Tuple[StructuralKey, int], Expression]) -> None:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_apply_local_store_effect', self, pcode_op, tracer, local_values, local_storages, local_memory)

    def _resolve_local_return_expression(self, pcode_op, tracer, local_values: Dict[Tuple[str, int, int], Expression], local_storages: Dict[Tuple[str, int, int], Any], local_memory: Dict[Tuple[StructuralKey, int], Expression], current_function=None) -> Expression:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_resolve_local_return_expression', self, pcode_op, tracer, local_values, local_storages, local_memory, current_function)

    def _lookup_local_alias_expression(self, varnode, tracer, local_values: Dict[Tuple[str, int, int], Expression], local_storages: Dict[Tuple[str, int, int], Any]) -> Optional[Expression]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_lookup_local_alias_expression', self, varnode, tracer, local_values, local_storages)

    def _lookup_local_expression_for_storage(self, target_storage: Optional[StorageInfo], local_values: Dict[Tuple[str, int, int], Expression], local_storages: Dict[Tuple[str, int, int], Any]) -> Optional[Expression]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_lookup_local_expression_for_storage', self, target_storage, local_values, local_storages)

    def _get_function_return_varnodes(self, function) -> List[Any]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_get_function_return_varnodes', self, function)

    def _get_current_prototype_return_varnodes(self) -> List[Any]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_get_current_prototype_return_varnodes', self)

    def _infer_abi_return_storages(self) -> List[StorageInfo]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_infer_abi_return_storages', self)

    def _get_implicit_return_target_storages(self, function, tracer: PcodeTracer) -> List[StorageInfo]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_get_implicit_return_target_storages', self, function, tracer)

    def _deduplicate_storage_infos(self, storages: List[StorageInfo]) -> List[StorageInfo]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_deduplicate_storage_infos', self, storages)

    def _get_instruction_with_fallback(self, addr):
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_get_instruction_with_fallback', self, addr)

    def _attempt_disassemble_at(self, addr) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_attempt_disassemble_at', self, addr)

    def _resolve_local_branch_target(self, instruction):
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_resolve_local_branch_target', self, instruction)

    def _get_or_analyze_call_target(self, target, active_functions: Set[Tuple[Any, ...]], minimum_param_count: int=0, args: Optional[Sequence[Expression]]=None) -> Optional[FunctionReturnAnalysis]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_get_or_analyze_call_target', self, target, active_functions, minimum_param_count, args)

    def _call_summary_is_safe(self, value: Expression, conditions: List[Condition], args: List[Expression]) -> bool:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_call_summary_is_safe', self, value, conditions, args)

    def _expression_unknowns_are_deferred_call_refs(self, expr: Optional[Expression]) -> bool:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_expression_unknowns_are_deferred_call_refs', self, expr)

    def _expression_contains_unknown_or_call(self, expr: Optional[Expression]) -> bool:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_expression_contains_unknown_or_call', self, expr)

    def _expression_contains_phi(self, expr: Optional[Expression]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_expression_contains_phi', self, expr)

    def _specialize_call_analysis(self, analysis: FunctionReturnAnalysis, args: List[Expression]) -> FunctionReturnAnalysis:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_specialize_call_analysis', self, analysis, args)

    def _merge_deferred_calls_into_current_analysis(self, deferred_calls: Optional[Dict[Tuple[object, ...], DeferredCallInfo]]) -> None:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_merge_deferred_calls_into_current_analysis', self, deferred_calls)

    @staticmethod
    def _merge_call_argument_recovery_state(existing_status: Optional[str], existing_reason: Optional[str], incoming_status: Optional[str], incoming_reason: Optional[str]) -> Tuple[str, Optional[str]]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_merge_call_argument_recovery_state', existing_status, existing_reason, incoming_status, incoming_reason)

    def _normalize_call_target_expression(self, expr: Optional[Expression]) -> Optional[Expression]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_normalize_call_target_expression', self, expr)

    def _rewrite_deferred_runtime_refs_in_expression(self, expr: Optional[Expression], deferred_mapping: Dict[Tuple[object, ...], DeferredCallInfo]) -> Optional[Expression]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_rewrite_deferred_runtime_refs_in_expression', self, expr, deferred_mapping)

    def _collect_expression_object_keys(self, expr: Optional[Expression], out: Set[Tuple[object, ...]]) -> None:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_collect_expression_object_keys', self, expr, out)

    def _expression_references_only_allowed_objects(self, expr: Optional[Expression], args: List[Expression]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_expression_references_only_allowed_objects', self, expr, args)

    def _expression_references_allowed_subtrees(self, expr: Optional[Expression], allowed_subtrees: Set[Tuple[object, ...]]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_expression_references_allowed_subtrees', self, expr, allowed_subtrees)

    def _detect_signedness(self, high_function) -> Optional[SignednessResult]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_detect_signedness', self, high_function)

    def _get_return_type_info(self, high_function):
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_get_return_type_info', self, high_function)

    def _get_return_type(self, high_function) -> Optional[str]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_get_return_type', self, high_function)

    def _collect_parameters(self, high_function) -> List[Dict]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_collect_parameters', self, high_function)

    def _is_signed_type(self, data_type) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_is_signed_type', self, data_type)

    def _is_void_type(self, data_type) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_is_void_type', self, data_type)

    def _get_storage_info(self, sym) -> Optional[Dict]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_get_storage_info', self, sym)

    def _analyze_return_op(self, return_op, tracer: PcodeTracer, condition_tracker: ConditionTracker, return_index: int, current_function, active_functions: Set[Tuple[Any, ...]], return_type_obj=None) -> List[ReturnInfo]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_analyze_return_op', self, return_op, tracer, condition_tracker, return_index, current_function, active_functions, return_type_obj)

    def _coerce_block_path_entries(self, path_entries) -> Optional[List[Tuple[List[Any], List[Condition]]]]:
        from .analyzer_services.control_recovery_1 import invoke as _invoke
        return _invoke('_coerce_block_path_entries', self, path_entries)

    def _filter_noreturn_return_path_entries(self, path_entries, tracer: PcodeTracer, return_op):
        from .analyzer_services.control_recovery_2 import invoke as _invoke
        return _invoke('_filter_noreturn_return_path_entries', self, path_entries, tracer, return_op)

    def _block_path_contains_noreturn_call(self, block_path, tracer: PcodeTracer, return_op) -> bool:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_block_path_contains_noreturn_call', self, block_path, tracer, return_op)

    def _is_noreturn_call_op(self, pcode_op, tracer: PcodeTracer) -> bool:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_is_noreturn_call_op', self, pcode_op, tracer)

    def _is_noreturn_control_transfer_op(self, pcode_op, tracer: PcodeTracer) -> bool:
        from .analyzer_services.control_recovery_2 import invoke as _invoke
        return _invoke('_is_noreturn_control_transfer_op', self, pcode_op, tracer)

    def _resolve_object_centric_call_targets(self, pcode_op, tracer: Optional[PcodeTracer]) -> List[CallTargetRef]:
        from .analyzer_services.call_recovery_1 import invoke as _invoke
        return _invoke('_resolve_object_centric_call_targets', self, pcode_op, tracer)

    def _resolve_object_centric_transfer_targets(self, pcode_op, tracer: Optional[PcodeTracer]) -> List[CallTargetRef]:
        from .analyzer_services.call_recovery_2 import invoke as _invoke
        return _invoke('_resolve_object_centric_transfer_targets', self, pcode_op, tracer)

    def _resolve_function_from_call_target_ref(self, target_ref: Optional[CallTargetRef]):
        from .analyzer_services.call_recovery_2 import invoke as _invoke
        return _invoke('_resolve_function_from_call_target_ref', self, target_ref)

    def _get_function_manager(self):
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_get_function_manager', self)

    def _resolve_function_from_address(self, address):
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_resolve_function_from_address', self, address)

    def _resolve_function_from_program_offset(self, address_value: int):
        from .analyzer_services.lifecycle import invoke as _invoke
        return _invoke('_resolve_function_from_program_offset', self, address_value)

    def _function_has_no_return(self, function) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_function_has_no_return', self, function)

    def _analyze_implicit_return_value(self, return_op, address: str, tracer: PcodeTracer, condition_tracker: ConditionTracker, path_conditions: List[Condition], return_index: int, all_path_conditions: Optional[List[List[Condition]]]=None, path_entries=None, active_functions: Optional[Set[Tuple[Any, ...]]]=None, current_function=None, site_metadata: Optional[Dict[str, Optional[object]]]=None, return_type_obj=None) -> Optional[List[ReturnInfo]]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_analyze_implicit_return_value', self, return_op, address, tracer, condition_tracker, path_conditions, return_index, all_path_conditions, path_entries, active_functions, current_function, site_metadata, return_type_obj)

    def _recover_implicit_return_from_block_paths(self, return_op, address: str, tracer: PcodeTracer, condition_tracker: ConditionTracker, return_index: int, path_entries, active_functions: Optional[Set[Tuple[Any, ...]]]=None, current_function=None, site_metadata: Optional[Dict[str, Optional[object]]]=None) -> Optional[List[ReturnInfo]]:
        from .analyzer_services.control_recovery_2 import invoke as _invoke
        return _invoke('_recover_implicit_return_from_block_paths', self, return_op, address, tracer, condition_tracker, return_index, path_entries, active_functions, current_function, site_metadata)

    def _recover_return_infos_from_tracked_sources(self, tracked_sources: List[_TrackedReturnValue], address: str, tracer: PcodeTracer, condition_tracker: ConditionTracker, path_conditions: List[Condition], return_index_base: int, all_path_conditions: Optional[List[List[Condition]]]=None, active_functions: Optional[Set[Tuple[Any, ...]]]=None, current_function=None, site_metadata: Optional[Dict[str, Optional[object]]]=None) -> Optional[List[ReturnInfo]]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_recover_return_infos_from_tracked_sources', self, tracked_sources, address, tracer, condition_tracker, path_conditions, return_index_base, all_path_conditions, active_functions, current_function, site_metadata)

    def _materialize_tracked_return_source(self, tracked: _TrackedReturnValue, address: str, tracer: PcodeTracer, condition_tracker: ConditionTracker, path_conditions: List[Condition], return_index: int, all_path_conditions: Optional[List[List[Condition]]]=None, active_functions: Optional[Set[Tuple[Any, ...]]]=None, current_function=None, site_metadata: Optional[Dict[str, Optional[object]]]=None) -> Optional[List[ReturnInfo]]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_materialize_tracked_return_source', self, tracked, address, tracer, condition_tracker, path_conditions, return_index, all_path_conditions, active_functions, current_function, site_metadata)

    def _select_path_specific_return_source(self, candidate, block_path, condition_tracker: Optional[ConditionTracker]=None, path_conditions: Optional[List[Condition]]=None):
        from .analyzer_services.control_recovery_2 import invoke as _invoke
        return _invoke('_select_path_specific_return_source', self, candidate, block_path, condition_tracker, path_conditions)

    def _find_block_index_on_path(self, block_path, target_block) -> Optional[int]:
        from .analyzer_services.control_recovery_2 import invoke as _invoke
        return _invoke('_find_block_index_on_path', self, block_path, target_block)

    def _select_multiequal_input_for_return_path(self, multiequal_op, predecessor, condition_tracker: Optional[ConditionTracker]=None, path_conditions: Optional[List[Condition]]=None):
        from .analyzer_services.control_recovery_2 import invoke as _invoke
        return _invoke('_select_multiequal_input_for_return_path', self, multiequal_op, predecessor, condition_tracker, path_conditions)

    def _score_multiequal_incoming_for_return_path(self, incoming_block, predecessor, condition_tracker: Optional[ConditionTracker], current_condition_keys: Set[object]) -> Tuple[int, int, int]:
        from .analyzer_services.control_recovery_2 import invoke as _invoke
        return _invoke('_score_multiequal_incoming_for_return_path', self, incoming_block, predecessor, condition_tracker, current_condition_keys)

    def _build_condition_signature_set(self, conditions: List[Condition]) -> Set[object]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_build_condition_signature_set', self, conditions)

    def _blocks_match(self, lhs, rhs) -> bool:
        from .analyzer_services.control_recovery_2 import invoke as _invoke
        return _invoke('_blocks_match', self, lhs, rhs)

    def _get_block_start_address(self, block) -> Optional[str]:
        from .analyzer_services.control_recovery_2 import invoke as _invoke
        return _invoke('_get_block_start_address', self, block)

    def _find_terminal_call_before_return(self, return_op, condition_tracker: ConditionTracker, tracer: Optional[PcodeTracer]=None, current_function=None):
        from .analyzer_services.call_recovery_2 import invoke as _invoke
        return _invoke('_find_terminal_call_before_return', self, return_op, condition_tracker, tracer, current_function)

    @staticmethod
    def _varnode_location_key(varnode) -> Optional[Tuple[str, int, int]]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_varnode_location_key', varnode)

    @classmethod
    def _varnodes_may_alias(cls, lhs, rhs) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_varnodes_may_alias', cls, lhs, rhs)

    def _recover_implicit_return_from_terminal_call(self, call_op, address: str, tracer: PcodeTracer, condition_tracker: ConditionTracker, path_conditions: List[Condition], return_index: int, all_path_conditions: Optional[List[List[Condition]]]=None, active_functions: Optional[Set[Tuple[Any, ...]]]=None, current_function=None, site_metadata: Optional[Dict[str, Optional[object]]]=None) -> Optional[List[ReturnInfo]]:
        from .analyzer_services.call_recovery_2 import invoke as _invoke
        return _invoke('_recover_implicit_return_from_terminal_call', self, call_op, address, tracer, condition_tracker, path_conditions, return_index, all_path_conditions, active_functions, current_function, site_metadata)

    def _storages_overlap_for_return_recovery(self, left, right) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_storages_overlap_for_return_recovery', self, left, right)

    def _analyze_return_value(self, return_varnode, address: str, tracer: PcodeTracer, condition_tracker: ConditionTracker, path_conditions: List[Condition], return_index: int, all_path_conditions: Optional[List[List[Condition]]]=None, active_functions: Optional[Set[Tuple[Any, ...]]]=None, current_function=None, site_metadata: Optional[Dict[str, Optional[object]]]=None) -> List[ReturnInfo]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_analyze_return_value', self, return_varnode, address, tracer, condition_tracker, path_conditions, return_index, all_path_conditions, active_functions, current_function, site_metadata)

    def _append_smt_lowerable_phi_return_fallback_infos(self, return_infos: List[ReturnInfo], *, tracer, return_varnode, path_condition_sets: Sequence[Sequence[Condition]], address: str, return_index: int, site_metadata: Optional[Dict[str, Optional[object]]]=None):
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_append_smt_lowerable_phi_return_fallback_infos', self, return_infos, tracer=tracer, return_varnode=return_varnode, path_condition_sets=path_condition_sets, address=address, return_index=return_index, site_metadata=site_metadata)

    def _phi_origin_keys_from_return_varnode_trace(self, tracer, return_varnode) -> Tuple[Tuple[Any, ...], ...]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_phi_origin_keys_from_return_varnode_trace', self, tracer, return_varnode)

    def _phi_origin_keys_from_varnode_defs(self, varnode, *, max_depth: int=8) -> Set[Tuple[Any, ...]]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_phi_origin_keys_from_varnode_defs', self, varnode, max_depth=max_depth)

    def _path_condition_sets_union_condition(self, path_condition_sets: Sequence[Sequence[Condition]]) -> Optional[Condition]:
        from .analyzer_services.control_recovery_2 import invoke as _invoke
        return _invoke('_path_condition_sets_union_condition', self, path_condition_sets)

    def _condition_set_conjunction_expression(self, conditions: Sequence[Condition]) -> Optional[Expression]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_condition_set_conjunction_expression', self, conditions)

    def _condition_to_expression(self, condition: Condition) -> Optional[Expression]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_condition_to_expression', self, condition)

    def _phi_free_finite_fallback_candidates(self, fallback_value: Expression, conditions: Sequence[Condition]) -> List[Tuple[List[Condition], Expression]]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_phi_free_finite_fallback_candidates', self, fallback_value, conditions)

    def _split_small_finite_parameter_reachability_conditions(self, conditions: Sequence[Condition], *, search_min: int=-8, search_max: int=64, max_cases: int=16) -> List[List[Condition]]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_split_small_finite_parameter_reachability_conditions', self, conditions, search_min=search_min, search_max=search_max, max_cases=max_cases)

    def _single_parameter_expression_in_conditions(self, conditions: Sequence[Condition]) -> Optional[Expression]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_single_parameter_expression_in_conditions', self, conditions)

    def _parameter_equals_condition(self, parameter: Expression, value: int) -> Condition:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_parameter_equals_condition', self, parameter, value)

    def _phi_expression_key_set(self, expr: Optional[Expression]) -> Set[Tuple[Any, ...]]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_phi_expression_key_set', self, expr)

    def _build_return_infos_from_expansions(self, address: str, expanded_values, return_index: int, site_metadata: Optional[Dict[str, Optional[object]]]=None, return_kind: Optional[str]=None, candidate_phi_origin_keys: Sequence[Tuple[Any, ...]]=()) -> List[ReturnInfo]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_build_return_infos_from_expansions', self, address, expanded_values, return_index, site_metadata, return_kind, candidate_phi_origin_keys)

    def _matches_blocked_return_path_conditions(self, conditions: List[Condition]) -> bool:
        from .analyzer_services.control_recovery_2 import invoke as _invoke
        return _invoke('_matches_blocked_return_path_conditions', self, conditions)

    def _split_object_centric_return_case(self, value: Expression, conditions: List[Condition]) -> List[Tuple[Expression, List[Condition]]]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_split_object_centric_return_case', self, value, conditions)

    def _fold_constant_expression(self, expr: Optional[Expression], *, fallback_expr: Optional[Expression]=None) -> Optional[Expression]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_fold_constant_expression', self, expr, fallback_expr=fallback_expr)

    def _split_effect_sensitive_return_case(self, value: Expression, conditions: List[Condition]) -> List[Tuple[Expression, List[Condition]]]:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_split_effect_sensitive_return_case', self, value, conditions)

    def _rewrite_effect_sensitive_return_value(self, value: Expression, conditions: List[Condition], effect_summary: EffectSummary) -> Optional[Expression]:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_rewrite_effect_sensitive_return_value', self, value, conditions, effect_summary)

    def _resolve_precise_object_state_value(self, value: Optional[Expression], conditions: List[Condition], effect_summary: EffectSummary) -> Optional[Expression]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_resolve_precise_object_state_value', self, value, conditions, effect_summary)

    def _accept_effect_rewrite_without_rank_gain(self, original: Optional[Expression], rewritten: Optional[Expression], conditions: List[Condition], effect_summary: EffectSummary) -> bool:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_accept_effect_rewrite_without_rank_gain', self, original, rewritten, conditions, effect_summary)

    def _rewrite_drops_composite_location_wrapper(self, original: Optional[Expression], rewritten: Optional[Expression], conditions: List[Condition]) -> bool:
        from .analyzer_services.return_normalization import invoke as _invoke
        return _invoke('_rewrite_drops_composite_location_wrapper', self, original, rewritten, conditions)

    def _is_direct_location_carrier(self, expr: Optional[Expression]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_is_direct_location_carrier', self, expr)

    def _expression_has_nontrivial_location_wrapper(self, expr: Optional[Expression], location: CanonicalLocation) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_expression_has_nontrivial_location_wrapper', self, expr, location)

    def _matched_effect_locations(self, expr: Optional[Expression], conditions: List[Condition], effect_summary: EffectSummary) -> set[tuple]:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_matched_effect_locations', self, expr, conditions, effect_summary)

    def _iter_effect_sensitive_rewrite_candidates(self, value: Expression, conditions: List[Condition], effect_summary: EffectSummary) -> Iterable[Tuple[str, Optional[Expression]]]:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_iter_effect_sensitive_rewrite_candidates', self, value, conditions, effect_summary)

    def _collapse_effect_sensitive_case_wrapper(self, original: Optional[Expression], rewritten: Optional[Expression], conditions: List[Condition], effect_summary: EffectSummary) -> Optional[Expression]:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_collapse_effect_sensitive_case_wrapper', self, original, rewritten, conditions, effect_summary)

    def _rebuild_effect_sensitive_case_wrapper(self, original: Optional[Expression], rewritten: Optional[Expression], conditions: List[Condition], effect_summary: EffectSummary) -> Optional[Expression]:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_rebuild_effect_sensitive_case_wrapper', self, original, rewritten, conditions, effect_summary)

    def _wrapper_preserves_collapsed_operand(self, operator: Optional[str], shared_operand: Optional[Expression], *, kept_operand_index: int) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_wrapper_preserves_collapsed_operand', self, operator, shared_operand, kept_operand_index=kept_operand_index)

    def _accept_effect_sensitive_rewrite(self, original: Optional[Expression], rewritten: Optional[Expression], conditions: List[Condition], effect_summary: EffectSummary, *, rewrite_kind: str) -> bool:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_accept_effect_sensitive_rewrite', self, original, rewritten, conditions, effect_summary, rewrite_kind=rewrite_kind)

    def _is_semantically_lossless_effect_sensitive_rewrite(self, original: Optional[Expression], rewritten: Optional[Expression], conditions: List[Condition], effect_summary: EffectSummary) -> bool:
        from .analyzer_services.call_recovery_2 import invoke as _invoke
        return _invoke('_is_semantically_lossless_effect_sensitive_rewrite', self, original, rewritten, conditions, effect_summary)

    def _effect_sensitive_rewrite_precision(self, expr: Optional[Expression], conditions: List[Condition], effect_summary: EffectSummary) -> _EffectRewritePrecision:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_effect_sensitive_rewrite_precision', self, expr, conditions, effect_summary)

    def _effect_sensitive_rewrite_rank(self, expr: Optional[Expression]) -> Tuple[int, int, int, int]:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_effect_sensitive_rewrite_rank', self, expr)

    def _count_unresolved_value_nodes(self, expr: Optional[Expression]) -> int:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_count_unresolved_value_nodes', self, expr)

    def _count_object_centric_unknowns(self, expr: Optional[Expression]) -> int:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_count_object_centric_unknowns', self, expr)

    def _count_opaque_unknowns(self, expr: Optional[Expression]) -> int:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_count_opaque_unknowns', self, expr)

    def _count_observed_loads(self, expr: Optional[Expression]) -> int:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_count_observed_loads', self, expr)

    def _count_phi_nodes(self, expr: Optional[Expression]) -> int:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_count_phi_nodes', self, expr)

    def _expand_object_centric_expression_cases(self, expr: Optional[Expression], base_conditions: List[Condition]) -> List[Tuple[Expression, List[Condition]]]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_expand_object_centric_expression_cases', self, expr, base_conditions)

    def _expand_boolean_expression_cases(self, expr: Optional[Expression], base_conditions: List[Condition]) -> Optional[List[Tuple[Expression, List[Condition]]]]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_expand_boolean_expression_cases', self, expr, base_conditions)

    def _is_boolean_expression(self, expr: Optional[Expression]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_is_boolean_expression', self, expr)

    def _deduplicate_expression_cases(self, cases: List[Tuple[Expression, List[Condition]]]) -> List[Tuple[Expression, List[Condition]]]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_deduplicate_expression_cases', self, cases)

    def _condition_lists_equivalent(self, left: List[Condition], right: List[Condition]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_condition_lists_equivalent', self, left, right)

    def _prune_less_precise_return_infos(self, return_infos: List[ReturnInfo]) -> List[ReturnInfo]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_prune_less_precise_return_infos', self, return_infos)

    def _return_value_is_multiplicative_phi_recurrence_candidate(self, value: Optional[Expression]) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_return_value_is_multiplicative_phi_recurrence_candidate', self, value)

    def _expression_contains_phi_circular_marker(self, expr: Optional[Expression]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_expression_contains_phi_circular_marker', self, expr)

    def _exclusivize_return_regions(self, return_infos: List[ReturnInfo]) -> List[ReturnInfo]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_exclusivize_return_regions', self, return_infos)

    def _return_info_effective_region_conditions(self, info: ReturnInfo) -> List[Condition]:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_return_info_effective_region_conditions', self, info)

    def _expression_runtime_guard_conditions(self, expr: Optional[Expression]) -> List[Condition]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_expression_runtime_guard_conditions', self, expr)

    def _iter_expression_nodes_for_unconditional_runtime_guards(self, expr: Optional[Expression]):
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_iter_expression_nodes_for_unconditional_runtime_guards', self, expr)

    def _direct_expression_runtime_guard_conditions(self, expr: Optional[Expression]) -> List[Condition]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_direct_expression_runtime_guard_conditions', self, expr)

    def _runtime_ref_guard_conditions(self, runtime_ref) -> List[Condition]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_runtime_ref_guard_conditions', self, runtime_ref)

    def _return_region_priority_key(self, info: ReturnInfo, original_index: int) -> Tuple[int, int, int, int, int, int]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_return_region_priority_key', self, info, original_index)

    def _compare_return_region_order(self, left_item: Tuple[int, ReturnInfo], right_item: Tuple[int, ReturnInfo]) -> int:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_compare_return_region_order', self, left_item, right_item)

    def _return_region_can_be_shadowed_by_prior(self, region: Sequence[Condition], current: ReturnInfo, prior: ReturnInfo, *, prior_conditions: Optional[Sequence[Condition]]=None) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_return_region_can_be_shadowed_by_prior', self, region, current, prior, prior_conditions=prior_conditions)

    def _expression_contains_deferred_call_value(self, expr: Optional[Expression]) -> bool:
        from .analyzer_services.call_recovery_2 import invoke as _invoke
        return _invoke('_expression_contains_deferred_call_value', self, expr)

    def _clear_resolved_call_effect_blockers(self, analysis: Optional[FunctionReturnAnalysis]) -> None:
        from .analyzer_services.call_recovery_2 import invoke as _invoke
        return _invoke('_clear_resolved_call_effect_blockers', self, analysis)

    def _return_region_conditions_imply(self, antecedent: Sequence[Condition], consequent: Sequence[Condition]) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_return_region_conditions_imply', self, antecedent, consequent)

    def _return_region_conditions_mutually_imply(self, left: Sequence[Condition], right: Sequence[Condition]) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_return_region_conditions_mutually_imply', self, left, right)

    def _condition_is_constant_equality_guard(self, condition: Condition) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_condition_is_constant_equality_guard', self, condition)

    def _condition_logical_operator(self, condition: Condition) -> Optional[str]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_condition_logical_operator', self, condition)

    def _readonly_reduction_contract_priority_score(self, info: ReturnInfo) -> int:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_readonly_reduction_contract_priority_score', self, info)

    def _readonly_reduction_ref_contract_priority_score(self, runtime_ref: ReadonlyReductionRef) -> int:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_readonly_reduction_ref_contract_priority_score', self, runtime_ref)

    def _subtract_return_region_conjunction(self, base_conditions: List[Condition], subtract_conditions: List[Condition]) -> List[List[Condition]]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_subtract_return_region_conjunction', self, base_conditions, subtract_conditions)

    def _split_branch_index(self, branch_index: Optional[int], original_index: int, split_index: int) -> Optional[int]:
        from .analyzer_services.control_recovery_2 import invoke as _invoke
        return _invoke('_split_branch_index', self, branch_index, original_index, split_index)

    def _analysis_has_ambiguous_condition_region_returns(self, analysis: Optional[FunctionReturnAnalysis]) -> bool:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_analysis_has_ambiguous_condition_region_returns', self, analysis)

    def _pruning_conditions_signature(self, conditions: List[Condition]):
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_pruning_conditions_signature', self, conditions)

    def _merge_equivalent_return_infos(self, return_infos: List[ReturnInfo]) -> List[ReturnInfo]:
        from .analyzer_services.return_extraction_1 import invoke as _invoke
        return _invoke('_merge_equivalent_return_infos', self, return_infos)

    def _merge_return_info_pair(self, left: ReturnInfo, right: ReturnInfo, all_infos: Optional[List[ReturnInfo]]=None, left_index: Optional[int]=None, right_index: Optional[int]=None) -> Optional[ReturnInfo]:
        from .analyzer_services.return_extraction_2 import invoke as _invoke
        return _invoke('_merge_return_info_pair', self, left, right, all_infos, left_index, right_index)

    def _can_safely_collapse_complementary_return_pair(self, left: ReturnInfo, right: ReturnInfo, merged_conditions: List[Condition], all_infos: List[ReturnInfo], left_index: Optional[int], right_index: Optional[int]) -> bool:
        from .analyzer_services.return_extraction_2 import invoke as _invoke
        return _invoke('_can_safely_collapse_complementary_return_pair', self, left, right, merged_conditions, all_infos, left_index, right_index)

    def _condition_sets_are_complementary(self, left_conditions: List[Condition], right_conditions: List[Condition]) -> bool:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_condition_sets_are_complementary', self, left_conditions, right_conditions)

    def _partition_return_conditions(self, left_conditions: List[Condition], right_conditions: List[Condition]) -> Tuple[List[Condition], List[Condition], List[Condition]]:
        from .analyzer_services.return_extraction_2 import invoke as _invoke
        return _invoke('_partition_return_conditions', self, left_conditions, right_conditions)

    def _make_merged_return_info(self, primary: ReturnInfo, secondary: ReturnInfo, merged_conditions: List[Condition], reason: str) -> ReturnInfo:
        from .analyzer_services.return_extraction_2 import invoke as _invoke
        return _invoke('_make_merged_return_info', self, primary, secondary, merged_conditions, reason)

    def _merge_return_info_summary_candidate_source_keys(self, primary: ReturnInfo, secondary: ReturnInfo) -> Optional[Tuple[Any, ...]]:
        from .analyzer_services.return_extraction_2 import invoke as _invoke
        return _invoke('_merge_return_info_summary_candidate_source_keys', self, primary, secondary)

    def _min_branch_index(self, left: Optional[int], right: Optional[int]) -> Optional[int]:
        from .analyzer_services.control_recovery_2 import invoke as _invoke
        return _invoke('_min_branch_index', self, left, right)

    def _normalize_expanded_return_value(self, value: Expression, conditions: List[Condition]) -> Expression:
        from .analyzer_services.return_normalization import invoke as _invoke
        return _invoke('_normalize_expanded_return_value', self, value, conditions)

    def _substitute_parameter_constants_under_conditions(self, expr: Optional[Expression], conditions: Sequence[Condition]) -> Optional[Expression]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_substitute_parameter_constants_under_conditions', self, expr, conditions)

    def _parameter_constant_assignments_from_conditions(self, conditions: Sequence[Condition]) -> Dict[Tuple[Any, ...], Tuple[Expression, int]]:
        from .analyzer_services.session_helpers_2 import invoke as _invoke
        return _invoke('_parameter_constant_assignments_from_conditions', self, conditions)

    def _substitute_parameter_constants(self, expr: Optional[Expression], assignments: Mapping[Tuple[Any, ...], Tuple[Expression, int]]) -> Optional[Expression]:
        from .analyzer_services.session_helpers_3 import invoke as _invoke
        return _invoke('_substitute_parameter_constants', self, expr, assignments)

    def _reduce_phi_expression_under_conditions_with_smt(self, expr: Optional[Expression], conditions: Sequence[Condition], *, _active_ids: Optional[Set[int]]=None) -> Optional[Expression]:
        from .analyzer_services.session_helpers_3 import invoke as _invoke
        return _invoke('_reduce_phi_expression_under_conditions_with_smt', self, expr, conditions, _active_ids=_active_ids)

    def _active_conditions_imply_all(self, active_conditions: Sequence[Condition], conclusions: Sequence[Condition], *, assignments: Optional[Mapping[Tuple[Any, ...], Tuple[Expression, int]]]=None) -> bool:
        from .analyzer_services.session_helpers_3 import invoke as _invoke
        return _invoke('_active_conditions_imply_all', self, active_conditions, conclusions, assignments=assignments)

    def _conditions_conjunction_is_false_under_assignments(self, conditions: Sequence[Condition], assignments: Mapping[Tuple[Any, ...], Tuple[Expression, int]]) -> bool:
        from .analyzer_services.session_helpers_3 import invoke as _invoke
        return _invoke('_conditions_conjunction_is_false_under_assignments', self, conditions, assignments)

    def _condition_truth_under_parameter_assignments(self, condition: Optional[Condition], assignments: Mapping[Tuple[Any, ...], Tuple[Expression, int]], *, _active_ids: Optional[Set[int]]=None) -> Optional[bool]:
        from .analyzer_services.session_helpers_3 import invoke as _invoke
        return _invoke('_condition_truth_under_parameter_assignments', self, condition, assignments, _active_ids=_active_ids)

    def _evaluate_expression_under_parameter_assignments(self, expr: Optional[Expression], assignments: Mapping[Tuple[Any, ...], Tuple[Expression, int]], *, _active_ids: Optional[Set[int]]=None) -> Optional[Expression]:
        from .analyzer_services.session_helpers_3 import invoke as _invoke
        return _invoke('_evaluate_expression_under_parameter_assignments', self, expr, assignments, _active_ids=_active_ids)

    def _normalize_return_value_with_effect_summary(self, value: Expression, conditions: List[Condition], effect_summary: EffectSummary) -> Optional[Expression]:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_normalize_return_value_with_effect_summary', self, value, conditions, effect_summary)

    def _prefer_lossless_materialized_post_state_roundtrip(self, canonicalized: Optional[Expression], original: Expression, conditions: List[Condition], effect_summary: EffectSummary) -> Optional[Expression]:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_prefer_lossless_materialized_post_state_roundtrip', self, canonicalized, original, conditions, effect_summary)

    def _should_replay_canonicalized_return(self, canonicalized: Optional[Expression], original: Expression) -> bool:
        from .analyzer_services.return_normalization import invoke as _invoke
        return _invoke('_should_replay_canonicalized_return', self, canonicalized, original)

    def _symbolic_post_state_roundtrip_rejected(self, canonicalized: Optional[Expression], original: Expression, conditions: List[Condition], effect_summary: EffectSummary) -> bool:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_symbolic_post_state_roundtrip_rejected', self, canonicalized, original, conditions, effect_summary)

    def _expression_contains_stale_effect_value_for_post_state(self, expr: Optional[Expression], target_post_state: Optional[Expression], conditions: List[Condition], effect_summary: EffectSummary) -> bool:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_expression_contains_stale_effect_value_for_post_state', self, expr, target_post_state, conditions, effect_summary)

    def _expression_contains_unresolved_value(self, expr: Optional[Expression]) -> bool:
        from .analyzer_services.session_helpers_3 import invoke as _invoke
        return _invoke('_expression_contains_unresolved_value', self, expr)

    def _count_memory_reads(self, expr: Optional[Expression]) -> int:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_count_memory_reads', self, expr)

    def _contains_multiequal(self, varnode, depth: int=0) -> bool:
        from .analyzer_services.session_helpers_3 import invoke as _invoke
        return _invoke('_contains_multiequal', self, varnode, depth)

    def analyze_function_by_name(self, function_name: str, timeout: int=60) -> Optional[FunctionReturnAnalysis]:
        from .analyzer_services.lifecycle import invoke as _invoke
        return _invoke('analyze_function_by_name', self, function_name, timeout)

    def refresh_structural_recurrence_summary(self, analysis: Optional[FunctionReturnAnalysis], timeout: int=60) -> Optional[FunctionReturnAnalysis]:
        from .analyzer_services.session_helpers_3 import invoke as _invoke
        return _invoke('refresh_structural_recurrence_summary', self, analysis, timeout)

    def get_last_function_lookup_error(self) -> Optional[str]:
        from .analyzer_services.session_helpers_3 import invoke as _invoke
        return _invoke('get_last_function_lookup_error', self)

    def get_last_analysis_failure(self) -> Optional[AnalysisFailure]:
        from .analyzer_services.session_helpers_3 import invoke as _invoke
        return _invoke('get_last_analysis_failure', self)

    def get_last_analysis_failure_status(self) -> Optional[str]:
        from .analyzer_services.session_helpers_3 import invoke as _invoke
        return _invoke('get_last_analysis_failure_status', self)

    def _concretize_readonly_loads(self, value: Expression, conditions: List[Condition], parameters: List[Dict]) -> Expression:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_concretize_readonly_loads', self, value, conditions, parameters)

    def _read_memory_value(self, address_value: int, size_bytes: int) -> Optional[int]:
        from .analyzer_services.effect_integration import invoke as _invoke
        return _invoke('_read_memory_value', self, address_value, size_bytes)

    def _find_function_by_name(self, function_name: str):
        from .analyzer_services.lifecycle import invoke as _invoke
        return _invoke('_find_function_by_name', self, function_name)
