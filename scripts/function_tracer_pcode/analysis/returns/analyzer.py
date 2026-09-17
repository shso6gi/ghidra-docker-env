# -*- coding: utf-8 -*-
"""Compatibility facade for ReturnAnalyzer."""
from contextlib import contextmanager

from scripts.function_tracer_pcode.analysis.returns import (
    call_recovery as _svc_call_recovery,
    control_recovery as _svc_control_recovery,
    lifecycle as _svc_lifecycle,
    return_extraction as _svc_return_extraction,
    analyze_function as _svc_analyze_function,
    expansion_budget as _svc_expansion_budget,
    callee_unbound_reuse as _svc_callee_unbound_reuse,
)
from typing import Any, Dict, List, Optional, Set, Tuple
from scripts.function_tracer_pcode.core.stage_clock import stage_region
from scripts.function_tracer_pcode.core.analysis import DeferredCallInfo, FunctionReturnAnalysis
from scripts.function_tracer_pcode.core.expression import Condition
from scripts.function_tracer_pcode.analysis.returns.local_values import LocalValueResolver
from scripts.function_tracer_pcode.analysis.returns.expression_cases import ExpressionCaseService
from scripts.function_tracer_pcode.analysis.returns.debug_reporter import DebugReporter
from scripts.function_tracer_pcode.analysis.runtime_state import AnalysisRuntimeState
from scripts.function_tracer_pcode.analysis.limits import AnalysisLimits
from scripts.function_tracer_pcode.analysis.diagnostics_state import AnalysisDiagnosticsState
from scripts.function_tracer_pcode.analysis.returns.condition_logic import ConditionLogicService
from scripts.function_tracer_pcode.analysis.returns.control_recovery import ReturnPathSelectionService
from scripts.function_tracer_pcode.analysis.returns.control_recovery import BranchGuardedWhileProofService
from scripts.function_tracer_pcode.analysis.returns.control_recovery import BlockGraphService
from scripts.function_tracer_pcode.analysis.returns.lifecycle import ProgramAccessService
from scripts.function_tracer_pcode.analysis.returns.effect_integration import EffectIntegrationService
from scripts.function_tracer_pcode.analysis.returns.parameters import ParameterService
from scripts.function_tracer_pcode.analysis.returns.divergence_proofs import DivergenceProofService
from scripts.function_tracer_pcode.analysis.returns.return_normalization import ReturnNormalizationService
from scripts.function_tracer_pcode.analysis.returns.pcode_sites import PcodeSiteService
from scripts.function_tracer_pcode.analysis.returns.phi_origins import PhiOriginService
from scripts.function_tracer_pcode.analysis.returns.stack_protector import StackProtectorService
from scripts.function_tracer_pcode.analysis.returns.placeholder_algebra import PlaceholderAlgebraService
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

    def __init__(self, program, debug: bool=False, binary_id: Optional[str]=None, *, enable_completed_recovery_proofs: bool=True, external_call_effect_policy=None, decompiler=None):
        self.program = program
        self._region_facts = RegionFacts(program)
        self._debug_reporter = DebugReporter(debug_flag=lambda: self.debug)
        self._local_values = LocalValueResolver(debug_reporter=self._debug_reporter)
        self._program_access = ProgramAccessService(
            debug_reporter=self._debug_reporter,
            decompile_with_broker=lambda *a, **kw: self._decompile_with_broker(*a, **kw),
            program_value=lambda: self.program,
            binary_id_value=lambda: self._binary_id,
            debug_flag=lambda: self.debug,
            decompiler_value=lambda: self._decompiler,
            set_decompiler=lambda value: setattr(self, "_decompiler", value),
            on_program_mutation=self._invalidate_decompile_derived_caches,
        )
        self.debug = debug
        self._binary_id = binary_id
        self.enable_completed_recovery_proofs = bool(enable_completed_recovery_proofs)
        # ``decompiler`` を与えた呼び出しでは lifecycle の遅延生成分岐
        # （``DecompInterface()`` の import と ``openProgram()``）に入らない。
        # 与えない既定の呼び出しでは従来どおり None から始める。
        self._decompiler = decompiler
        self._analysis_session = AnalysisSession()
        # 長寿命の可変 runtime 状態と bounded-call 設定は collaborator 構築より前に所有者を作る（6a-2 / 6a-3）。
        self._runtime_state = AnalysisRuntimeState()
        # Issue #104 (Gap 4): observation policy for external / thunk callees
        # in the effect lane (configuration, supplied to the effect collaborator).
        from scripts.function_tracer_pcode.analysis.effects.external_call_models import (
            ExternalCallEffectPolicy,
        )

        if external_call_effect_policy is None:
            external_call_effect_policy = ExternalCallEffectPolicy()
        if type(external_call_effect_policy) is not ExternalCallEffectPolicy:
            raise TypeError("external call effect policy must be an exact ExternalCallEffectPolicy")
        self._external_call_effect_policy = external_call_effect_policy
        self._limits = AnalysisLimits.from_settings()
        self._diagnostics = AnalysisDiagnosticsState()
        self._current_parameters: List[Dict] = []
        self._expression_cases = ExpressionCaseService(
            session=self._ensure_analysis_session,
        )
        self._stack_protector = StackProtectorService(
            extract_stack_protector_memory_probe=lambda *a, **kw: self._extract_stack_protector_memory_probe(*a, **kw),
            return_site_metadata_from_info=lambda *a, **kw: self._return_site_metadata_from_info(*a, **kw),
            make_return_info=lambda *a, **kw: self._make_return_info(*a, **kw),
            debug_reporter=self._debug_reporter,
            debug_flag=lambda: self.debug,
        )
        self._condition_logic = ConditionLogicService(
            stack_protector=self._stack_protector,
            fold_constant_expression=lambda expr, **kw: self._fold_constant_expression(expr, **kw),
        )
        self._pcode_sites = PcodeSiteService(
            program_access=self._program_access,
            storages_overlap_for_return_recovery=lambda *a, **kw: self._storages_overlap_for_return_recovery(*a, **kw),
            current_function_entry_address=lambda *a, **kw: self._current_function_entry_address(*a, **kw),
            is_pcode_call_op=lambda *a, **kw: self._is_pcode_call_op(*a, **kw),
            get_implicit_return_target_storages=lambda *a, **kw: self._get_implicit_return_target_storages(*a, **kw),
            binary_id_value=lambda: self._binary_id,
        )
        self._block_graph = BlockGraphService(
            pcode_sites=self._pcode_sites,
            cbranch_direct_target_keys=lambda *a, **kw: self._cbranch_direct_target_keys(*a, **kw),
        )
        self._return_paths = ReturnPathSelectionService(
            session=self._ensure_analysis_session,
            condition_logic=self._condition_logic,
            block_graph=self._block_graph,
            expression_cases=self._expression_cases,
            debug_reporter=self._debug_reporter,
            make_tracked_return_value=lambda *a, **kw: self._make_tracked_return_value(*a, **kw),
            return_info_effective_region_conditions=lambda *a, **kw: self._return_info_effective_region_conditions(*a, **kw),
            debug_flag=lambda: self.debug,
        )
        self._return_normalization = ReturnNormalizationService(
            session=self._ensure_analysis_session,
            return_paths=self._return_paths,
            expression_cases=self._expression_cases,
            condition_logic=self._condition_logic,
            stack_protector=self._stack_protector,
            pcode_sites=self._pcode_sites,
            debug_reporter=self._debug_reporter,
            count_memory_reads=lambda *a, **kw: self._count_memory_reads(*a, **kw),
            propagate_indirect_return_effect=lambda *a, **kw: self._propagate_indirect_return_effect(*a, **kw),
            normalize_return_value_with_effect_summary=lambda *a, **kw: self._normalize_return_value_with_effect_summary(*a, **kw),
            tracked_return_value_is_affected_by_op=lambda *a, **kw: self._tracked_return_value_is_affected_by_op(*a, **kw),
            merge_equivalent_return_infos=lambda *a, **kw: self._merge_equivalent_return_infos(*a, **kw),
            exclusivize_return_regions=lambda *a, **kw: self._exclusivize_return_regions(*a, **kw),
            deduplicate_tracked_return_values=lambda *a, **kw: self._deduplicate_tracked_return_values(*a, **kw),
            propagate_passthrough_input_from_op=lambda *a, **kw: self._propagate_passthrough_input_from_op(*a, **kw),
            normalize_return_callother_userops=lambda *a, **kw: self._normalize_return_callother_userops(*a, **kw),
            debug_flag=lambda: self.debug,
        )
        self._parameters = ParameterService(
            pcode_sites=self._pcode_sites,
            return_normalization=self._return_normalization,
            debug_reporter=self._debug_reporter,
            target_active_key=lambda *a, **kw: self._target_active_key(*a, **kw),
            should_synthesize_implicit_passthrough_for_call=lambda *a, **kw: self._should_synthesize_implicit_passthrough_for_call(*a, **kw),
            return_site_metadata_from_info=lambda *a, **kw: self._return_site_metadata_from_info(*a, **kw),
            make_tracked_return_value=lambda *a, **kw: self._make_tracked_return_value(*a, **kw),
            make_return_info=lambda *a, **kw: self._make_return_info(*a, **kw),
            get_freshest_callee_parameters=lambda *a, **kw: self._get_freshest_callee_parameters(*a, **kw),
            program_value=lambda: self.program,
            debug_flag=lambda: self.debug,
            set_current_parameters=lambda value: setattr(self, "_current_parameters", value),
        )
        self._placeholder_algebra = PlaceholderAlgebraService(
            session=self._ensure_analysis_session,
            condition_logic=self._condition_logic,
            stack_protector=self._stack_protector,
            branch_guarded_expression_is_param_minus_one=lambda *a, **kw: self._branch_guarded_expression_is_param_minus_one(*a, **kw),
        )
        self._divergence_proofs = DivergenceProofService(
            runtime_state=self._runtime_state,
            block_graph=self._block_graph,
            program_access=self._program_access,
            condition_logic=self._condition_logic,
            placeholder_algebra=self._placeholder_algebra,
            stack_protector=self._stack_protector,
            debug_reporter=self._debug_reporter,
            program_value=lambda: self.program,
        )
        self._phi_origins = PhiOriginService(
            condition_logic=self._condition_logic,
            stack_protector=self._stack_protector,
            pcode_sites=self._pcode_sites,
            return_normalization=self._return_normalization,
            debug_reporter=self._debug_reporter,
            debug_flag=lambda: self.debug,
        )
        self._branch_guarded_while = BranchGuardedWhileProofService(
            session=self._ensure_analysis_session,
            return_paths=self._return_paths,
            condition_logic=self._condition_logic,
            placeholder_algebra=self._placeholder_algebra,
            divergence_proofs=self._divergence_proofs,
            block_graph=self._block_graph,
            stack_protector=self._stack_protector,
            debug_reporter=self._debug_reporter,
            expression_cases=self._expression_cases,
            phi_origins=self._phi_origins,
            program_access=self._program_access,
            parameters=self._parameters,
            pcode_sites=self._pcode_sites,
            acc_phi_flows_to_return_origin_phi=lambda *a, **kw: self._acc_phi_flows_to_return_origin_phi(*a, **kw),
            return_conditions_cover_region=lambda *a, **kw: self._return_conditions_cover_region(*a, **kw),
            return_info_candidate_phi_origin_keys=lambda *a, **kw: self._return_info_candidate_phi_origin_keys(*a, **kw),
            return_info_return_phi_origin_keys=lambda *a, **kw: self._return_info_return_phi_origin_keys(*a, **kw),
            return_info_summary_identity_key=lambda *a, **kw: self._return_info_summary_identity_key(*a, **kw),
            return_site_key=lambda *a, **kw: self._return_site_key(*a, **kw),
            debug_flag=lambda: self.debug,
            enable_completed_recovery_proofs_value=lambda: self.enable_completed_recovery_proofs,
            program_value=lambda: self.program,
        )
        self._effect_integration = EffectIntegrationService(
            runtime_state=self._runtime_state,
            session=self._ensure_analysis_session,
            program_access=self._program_access,
            expression_cases=self._expression_cases,
            return_normalization=self._return_normalization,
            stack_protector=self._stack_protector,
            pcode_sites=self._pcode_sites,
            phi_origins=self._phi_origins,
            divergence_proofs=self._divergence_proofs,
            parameters=self._parameters,
            region_facts=self._region_facts,
            local_values=self._local_values,
            debug_reporter=self._debug_reporter,
            extend_active_functions=lambda *a, **kw: self._extend_active_functions(*a, **kw),
            current_function_entry_address=lambda *a, **kw: self._current_function_entry_address(*a, **kw),
            analysis_scope_key=lambda *a, **kw: self._analysis_scope_key(*a, **kw),
            get_freshest_callee_parameters=lambda *a, **kw: self._get_freshest_callee_parameters(*a, **kw),
            make_call_resolver=lambda *a, **kw: self._make_call_resolver(*a, **kw),
            bound_parameter_values_from_call_args=lambda *a, **kw: self._bound_parameter_values_from_call_args(*a, **kw),
            bound_parameter_storage_values_from_call_args=lambda *a, **kw: self._bound_parameter_storage_values_from_call_args(*a, **kw),
            target_active_key=lambda *a, **kw: self._target_active_key(*a, **kw),
            resolve_target_function=lambda *a, **kw: self._resolve_target_function(*a, **kw),
            make_deferred_call_recorder=lambda *a, **kw: self._make_deferred_call_recorder(*a, **kw),
            is_semantically_lossless_effect_sensitive_rewrite=lambda *a, **kw: self._is_semantically_lossless_effect_sensitive_rewrite(*a, **kw),
            direct_call_target_function_key=lambda *a, **kw: self._direct_call_target_function_key(*a, **kw),
            coerce_runtime_target_ref=lambda *a, **kw: self._coerce_runtime_target_ref(*a, **kw),
            make_tracked_return_value=lambda *a, **kw: self._make_tracked_return_value(*a, **kw),
            function_body_has_phase1_pure_return_forbidden_ops=lambda *a, **kw: self._function_body_has_phase1_pure_return_forbidden_ops(*a, **kw),
            high_function_has_phase1_pure_return_forbidden_ops=lambda *a, **kw: self._high_function_has_phase1_pure_return_forbidden_ops(*a, **kw),
            phase1_return_type_is_float=lambda *a, **kw: self._phase1_return_type_is_float(*a, **kw),
            decompile_with_broker=lambda *a, **kw: self._decompile_with_broker(*a, **kw),
            program_value=lambda: self.program,
            binary_id_value=lambda: self._binary_id,
            debug_flag=lambda: self.debug,
            external_call_effect_policy=lambda: self._external_call_effect_policy,
        )
        self._current_effect_summary: Optional[EffectSummary] = None
        self._current_deferred_calls: Dict[Tuple[Any, ...], DeferredCallInfo] = {}
        self._return_path_entry_cache: Dict[Tuple[Any, ...], Optional[List[Tuple[List[Any], List[Condition]]]]] = {}
        self._current_blocked_return_path_conditions: List[List[Condition]] = []
        self._current_noreturn_terminal_observations: List[Dict[str, Any]] = []
        self._current_function_prototype = None
        self._current_function_entry_address_value = None

    def _ensure_analysis_session(self) -> AnalysisSession:
        try:
            return object.__getattribute__(self, '_analysis_session')
        except AttributeError:
            session = AnalysisSession()
            object.__setattr__(self, '_analysis_session', session)
            return session

    def _install_analysis_session(self, session: AnalysisSession) -> None:
        """現在の :class:`AnalysisSession` object を差し替える（``_analysis_context`` の push/pop 用）。"""
        object.__setattr__(self, '_analysis_session', session)

    def _ensure_runtime_state(self) -> AnalysisRuntimeState:
        try:
            return object.__getattribute__(self, '_runtime_state')
        except AttributeError:
            state = AnalysisRuntimeState()
            object.__setattr__(self, '_runtime_state', state)
            return state

    def _ensure_limits(self) -> AnalysisLimits:
        try:
            return object.__getattribute__(self, '_limits')
        except AttributeError:
            limits = AnalysisLimits.from_settings()
            object.__setattr__(self, '_limits', limits)
            return limits

    def _ensure_diagnostics(self) -> AnalysisDiagnosticsState:
        try:
            return object.__getattribute__(self, '_diagnostics')
        except AttributeError:
            diagnostics = AnalysisDiagnosticsState()
            object.__setattr__(self, '_diagnostics', diagnostics)
            return diagnostics

    @property
    def _last_function_lookup_error(self):
        return self._ensure_diagnostics().last_function_lookup_error

    @_last_function_lookup_error.setter
    def _last_function_lookup_error(self, value):
        self._ensure_diagnostics().last_function_lookup_error = value

    @property
    def _last_analysis_failure(self):
        return self._ensure_diagnostics().last_analysis_failure

    @_last_analysis_failure.setter
    def _last_analysis_failure(self, value):
        self._ensure_diagnostics().last_analysis_failure = value

    @property
    def _bounded_call_refinement_enabled(self):
        return self._ensure_limits().bounded_call_refinement_enabled

    @_bounded_call_refinement_enabled.setter
    def _bounded_call_refinement_enabled(self, value):
        self._ensure_limits().bounded_call_refinement_enabled = value

    @property
    def _bounded_call_unroll_limit(self):
        return self._ensure_limits().bounded_call_unroll_limit

    @_bounded_call_unroll_limit.setter
    def _bounded_call_unroll_limit(self, value):
        self._ensure_limits().bounded_call_unroll_limit = value

    @property
    def _bounded_call_max_cases(self):
        return self._ensure_limits().bounded_call_max_cases

    @_bounded_call_max_cases.setter
    def _bounded_call_max_cases(self, value):
        self._ensure_limits().bounded_call_max_cases = value

    @property
    def _call_analysis_cache(self):
        return self._ensure_runtime_state().call_analysis_cache

    @_call_analysis_cache.setter
    def _call_analysis_cache(self, value):
        self._ensure_runtime_state().call_analysis_cache = value

    @property
    def _local_target_cache(self):
        return self._ensure_runtime_state().local_target_cache

    @_local_target_cache.setter
    def _local_target_cache(self, value):
        self._ensure_runtime_state().local_target_cache = value

    @property
    def _effect_summary_cache(self):
        return self._ensure_runtime_state().effect_summary_cache

    @_effect_summary_cache.setter
    def _effect_summary_cache(self, value):
        self._ensure_runtime_state().effect_summary_cache = value

    @property
    def _effect_summary_budget_diagnostics(self):
        return self._ensure_runtime_state().effect_summary_budget_diagnostics

    @_effect_summary_budget_diagnostics.setter
    def _effect_summary_budget_diagnostics(self, value):
        self._ensure_runtime_state().effect_summary_budget_diagnostics = value

    @property
    def _effect_summary_parameter_cache(self):
        return self._ensure_runtime_state().effect_summary_parameter_cache

    @_effect_summary_parameter_cache.setter
    def _effect_summary_parameter_cache(self, value):
        self._ensure_runtime_state().effect_summary_parameter_cache = value

    @property
    def _callee_parameter_decompile_cache(self):
        return self._ensure_runtime_state().callee_parameter_decompile_cache

    @_callee_parameter_decompile_cache.setter
    def _callee_parameter_decompile_cache(self, value):
        self._ensure_runtime_state().callee_parameter_decompile_cache = value

    @property
    def _callee_parameter_decompile_stats(self):
        return self._ensure_runtime_state().callee_parameter_decompile_stats

    @_callee_parameter_decompile_stats.setter
    def _callee_parameter_decompile_stats(self, value):
        self._ensure_runtime_state().callee_parameter_decompile_stats = value

    @property
    def _callee_analysis_cache_stats(self):
        return self._ensure_runtime_state().callee_analysis_cache_stats

    @_callee_analysis_cache_stats.setter
    def _callee_analysis_cache_stats(self, value):
        self._ensure_runtime_state().callee_analysis_cache_stats = value

    @property
    def _callee_unbound_reuse_verdicts(self):
        return self._ensure_runtime_state().callee_unbound_reuse_verdicts

    @_callee_unbound_reuse_verdicts.setter
    def _callee_unbound_reuse_verdicts(self, value):
        self._ensure_runtime_state().callee_unbound_reuse_verdicts = value

    @property
    def _callee_unbound_reuse_cache_ownership(self):
        return self._ensure_runtime_state().callee_unbound_reuse_cache_ownership

    @_callee_unbound_reuse_cache_ownership.setter
    def _callee_unbound_reuse_cache_ownership(self, value):
        self._ensure_runtime_state().callee_unbound_reuse_cache_ownership = value

    @property
    def _callee_unbound_reuse_stats(self):
        return self._ensure_runtime_state().callee_unbound_reuse_stats

    @_callee_unbound_reuse_stats.setter
    def _callee_unbound_reuse_stats(self, value):
        self._ensure_runtime_state().callee_unbound_reuse_stats = value

    def callee_unbound_reuse_diagnostics(self) -> Dict[str, Any]:
        """external placeholder callee の束縛ゼロ解析再利用の診断（Issue #47 PR-B）。

        判定には使わない観測値なので、失敗しても呼び出し側に例外を出さない。
        """
        try:
            payload = self._callee_unbound_reuse_stats.snapshot()
            payload["entries"] = len(self._callee_unbound_reuse_verdicts)
            payload["owned_cache_entries"] = len(
                self._callee_unbound_reuse_cache_ownership.owned_keys()
            )
            return payload
        except Exception as exc:  # diagnostics never fail the verdict
            return {"error": f"{type(exc).__name__}: {exc}"[:200]}

    def callee_analysis_cache_diagnostics(self) -> Dict[str, Any]:
        """callee 解析 cache（``call_analysis_cache``）の hit/miss 診断（Issue #47）。

        parameter snapshot cache（``callee_parameter_cache_diagnostics``）とは対象が別。
        判定には使わない観測値なので、失敗しても呼び出し側に例外を出さない。
        """
        try:
            payload = self._callee_analysis_cache_stats.snapshot()
            payload["entries"] = len(self._call_analysis_cache)
            return payload
        except Exception as exc:  # diagnostics never fail the verdict
            return {"error": f"{type(exc).__name__}: {exc}"[:200]}

    def callee_parameter_cache_diagnostics(self) -> Dict[str, Any]:
        """callee parameter snapshot cache の hit/miss 診断（Issue #47 PR-A）。

        判定には使わない観測値なので、失敗しても呼び出し側に例外を出さない。
        """
        try:
            payload = self._callee_parameter_decompile_stats.snapshot()
            payload["entries"] = len(self._callee_parameter_decompile_cache)
            return payload
        except Exception as exc:  # diagnostics never fail the verdict
            return {"error": f"{type(exc).__name__}: {exc}"[:200]}

    def _invalidate_decompile_derived_caches(self) -> None:
        """program を書き換えたら、decompile 由来の snapshot は証拠として無効にする。

        ``_effect_summary_parameter_cache``（partial cache）は従来どおり残す。破棄するのは
        「再 decompile の代わりに使える」と主張していた snapshot だけで、次回は必ず
        decompile し直す（fail-closed）。
        """
        cache = self._callee_parameter_decompile_cache
        entries = len(cache)
        cache.clear()
        self._callee_parameter_decompile_stats.record_invalidation(entries)
        # Issue #47 (PR-B): 再利用の適格判定と、その判定に基づいて再利用の根拠として
        # 使った解析 cache entry（束縛ゼロ entry / そこから作った束縛 view / 同じ解析を
        # 指す generic 別名）も decompile 由来の証拠なので捨てる。判定だけ捨てても、
        # ``analyze_function()`` 冒頭の cache 参照が判定より先に書き換え前の解析を
        # 返してしまう。所有していない entry は落とさない。
        verdicts = self._callee_unbound_reuse_verdicts
        verdict_entries = len(verdicts)
        verdicts.clear()
        evicted = self._callee_unbound_reuse_cache_ownership.evict_from(
            self._call_analysis_cache
        )
        self._callee_unbound_reuse_stats.record_invalidation(verdict_entries, evicted)

    @property
    def _direct_call_graph(self):
        return self._ensure_runtime_state().direct_call_graph

    @_direct_call_graph.setter
    def _direct_call_graph(self, value):
        self._ensure_runtime_state().direct_call_graph = value

    @property
    def _direct_call_graph_complete_nodes(self):
        return self._ensure_runtime_state().direct_call_graph_complete_nodes

    @_direct_call_graph_complete_nodes.setter
    def _direct_call_graph_complete_nodes(self, value):
        self._ensure_runtime_state().direct_call_graph_complete_nodes = value

    @property
    def _analysis_in_progress(self):
        return self._ensure_runtime_state().analysis_in_progress

    @_analysis_in_progress.setter
    def _analysis_in_progress(self, value):
        self._ensure_runtime_state().analysis_in_progress = value

    @property
    def _deferred_call_counter(self):
        return self._ensure_runtime_state().deferred_call_counter

    @_deferred_call_counter.setter
    def _deferred_call_counter(self, value):
        self._ensure_runtime_state().deferred_call_counter = value

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
    def _current_expansion_budget_collector(self):
        """現在の解析 scope が所有する切り捨て collector（Issue #131）。

        ``_analysis_context`` が push する子 session は自分の collector を新規に所有
        するので、子解析の記録が親 session へ混入しない。
        """
        return self._ensure_analysis_session().expansion_budget_collector

    @_current_expansion_budget_collector.setter
    def _current_expansion_budget_collector(self, value):
        self._ensure_analysis_session().expansion_budget_collector = value

    @property
    def _current_analysis_scope_key(self):
        return self._ensure_analysis_session().analysis_scope_key

    @_current_analysis_scope_key.setter
    def _current_analysis_scope_key(self, value):
        self._ensure_analysis_session().analysis_scope_key = value

    @property
    def _return_path_entry_cache(self):
        return self._ensure_analysis_session().return_path_entry_cache

    @_return_path_entry_cache.setter
    def _return_path_entry_cache(self, value):
        self._ensure_analysis_session().return_path_entry_cache = value

    @contextmanager
    def _analysis_context(self, parameters: List[Dict], effect_summary: Optional[EffectSummary], function_prototype=None, function_entry_address=None, analysis_scope_key=None):
        """Push a fresh per-analysis :class:`AnalysisSession` and restore the parent on exit.

        子 session は context が明示的に束縛する値（parameters / effect_summary / function_prototype /
        function_entry_address）で初期化し、``deferred_calls`` / ``blocked_return_path_conditions`` /
        ``noreturn_terminal_observations`` / ``return_path_entry_cache`` は子が新規に所有する。finally では
        親 session object をそのまま（同一性で）復元する。旧実装は 5 フィールドを個別に退避・復元し、
        ``noreturn_terminal_observations`` / ``blocked_return_path_conditions`` / ``return_path_entry_cache``
        は退避していなかった（子の変更が親へ漏れていた）。8 フィールドの寿命を context に揃えるのは
        意図的な state-lifetime の修正（Phase 6a-1）。
        """
        parent = self._ensure_analysis_session()
        child = AnalysisSession(
            parameters=parameters,
            effect_summary=effect_summary,
            function_prototype=function_prototype,
            function_entry_address=function_entry_address,
            analysis_scope_key=analysis_scope_key,
        )
        self._install_analysis_session(child)
        try:
            yield
        finally:
            self._install_analysis_session(parent)

    # ---- service implementations (bound explicitly; see <pkg>/*.py) ----
    # expansion_budget (Issue #131)
    _absorb_effect_summary_budget_diagnostics = _svc_expansion_budget._impl__absorb_effect_summary_budget_diagnostics
    _make_expansion_budget_sink = _svc_expansion_budget._impl__make_expansion_budget_sink
    _record_callee_analysis_expansion_budget = _svc_expansion_budget._impl__record_callee_analysis_expansion_budget
    _record_expansion_budget_truncations = _svc_expansion_budget._impl__record_expansion_budget_truncations
    _sync_expansion_budget_truncations = _svc_expansion_budget._impl__sync_expansion_budget_truncations
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
    def _block_debug_key(self, block):
        return self._block_graph.block_debug_key(block)
    def _block_has_return_op(self, block):
        return self._block_graph.block_has_return_op(block)
    def _block_predecessor_count(self, block):
        return self._block_graph.block_predecessor_count(block)
    def _block_reaches(self, start, target, allowed):
        return self._block_graph.block_reaches(start, target, allowed)
    def _block_start_address_keys(self, block):
        return self._block_graph.block_start_address_keys(block)
    def _block_start_address_spaces(self, block):
        return self._block_graph.block_start_address_spaces(block)
    def _block_successors(self, block):
        return self._block_graph.block_successors(block)
    def _block_writes_outcome_guard_state(self, block):
        return self._block_graph.block_writes_outcome_guard_state(block)
    def _branch_guarded_affine_ignored_artifacts_are_shadowed(self, ignored_artifacts, recursive_returns, parameters):
        return self._branch_guarded_while.branch_guarded_affine_ignored_artifacts_are_shadowed(ignored_artifacts, recursive_returns, parameters)
    def _branch_guarded_affine_phi_step(self, value):
        return self._branch_guarded_while.branch_guarded_affine_phi_step(value)
    def _branch_guarded_affine_singleton_base_anchor_matches(self, value, conditions, c_param, target_conditions):
        return self._branch_guarded_while.branch_guarded_affine_singleton_base_anchor_matches(value, conditions, c_param, target_conditions)
    def _branch_guarded_artifact_is_imprecise_zero_seed(self, artifact, *, zero_ret, parameters):
        return self._branch_guarded_while.branch_guarded_artifact_is_imprecise_zero_seed(artifact, zero_ret=zero_ret, parameters=parameters)
    def _branch_guarded_artifact_is_structural_accumulator_seed_projection(self, artifact, *, recursive_returns, parameters):
        return self._branch_guarded_while.branch_guarded_artifact_is_structural_accumulator_seed_projection(artifact, recursive_returns=recursive_returns, parameters=parameters)
    def _branch_guarded_expression_is_param_minus_one(self, expr, param, target_conditions):
        return self._branch_guarded_while.branch_guarded_expression_is_param_minus_one(expr, param, target_conditions)
    def _branch_guarded_structural_proof_from_return(self, ret):
        return self._branch_guarded_while.branch_guarded_structural_proof_from_return(ret)
    def _check_condition_coverage(self, analysis):
        return self._return_paths.check_condition_coverage(analysis)
    def _coerce_block_path_entries(self, path_entries):
        return self._block_graph.coerce_block_path_entries(path_entries)
    _collect_switch_impacted_return_sites = _svc_control_recovery._impl__collect_switch_impacted_return_sites
    def _control_region_returns_are_safe(self, return_infos):
        return self._return_paths.control_region_returns_are_safe(return_infos)
    def _direct_cbranch_successor_relation(self, cbranch, block, successor):
        return self._block_graph.direct_cbranch_successor_relation(cbranch, block, successor)
    def _find_branch_guarded_structural_proof_tuple(self, value):
        return self._branch_guarded_while.find_branch_guarded_structural_proof_tuple(value)
    def _find_branch_guarded_while_return_partition(self, analysis, *, high_function, c_param, c_nonpositive, c_positive, t_positive):
        return self._branch_guarded_while.find_branch_guarded_while_return_partition(analysis, high_function=high_function, c_param=c_param, c_nonpositive=c_nonpositive, c_positive=c_positive, t_positive=t_positive)
    def _first_high_block_cbranch(self, block):
        return self._block_graph.first_high_block_cbranch(block)
    _get_cached_return_path_entries = _svc_control_recovery._impl__get_cached_return_path_entries
    def _high_function_cbranch_count(self, high_function):
        return self._block_graph.high_function_cbranch_count(high_function)
    def _high_function_has_forbidden_control_outcome_ops(self, high_function, *, allow_call):
        return self._return_paths.high_function_has_forbidden_control_outcome_ops(high_function, allow_call=allow_call)
    def _infer_branch_guarded_while_role_parameters(self, analysis):
        return self._branch_guarded_while.infer_branch_guarded_while_role_parameters(analysis)
    def _is_control_outcome_forbidden_fp_mnemonic(self, mnemonic):
        return self._return_paths.is_control_outcome_forbidden_fp_mnemonic(mnemonic)
    def _iter_high_basic_blocks(self, high_function):
        return self._block_graph.iter_high_basic_blocks(high_function)
    def _iter_high_block_ops(self, block):
        return self._block_graph.iter_high_block_ops(block)
    def _mark_incomplete_control_flow(self, analysis):
        return self._return_paths.mark_incomplete_control_flow(analysis)
    _materialize_direct_path_specific_return_source = _svc_control_recovery._impl__materialize_direct_path_specific_return_source
    _phase1_direct_branch_escapes_function_body = _svc_control_recovery._impl__phase1_direct_branch_escapes_function_body
    def _propagate_multiequal_input_for_return_path(self, pcode_op, *, tracer, condition_tracker, path_conditions=None):
        return self._return_paths.propagate_multiequal_input_for_return_path(pcode_op, tracer=tracer, condition_tracker=condition_tracker, path_conditions=path_conditions)
    def _prove_branch_guarded_affine_unit_count_recurrence(self, high_function, *, analysis, c_param, target_conditions, recursive_returns, candidate_phi_origin_keys=(), return_phi_origin_keys=(), nonprogress_conditions=(), allow_latch_progress_guard=False):
        return self._branch_guarded_while.prove_branch_guarded_affine_unit_count_recurrence(high_function, analysis=analysis, c_param=c_param, target_conditions=target_conditions, recursive_returns=recursive_returns, candidate_phi_origin_keys=candidate_phi_origin_keys, return_phi_origin_keys=return_phi_origin_keys, nonprogress_conditions=nonprogress_conditions, allow_latch_progress_guard=allow_latch_progress_guard)
    def _prove_branch_guarded_structural_nonprogress_must_diverge(self, high_function, *, analysis=None, initial_c_ret, invariant_conditions):
        return self._branch_guarded_while.prove_branch_guarded_structural_nonprogress_must_diverge(high_function, analysis=analysis, initial_c_ret=initial_c_ret, invariant_conditions=invariant_conditions)
    def _prove_branch_guarded_while_nonprogress_must_diverge(self, high_function, *, invariant_conditions):
        return self._branch_guarded_while.prove_branch_guarded_while_nonprogress_must_diverge(high_function, invariant_conditions=invariant_conditions)
    _recover_control_flow_returns_from_block_paths = _svc_control_recovery._impl__recover_control_flow_returns_from_block_paths
    _recover_control_region_returns_early = _svc_control_recovery._impl__recover_control_region_returns_early
    _recover_explicit_return_from_block_paths = _svc_control_recovery._impl__recover_explicit_return_from_block_paths
    _recover_explicit_return_from_path_source = _svc_control_recovery._impl__recover_explicit_return_from_path_source
    _recover_switch_like_returns_from_pcode = _svc_control_recovery._impl__recover_switch_like_returns_from_pcode
    _recover_switch_like_returns_from_placeholder_analysis = _svc_control_recovery._impl__recover_switch_like_returns_from_placeholder_analysis
    def _return_path_is_covered_by_existing_return(self, analysis, path_conditions):
        return self._return_paths.return_path_is_covered_by_existing_return(analysis, path_conditions)
    def _same_high_block(self, left, right):
        return self._block_graph.same_high_block(left, right)
    _should_attempt_switch_recovery = _svc_control_recovery._impl__should_attempt_switch_recovery
    _switch_recovery_conflicts_with_unaffected_returns = _svc_control_recovery._impl__switch_recovery_conflicts_with_unaffected_returns
    _switch_recovery_improves_returns = _svc_control_recovery._impl__switch_recovery_improves_returns
    def _synthesize_branch_guarded_affine_initial_count_return(self, high_function, analysis, *, c_param, c_positive, t_positive, zero_ret):
        return self._branch_guarded_while.synthesize_branch_guarded_affine_initial_count_return(high_function, analysis, c_param=c_param, c_positive=c_positive, t_positive=t_positive, zero_ret=zero_ret)
    def _try_apply_branch_guarded_while_outcomes(self, high_function, analysis):
        return self._branch_guarded_while.try_apply_branch_guarded_while_outcomes(high_function, analysis)
    def _validate_branch_guarded_structural_proof(self, high_function, *, structural_proof, analysis, initial_c_ret, invariant_conditions):
        return self._branch_guarded_while.validate_branch_guarded_structural_proof(high_function, structural_proof=structural_proof, analysis=analysis, initial_c_ret=initial_c_ret, invariant_conditions=invariant_conditions)
    # control_recovery (continued)
    def _blocks_match(self, lhs, rhs):
        return self._block_graph.blocks_match(lhs, rhs)
    _filter_noreturn_return_path_entries = _svc_control_recovery._impl__filter_noreturn_return_path_entries
    def _find_block_index_on_path(self, block_path, target_block):
        return self._block_graph.find_block_index_on_path(block_path, target_block)
    def _get_block_start_address(self, block):
        return self._block_graph.get_block_start_address(block)
    _is_noreturn_control_transfer_op = _svc_control_recovery._impl__is_noreturn_control_transfer_op
    def _matches_blocked_return_path_conditions(self, conditions):
        return self._return_paths.matches_blocked_return_path_conditions(conditions)
    def _min_branch_index(self, left, right):
        return self._return_paths.min_branch_index(left, right)
    def _path_condition_sets_union_condition(self, path_condition_sets):
        return self._return_paths.path_condition_sets_union_condition(path_condition_sets)
    _recover_implicit_return_from_block_paths = _svc_control_recovery._impl__recover_implicit_return_from_block_paths
    def _score_multiequal_incoming_for_return_path(self, incoming_block, predecessor, condition_tracker, current_condition_keys):
        return self._return_paths.score_multiequal_incoming_for_return_path(incoming_block, predecessor, condition_tracker, current_condition_keys)
    def _select_multiequal_input_for_return_path(self, multiequal_op, predecessor, condition_tracker=None, path_conditions=None):
        return self._return_paths.select_multiequal_input_for_return_path(multiequal_op, predecessor, condition_tracker, path_conditions)
    def _select_path_specific_return_source(self, candidate, block_path, condition_tracker=None, path_conditions=None):
        return self._return_paths.select_path_specific_return_source(candidate, block_path, condition_tracker, path_conditions)
    def _split_branch_index(self, branch_index, original_index, split_index):
        return self._return_paths.split_branch_index(branch_index, original_index, split_index)
    # analyzer_services.effect_integration
    def _accept_effect_rewrite_without_rank_gain(self, original, rewritten, conditions, effect_summary):
        return self._effect_integration.accept_effect_rewrite_without_rank_gain(original, rewritten, conditions, effect_summary)
    def _accept_effect_sensitive_rewrite(self, original, rewritten, conditions, effect_summary, *, rewrite_kind):
        return self._effect_integration.accept_effect_sensitive_rewrite(original, rewritten, conditions, effect_summary, rewrite_kind=rewrite_kind)
    def _apply_local_store_effect(self, pcode_op, tracer, local_values, local_storages, local_memory):
        return self._effect_integration.apply_local_store_effect(pcode_op, tracer, local_values, local_storages, local_memory)
    def _apply_observable_effect_surface(self, result, return_type_obj, return_type):
        return self._effect_integration.apply_observable_effect_surface(result, return_type_obj, return_type)
    def _build_effect_summary(self, function, high_function, tracer, condition_tracker, parameters, active_functions, bound_parameter_values=None, bound_parameter_storage_values=None):
        return self._effect_integration.build_effect_summary(function, high_function, tracer, condition_tracker, parameters, active_functions, bound_parameter_values, bound_parameter_storage_values)
    def _build_function_control_effect_profile(self, high_function, function=None, parameters=None):
        return self._effect_integration.build_function_control_effect_profile(high_function, function, parameters)
    def _collapse_effect_sensitive_case_wrapper(self, original, rewritten, conditions, effect_summary):
        return self._effect_integration.collapse_effect_sensitive_case_wrapper(original, rewritten, conditions, effect_summary)
    def _concretize_readonly_loads(self, value, conditions, parameters):
        return self._effect_integration.concretize_readonly_loads(value, conditions, parameters)
    def _count_memory_reads(self, expr):
        return self._effect_integration.count_memory_reads(expr)
    def _count_observed_loads(self, expr):
        return self._effect_integration.count_observed_loads(expr)
    def _effect_sensitive_rewrite_precision(self, expr, conditions, effect_summary):
        return self._effect_integration.effect_sensitive_rewrite_precision(expr, conditions, effect_summary)
    def _effect_sensitive_rewrite_rank(self, expr):
        return self._effect_integration.effect_sensitive_rewrite_rank(expr)
    def _decompile_with_broker(self, function, timeout, monitor, **kwargs):
        """decompilation_broker.decompile_function を facade（analyzer）を第 1 引数として呼ぶ。"""
        from scripts.function_tracer_pcode.ghidra.decompilation_broker import decompile_function

        # Issue #124: decompile は解析のどの段からでも呼ばれるので、region として
        # 「どの段が decompile を払ったか」を残す（入れ子の再入は最外だけ計測）。
        with stage_region("decompile"):
            return decompile_function(self, function, timeout, monitor, **kwargs)

    def _effect_summary_allows_pre_return_structural_summary(self, effect_summary, *, function=None, high_function=None, return_type=None, return_type_obj=None):
        return self._effect_integration.effect_summary_allows_pre_return_structural_summary(effect_summary, function=function, high_function=high_function, return_type=return_type, return_type_obj=return_type_obj)
    def _expression_contains_stale_effect_value_for_post_state(self, expr, target_post_state, conditions, effect_summary):
        return self._effect_integration.expression_contains_stale_effect_value_for_post_state(expr, target_post_state, conditions, effect_summary)
    def _extract_stack_protector_memory_probe(self, expr):
        return self._effect_integration.extract_stack_protector_memory_probe(expr)
    def _invoke_build_effect_summary(self, function, high_function, tracer, condition_tracker, parameters, active_functions, *, bound_parameter_values=None, bound_parameter_storage_values=None):
        return self._effect_integration.invoke_build_effect_summary(function, high_function, tracer, condition_tracker, parameters, active_functions, bound_parameter_values=bound_parameter_values, bound_parameter_storage_values=bound_parameter_storage_values)
    def _iter_effect_sensitive_rewrite_candidates(self, value, conditions, effect_summary):
        return self._effect_integration.iter_effect_sensitive_rewrite_candidates(value, conditions, effect_summary)
    def _local_memory_key(self, addr_expr, size):
        return self._effect_integration.local_memory_key(addr_expr, size)
    def _make_empty_effect_summary(self, parameters):
        return self._effect_integration.make_empty_effect_summary(parameters)
    def _matched_effect_locations(self, expr, conditions, effect_summary):
        return self._effect_integration.matched_effect_locations(expr, conditions, effect_summary)
    def _normalize_return_value_with_effect_summary(self, value, conditions, effect_summary):
        return self._effect_integration.normalize_return_value_with_effect_summary(value, conditions, effect_summary)
    def _prefer_lossless_materialized_post_state_roundtrip(self, canonicalized, original, conditions, effect_summary):
        return self._effect_integration.prefer_lossless_materialized_post_state_roundtrip(canonicalized, original, conditions, effect_summary)
    def _propagate_indirect_return_effect(self, tracked, pcode_op, tracer):
        return self._effect_integration.propagate_indirect_return_effect(tracked, pcode_op, tracer)
    def _read_memory_value(self, address_value, size_bytes):
        return self._effect_integration.read_memory_value(address_value, size_bytes)
    def _rebuild_effect_sensitive_case_wrapper(self, original, rewritten, conditions, effect_summary):
        return self._effect_integration.rebuild_effect_sensitive_case_wrapper(original, rewritten, conditions, effect_summary)
    def _return_info_effective_region_conditions(self, info):
        return self._effect_integration.return_info_effective_region_conditions(info)
    def _rewrite_effect_sensitive_return_value(self, value, conditions, effect_summary):
        return self._effect_integration.rewrite_effect_sensitive_return_value(value, conditions, effect_summary)
    def _split_effect_sensitive_return_case(self, value, conditions):
        return self._effect_integration.split_effect_sensitive_return_case(value, conditions)
    def _symbolic_post_state_roundtrip_rejected(self, canonicalized, original, conditions, effect_summary):
        return self._effect_integration.symbolic_post_state_roundtrip_rejected(canonicalized, original, conditions, effect_summary)
    # analyzer_services.lifecycle
    def _decompile_function(self, function, timeout=60):
        return self._program_access.decompile_function(function, timeout)
    _decompose_comparison_condition = _svc_lifecycle._impl__decompose_comparison_condition
    def _find_block_info_for_program_offset(self, condition_tracker, address_value):
        return self._program_access.find_block_info_for_program_offset(condition_tracker, address_value)
    def _find_function_by_name(self, function_name):
        return self._program_access.find_function_by_name(function_name)
    def _get_decompiler(self):
        return self._program_access.get_decompiler()
    def _program_identity(self):
        return self._program_access.program_identity()
    def _program_is_big_endian(self):
        return self._program_access.program_is_big_endian()
    def _program_transaction(self, description):
        return self._program_access.program_transaction(description)
    def _program_userop_name(self, userop_id):
        return self._program_access.program_userop_name(userop_id)
    def _resolve_function_from_program_offset(self, address_value):
        return self._program_access.resolve_function_from_program_offset(address_value)
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
    def _normalize_bound_parameter_storage_values(self, bound_parameter_storage_values):
        return self._return_normalization.normalize_bound_parameter_storage_values(bound_parameter_storage_values)
    def _normalize_bound_parameter_values(self, bound_parameter_values):
        return self._return_normalization.normalize_bound_parameter_values(bound_parameter_values)
    def _normalize_expanded_return_value(self, value, conditions):
        return self._return_normalization.normalize_expanded_return_value(value, conditions)
    def _normalize_return_partition(self, analysis):
        return self._return_normalization.normalize_return_partition(analysis)
    def _rewrite_drops_composite_location_wrapper(self, original, rewritten, conditions):
        return self._return_normalization.rewrite_drops_composite_location_wrapper(original, rewritten, conditions)
    def _rewrite_expression_signedness(self, expr, preferred):
        return self._return_normalization.rewrite_expression_signedness(expr, preferred)
    def _rewrite_single_tracked_return_value_for_op(self, tracked, pcode_op, *, tracer, condition_tracker, path_conditions=None, current_function=None):
        return self._return_normalization.rewrite_single_tracked_return_value_for_op(tracked, pcode_op, tracer=tracer, condition_tracker=condition_tracker, path_conditions=path_conditions, current_function=current_function)
    def _rewrite_tracked_return_values_for_op(self, tracked_values, pcode_op, *, tracer, condition_tracker, path_conditions=None, current_function=None):
        return self._return_normalization.rewrite_tracked_return_values_for_op(tracked_values, pcode_op, tracer=tracer, condition_tracker=condition_tracker, path_conditions=path_conditions, current_function=current_function)
    def _should_replay_canonicalized_return(self, canonicalized, original):
        return self._return_normalization.should_replay_canonicalized_return(canonicalized, original)
    # lifecycle / analyze_function / condition_logic / ... (session helpers)
    def _address_like_keys(self, value, *, default_space=None):
        return self._pcode_sites.address_like_keys(value, default_space=default_space)
    def _address_space_name(self, address):
        return self._pcode_sites.address_space_name(address)
    _apply_structural_recurrence_summary = _svc_analyze_function._impl__apply_structural_recurrence_summary
    def _candidate_phi_origin_keys_from_summary_source_key(self, value):
        return self._phi_origins.candidate_phi_origin_keys_from_summary_source_key(value)
    def _classify_param_condition(self, condition, param_name):
        return self._condition_logic.classify_param_condition(condition, param_name)
    def _coerce_optional_int(self, value):
        return self._pcode_sites.coerce_optional_int(value)
    def _collect_guard_dependency_varnodes(self, varnode, guard_dependency_keys, *, is_root, seen):
        return self._divergence_proofs.collect_guard_dependency_varnodes(varnode, guard_dependency_keys, is_root=is_root, seen=seen)
    _collect_java_or_python_iterable = staticmethod(_svc_lifecycle._impl__collect_java_or_python_iterable)
    def _collect_parameter_descriptors_from_expression(self, expr, discovered):
        return self._parameters.collect_parameter_descriptors_from_expression(expr, discovered)
    def _collect_referenced_parameter_descriptors(self, return_infos):
        return self._parameters.collect_referenced_parameter_descriptors(return_infos)
    def _collect_scalar_signedness_profiles(self, return_infos):
        return self._parameters.collect_scalar_signedness_profiles(return_infos)
    def _condition_for_identity_key(self, key, conditions):
        return self._divergence_proofs.condition_for_identity_key(key, conditions)
    @staticmethod
    def _condition_identity_key(condition):
        return DivergenceProofService.condition_identity_key(condition)
    def _condition_looks_like_stack_protector_guard(self, condition):
        return self._stack_protector.condition_looks_like_stack_protector_guard(condition)
    def _condition_mentions_param(self, condition, param_name):
        return self._condition_logic.condition_mentions_param(condition, param_name)
    def _conditional_progress_guard_keys_from_structural_proof(self, proof):
        return self._divergence_proofs.conditional_progress_guard_keys_from_structural_proof(proof)
    def _conditional_progress_guards_contradict_invariant(self, guard_keys, *, target_conditions, invariant_conditions):
        return self._divergence_proofs.conditional_progress_guards_contradict_invariant(guard_keys, target_conditions=target_conditions, invariant_conditions=invariant_conditions)
    def _conditions_have_contradictory_pair(self, left, right):
        return self._divergence_proofs.conditions_have_contradictory_pair(left, right)
    @staticmethod
    def _constant_expression_value(expr):
        return ConditionLogicService.constant_expression_value(expr)
    def _constant_int_value(self, expr):
        return self._stack_protector.constant_int_value(expr)
    _current_function_entry_address = _svc_lifecycle._impl__current_function_entry_address
    def _debug_available(self):
        return self._debug_reporter.debug_available()
    def _debug_expr_identity_summary(self, expr, max_depth=3):
        return self._debug_reporter.debug_expr_identity_summary(expr, max_depth)
    def _debug_expr_summary(self, expr, max_depth=4):
        return self._debug_reporter.debug_expr_summary(expr, max_depth)
    def _debug_print(self, msg, indent=0):
        return self._debug_reporter.debug_print(msg, indent)
    def _describe_pcode_site(self, pcode_op, fallback_address=None, *, identity_prefix=None):
        return self._pcode_sites.describe_pcode_site(pcode_op, fallback_address, identity_prefix=identity_prefix)
    def _edge_condition_for_successor(self, block, successor, tracer):
        return self._divergence_proofs.edge_condition_for_successor(block, successor, tracer)
    def _expression_contains_equivalent_subexpr(self, expr, target):
        return self._expression_cases.expression_contains_equivalent_subexpr(expr, target)
    @staticmethod
    def _expression_has_param(expr, param_name):
        return ConditionLogicService.expression_has_param(expr, param_name)
    def _expression_is_placeholder_minus_one(self, expr, placeholder):
        return self._placeholder_algebra.expression_is_placeholder_minus_one(expr, placeholder)
    def _expression_is_placeholder_minus_one_under_conditions(self, expr, placeholder, conditions):
        return self._placeholder_algebra.expression_is_placeholder_minus_one_under_conditions(expr, placeholder, conditions)
    def _expression_is_placeholder_minus_one_unit_condition(self, expr, placeholder, conditions):
        return self._placeholder_algebra.expression_is_placeholder_minus_one_unit_condition(expr, placeholder, conditions)
    def _expression_is_placeholder_plus_constant(self, expr, placeholder, constant):
        return self._placeholder_algebra.expression_is_placeholder_plus_constant(expr, placeholder, constant)
    def _expression_is_placeholder_plus_one(self, expr, placeholder):
        return self._placeholder_algebra.expression_is_placeholder_plus_one(expr, placeholder)
    def _expression_is_placeholder_plus_one_under_conditions(self, expr, placeholder, conditions):
        return self._placeholder_algebra.expression_is_placeholder_plus_one_under_conditions(expr, placeholder, conditions)
    def _expression_is_placeholder_plus_unit_condition(self, expr, placeholder, conditions):
        return self._placeholder_algebra.expression_is_placeholder_plus_unit_condition(expr, placeholder, conditions)
    def _expression_is_placeholder_plus_zero_under_conditions(self, expr, placeholder, conditions):
        return self._placeholder_algebra.expression_is_placeholder_plus_zero_under_conditions(expr, placeholder, conditions)
    def _expression_is_zero_constant(self, expr):
        return self._condition_logic.expression_is_zero_constant(expr)
    def _expression_is_zero_under_conditions(self, expr, conditions):
        return self._placeholder_algebra.expression_is_zero_under_conditions(expr, conditions)
    def _extract_difference_pair(self, expr):
        return self._stack_protector.extract_difference_pair(expr)
    def _extract_indirect_probe(self, expr):
        return self._stack_protector.extract_indirect_probe(expr)
    def _extract_stack_protector_compare_pair(self, condition):
        return self._stack_protector.extract_stack_protector_compare_pair(condition)
    @staticmethod
    def _field_value_from_structural_proof(proof, field_name):
        return DivergenceProofService.field_value_from_structural_proof(proof, field_name)
    def _find_matching_parameter_descriptor_index(self, parameters, candidate):
        return self._parameters.find_matching_parameter_descriptor_index(parameters, candidate)
    _function_entry_address = staticmethod(_svc_lifecycle._impl__function_entry_address)
    def _high_function_cyclic_sccs(self, blocks):
        return self._divergence_proofs.high_function_cyclic_sccs(blocks)
    def _is_zero_constant(self, expr):
        return self._stack_protector.is_zero_constant(expr)
    def _merge_parameter_descriptors(self, existing, candidate):
        return self._parameters.merge_parameter_descriptors(existing, candidate)
    def _negated_unit_condition_key_for_expression(self, expr, conditions):
        return self._placeholder_algebra.negated_unit_condition_key_for_expression(expr, conditions)
    def _parameter_descriptor_from_expression(self, expr):
        return self._parameters.parameter_descriptor_from_expression(expr)
    def _parameter_descriptor_key(self, descriptor):
        return self._parameters.parameter_descriptor_key(descriptor)
    def _pcode_op_identity_key(self, pcode_op):
        return self._pcode_sites.pcode_op_identity_key(pcode_op)
    def _pcode_op_input_def_reaches_phi(self, op, target_phi_key, *, max_depth):
        return self._pcode_sites.pcode_op_input_def_reaches_phi(op, target_phi_key, max_depth=max_depth)
    def _pcode_op_stable_key(self, op):
        return self._pcode_sites.pcode_op_stable_key(op)
    def _pcode_ops_match(self, lhs, rhs):
        return self._pcode_sites.pcode_ops_match(lhs, rhs)
    _phase1_body_contains_address = staticmethod(_svc_analyze_function._impl__phase1_body_contains_address)
    def _phi_circular_origin_stable_keys(self, expr):
        return self._phi_origins.phi_circular_origin_stable_keys(expr)
    def _placeholder_minus_one_unit_condition_guard_key(self, expr, placeholder, conditions):
        return self._placeholder_algebra.placeholder_minus_one_unit_condition_guard_key(expr, placeholder, conditions)
    def _placeholder_plus_unit_condition_guard_key(self, expr, placeholder, conditions):
        return self._placeholder_algebra.placeholder_plus_unit_condition_guard_key(expr, placeholder, conditions)
    def _prove_scc_must_diverge_under_guard(self, scc, *, all_blocks, divergence_guard, param, tracer):
        return self._divergence_proofs.prove_scc_must_diverge_under_guard(scc, all_blocks=all_blocks, divergence_guard=divergence_guard, param=param, tracer=tracer)
    def _prove_single_guard_nonprogress_region_must_diverge(self, high_function, analysis, *, divergence_guard, param):
        return self._divergence_proofs.prove_single_guard_nonprogress_region_must_diverge(high_function, analysis, divergence_guard=divergence_guard, param=param)
    def _reads_share_stack_protector_probe(self, left, right):
        return self._stack_protector.reads_share_stack_protector_probe(left, right)
    def _record_scalar_signedness_from_expression(self, expr, profiles):
        return self._parameters.record_scalar_signedness_from_expression(expr, profiles)
    def _recursive_scc_certificate(self, function_key):
        return self._divergence_proofs.recursive_scc_certificate(function_key)
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
    def _repair_mixed_scalar_signedness(self, analysis):
        return self._parameters.repair_mixed_scalar_signedness(analysis)
    def _scc_preserves_guard_dependencies(self, scc_set):
        return self._divergence_proofs.scc_preserves_guard_dependencies(scc_set)
    def _single_guard_condition_matches(self, condition, divergence_guard, param):
        return self._divergence_proofs.single_guard_condition_matches(condition, divergence_guard, param)
    def _single_guard_conditions_are_contradictory(self, divergence_guard, edge_condition, param):
        return self._divergence_proofs.single_guard_conditions_are_contradictory(divergence_guard, edge_condition, param)
    def _strip_stack_protector_only_conditions(self, return_infos):
        return self._stack_protector.strip_stack_protector_only_conditions(return_infos)
    @staticmethod
    def _strip_transparent_unary(expr):
        return PlaceholderAlgebraService.strip_transparent_unary(expr)
    def _synchronize_parameters_with_referenced_parameter_expressions(self, analysis):
        return self._parameters.synchronize_parameters_with_referenced_parameter_expressions(analysis)
    @staticmethod
    def _tuple_field_from_structural_proof(proof, field_name):
        return DivergenceProofService.tuple_field_from_structural_proof(proof, field_name)
    def _unit_condition_key_for_expression(self, expr, conditions):
        return self._placeholder_algebra.unit_condition_key_for_expression(expr, conditions)
    def _varnode_guard_dependency_key(self, varnode):
        return self._divergence_proofs.varnode_guard_dependency_key(varnode)
    def _varnodes_same_storage(self, left, right):
        return self._pcode_sites.varnodes_same_storage(left, right)
    analyze_function = _svc_analyze_function._impl_analyze_function
    # Issue #47 (PR-B): external placeholder callee の束縛ゼロ解析の再利用。
    _callee_unbound_reuse_verdict = _svc_callee_unbound_reuse._impl__callee_unbound_reuse_verdict
    _reuse_unbound_placeholder_analysis = _svc_callee_unbound_reuse._impl__reuse_unbound_placeholder_analysis
    _suspended_callee_unbound_reuse = _svc_callee_unbound_reuse._impl__suspended_callee_unbound_reuse
    def dispose(self):
        return self._program_access.dispose()
    # session helpers (continued)
    _analysis_is_fully_argument_specialized = _svc_analyze_function._impl__analysis_is_fully_argument_specialized
    _analysis_needs_wrapper_recovery = _svc_analyze_function._impl__analysis_needs_wrapper_recovery
    _analysis_scope_key = _svc_lifecycle._impl__analysis_scope_key
    def _attempt_disassemble_at(self, addr):
        return self._program_access.attempt_disassemble_at(addr)
    def _augment_parameters_with_implicit_passthrough(self, parameters, tracer, active_functions):
        return self._parameters.augment_parameters_with_implicit_passthrough(parameters, tracer, active_functions)
    def _build_condition_signature_set(self, conditions):
        return self._condition_logic.build_condition_signature_set(conditions)
    def _choose_richer_parameter_descriptors(self, cached_parameters, fresh_parameters):
        return self._parameters.choose_richer_parameter_descriptors(cached_parameters, fresh_parameters)
    def _clone_expression(self, expr):
        return self._expression_cases.clone_expression(expr)
    def _coerce_expression_size(self, expr, size):
        return self._condition_logic.coerce_expression_size(expr, size)
    def _coerce_order_key(self, value):
        return self._condition_logic.coerce_order_key(value)
    def _coerce_wrapper_storage_info(self, storage):
        return self._parameters.coerce_wrapper_storage_info(storage)
    def _collect_expression_object_keys(self, expr, out):
        return self._expression_cases.collect_expression_object_keys(expr, out)
    def _collect_parameters(self, high_function):
        return self._parameters.collect_parameters(high_function)
    def _condition_contradicts_any(self, condition, others):
        return self._condition_logic.condition_contradicts_any(condition, others)
    def _condition_is_constant_equality_guard(self, condition):
        return self._condition_logic.condition_is_constant_equality_guard(condition)
    def _condition_is_param_equal_const(self, condition, param, value):
        return self._condition_logic.condition_is_param_equal_const(condition, param, value)
    def _condition_is_param_minus_one_nonpositive(self, condition, param, target_conditions=()):
        return self._placeholder_algebra.condition_is_param_minus_one_nonpositive(condition, param, target_conditions)
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
    def _deduplicate_storage_infos(self, storages):
        return self._parameters.deduplicate_storage_infos(storages)
    def _detect_signedness(self, high_function):
        return self._parameters.detect_signedness(high_function)
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
    def _expression_contains_phi(self, expr):
        return self._phi_origins.expression_contains_phi(expr)
    def _expression_contains_phi_circular(self, expr):
        return self._phi_origins.expression_contains_phi_circular(expr)
    def _expression_contains_phi_circular_marker(self, expr):
        return self._phi_origins.expression_contains_phi_circular_marker(expr)
    def _expression_has_nontrivial_location_wrapper(self, expr, location):
        return self._expression_cases.expression_has_nontrivial_location_wrapper(expr, location)
    def _expression_is_one_under_conditions(self, expr, target_conditions):
        return self._placeholder_algebra.expression_is_one_under_conditions(expr, target_conditions)
    def _expression_is_param_minus_one(self, expr, param):
        return self._placeholder_algebra.expression_is_param_minus_one(expr, param)
    def _expression_is_positive_after_unit_progress_guard(self, expr, state_placeholder, conditions):
        return self._divergence_proofs.expression_is_positive_after_unit_progress_guard(expr, state_placeholder, conditions)
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
    def _get_function_manager(self):
        return self._program_access.get_function_manager()
    def _get_instruction_with_fallback(self, addr):
        return self._program_access.get_instruction_with_fallback(addr)
    def _get_pcode_opcode(self, pcode_op):
        return self._pcode_sites.get_pcode_opcode(pcode_op)
    def _get_storage_info(self, sym):
        return self._parameters.get_storage_info(sym)
    def _has_non_parameter_symbol_for_storage(self, tracer, target_storage):
        return self._parameters.has_non_parameter_symbol_for_storage(tracer, target_storage)
    def _high_function_has_cfg_cycle(self, high_function):
        return self._divergence_proofs.high_function_has_cfg_cycle(high_function)
    def _is_boolean_expression(self, expr):
        return self._expression_cases.is_boolean_expression(expr)
    def _is_direct_location_carrier(self, expr):
        return self._expression_cases.is_direct_location_carrier(expr)
    def _is_signed_type(self, data_type):
        return self._parameters.is_signed_type(data_type)
    def _is_void_type(self, data_type):
        return self._parameters.is_void_type(data_type)
    def _is_zero_constant_varnode(self, varnode):
        return self._pcode_sites.is_zero_constant_varnode(varnode)
    def _iter_expression_nodes_for_unconditional_runtime_guards(self, expr):
        return self._expression_cases.iter_expression_nodes_for_unconditional_runtime_guards(expr)
    def _local_varnode_key(self, varnode):
        return self._local_values.varnode_key(varnode)

    def _lookup_local_alias_expression(self, varnode, tracer, local_values, local_storages):
        return self._local_values.lookup_alias(varnode, tracer, local_values, local_storages)

    def _lookup_local_expression_for_storage(self, target_storage, local_values, local_storages):
        return self._local_values.lookup_for_storage(target_storage, local_values, local_storages)
    def _make_tracer(self, high_function, *, bound_parameter_values=None, bound_parameter_storage_values=None):
        return self._program_access.make_tracer(high_function, bound_parameter_values=bound_parameter_values, bound_parameter_storage_values=bound_parameter_storage_values)
    def _parameter_constant_assignments_from_conditions(self, conditions):
        return self._condition_logic.parameter_constant_assignments_from_conditions(conditions)
    def _parameter_descriptor_quality(self, parameters):
        return self._parameters.parameter_descriptor_quality(parameters)
    def _parameter_equals_condition(self, parameter, value):
        return self._phi_origins.parameter_equals_condition(parameter, value)
    def _parameter_expression(self, analysis, index):
        return self._parameters.parameter_expression(analysis, index)
    def _parameter_storages_match_for_passthrough(self, caller_storage, callee_storage):
        return self._parameters.parameter_storages_match_for_passthrough(caller_storage, callee_storage)
    def _parameter_storages_overlap_for_passthrough(self, caller_storage, callee_storage):
        return self._parameters.parameter_storages_overlap_for_passthrough(caller_storage, callee_storage)
    def _pcode_op_affects_tracked_storage(self, pcode_op, target_storage, tracer, current_function=None):
        return self._pcode_sites.pcode_op_affects_tracked_storage(pcode_op, target_storage, tracer, current_function)
    def _pcode_op_debug_name(self, pcode_op):
        return self._pcode_sites.pcode_op_debug_name(pcode_op)
    def _phi_circular_additive_signature(self, expr):
        return self._phi_origins.phi_circular_additive_signature(expr)
    def _phi_expression_key_set(self, expr):
        return self._phi_origins.phi_expression_key_set(expr)
    def _phi_free_finite_fallback_candidates(self, fallback_value, conditions):
        return self._phi_origins.phi_free_finite_fallback_candidates(fallback_value, conditions)
    def _phi_origin_keys_from_varnode_defs(self, varnode, *, max_depth=8):
        return self._phi_origins.phi_origin_keys_from_varnode_defs(varnode, max_depth=max_depth)
    def _propagate_passthrough_input_from_op(self, pcode_op, tracer):
        return self._parameters.propagate_passthrough_input_from_op(pcode_op, tracer)
    def _pruning_conditions_signature(self, conditions):
        return self._condition_logic.pruning_conditions_signature(conditions)
    def _reachable_cycle_keys(self, reachable, adjacency):
        return self._divergence_proofs.reachable_cycle_keys(reachable, adjacency)
    def _readonly_reduction_contract_priority_score(self, info):
        return self._phi_origins.readonly_reduction_contract_priority_score(info)
    def _readonly_reduction_ref_contract_priority_score(self, runtime_ref):
        return self._phi_origins.readonly_reduction_ref_contract_priority_score(runtime_ref)
    def _resolve_function_from_address(self, address):
        return self._program_access.resolve_function_from_address(address)
    def _resolve_precise_object_state_value(self, value, conditions, effect_summary):
        return self._expression_cases.resolve_precise_object_state_value(value, conditions, effect_summary)
    def _runtime_ref_guard_conditions(self, runtime_ref):
        return self._expression_cases.runtime_ref_guard_conditions(runtime_ref)
    def _signed_positive_condition(self, expr):
        return self._condition_logic.signed_positive_condition(expr)
    def _signed_unit_constant_matches(self, value, expected, size):
        return self._placeholder_algebra.signed_unit_constant_matches(value, expected, size)
    def _single_parameter_expression_in_conditions(self, conditions):
        return self._phi_origins.single_parameter_expression_in_conditions(conditions)
    def _split_small_finite_parameter_reachability_conditions(self, conditions, *, search_min=-8, search_max=64, max_cases=16):
        return self._phi_origins.split_small_finite_parameter_reachability_conditions(conditions, search_min=search_min, search_max=search_max, max_cases=max_cases)
    def _state_phi_feeds_positive_loop_guard(self, high_function, *, summarizer, header_block, backedge_indices, state_phi, state_placeholder, target_conditions, allow_latch_progress_guard):
        return self._divergence_proofs.state_phi_feeds_positive_loop_guard(high_function, summarizer=summarizer, header_block=header_block, backedge_indices=backedge_indices, state_phi=state_phi, state_placeholder=state_placeholder, target_conditions=target_conditions, allow_latch_progress_guard=allow_latch_progress_guard)
    def _substitute_parameter_constants_under_conditions(self, expr, conditions):
        return self._condition_logic.substitute_parameter_constants_under_conditions(expr, conditions)
    def _synthesize_implicit_passthrough_parameter(self, current_parameters, callee_param, callee_storage):
        return self._parameters.synthesize_implicit_passthrough_parameter(current_parameters, callee_param, callee_storage)
    @staticmethod
    def _varnode_location_key(varnode):
        return PcodeSiteService.varnode_location_key(varnode)
    def _varnodes_may_alias(self, lhs, rhs):
        return self._pcode_sites.varnodes_may_alias(lhs, rhs)
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
