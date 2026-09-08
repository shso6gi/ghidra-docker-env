"""Top-level analyze_function orchestration and structural-recurrence refresh."""

from __future__ import annotations

from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple, cast
from scripts.function_tracer_pcode.core.analysis import ComparisonSurface, FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.core.call_target import CallTargetRef
from scripts.function_tracer_pcode.core.expression import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.core.structural import StructuralKey, expression_key_safe
from scripts.function_tracer_pcode.analysis.returns._shared import (
    ANALYSIS_STATUS_DECOMPILATION_FAILED,
    ANALYSIS_STATUS_HIGH_FUNCTION_MISSING,
    AnalysisFailure,
    ConditionNormalizer,
    ConditionSMTOracle,
    ConditionSimplifier,
    EffectSummary,
    PcodeTracer,
    _expressions_equivalent,
    _iter_expression_nodes,
    attach_quarantined_recurrence_proposal,
)
from scripts.function_tracer_pcode.analysis.returns._api import (
    ConditionTracker,
    StructuralRecurrenceSummarizer,
)
from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple
from scripts.function_tracer_pcode.analysis.returns._shared import (
    StructuralRecurrenceSummarizer,
    eval_constant_raw,
)
from scripts.function_tracer_pcode.analysis.returns._api import PcodeTracer
from typing import Any, Optional, Set, Tuple
from scripts.function_tracer_pcode.analysis.returns._shared import (
    AnalysisFailure,
)
from scripts.function_tracer_pcode.analysis.returns.parameters import (
    _sealed_return_abi_facts,
)
from scripts.function_tracer_pcode.analysis.returns.expansion_budget import (
    emit_analysis_expansion_budget_diagnostics,
)


def _effect_summary_incomplete_reasons(effect_summary) -> tuple:
    reasons = getattr(effect_summary, "incomplete_reasons", ())
    if not isinstance(reasons, (list, tuple, set, frozenset)):
        return ()
    return tuple(reasons)


def _impl_analyze_function(
    self,
    function,
    timeout: int = 60,
    active_functions: Optional[Set[Tuple[Any, ...]]] = None,
    bound_parameter_values: Optional[Dict[int, Expression]] = None,
    bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]] = None,
) -> Optional[FunctionReturnAnalysis]:
     # デバッグフラグを ConditionSimplifier に伝播
    from scripts.function_tracer_pcode.analysis.condition import ConditionSimplifier
    ConditionSimplifier.DEBUG = self.debug
    ConditionSimplifier.reset_debug_state()

    current_function_ref = CallTargetRef.from_function(function)
    normalized_bound_parameter_values = self._normalize_bound_parameter_values(
        bound_parameter_values,
    )
    normalized_bound_parameter_storage_values = self._normalize_bound_parameter_storage_values(
        bound_parameter_storage_values,
    )
    analysis_scope_key = self._analysis_scope_key(
        current_function_ref,
        normalized_bound_parameter_values,
        normalized_bound_parameter_storage_values,
    )
    cached_analysis = self._call_analysis_cache.get(analysis_scope_key)
    if cached_analysis is not None:
        return cached_analysis
    active_functions = self._extend_active_functions(
        active_functions,
        current_function_ref,
    )
    # return_path_entry_cache は _analysis_context が生成する子 AnalysisSession が新規に所有する（6a-1）
    current_active_key = analysis_scope_key

    self._debug_print("=" * 60)
    self._debug_print(f"Analyzing function: {function.getName()}")
    self._debug_print("=" * 60)

    from scripts.function_tracer_pcode.ghidra.decompilation_broker import (
        TOP_LEVEL_SOURCE_CONTRACT,
        decompile_function,
    )
    results = decompile_function(
        self, function, timeout, None,
        source_contract_id=TOP_LEVEL_SOURCE_CONTRACT,
        semantic_owner="slice6",
    )

    if not results.decompileCompleted():
        message = "Decompilation failed!"
        self._last_analysis_failure = AnalysisFailure(
            status=ANALYSIS_STATUS_DECOMPILATION_FAILED,
            message=message,
            function_name=str(function.getName()),
        )
        self._debug_print(message)
        return None

    high_function = results.getHighFunction()
    if high_function is None:
        message = "HighFunction is None!"
        self._last_analysis_failure = AnalysisFailure(
            status=ANALYSIS_STATUS_HIGH_FUNCTION_MISSING,
            message=message,
            function_name=str(function.getName()),
        )
        self._debug_print(message)
        return None

    # Step 1: tracer / CFG infrastructure を先に構築する。
    # implicit passthrough parameter recovery でも CALLIND target を追跡するため、
    # PhiHandler が有効な状態で tracer を使えるようにしておく。
    tracer = self._make_tracer(
        high_function,
        bound_parameter_values=normalized_bound_parameter_values,
        bound_parameter_storage_values=normalized_bound_parameter_storage_values,
    )
    tracer.record_deferred_call = self._make_deferred_call_recorder(function)
    condition_tracker = ConditionTracker(tracer)
    tracer.condition_tracker = condition_tracker
    from scripts.function_tracer_pcode.analysis.phi_resolver import PhiHandler

    phi_handler = PhiHandler(tracer, condition_tracker)
    tracer.phi_handler = phi_handler
    condition_tracker.build()

    parameters = self._collect_parameters(high_function)
    parameters = self._augment_parameters_with_implicit_passthrough(
        parameters,
        tracer,
        active_functions,
    )
    function_prototype = None
    try:
        function_prototype = high_function.getFunctionPrototype()
    except Exception:
        function_prototype = None

    with self._analysis_context(
        parameters,
        None,
        function_prototype=function_prototype,
        function_entry_address=self._function_entry_address(function),
        analysis_scope_key=analysis_scope_key,
    ):
        self._debug_print(f"Parameters: {[p['name'] for p in parameters]}")
        image_base = None
        try:
            image_base = self.program.getImageBase().getOffset()
        except Exception:
            image_base = None
        condition_tracker.refine_branch_conditions(
            call_resolver=self._make_call_resolver(active_functions, function),
            parameters=parameters,
            resolve_callee_parameters=self._get_freshest_callee_parameters,
            read_memory_value=self._read_memory_value,
            image_base=image_base,
            budget_sink=self._make_expansion_budget_sink(
                surface="branch_condition",
                owner_scope_key=analysis_scope_key,
            ),
        )

        # 戻り値の型を取得
        return_type_obj, return_type = self._get_return_type_info(high_function)
        return_abi_facts = _sealed_return_abi_facts(
            function_prototype, return_type_obj, return_type
        )
        self._debug_print(f"Return type: {return_type}")

        # === Phase 1: 符号性検出 ===
        signedness_result = self._detect_signedness(high_function)
        if signedness_result:
            self._debug_print(f"Inferred signedness: {signedness_result.signedness}")
            if self.debug:
                self._debug_print(f"Evidence summary: {signedness_result.evidence_summary}")
                self._debug_print(f"Opcode counts: {signedness_result.opcode_counts}")

        return_ops = tracer.find_return_ops()
        self._debug_print(f"Found {len(return_ops)} RETURN operations")

        empty_effect_summary = self._make_empty_effect_summary(parameters)
        recovered_control_returns, control_region_notes = self._recover_control_region_returns_early(
            function,
            tracer,
            condition_tracker,
            return_ops,
            active_functions=active_functions,
        )

        effect_summary = empty_effect_summary
        if recovered_control_returns is not None:
            self._current_effect_summary = empty_effect_summary
            return_infos = list(recovered_control_returns)
        else:
            effect_summary = self._invoke_build_effect_summary(
                function,
                high_function,
                tracer,
                condition_tracker,
                parameters,
                active_functions=active_functions,
                bound_parameter_values=normalized_bound_parameter_values,
                bound_parameter_storage_values=normalized_bound_parameter_storage_values,
            )
            self._current_effect_summary = effect_summary
            # Issue #131: 自分自身の効果要約で観測した切り捨て（STORE 値展開と、その
            # 中で採用した callee 要約への参照）を現在の解析 scope へ取り込む。
            self._absorb_effect_summary_budget_diagnostics(analysis_scope_key)

            pre_return_structural_result = self._try_pre_return_counted_loop_summary(
                function=function,
                high_function=high_function,
                tracer=tracer,
                parameters=parameters,
                return_ops=return_ops,
                current_function_ref=current_function_ref,
                analysis_scope_key=analysis_scope_key,
                return_type=return_type,
                return_type_obj=return_type_obj,
                signedness_result=signedness_result,
                effect_summary=effect_summary,
            )
            if pre_return_structural_result is not None:
                # 早期終了経路でも、cache へ入れる前に最新の marker を反映する。
                self._sync_expansion_budget_truncations(pre_return_structural_result)
                emit_analysis_expansion_budget_diagnostics(pre_return_structural_result)
                self._call_analysis_cache[analysis_scope_key] = pre_return_structural_result
                function_cache_key = self._function_cache_key(function)
                if function_cache_key is not None and not normalized_bound_parameter_values:
                    self._call_analysis_cache[function_cache_key] = pre_return_structural_result
                return pre_return_structural_result

            return_infos = []
            for i, return_op in enumerate(return_ops):
                self._debug_print(f"--- Analyzing RETURN #{i + 1} ---")
                infos = self._analyze_return_op(
                    return_op,
                    tracer,
                    condition_tracker,
                    i,
                    current_function=function,
                    active_functions=active_functions,
                    return_type_obj=return_type_obj,
                )
                return_infos.extend(infos)

        result = FunctionReturnAnalysis(
            function_name=function.getName(),
            entry_point=str(function.getEntryPoint()),
            parameters=parameters,
            returns=return_infos,
            function_ref=current_function_ref,
            analysis_scope_key=analysis_scope_key,
            return_type=return_type,
            return_type_obj=return_type_obj,
            return_abi_facts=return_abi_facts,
            signedness_result=signedness_result,
            deferred_calls=dict(self._current_deferred_calls),
            effect_summary=effect_summary,
            program_is_big_endian=self._program_is_big_endian(),
            binary_id=self._binary_id,
        )
        # Issue #131: 構築時の値は途中の写し。以降の復元・要約・refinement で増えた
        # marker も、証明利用と cache 保存の前に同期する。
        self._sync_expansion_budget_truncations(result)
        result.unknown_event_count = len(tracer.unknown_tracker.events)
        result.unknown_event_reasons = sorted(
            {
                getattr(event, "reason_str", None) or getattr(event.reason, "value", "unknown")
                for event in tracer.unknown_tracker.events
            }
        )

        for note in control_region_notes:
            if note not in result.analysis_notes:
                result.analysis_notes.append(note)
        effect_incomplete_reasons = getattr(effect_summary, "incomplete_reasons", ())
        if not isinstance(effect_incomplete_reasons, (list, tuple, set, frozenset)):
            effect_incomplete_reasons = ()
        for note in effect_incomplete_reasons:
            if note not in result.analysis_notes:
                result.analysis_notes.append(note)
        if getattr(effect_summary, "call_target_resolution_evidence", None):
            note = "effect_call_target_resolution_evidence"
            if note not in result.analysis_notes:
                result.analysis_notes.append(note)

        if recovered_control_returns is None:
            if (
                return_type_obj is not None
                and self._is_void_type(return_type_obj)
                and effect_summary.synthetic_expr is not None
                and not effect_summary.has_unsupported_call
                and not _effect_summary_incomplete_reasons(effect_summary)
            ):
                result.returns = [
                    self._make_return_info(
                        address=str(function.getEntryPoint()),
                        conditions=[],
                        branch_index=0,
                        value=effect_summary.synthetic_expr,
                    )
                ]
                result.comparison_surface = ComparisonSurface(
                    kind="memory_effect",
                    explicit_bit_width=max(1, effect_summary.synthetic_expr.get_bit_width()),
                    use_sign_extension=False,
                    evidence={
                        "source": "effect_summary.synthetic_expr",
                        "effect_count": len(getattr(effect_summary, "effects", []) or []),
                    },
                )

            if not (return_type_obj is not None and self._is_void_type(return_type_obj)):
                recovered_returns = self._recover_call_wrapper_returns(
                    results,
                    result,
                    function,
                    tracer,
                    condition_tracker,
                    return_ops,
                    active_functions,
                )
                if recovered_returns is not None:
                    result.returns = recovered_returns
                    result.analysis_notes.append("call_wrapper_return_recovery")

            recovered_switch_returns = self._recover_switch_like_returns_from_pcode(
                result,
                tracer,
                condition_tracker,
                return_ops=return_ops,
                current_function=function,
                active_functions=active_functions,
            )
            if recovered_switch_returns is not None:
                result.returns = recovered_switch_returns
                if "switch_return_recovery" not in result.analysis_notes:
                    result.analysis_notes.append("switch_return_recovery")

        # call wrapper / switch 復元は結果構築の後に走るので、要約適用（= 最初の
        # 証明処理）より前にここで同期する。
        self._sync_expansion_budget_truncations(result)
        result.deferred_calls = dict(self._current_deferred_calls)
        self._apply_effect_call_argument_evidence_to_deferred_calls(result)

        # Close direct structural recurrences before bounded refinement peels
        # them into several overlapping finite-unroll members.  Rejected
        # proposals remain diagnostics-only and continue through the legacy
        # refinement path unchanged.
        pre_refinement_summary = self._apply_structural_recurrence_summary(
            function,
            high_function,
            result,
            tracer,
        )
        if pre_refinement_summary is not None:
            result = pre_refinement_summary
        self._sync_expansion_budget_truncations(result)

        if current_active_key is not None:
            self._analysis_in_progress[current_active_key] = result
        try:
            if (
                result.deferred_calls
                and not result.quarantined_recurrence_proposals
            ):
                self._apply_bounded_call_refinement(
                    result,
                    active_functions,
                    CallTargetRef.from_function(function),
                )
        finally:
            if current_active_key is not None:
                self._analysis_in_progress.pop(current_active_key, None)
        self._sync_expansion_budget_truncations(result)
        self._clear_resolved_call_effect_blockers(result)

        self._synchronize_parameters_with_referenced_parameter_expressions(result)
        self._repair_mixed_scalar_signedness(result)
        recurrence_proposal_open = bool(
            result.quarantined_recurrence_proposals
        )
        if not recurrence_proposal_open:
            self._normalize_return_partition(result)
        self._mark_incomplete_control_flow(result)

        if not recurrence_proposal_open:
            self._sync_expansion_budget_truncations(result)
            summary_view = self._apply_structural_recurrence_summary(
                function,
                high_function,
                result,
                tracer,
            )
            if summary_view is not None:
                result = summary_view
                self._normalize_return_partition(result)
                self._mark_incomplete_control_flow(result)
            self._sync_expansion_budget_truncations(result)
            if result.deferred_calls:
                if current_active_key is not None:
                    self._analysis_in_progress[current_active_key] = result
                try:
                    self._apply_bounded_call_refinement(
                        result,
                        active_functions,
                        CallTargetRef.from_function(function),
                    )
                finally:
                    if current_active_key is not None:
                        self._analysis_in_progress.pop(current_active_key, None)
                self._sync_expansion_budget_truncations(result)
                self._clear_resolved_call_effect_blockers(result)
                self._normalize_return_partition(result)
                self._mark_incomplete_control_flow(result)
        if (
            result.has_symbolic_post_state_reads()
            and "symbolic_post_state_reads" not in result.analysis_notes
        ):
            result.analysis_notes.append("symbolic_post_state_reads")

        # Non-void functions with caller-observable stores are compared on
        # stores ⊕ return value (Issue #13); done before the outcome
        # partition summaries so they describe the compared surface.
        self._apply_observable_effect_surface(result, return_type_obj, return_type)

        self._apply_outcome_partition_summaries(
            function,
            high_function,
            result,
        )
        self._sync_expansion_budget_truncations(result)
        self._normalize_return_partition(result)
        self._mark_incomplete_control_flow(result)

        # デバッグダンプ（解析結果の可視化）
        self._dump_return_infos(result)

        # Unknown発生サマリー
        if self.debug:
            print("\n" + "=" * 70)
            print("UNKNOWN EVENTS SUMMARY")
            print("=" * 70)
            print(tracer.unknown_tracker.get_summary())
            phi_events = tracer.unknown_tracker.filter_phi_related()
            if phi_events:
                print("\n--- PHI-related events ---")
                for event in phi_events:
                    print(event.format_detail(indent=0))
        elif len(tracer.unknown_tracker.events) > 0:
            print(f"\n[Info] {len(tracer.unknown_tracker.events)} unknown events occurred")
            print("  Use --debug flag for detailed report")

        # 通常終了。cache へ保存する前に最終同期する（cache 保存はこの関数の中で
        # return の直前に行われるため、外側からでは間に合わない）。
        self._sync_expansion_budget_truncations(result)
        emit_analysis_expansion_budget_diagnostics(result)
        self._call_analysis_cache[analysis_scope_key] = result
        function_cache_key = self._function_cache_key(function)
        if function_cache_key is not None and not normalized_bound_parameter_values:
            self._call_analysis_cache[function_cache_key] = result
        return result


def _impl__apply_structural_recurrence_summary(
    self,
    function,
    high_function,
    analysis: FunctionReturnAnalysis,
    tracer: PcodeTracer,
) -> Optional[FunctionReturnAnalysis]:
    if analysis is None or not analysis.returns:
        return None

    summarizer = StructuralRecurrenceSummarizer(
        tracer,
        debug=self.debug,
        enable_completed_recovery_proofs=self.enable_completed_recovery_proofs,
    )
    should_try = analysis.has_unresolved_return_value() or any(
        reason in {"call_out_of_scope", "max_depth_exceeded", "phi_no_valid_branch", "phi_circular"}
        for reason in getattr(analysis, "unknown_event_reasons", [])
    )
    if not should_try:
        should_try = summarizer.has_summary_candidate(function, high_function, analysis)
    if not should_try:
        return None

    summary = summarizer.try_summarize_function(function, high_function, analysis)
    if summary is None:
        if self.debug:
            print("Summary return diagnostic: no_summary_candidate")
        return None
    summary_returns, summary_note = summary
    try:
        proposal = attach_quarantined_recurrence_proposal(
            analysis,
            proposed_returns=summary_returns,
            summary_note=summary_note,
        )
    except (TypeError, ValueError) as exc:
        if self.debug:
            print(
                "Recurrence proposal quarantine declined: "
                f"{type(exc).__name__}: {exc}"
            )
        return analysis.with_summary_return_diagnostics(
            blockers=(
                "recurrence_proposal_encoding_failed:"
                f"{type(exc).__name__}:{exc}",
            ),
            reason=summary_note,
        )
    return analysis if proposal is not None else None


def _impl__phase1_body_contains_address(body, target) -> bool:
    if body is None or target is None:
        return False
    contains = getattr(body, "contains", None)
    if callable(contains):
        try:
            return bool(contains(target))
        except Exception:
            pass
    try:
        min_addr = body.getMinAddress()
        max_addr = body.getMaxAddress()
        get_offset = getattr(target, "getOffset", None)
        min_offset = getattr(min_addr, "getOffset", None)
        max_offset = getattr(max_addr, "getOffset", None)
        if callable(get_offset) and callable(min_offset) and callable(max_offset):
            offset = int(get_offset())
            return int(min_offset()) <= offset <= int(max_offset())
    except Exception:
        return False
    return False


def _impl__analysis_needs_wrapper_recovery(
    self,
    analysis: Optional[FunctionReturnAnalysis],
) -> bool:
    if analysis is None or not analysis.returns:
        return False
    return analysis.has_unknown_return() or analysis.has_unresolved_return_value()


def _impl__analysis_is_fully_argument_specialized(
    self,
    analysis: Optional[FunctionReturnAnalysis],
) -> bool:
    if analysis is None:
        return False
    parameter_count = len(getattr(analysis, "parameters", ()) or ())
    if parameter_count <= 0:
        return False
    scope_key = getattr(analysis, "analysis_scope_key", None)
    if not isinstance(scope_key, tuple) or len(scope_key) < 4:
        return False
    bound_by_index = scope_key[2] if isinstance(scope_key[2], tuple) else ()
    bound_by_storage = scope_key[3] if isinstance(scope_key[3], tuple) else ()
    return bool(bound_by_index or bound_by_storage)


def _impl_refresh_structural_recurrence_summary(
    self,
    analysis: Optional[FunctionReturnAnalysis],
    timeout: int = 60,
) -> Optional[FunctionReturnAnalysis]:
    """既存解析ビューに対して structural recurrence summary を再構築する。"""
    if analysis is None or not analysis.returns:
        return analysis

    function = self._find_function_by_name(analysis.function_name)
    if function is None:
        return analysis

    from scripts.function_tracer_pcode.ghidra.decompilation_broker import (
        RECURRENCE_REFRESH_SOURCE_CONTRACT,
        decompile_function,
    )
    parent_binding = None
    recurrence_proposals = tuple(
        getattr(analysis, "quarantined_recurrence_proposals", ()) or ()
    )
    if len(recurrence_proposals) > 1:
        from scripts.function_tracer_pcode.authority.lifecycle.production_context import (
            active_production_pilot_session,
        )
        from scripts.function_tracer_pcode.authority.process.subordinate_decompilation import (
            SubordinateParentBindingRequiredDiagnostic,
        )

        active_session = active_production_pilot_session()
        diagnostic = SubordinateParentBindingRequiredDiagnostic(
            RECURRENCE_REFRESH_SOURCE_CONTRACT,
            tuple(proposal.digest for proposal in recurrence_proposals),
            (
                active_session.identity.result_occurrence_id
                if active_session is not None else None
            ),
        )
        note = (
            "diagnostic:subordinate_parent_binding_required:"
            f"{diagnostic.diagnostic_digest}"
        )
        if note not in analysis.analysis_notes:
            analysis.analysis_notes.append(note)
        self._debug_print(
            "Structural recurrence refresh refused unbound subordinate "
            f"decompilation; signed_diagnostic={diagnostic.to_signed_authority_dict()!r}"
        )
        return analysis
    if len(recurrence_proposals) == 1:
        from scripts.function_tracer_pcode.authority.lifecycle.production_context import (
            active_production_pilot_session,
        )
        from scripts.function_tracer_pcode.authority.contracts import authority_digest
        from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
            LoopBlockerProductionSignal,
        )
        from scripts.function_tracer_pcode.authority.process.subordinate_decompilation import (
            SubordinateParentBinding,
        )

        active_session = active_production_pilot_session()
        if active_session is not None:
            blocker = LoopBlockerProductionSignal.from_recurrence_proposal(
                analysis, recurrence_proposals[0]
            )
            resolver = getattr(
                active_session.domain_signal_encoder, "authority_for_signal", None
            )
            if not callable(resolver):
                raise TypeError(
                    "recurrence refresh lacks parent occurrence authority resolver"
                )
            parent_authority = resolver(active_session, blocker)
            slot_bindings = tuple(parent_authority.bound_contract.slot_bindings)
            if len(slot_bindings) != 1:
                raise ValueError(
                    "recurrence refresh requires one exact parent proof requirement"
                )
            requirement = slot_bindings[0][1]
            parent_binding = SubordinateParentBinding(
                active_session.identity.result_occurrence_id,
                parent_authority.occurrence.occurrence_id,
                parent_authority.occurrence.cause_id.value,
                requirement.requirement_id,
                authority_digest(requirement.semantic_target_key),
            )
    results = decompile_function(
        self, function, timeout, None,
        source_contract_id=RECURRENCE_REFRESH_SOURCE_CONTRACT,
        semantic_owner="subordinate",
        parent_binding=parent_binding,
    )
    if not results.decompileCompleted():
        self._debug_print(
            f"Structural summary refresh decompilation failed for '{analysis.function_name}'"
        )
        return analysis

    high_function = results.getHighFunction()
    if high_function is None:
        self._debug_print(
            f"Structural summary refresh HighFunction is None for '{analysis.function_name}'"
        )
        return analysis

    tracer = self._make_tracer(high_function)
    summary = self._apply_structural_recurrence_summary(
        function,
        high_function,
        analysis,
        tracer,
    )
    if summary is None:
        return analysis

    self._normalize_return_partition(summary)
    self._mark_incomplete_control_flow(summary)
    return summary
