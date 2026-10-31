"""Call-site recovery: deferred/indirect call targets, bounded refinement and call argument alignment."""

from __future__ import annotations

from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple, cast
from dataclasses import replace
from scripts.function_tracer_pcode.core.operand_derivation import OperandDerivationRefused
from scripts.function_tracer_pcode.core.stage_clock import stage_region
from scripts.function_tracer_pcode.core.analysis import (
    DeferredCallInfo,
    FunctionReturnAnalysis,
    ReturnInfo,
    ReturnOutcome,
    UnknownOutcome,
)
from scripts.function_tracer_pcode.core.call_target import CallTargetRef, coerce_call_target_ref
from scripts.function_tracer_pcode.core.expression import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.core.intrinsics import resolve_pcode_intrinsic
from scripts.function_tracer_pcode.core.runtime_refs import (
    AddressValueRef,
    DeferredCallRef,
    ExpansionBudgetCollector,
    PcodeOpRef,
    UnknownValueRef,
)
from scripts.function_tracer_pcode.core.signature import get_declared_type_signedness
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.core.structural import StructuralKey
from scripts.function_tracer_pcode.analysis.effects.call_boundary import (
    CallSite,
    CalleeTimeline,
    import_callee_condition,
    import_callee_expression,
)
from scripts.function_tracer_pcode.analysis.effects.pure_function_catalog import (
    resolve_call_model_candidate_ref,
)
from scripts.function_tracer_pcode.analysis.returns._shared import (
    BoundedCallRefiner,
    CallArgumentEvidence,
    ConditionSimplifier,
    ConditionTracker,
    PcodeTracer,
    _PCODE_CALL_OPCODES,
    _TrackedReturnValue,
    _build_parameter_replacements,
    _call_argument_evidence_storage_key,
    _enumerate_constant_expression_branches,
    _expressions_equivalent,
    _reduce_expression_under_conditions,
    _resolve_call_argument_expression,
    _select_explicit_call_arguments_by_semantic_window,
    substitute_condition,
    substitute_expression,
)
from scripts.function_tracer_pcode.analysis.returns._shared import (
    EffectSummary,
    _expression_contains_observed_loads,
    _expressions_equivalent_under_conditions,
    _resolve_call_target_ref,
    canonicalize_expr_read_location,
    expression_contains_post_state_reads,
    lower_post_state_expression_for_smt,
    promote_effect_value_match_to_post_state_read,
    promote_observed_loads_to_post_state_reads,
    rewrite_observed_loads_from_effects,
)
from scripts.function_tracer_pcode.analysis.returns._api import resolve_call_targets
from scripts.function_tracer_pcode.analysis.runtime_state import SuccessfulDecompileParameterSnapshot
from scripts.function_tracer_pcode.analysis.debug import summarize_expression, summarize_expressions


def _impl__direct_call_target_function_key(self, op) -> Optional[Tuple[object, ...]]:
    try:
        if op.getMnemonic() != "CALL" or op.getNumInputs() < 1:
            return None
        target_varnode = op.getInput(0)
        target_address = target_varnode.getAddress()
    except Exception:
        return None
    try:
        manager = self.program.getFunctionManager()
        target_function = manager.getFunctionAt(target_address)
        if target_function is None:
            target_function = manager.getFunctionContaining(target_address)
        if target_function is None:
            return None
        return CallTargetRef.from_function(target_function).stable_key()
    except Exception:
        return None


def _impl__normalize_return_callother_userops(self, analysis: FunctionReturnAnalysis) -> None:
    if analysis is None or not analysis.returns:
        return
    rewritten_returns: List[ReturnInfo] = []
    changed = False
    for info in analysis.returns or []:
        rewritten_value, value_changed = self._normalize_callother_userop_expression(info.value)
        rewritten_conditions: List[Condition] = []
        conditions_changed = False
        for condition in info.conditions or []:
            rewritten_expr, expr_changed = self._normalize_callother_userop_expression(condition.expression)
            rewritten_conditions.append(Condition(rewritten_expr, condition.negated))
            conditions_changed = conditions_changed or expr_changed
        if value_changed or conditions_changed:
            changed = True
            rewritten_returns.append(
                replace(
                    info,
                    value=rewritten_value,
                    conditions=rewritten_conditions,
                )
            )
        else:
            rewritten_returns.append(info)
    if not changed:
        return
    analysis.returns = rewritten_returns
    note = "object_centric_callother_userop_normalization"
    if note not in analysis.analysis_notes:
        analysis.analysis_notes.append(note)


def _impl__normalize_callother_userop_expression(self, expr: Optional[Expression]) -> Tuple[Optional[Expression], bool]:
    if expr is None:
        return expr, False
    if getattr(expr, "expr_type", None) == ExpressionType.PHI:
        changed = False
        branches = []
        for condition, value in getattr(expr, "value", None) or []:
            rewritten_condition = condition
            if condition is not None:
                rewritten_condition_expr, condition_changed = self._normalize_callother_userop_expression(
                    condition.expression,
                )
                rewritten_condition = Condition(rewritten_condition_expr, condition.negated)
                changed = changed or condition_changed
            rewritten_value, value_changed = self._normalize_callother_userop_expression(value)
            branches.append((rewritten_condition, rewritten_value))
            changed = changed or value_changed
        if changed:
            return expr.clone_with(value=branches), True
        return expr, False

    operands = list(getattr(expr, "operands", None) or [])
    changed = False
    rewritten_operands = []
    for operand in operands:
        rewritten_operand, operand_changed = self._normalize_callother_userop_expression(operand)
        rewritten_operands.append(rewritten_operand)
        changed = changed or operand_changed

    if (
        getattr(expr, "expr_type", None) == ExpressionType.INTRINSIC
        and getattr(expr, "name", None) == "CALLOTHER"
        and getattr(expr, "opcode", None) == 9
        and rewritten_operands
    ):
        userop_id = self._constant_expression_value(rewritten_operands[0])
        userop_name = self._program_userop_name(userop_id)
        intrinsic = resolve_pcode_intrinsic(mnemonic=userop_name) if userop_name else None
        if intrinsic is not None:
            return (
                Expression.intrinsic(
                    intrinsic.mnemonic,
                    rewritten_operands[1:],
                    size=max(1, int(getattr(expr, "size", 0) or 0)),
                    runtime_ref=getattr(expr, "runtime_ref", None),
                    opcode=intrinsic.opcode,
                ),
                True,
            )

    if changed:
        return expr.clone_with(operands=rewritten_operands), True
    return expr, False


def _impl__cbranch_direct_target_keys(self, cbranch, block) -> Set[Tuple[str, int]]:
    try:
        if int(getattr(cbranch, "getNumInputs", lambda: 0)() or 0) < 1:
            return set()
        target = cbranch.getInput(0)
    except Exception:
        return set()
    source_spaces = self._block_start_address_spaces(block)
    if len(source_spaces) != 1:
        return set()
    return self._address_like_keys(target, default_space=next(iter(source_spaces)))


def _impl__iter_outcome_call_candidates(
    self,
    analysis: FunctionReturnAnalysis,
) -> Iterable[Tuple[Optional[CallTargetRef], Tuple[Expression, ...], str, str]]:
    seen: Set[Tuple[Any, ...]] = set()
    for info in getattr(analysis, "deferred_calls", {}).values():
        deferred_ref = getattr(info, "deferred_call_ref", None)
        pcode_ref = getattr(deferred_ref, "pcode_op_ref", None)
        stable_key_fn = getattr(pcode_ref, "stable_key", None)
        key = stable_key_fn() if callable(stable_key_fn) else ("deferred", id(info))
        if key in seen:
            continue
        seen.add(key)
        yield (
            getattr(info, "target_ref", None),
            tuple(getattr(info, "arguments", None) or ()),
            getattr(info, "call_argument_recovery_status", "inconclusive"),
            "deferred_call",
        )

    effect_summary = getattr(analysis, "effect_summary", None)
    evidence = getattr(effect_summary, "call_argument_evidence", None)
    if not evidence:
        return
    for key, call_evidence in evidence.items():
        stable_key = getattr(call_evidence, "stable_key", lambda: None)()
        candidate_key = stable_key if stable_key is not None else ("effect", key)
        if candidate_key in seen:
            continue
        seen.add(candidate_key)
        is_usable = getattr(call_evidence, "is_usable", lambda: False)
        if not callable(is_usable) or not is_usable():
            continue
        yield (
            getattr(call_evidence, "target_ref", None),
            tuple(getattr(call_evidence, "arguments", None) or ()),
            getattr(call_evidence, "recovery_status", "inconclusive"),
            "effect_call_argument_evidence",
        )


def _impl__try_apply_triangular_mod_caller_outcomes(
    self,
    high_function,
    analysis: FunctionReturnAnalysis,
) -> bool:
    if len(getattr(analysis, "parameters", []) or []) != 1:
        self._debug_print("Outcome caller summary declined: expected one parameter")
        return False
    if self._high_function_has_forbidden_control_outcome_ops(high_function, allow_call=True):
        self._debug_print("Outcome caller summary declined: forbidden control/effect op present")
        return False

    param = self._parameter_expression(analysis, 0)
    if param is None:
        self._debug_print("Outcome caller summary declined: parameter expression unavailable")
        return False
    matched_call = None
    matched_source = None
    matched_callee_analysis = None
    for target_ref, args_tuple, status, source in self._iter_outcome_call_candidates(analysis):
        args = list(args_tuple or ())
        if len(args) != 1 or not self._expression_is_param_minus_one(args[0], param):
            self._debug_print("Outcome caller summary skipped deferred call: argument is not param_minus_one")
            continue
        if status != "complete":
            self._debug_print(f"Outcome caller summary skipped deferred call: argument recovery status={status}")
            continue
        callee_analysis = self._cached_callee_analysis_for_outcome_summary(target_ref)
        if not self._analysis_has_positive_region_outcome_obligation(callee_analysis):
            self._debug_print("Outcome caller summary skipped deferred call: callee outcome contract unavailable")
            continue
        matched_call = (target_ref, args[0], status)
        matched_source = source
        matched_callee_analysis = callee_analysis
        break
    if matched_call is None:
        self._debug_print("Outcome caller summary declined: no matching callee outcome contract for param_minus_one call")
        return False

    return_size = self._analysis_return_size_bytes(analysis)
    one = Expression.constant(1, max(1, int(param.size or return_size or 4)))
    nonpositive = self._signed_positive_condition(param).negate()
    eq_one = Condition(Expression.binary_op("INT_EQUAL", param, one), False)

    zero_ret, one_ret = self._find_caller_return_partition_for_param_minus_one_obligation(
        analysis,
        param=param,
        nonpositive=nonpositive,
        eq_one=eq_one,
    )
    if zero_ret is None or one_ret is None:
        self._debug_print("Outcome caller summary declined: caller return partition/value proof unavailable")
        return False
    # Issue #131: callee の outcome 契約を実際に採用した箇所（候補を見ただけで
    # 降りた経路では記録しない）。周囲の session ではなく解析結果へ直接反映する。
    # PR-B: 同期は派生 authority を無効化するので、下で書く outcome を消さないよう
    # 採用が確定した直後・書き込みの前に行う（以降に early return はない）。
    outcome_collector = ExpansionBudgetCollector()
    self._record_callee_analysis_expansion_budget(
        matched_callee_analysis,
        owner_scope_key=getattr(analysis, "analysis_scope_key", None),
        collector=outcome_collector,
    )
    self._sync_expansion_budget_truncations(analysis, collector=outcome_collector)
    analysis.returns = [zero_ret, one_ret]
    analysis.return_outcomes = (
        ReturnOutcome(guard=tuple(zero_ret.conditions), value=zero_ret.value, provenance={"source": "callee_positive_region_caller_summary"}, return_info=zero_ret),
        ReturnOutcome(guard=tuple(one_ret.conditions), value=one_ret.value, provenance={"source": "callee_positive_region_caller_summary"}, return_info=one_ret),
    )
    analysis.divergence_outcomes = ()
    analysis.unknown_outcomes = (
        UnknownOutcome(
            guard=(self._return_partition_miss_guard([zero_ret, one_ret]),),
            reason="callee_positive_region_outcome_proof_missing",
            evidence={
                "candidate_rule": "callee_positive_region_outcome_obligation_bv_argument_binding",
                "argument_binding": "param_minus_one",
                "argument_recovery_status": matched_call[2],
                "call_evidence_source": matched_source,
                "missing_proof": "callee_positive_region_outcome_resolution_and_bv_substitution",
            },
        ),
    )
    if "outcome_partition_unknown_callee_positive_region" not in analysis.analysis_notes:
        analysis.analysis_notes.append("outcome_partition_unknown_callee_positive_region")
    return True


def _impl__find_caller_return_partition_for_param_minus_one_obligation(
    self,
    analysis: FunctionReturnAnalysis,
    *,
    param: Expression,
    nonpositive: Condition,
    eq_one: Condition,
) -> Tuple[Optional[ReturnInfo], Optional[ReturnInfo]]:
    zero_ret = None
    one_ret = None
    for ret in getattr(analysis, "returns", []) or ():
        conditions = tuple(getattr(ret, "conditions", ()) or ())
        if zero_ret is None and self._constant_int_value(getattr(ret, "value", None)) == 0:
            if self._conditions_equivalent(conditions, [nonpositive]) or (
                len(conditions) == 1
                and self._condition_is_signed_nonpositive_of_param(conditions[0], param)
            ):
                zero_ret = ret
                continue
        if one_ret is None and self._caller_return_value_matches_param_on_eq_one(
            getattr(ret, "value", None),
            param,
        ):
            if self._conditions_equivalent(conditions, [eq_one]) or any(
                self._condition_is_param_equal_const(condition, param, 1)
                for condition in conditions
            ):
                one_ret = ret
    return zero_ret, one_ret


def _impl__caller_return_value_matches_param_on_eq_one(
    self,
    value: Optional[Expression],
    param: Expression,
) -> bool:
    if value is None:
        return False
    if self._expression_is_same_parameter_ignoring_subpiece(value, param):
        return True
    return self._constant_int_value(value) == 1


def _impl__cached_callee_analysis_for_outcome_summary(
    self,
    target_ref: Optional[CallTargetRef],
) -> Optional[FunctionReturnAnalysis]:
    if target_ref is None:
        return None
    candidate_keys: List[Tuple[Any, ...]] = []
    try:
        candidate_keys.append(self._analysis_scope_key(target_ref))
    except Exception:
        pass
    active_key = self._target_active_key(target_ref)
    if active_key is not None:
        candidate_keys.append(active_key)
    try:
        function_obj = getattr(target_ref, "function_obj", None) or self._resolve_target_function(target_ref)
    except Exception:
        function_obj = None
    function_key = self._function_cache_key(function_obj)
    if function_key is not None:
        candidate_keys.append(function_key)
    seen: Set[Tuple[Any, ...]] = set()
    for key in candidate_keys:
        if key in seen:
            continue
        seen.add(key)
        cached = self._call_analysis_cache.get(key)
        if cached is not None:
            return cached
    return None


def _impl__make_deferred_call_recorder(self, current_function=None):
    current_function_ref = (
        CallTargetRef.from_function(current_function)
        if current_function is not None
        else CallTargetRef.unknown()
    )
    caller_parameters = [dict(param) for param in (self._current_parameters or [])]
    # decision-neutral な call-model candidate（Issue #20 PR-B1）。同じ callee を
    # 何度呼んでも Ghidra signature の読み出しは 1 度で足りるのでキャッシュする。
    candidate_cache: Dict[Any, Any] = {}

    def call_model_candidate_for(target_ref: CallTargetRef):
        """catalog candidate metadata を返す。判定は一切変えない。

        candidate は「仮定を置けば model 化し得る」という分類にすぎず、
        ``effect_class`` にも引数復元にも影響しない。
        """
        # policy が無い host では observation 境界を確認できないので fail closed。
        policy = getattr(self, "_external_call_effect_policy", None)
        try:
            cache_key = (target_ref.stable_key(), policy)
        except Exception:  # noqa: BLE001 - 識別できないなら候補にしない
            return None
        if cache_key in candidate_cache:
            return candidate_cache[cache_key]
        candidate = resolve_call_model_candidate_ref(target_ref, policy=policy)
        candidate_cache[cache_key] = candidate
        return candidate

    def record_call(
        target,
        args: List[Expression],
        call_target_expr: Optional[Expression] = None,
        pcode_op_ref: Optional[PcodeOpRef] = None,
    ) -> UnknownValueRef:
        target_ref = self._coerce_runtime_target_ref(target) or CallTargetRef.unknown()
        sequence = self._deferred_call_counter
        self._deferred_call_counter += 1
        aligned_args = self._align_deferred_call_arguments_for_recording(
            target_ref,
            args,
            caller_parameters,
        )
        cloned_args = [self._clone_expression(arg) for arg in aligned_args]
        cloned_target_expr = (
            self._clone_expression(call_target_expr)
            if call_target_expr is not None
            else None
        )
        deferred_call_ref = DeferredCallRef(
            caller_program_id=current_function_ref.program_id,
            caller_entry_offset=current_function_ref.entry_offset,
            pcode_op_ref=pcode_op_ref,
            target_ref=target_ref,
            sequence=sequence,
        )
        info = DeferredCallInfo(
            target_ref=target_ref,
            arguments=cloned_args,
            call_target_expr=cloned_target_expr,
            deferred_call_ref=deferred_call_ref,
            placeholder_name=deferred_call_ref.display_name(),
            call_model_candidate=call_model_candidate_for(target_ref),
        )
        self._current_deferred_calls[deferred_call_ref.stable_key()] = info
        if self.debug:
            self._debug_print(
                f"Recorded deferred call in '{current_function_ref.display_name()}': "
                f"{info.placeholder_name} -> "
                f"{target_ref.display_name()}({summarize_expressions(cloned_args)}) "
                f"target_expr={summarize_expression(cloned_target_expr)}"
            )
        return info.unknown_ref

    return record_call


def _impl__align_deferred_call_arguments_for_recording(
    self,
    target_ref: CallTargetRef,
    args: Sequence[Expression],
    caller_parameters: Sequence[Dict],
) -> List[Expression]:
    raw_args = list(args or [])
    if target_ref is None or target_ref.is_unknown() or len(raw_args) <= 1:
        return raw_args
    callee_parameters = list(self._get_freshest_callee_parameters(target_ref) or [])
    if not callee_parameters or len(raw_args) <= len(callee_parameters):
        return raw_args
    aligned = _select_explicit_call_arguments_by_semantic_window(
        callee_parameters,
        raw_args,
        caller_parameters,
    )
    if aligned is None:
        return raw_args
    return list(aligned)


def _impl__apply_bounded_call_refinement(
    self,
    analysis: FunctionReturnAnalysis,
    active_functions: Set[Tuple[Any, ...]],
    current_function_ref: Optional[CallTargetRef],
) -> None:
    if (
        not self._bounded_call_refinement_enabled
        or analysis is None
        or not analysis.deferred_calls
        or self._bounded_call_unroll_limit <= 0
    ):
        return

    def provide_analysis(
        target,
        args: Optional[Sequence[Expression]] = None,
    ) -> Optional[FunctionReturnAnalysis]:
        target_ref = self._coerce_runtime_target_ref(target)
        if target_ref is None:
            return None
        bound_parameter_values, bound_parameter_storage_values = (
            self._bound_parameter_maps_for_target_args(target_ref, args)
        )
        scope_key = self._analysis_scope_key(
            target_ref,
            bound_parameter_values,
            bound_parameter_storage_values,
        )
        if (
            current_function_ref is not None
            and analysis.analysis_scope_key == scope_key
        ):
            return analysis
        in_progress = self._analysis_in_progress.get(scope_key)
        if in_progress is not None:
            return in_progress
        active_key = self._target_active_key(target_ref)
        if active_key is not None and active_key in active_functions:
            return None
        return self._invoke_get_or_analyze_call_target(
            target_ref,
            active_functions,
            args=args,
        )

    # Issue #131: refiner が callee の戻り値を caller の展開へ実際に積んだ地点だけを
    # 記録する。provider が返しただけの候補（引数 alignment 失敗・width 安全性違反・
    # 条件矛盾・展開不成立）では marker を作らない。記録先は refine 対象の analysis
    # scope で、周囲の session へは混ぜない。
    refinement_collector = ExpansionBudgetCollector()
    refinement_owner_scope_key = getattr(analysis, "analysis_scope_key", None)

    def record_adopted_callee(callee_analysis) -> None:
        self._record_callee_analysis_expansion_budget(
            callee_analysis,
            owner_scope_key=refinement_owner_scope_key,
            collector=refinement_collector,
        )

    refiner = BoundedCallRefiner(
        provide_analysis,
        max_unroll=self._bounded_call_unroll_limit,
        max_cases=self._bounded_call_max_cases,
        debug=self.debug,
        on_callee_adopted=record_adopted_callee,
    )
    returns_before_refinement = analysis.returns
    changed = refiner.refine_analysis(analysis)
    if analysis.returns is not returns_before_refinement:
        # 展開結果が実際に採用された（returns が置き換わった）ときだけ反映する。
        self._sync_expansion_budget_truncations(
            analysis,
            collector=refinement_collector,
        )
    if changed:
        self._debug_print(
            f"Applied bounded call refinement to '{analysis.function_name}' "
            f"(remaining deferred calls={len(analysis.deferred_calls)})"
        )


def _impl__apply_effect_call_argument_evidence_to_deferred_calls(
    self,
    analysis: FunctionReturnAnalysis,
) -> None:
    effect_summary = getattr(analysis, "effect_summary", None)
    evidence = getattr(effect_summary, "call_argument_evidence", None)
    if not evidence or not getattr(analysis, "deferred_calls", None):
        return
    changed = False
    incomplete = False
    for info in analysis.deferred_calls.values():
        deferred_ref = getattr(info, "deferred_call_ref", None)
        pcode_ref = getattr(deferred_ref, "pcode_op_ref", None)
        stable_key_fn = getattr(pcode_ref, "stable_key", None)
        if not callable(stable_key_fn):
            continue
        pcode_key = stable_key_fn()
        target_specific_key = _call_argument_evidence_storage_key(
            pcode_key,
            getattr(info, "target_ref", None),
        )
        call_evidence = (
            evidence.get(target_specific_key)
            if target_specific_key is not None
            else None
        )
        if call_evidence is None:
            call_evidence = evidence.get(pcode_key)
        if call_evidence is None:
            continue
        target_matches = getattr(call_evidence, "target_matches", None)
        target_match_ok = not callable(target_matches) or target_matches(getattr(info, "target_ref", None))
        reason = getattr(call_evidence, "reason", None)
        if not target_match_ok:
            status = CallArgumentEvidence.RECOVERY_INCONCLUSIVE
            is_blocker = True
        else:
            status = getattr(call_evidence, "recovery_status", CallArgumentEvidence.RECOVERY_INCONCLUSIVE)
            if status not in {
                CallArgumentEvidence.RECOVERY_COMPLETE,
                CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL,
                CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
            }:
                status = CallArgumentEvidence.RECOVERY_INCONCLUSIVE
        if status == CallArgumentEvidence.RECOVERY_COMPLETE:
            args = getattr(call_evidence, "arguments", ())
            info.arguments = [self._clone_expression(arg) for arg in args]
            changed = True
            is_blocker = False
        elif status == CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL:
            is_blocker = False
        else:
            status = CallArgumentEvidence.RECOVERY_INCONCLUSIVE
            is_blocker = True

        if callable(getattr(info, "set_call_argument_recovery_state", None)):
            info.set_call_argument_recovery_state(status, reason)
        else:
            info.call_argument_recovery_status = status
            info.call_argument_recovery_reason = reason
        if is_blocker:
            incomplete = True
    if changed and "effect_call_argument_evidence" not in analysis.analysis_notes:
        analysis.analysis_notes.append("effect_call_argument_evidence")
    if incomplete and "effect_call_argument_evidence_incomplete" not in analysis.analysis_notes:
        analysis.analysis_notes.append("effect_call_argument_evidence_incomplete")


def _impl__recover_call_wrapper_returns(
    self,
    decompile_results,
    analysis: FunctionReturnAnalysis,
    current_function,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    return_ops: List[Any],
    active_functions: Optional[Set[Tuple[Any, ...]]] = None,
) -> Optional[List[ReturnInfo]]:
    """wrapper らしい unknown return を P-code/CFG ベースでのみ復元する。"""
    needs_wrapper_recovery = self._analysis_needs_wrapper_recovery(analysis)

    if needs_wrapper_recovery:
        recovered_from_pcode = self._recover_call_wrapper_returns_from_pcode(
            analysis,
            tracer,
            condition_tracker,
            return_ops,
            current_function,
            active_functions or set(),
        )
        if recovered_from_pcode is not None:
            if self.debug:
                self._debug_print(
                    f"Call-wrapper recovery reconstructed {len(recovered_from_pcode)} return case(s) "
                    "from P-code block paths"
                )
            return recovered_from_pcode

    recovered_uncovered = self._recover_uncovered_terminal_call_returns_from_pcode(
        analysis,
        tracer,
        condition_tracker,
        return_ops,
        current_function,
        active_functions or set(),
    )
    if recovered_uncovered is not None:
        if self.debug:
            self._debug_print(
                f"Call-wrapper recovery supplemented {len(recovered_uncovered)} return case(s) "
                "after detecting uncovered terminal-call return path(s)"
            )
        return recovered_uncovered

    if self.debug:
        if needs_wrapper_recovery:
            self._debug_print(
                "Call-wrapper recovery declined: no safe P-code/CFG reconstruction was available"
            )
        else:
            self._debug_print(
                "Call-wrapper recovery declined: no unresolved return or uncovered terminal-call path"
            )
    return None


def _impl__recover_uncovered_terminal_call_returns_from_pcode(
    self,
    analysis: FunctionReturnAnalysis,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    return_ops: List[Any],
    current_function,
    active_functions: Set[Tuple[Any, ...]],
) -> Optional[List[ReturnInfo]]:
    """既存 return partition から漏れた terminal CALL/CALLIND path だけを補完する。"""
    if analysis is None or not analysis.returns or not return_ops:
        return None

    recovered: List[ReturnInfo] = []
    for return_index, return_op in enumerate(return_ops):
        raw_entries = condition_tracker.get_all_valid_block_paths_to_return(return_op)
        path_entries = self._coerce_block_path_entries(raw_entries)
        if not path_entries:
            return None

        site_metadata = self._describe_pcode_site(return_op, analysis.entry_point)
        address = cast(str, site_metadata.get("address") or analysis.entry_point)

        for path_index, (block_path, path_conditions) in enumerate(path_entries):
            if self._return_path_is_covered_by_existing_return(
                analysis,
                path_conditions,
            ):
                continue

            terminal_call = self._find_terminal_call_on_block_path(
                block_path,
                return_op,
                tracer=tracer,
                condition_tracker=condition_tracker,
                current_function=current_function,
                path_conditions=path_conditions,
            )
            if terminal_call is None:
                if self.debug:
                    self._debug_print(
                        "Call-wrapper uncovered-path recovery declined: uncovered path "
                        f"{path_index} to RETURN #{return_index} has no safe terminal CALL/CALLIND"
                    )
                return None

            path_recovered = self._recover_implicit_return_from_terminal_call(
                terminal_call,
                address,
                tracer,
                condition_tracker,
                list(path_conditions),
                return_index * 1000 + path_index * 100,
                all_path_conditions=[list(path_conditions)],
                active_functions=active_functions,
                current_function=current_function,
                site_metadata=site_metadata,
            )
            if not path_recovered:
                if self.debug:
                    self._debug_print(
                        "Call-wrapper uncovered-path recovery declined: terminal call expansion "
                        f"failed on path {path_index} to RETURN #{return_index}"
                    )
                return None
            recovered.extend(path_recovered)

    if not recovered:
        return None

    if self._call_wrapper_recovery_conflicts_with_existing_returns(
        list(analysis.returns),
        recovered,
    ):
        return None
    if "uncovered_terminal_call_return_recovery" not in analysis.analysis_notes:
        analysis.analysis_notes.append("uncovered_terminal_call_return_recovery")
    merged = self._merge_equivalent_return_infos(
        self._prune_less_precise_return_infos(list(analysis.returns) + recovered)
    )
    return merged


def _impl__call_wrapper_recovery_conflicts_with_existing_returns(
    self,
    existing_returns: List[ReturnInfo],
    recovered_returns: List[ReturnInfo],
) -> bool:
    for existing in existing_returns or []:
        existing_conditions = self._return_info_effective_region_conditions(existing)
        for recovered in recovered_returns or []:
            recovered_conditions = self._return_info_effective_region_conditions(recovered)
            combined = ConditionSimplifier.simplify_conditions_object_centric(
                list(existing_conditions) + list(recovered_conditions)
            )
            if ConditionSimplifier.object_centric_is_contradiction(combined):
                continue
            if _expressions_equivalent(existing.value, recovered.value):
                continue
            return True
    return False


def _impl__recover_call_wrapper_returns_from_pcode(
    self,
    analysis: FunctionReturnAnalysis,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    return_ops: List[Any],
    current_function,
    active_functions: Set[Tuple[Any, ...]],
) -> Optional[List[ReturnInfo]]:
    """entry -> RETURN の block path 上の terminal CALL を callee summary から復元する。"""
    if not self._analysis_needs_wrapper_recovery(analysis):
        return None

    recovered: List[ReturnInfo] = []
    for return_index, return_op in enumerate(return_ops):
        path_entries = condition_tracker.get_all_valid_block_paths_to_return(return_op)
        if not path_entries:
            if self.debug:
                self._debug_print(
                    f"P-code call-wrapper recovery aborted: no valid block path to RETURN #{return_index}"
                )
            return None

        site_metadata = self._describe_pcode_site(return_op, analysis.entry_point)
        address = cast(str, site_metadata.get("address") or analysis.entry_point)
        return_results: List[ReturnInfo] = []

        for path_index, (block_path, path_conditions) in enumerate(path_entries):
            terminal_call = self._find_terminal_call_on_block_path(
                block_path,
                return_op,
                tracer=tracer,
                condition_tracker=condition_tracker,
                current_function=current_function,
                path_conditions=path_conditions,
            )
            if terminal_call is None:
                if self.debug:
                    block_indexes = [block.index for block in block_path]
                    self._debug_print(
                        "P-code call-wrapper recovery aborted: no safe terminal CALL/CALLIND "
                        f"found on path {path_index} to RETURN #{return_index} "
                        f"(blocks={block_indexes})"
                    )
                return None

            path_recovered = self._recover_implicit_return_from_terminal_call(
                terminal_call,
                address,
                tracer,
                condition_tracker,
                path_conditions,
                return_index,
                all_path_conditions=[path_conditions],
                active_functions=active_functions,
                current_function=current_function,
                site_metadata=site_metadata,
            )
            if not path_recovered:
                if self.debug:
                    self._debug_print(
                        "P-code call-wrapper recovery aborted: terminal call expansion "
                        f"failed on path {path_index} to RETURN #{return_index}"
                    )
                return None
            return_results.extend(path_recovered)

        if not return_results:
            return None
        recovered.extend(return_results)

    return recovered or None


def _impl__find_indirect_dispatch_op_on_block(
    self,
    block_info,
    mnemonics: Optional[Set[str]] = None,
) -> Optional[Any]:
    if block_info is None:
        return None
    allowed_mnemonics = mnemonics or {"BRANCHIND", "CALLIND"}
    for pcode_op in reversed(list(getattr(block_info, "pcode_ops", []) or [])):
        try:
            if str(pcode_op.getMnemonic()) in allowed_mnemonics:
                return pcode_op
        except Exception:
            continue
    return None


def _impl__enumerate_switch_dispatch_targets(
    self,
    dispatch_summary,
) -> List[Tuple[int, List[Condition]]]:
    resolved_targets: List[Tuple[int, List[Condition]]] = []
    seen = set()

    for path_summary in getattr(dispatch_summary, "paths", []) or []:
        for dispatch_case in getattr(path_summary, "cases", []) or []:
            merged_conditions = ConditionSimplifier.simplify_conditions(
                list(getattr(dispatch_case, "conditions", []) or [])
            )
            if ConditionSimplifier.is_contradiction(merged_conditions):
                continue
            key = (
                int(getattr(dispatch_case, "target_address", 0)),
                tuple(
                    ConditionSimplifier.get_simplified_condition_string(cond)
                    for cond in merged_conditions
                ),
            )
            if key in seen:
                continue
            seen.add(key)
            resolved_targets.append(
                (
                    int(getattr(dispatch_case, "target_address", 0)),
                    merged_conditions,
                )
            )

    if len(resolved_targets) > self._bounded_call_max_cases:
        if self.debug:
            self._debug_print(
                "Switch recovery skipped: dispatch fanout exceeds configured safety limit "
                f"({len(resolved_targets)} > {self._bounded_call_max_cases})"
            )
        return []
    return resolved_targets


def _impl__recover_dispatch_call_arguments(
    self,
    dispatch_op,
    tracer: PcodeTracer,
) -> List[Expression]:
    if dispatch_op is None:
        return []
    try:
        mnemonic = dispatch_op.getMnemonic()
    except Exception:
        mnemonic = None
    if mnemonic != "CALLIND":
        return []

    recovered: List[Expression] = []
    try:
        num_inputs = int(dispatch_op.getNumInputs())
    except Exception:
        num_inputs = 0
    for input_index in range(1, max(0, num_inputs)):
        try:
            varnode = dispatch_op.getInput(input_index)
        except Exception:
            continue
        recovered.append(
            _resolve_call_argument_expression(
                varnode,
                tracer,
                self._current_parameters or [],
            )
        )
    return recovered


def _impl__resolve_switch_case_target_expansions(
    self,
    address_value: int,
    dispatch_conditions: List[Condition],
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    return_ops: List[Any],
    *,
    active_functions: Set[Tuple[Any, ...]],
    current_function=None,
):
    from scripts.function_tracer_pcode.semantics.transform.expander import ExpandedValue

    target_block = self._find_block_info_for_program_offset(condition_tracker, address_value)
    if target_block is None:
        return None

    recovered_infos: List[ReturnInfo] = []
    get_paths_to_return = getattr(condition_tracker, "get_all_valid_block_paths_to_return", None)
    if not callable(get_paths_to_return):
        return None

    fallback_address = (
        str(current_function.getEntryPoint())
        if current_function is not None and hasattr(current_function, "getEntryPoint")
        else "unknown"
    )

    for return_index, return_op in enumerate(return_ops or []):
        path_entries = self._get_cached_return_path_entries(
            condition_tracker,
            return_op,
        )
        if not path_entries:
            continue

        for path_index, (block_path, path_conditions) in enumerate(path_entries):
            start_index = self._find_block_index_on_path(block_path, target_block)
            if start_index is None:
                continue

            combined_conditions = ConditionSimplifier.simplify_conditions(
                list(path_conditions) + list(dispatch_conditions)
            )
            if ConditionSimplifier.is_contradiction(combined_conditions):
                continue

            site_metadata = self._describe_pcode_site(return_op, fallback_address)
            suffix_path = list(block_path[start_index:])
            linear_ops = self._collect_linear_ops_to_return(suffix_path, return_op)
            if not linear_ops:
                continue

            tracked_values = self._build_return_tracking_targets(
                return_op,
                tracer=tracer,
                current_function=current_function,
            )
            if not tracked_values:
                continue

            for pcode_op in reversed(linear_ops[:-1]):
                tracked_values = self._rewrite_tracked_return_values_for_op(
                    tracked_values,
                    pcode_op,
                    tracer=tracer,
                    condition_tracker=condition_tracker,
                    path_conditions=combined_conditions,
                    current_function=current_function,
                )
                if not tracked_values:
                    break

            if not tracked_values:
                continue

            path_results = self._recover_return_infos_from_tracked_sources(
                tracked_values,
                cast(str, site_metadata.get("address") or fallback_address),
                tracer,
                condition_tracker,
                combined_conditions,
                return_index * 1000 + path_index,
                all_path_conditions=[combined_conditions],
                active_functions=active_functions,
                current_function=current_function,
                site_metadata=site_metadata,
            )

            if path_results:
                recovered_infos.extend(path_results)

    if not recovered_infos:
        return None

    normalized_infos = self._merge_equivalent_return_infos(
        self._prune_less_precise_return_infos(recovered_infos)
    )
    if not normalized_infos:
        return None

    expanded_values = []
    for ret_info in normalized_infos:
        residual_conditions = ConditionSimplifier.subtract_implied_conditions(
            list(ret_info.conditions),
            list(dispatch_conditions),
        )
        expanded_values.append(
            ExpandedValue(
                value=self._clone_expression(ret_info.value),
                conditions=residual_conditions,
            )
        )
    return expanded_values or None


def _impl__enumerate_switch_branch_targets(
    self,
    switch_block,
    indirect_op,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
) -> List[Tuple[int, List[Condition]]]:
    if indirect_op is None or indirect_op.getNumInputs() < 1:
        return []

    base_paths = condition_tracker.get_all_valid_block_paths_to_block(switch_block)
    if not base_paths:
        base_paths = [([switch_block], [])]

    resolved_targets: List[Tuple[int, List[Condition]]] = []
    seen = set()
    for _blocks, base_conditions in base_paths:
        try:
            target_varnode = indirect_op.getInput(0)
        except Exception:
            return []

        target_expr = tracer.trace_varnode(target_varnode, use_cache=False)
        target_expr = self._concretize_readonly_loads(
            target_expr,
            list(base_conditions),
            self._current_parameters,
        )
        target_branches = _enumerate_constant_expression_branches(target_expr)
        if not target_branches:
            if self.debug:
                self._debug_print(
                    "Switch recovery skipped on block "
                    f"{switch_block.index}: indirect target was not finitely enumerable"
                )
            return []

        for branch_conditions, address_value in target_branches:
            merged_conditions = ConditionSimplifier.simplify_conditions(
                list(base_conditions) + list(branch_conditions)
            )
            if ConditionSimplifier.is_contradiction(merged_conditions):
                continue
            key = (
                int(address_value),
                tuple(
                    ConditionSimplifier.get_simplified_condition_string(cond)
                    for cond in merged_conditions
                ),
            )
            if key in seen:
                continue
            seen.add(key)
            resolved_targets.append((int(address_value), merged_conditions))

    if len(resolved_targets) > self._bounded_call_max_cases:
        if self.debug:
            self._debug_print(
                "Switch recovery skipped: branch target fanout exceeds configured safety limit "
                f"({len(resolved_targets)} > {self._bounded_call_max_cases})"
            )
        return []

    return resolved_targets


def _impl__switch_recovery_targets_problematic_region(
    self,
    analysis: FunctionReturnAnalysis,
    affected_returns: List[ReturnInfo],
) -> bool:
    if not affected_returns:
        return False

    affected_analysis = analysis.semantic_successor(
        returns=list(affected_returns),
    )
    if affected_analysis.has_unknown_return():
        return True
    if affected_analysis.has_unresolved_return_value():
        return True
    if affected_analysis.has_overlapping_unconditional_returns():
        return True
    return self._analysis_has_ambiguous_condition_region_returns(affected_analysis)


def _impl__find_terminal_call_on_block_path(
    self,
    block_path: List[Any],
    return_op,
    *,
    tracer: Optional[PcodeTracer] = None,
    condition_tracker: Optional[ConditionTracker] = None,
    current_function=None,
    path_conditions: Optional[List[Condition]] = None,
):
    """block path 上で RETURN 値 provenance を満たす wrapper 候補 CALL/CALLIND を探す。"""
    linear_ops = self._collect_linear_ops_to_return(block_path, return_op)
    if not linear_ops:
        return None
    return self._find_terminal_call_from_linear_ops(
        linear_ops,
        return_op,
        tracer=tracer,
        condition_tracker=condition_tracker,
        current_function=current_function,
        block_path=block_path,
        path_conditions=path_conditions,
    )


def _impl__find_terminal_call_from_linear_ops(
    self,
    linear_ops: List[Any],
    return_op,
    *,
    tracer: Optional[PcodeTracer] = None,
    condition_tracker: Optional[ConditionTracker] = None,
    current_function=None,
    block_path=None,
    path_conditions: Optional[List[Condition]] = None,
):
    for index in range(len(linear_ops) - 2, -1, -1):
        pcode_op = linear_ops[index]
        if not self._is_pcode_call_op(pcode_op):
            continue
        if self._call_output_proves_wrapper_return(
            linear_ops,
            index,
            return_op,
            tracer=tracer,
            condition_tracker=condition_tracker,
            current_function=current_function,
            block_path=block_path,
            path_conditions=path_conditions,
        ):
            if self.debug:
                self._debug_print(
                    "Wrapper provenance selected terminal "
                    f"{self._pcode_op_debug_name(pcode_op)} before RETURN"
                )
            return pcode_op
    return None


def _impl__is_pcode_call_op(self, pcode_op) -> bool:
    opcode = self._get_pcode_opcode(pcode_op)
    return opcode in _PCODE_CALL_OPCODES


def _impl__build_return_tracking_targets(
    self,
    return_op,
    *,
    tracer: Optional[PcodeTracer],
    current_function,
) -> List[_TrackedReturnValue]:
    tracked_values: List[_TrackedReturnValue] = []

    explicit_inputs = self._coerce_optional_int(
        getattr(return_op, "getNumInputs", lambda: 0)()
    )
    explicit_inputs = explicit_inputs if explicit_inputs is not None else 0
    if explicit_inputs >= 2:
        try:
            tracked_values.append(
                self._make_tracked_return_value(return_op.getInput(1), tracer)
            )
        except Exception:
            pass

    if not tracked_values and tracer is not None:
        for storage in self._get_implicit_return_target_storages(current_function, tracer):
            tracked_values.append(self._make_tracked_return_storage_value(storage))

    return self._deduplicate_tracked_return_values(tracked_values)


def _impl__call_output_proves_wrapper_return(
    self,
    linear_ops: List[Any],
    candidate_index: int,
    return_op,
    *,
    tracer: Optional[PcodeTracer],
    condition_tracker: Optional[ConditionTracker],
    current_function,
    block_path=None,
    path_conditions: Optional[List[Condition]] = None,
) -> bool:
    tracked_values = self._build_return_tracking_targets(
        return_op,
        tracer=tracer,
        current_function=current_function,
    )
    if not tracked_values:
        if self.debug:
            self._debug_print(
                "Wrapper provenance failed: no return tracking targets were available"
            )
        return False

    for pcode_op in reversed(linear_ops[candidate_index + 1:-1]):
        tracked_values = self._rewrite_tracked_return_values_for_op(
            tracked_values,
            pcode_op,
            tracer=tracer,
            condition_tracker=condition_tracker,
            path_conditions=path_conditions,
            current_function=current_function,
        )
        if not tracked_values:
            if self.debug:
                self._debug_print(
                    "Wrapper provenance rejected due to intervening op "
                    f"{self._pcode_op_debug_name(pcode_op)}"
                )
            return False

    return self._tracked_values_match_call_output(
        tracked_values,
        linear_ops[candidate_index],
        tracer=tracer,
        current_function=current_function,
    )


def _impl__tracked_values_match_call_output(
    self,
    tracked_values: List[_TrackedReturnValue],
    call_op,
    *,
    tracer: Optional[PcodeTracer],
    current_function=None,
) -> bool:
    call_output = getattr(call_op, "getOutput", lambda: None)()
    call_output_storage = None
    if tracer is not None and call_output is not None:
        try:
            call_output_storage = tracer._get_storage_info_from_varnode(call_output)
        except Exception:
            call_output_storage = None

    if call_output is None:
        if tracer is None:
            return False
        return_storages = self._get_implicit_return_target_storages(current_function, tracer)
        for tracked in tracked_values:
            tracked_storage = tracked.storage
            if tracked_storage is None and tracked.varnode is not None:
                try:
                    tracked_storage = tracer._get_storage_info_from_varnode(tracked.varnode)
                except Exception:
                    tracked_storage = None
            if tracked_storage is None:
                continue
            if any(
                self._storages_overlap_for_return_recovery(tracked_storage, return_storage)
                for return_storage in return_storages
            ):
                return True
        return False

    for tracked in tracked_values:
        if tracked.varnode is not None and self._varnodes_may_alias(tracked.varnode, call_output):
            return True
        tracked_storage = tracked.storage
        if tracked_storage is None and tracked.varnode is not None and tracer is not None:
            try:
                tracked_storage = tracer._get_storage_info_from_varnode(tracked.varnode)
            except Exception:
                tracked_storage = None
        if tracked_storage is not None and call_output_storage is not None:
            if self._storages_overlap_for_return_recovery(tracked_storage, call_output_storage):
                return True
    return False


def _impl__coerce_runtime_target_ref(self, target) -> Optional[CallTargetRef]:
    return coerce_call_target_ref(target)


def _impl__bound_parameter_values_from_call_args(
    self,
    args: Optional[Sequence[Expression]],
    callee_parameters: Optional[Sequence[Dict]],
) -> Dict[int, Expression]:
    bound_by_identity: Dict[int, Expression] = {}
    for ordinal, arg in enumerate(args or []):
        if arg is None or callee_parameters is None or ordinal >= len(callee_parameters):
            continue
        callee_param = callee_parameters[ordinal] or {}
        try:
            parameter_index = int(callee_param.get("index"))
        except Exception:
            continue
        if parameter_index < 0:
            continue
        bound_by_identity[parameter_index] = arg
    return self._normalize_bound_parameter_values(bound_by_identity)


def _impl__bound_parameter_storage_values_from_call_args(
    self,
    args: Optional[Sequence[Expression]],
    callee_parameters: Optional[Sequence[Dict]],
) -> Dict[Tuple[Any, ...], Expression]:
    bound_by_storage: Dict[Tuple[Any, ...], Expression] = {}
    for ordinal, arg in enumerate(args or []):
        if arg is None or callee_parameters is None or ordinal >= len(callee_parameters):
            continue
        callee_param = callee_parameters[ordinal] or {}
        storage_info = self._coerce_wrapper_storage_info(callee_param.get("storage"))
        if storage_info is None:
            continue
        try:
            storage_key = storage_info.storage_identity_key()
        except Exception:
            storage_key = None
        if storage_key is None:
            continue
        bound_by_storage[tuple(storage_key)] = arg
    return self._normalize_bound_parameter_storage_values(bound_by_storage)


def _impl__bound_parameter_maps_for_target_args(
    self,
    target,
    args: Optional[Sequence[Expression]],
) -> Tuple[Dict[int, Expression], Dict[Tuple[Any, ...], Expression]]:
    target_ref = self._coerce_runtime_target_ref(target)
    if target_ref is None:
        return {}, {}
    callee_parameters = self._get_freshest_callee_parameters(target_ref)
    return (
        self._bound_parameter_values_from_call_args(args, callee_parameters),
        self._bound_parameter_storage_values_from_call_args(args, callee_parameters),
    )


def _impl__target_active_key(self, target_ref: Optional[CallTargetRef]) -> Optional[Tuple[Any, ...]]:
    if target_ref is None:
        return None
    return target_ref.analysis_key()


def _impl__resolve_target_function(self, target) -> Optional[Any]:
    target_ref = self._coerce_runtime_target_ref(target)
    if target_ref is None or self.program is None:
        return None
    if target_ref.function_obj is not None:
        return target_ref.function_obj
    if target_ref.entry_offset is not None:
        return self._resolve_function_from_program_offset(target_ref.entry_offset)
    if target_ref.address_offset is not None:
        return self._resolve_function_from_program_offset(target_ref.address_offset)
    if target_ref.function_name:
        return self._find_function_by_name(target_ref.function_name)
    return None


CALLEE_PARAMETER_DECOMPILE_TIMEOUT = 60


def _callee_parameter_decompile_contract_id(timeout: int) -> str:
    """snapshot を観測した decompile 条件の identity（contract + timeout）。

    条件が変われば同じ callee でも別観測なので、snapshot は再利用せず decompile し直す。
    """
    from scripts.function_tracer_pcode.ghidra.decompilation_broker import (
        LIFECYCLE_HELPER_SOURCE_CONTRACT,
    )

    return f"{LIFECYCLE_HELPER_SOURCE_CONTRACT}:timeout={int(timeout)}"


def _impl__get_freshest_callee_parameters(self, target) -> List[Dict]:
    """callee の parameter descriptor を返す（Issue #47 PR-A の 2-cache model）。

    - ``_effect_summary_parameter_cache``: partial / richer descriptor cache。
      effect lane など複数の producer が書き込むので **complete である保証はなく**、
      fresh 観測と ``_choose_richer_parameter_descriptors`` で併合する入力にすぎない。
    - ``_callee_parameter_decompile_cache``: decompile が完了し HighFunction が存在した
      場合にだけ作る complete snapshot。同じ観測条件（contract / program identity）の
      下でのみ、fresh decompile の代わりに使える唯一の freshness evidence。

    decompile 失敗・HighFunction 欠落は snapshot 化しない（次回また decompile する）。
    """
    stats = self._callee_parameter_decompile_stats
    callee = self._resolve_target_function(target)
    if callee is None:
        stats.record_uncacheable("callee_unresolved")
        return []

    callee_key = self._function_cache_key(callee)
    if callee_key is None:
        stats.record_uncacheable("cache_key_unavailable")
        return []
    cached_parameters = self._effect_summary_parameter_cache.get(callee_key)

    timeout = CALLEE_PARAMETER_DECOMPILE_TIMEOUT
    contract_id = _callee_parameter_decompile_contract_id(timeout)
    program_identity = self._program_identity()
    snapshot_cache = self._callee_parameter_decompile_cache
    snapshot = snapshot_cache.get(callee_key)
    if snapshot is not None and snapshot.matches_observation_contract(
        decompile_contract_id=contract_id,
        program_identity=program_identity,
    ):
        stats.record_hit()
        fresh_parameters = snapshot.materialize_parameters()
    else:
        stats.record_miss("no_snapshot" if snapshot is None else "observation_contract_mismatch")
        results = self._decompile_function(callee, timeout=timeout)
        if results is None:
            stats.record_uncacheable("decompile_incomplete")
            return list(cached_parameters or [])

        callee_high = results.getHighFunction()
        if callee_high is None:
            stats.record_uncacheable("high_function_missing")
            return list(cached_parameters or [])

        fresh_parameters = self._collect_parameters(callee_high)
        snapshot_cache[callee_key] = SuccessfulDecompileParameterSnapshot.from_successful_decompile(
            fresh_parameters,
            decompile_contract_id=contract_id,
            program_identity=program_identity,
        )
        stats.record_snapshot_stored()

    merged_parameters = self._choose_richer_parameter_descriptors(
        cached_parameters,
        fresh_parameters,
    )
    self._effect_summary_parameter_cache[callee_key] = list(merged_parameters)
    return list(merged_parameters)


def _impl__should_synthesize_implicit_passthrough_for_call(
    self,
    tracer: PcodeTracer,
    call_op,
    target_storage: StorageInfo,
) -> bool:
    if self._has_non_parameter_symbol_for_storage(tracer, target_storage):
        return False
    if self._is_passthrough_storage_live_in_for_call(tracer, call_op, target_storage):
        return True
    return True


def _impl__is_passthrough_storage_live_in_for_call(
    self,
    tracer: PcodeTracer,
    call_op,
    target_storage: StorageInfo,
) -> bool:
    get_order_key = getattr(tracer, "_get_op_order_key", None)
    if not callable(get_order_key):
        return True

    call_order = self._coerce_order_key(get_order_key(call_op))
    if call_order is None:
        return True

    for op in tracer.get_all_pcode_ops():
        op_order = self._coerce_order_key(get_order_key(op))
        if op_order is None:
            continue
        if op_order >= call_order:
            continue
        output = getattr(op, "getOutput", lambda: None)()
        if output is None:
            continue
        output_storage = tracer._get_storage_info_from_varnode(output)
        if output_storage is None or not getattr(output_storage, "is_register", False):
            continue
        try:
            same_base = output_storage.shares_base_register_with(target_storage)
            overlaps = output_storage.bit_range_overlaps_with(target_storage)
        except Exception:
            same_base = False
            overlaps = False
        if same_base and overlaps:
            return False
    return True


def _impl__invoke_get_or_analyze_call_target(
    self,
    target,
    active_functions: Set[Tuple[Any, ...]],
    *,
    minimum_param_count: int = 0,
    args: Optional[Sequence[Expression]] = None,
) -> Optional[FunctionReturnAnalysis]:
    try:
        return self._get_or_analyze_call_target(
            target,
            active_functions,
            minimum_param_count=minimum_param_count,
            args=args,
        )
    except TypeError:
        try:
            return self._get_or_analyze_call_target(
                target,
                active_functions,
                minimum_param_count=minimum_param_count,
            )
        except TypeError:
            return self._get_or_analyze_call_target(
                target,
                active_functions,
            )


def _impl__make_call_resolver(
    self,
    active_functions: Set[Tuple[Any, ...]],
    current_function=None,
    *,
    budget_collector=None,
    budget_owner_scope_key=None,
):
    """CALL 展開用の resolver を作る。

    Issue #131: 採用した callee の切り捨て marker をどこへ残すかは、resolver を作る側
    （= その展開を所有する scope）が束縛する。効果要約の構築中は要約自身の局所
    collector と summary cache key を渡すこと。省略時は現在の解析 session。
    """

    def resolve_call(target, args, call_site: Optional[CallSite] = None):
        return self._resolve_call_expansions(
            target,
            args,
            active_functions,
            current_function,
            budget_collector=budget_collector,
            budget_owner_scope_key=budget_owner_scope_key,
            call_site=call_site,
        )

    return resolve_call


def _impl__resolve_call_expansions(
    self,
    target,
    args: List[Expression],
    active_functions: Set[Tuple[Any, ...]],
    current_function=None,
    *,
    budget_collector=None,
    budget_owner_scope_key=None,
    call_site: Optional[CallSite] = None,
):
    """callee の return case を caller の呼び出し位置へ展開する。

    `call_site` は caller の中の呼び出しの位置（Issue #281: callee の memory 読み出しを caller の時間軸へ移す
    `analysis.effects.call_boundary` が使う）。渡さなければ位置は不明で、memory を読む callee は展開しない。
    """
    from scripts.function_tracer_pcode.semantics.transform.expander import ExpandedValue

    call_site = call_site if call_site is not None else CallSite(None)
    target_ref = self._coerce_runtime_target_ref(target)
    if target_ref is None:
        return None
    target_label = target_ref.display_name()

    if target_ref.is_code_address() and target_ref.address_offset is not None:
        return self._resolve_local_code_target_expansions(
            target_ref.address_offset,
            active_functions,
            current_function,
            args=args,
            call_site=call_site,
        )

    active_key = self._target_active_key(target_ref)
    if active_key is not None and active_key in active_functions:
        self._debug_print(f"Skipping recursive call expansion for '{target_label}'")
        return None

    analysis = self._invoke_get_or_analyze_call_target(
        target_ref,
        active_functions,
        args=args,
    )
    if analysis is None:
        self._debug_print(f"Call expansion skipped for '{target_label}': analysis unavailable")
        return None

    already_specialized = self._analysis_is_fully_argument_specialized(analysis)
    if len(args) < len(analysis.parameters) and not already_specialized:
        self._debug_print(
            f"Call expansion skipped for '{target_label}': "
            f"expected {len(analysis.parameters)} args, got {len(args)}"
        )
        return None

    try:
        # Issue #281: 引数で特殊化済みの callee も、式は callee の時間軸の上にある。置き換えは要らないが、
        # memory 読み出しは caller の呼び出し位置へ移す（`call_boundary`）
        specialized = self._specialize_call_analysis(
            analysis,
            args,
            call_site,
            substitute_parameters=not already_specialized,
        )
    except OperandDerivationRefused as refusal:
        # Issue #281: 引数へ置き換えた派生が ref を保てない、または memory 読み出しを caller の時間軸へ
        # 移せない（`CallBoundaryRefused` はこの型の派生）。callee の元の式は caller の文脈では別の値なので、
        # その node だけを戻せない。この呼び出しの展開をまるごとやめる（上の None と同じ扱い）
        self._debug_print(f"Call expansion skipped for '{target_label}': {refusal}")
        return None
    if specialized.deferred_calls:
        # bounded refinement の marker は specialized 自身へ載る（呼び出し元 session
        # には混ぜない）。下の callee_analysis marker がそれを参照 ID で拾う。
        self._apply_bounded_call_refinement(
            specialized,
            active_functions,
            analysis.function_ref,
        )
        self._merge_deferred_calls_into_current_analysis(specialized.deferred_calls)

    preserve_non_exhaustive_returns = bool(
        specialized.deferred_calls
        or specialized.unknown_event_count
        or specialized.incomplete_control_flow
    )

    class _CompleteCallExpansions(list):
        coverage_complete: bool = False
        return_semantic_bit_width: Optional[int] = None
        return_signed: Optional[bool] = None

    expanded = _CompleteCallExpansions()
    rejected_returns = 0
    for ret in specialized.returns:
        simplified_conditions = ConditionSimplifier.simplify_conditions_object_centric(
            ret.conditions
        )
        contradictory_conditions = ConditionSimplifier.object_centric_is_contradiction(
            simplified_conditions
        )
        if contradictory_conditions and not preserve_non_exhaustive_returns:
            rejected_returns += 1
            continue

        effective_conditions = (
            list(ret.conditions)
            if contradictory_conditions and preserve_non_exhaustive_returns
            else simplified_conditions
        )
        if contradictory_conditions and preserve_non_exhaustive_returns:
            effective_value = ret.value
        else:
            reduced_value = _reduce_expression_under_conditions(
                ret.value,
                effective_conditions,
            )
            effective_value = reduced_value if reduced_value is not None else ret.value

        if not self._call_summary_is_safe(effective_value, effective_conditions, args):
            self._debug_print(
                f"Call expansion rejected for '{target_label}': "
                "summary not safe enough for inlining"
            )
            rejected_returns += 1
            continue

        # Keep safe return candidates even if others are rejected.
        expanded.append(
            ExpandedValue(
                value=effective_value,
                conditions=effective_conditions,
            )
        )

    if not expanded and rejected_returns:
        self._debug_print(
            f"Call expansion for '{target_label}' dropped all "
            f"({rejected_returns}) inlining candidates; keeping unresolved"
        )
        return None
    expanded.coverage_complete = bool(
        expanded
        and rejected_returns == 0
        and not preserve_non_exhaustive_returns
        and not bool(getattr(analysis, "incomplete_control_flow", False))
        and int(getattr(analysis, "unknown_event_count", 0) or 0) == 0
    )
    try:
        expanded.return_semantic_bit_width = int(
            specialized.get_return_value_solver_bit_width()
        )
    except (AttributeError, TypeError, ValueError):
        expanded.return_semantic_bit_width = None
    try:
        expanded.return_signed = bool(
            get_declared_type_signedness(
                specialized.get_comparison_type_obj(),
                specialized.get_comparison_type_name(),
            )
        )
    except (AttributeError, TypeError, ValueError):
        expanded.return_signed = None
    if expanded:
        # Issue #131: callee 解析を意味入力として採用した箇所。展開候補を 1 件も返さ
        # なかった callee は利用していないので記録しない。callee の marker 本体は複製
        # せず、callee scope と参照 event ID だけを利用側 scope へ残す。効果要約の構築
        # 中は要約自身の collector（= その要約の診断 cache）へ入る。
        self._record_callee_analysis_expansion_budget(
            specialized,
            owner_scope_key=budget_owner_scope_key,
            collector=budget_collector,
        )
    return expanded


def _impl__resolve_local_code_target_expansions(
    self,
    address_value: int,
    active_functions: Set[Tuple[Any, ...]],
    current_function=None,
    args: Optional[List[Expression]] = None,
    call_site: Optional[CallSite] = None,
):

    args = list(args or [])
    call_site = call_site if call_site is not None else CallSite(None)
    cache_key = self._local_target_cache_key(address_value, args, call_site)
    if cache_key in self._local_target_cache:
        return self._local_target_cache[cache_key]

    try:
        default_space = self.program.getAddressFactory().getDefaultAddressSpace()
        addr = default_space.getAddress(address_value)
    except Exception:
        self._debug_print(f"Local target resolution failed: invalid address 0x{address_value:x}")
        self._local_target_cache[cache_key] = None
        return None

    function_manager = self.program.getFunctionManager()
    containing = function_manager.getFunctionContaining(addr)
    if containing is None and current_function is not None:
        try:
            body = current_function.getBody()
            body_contains = body is not None and body.contains(addr)
            if not body_contains and body is not None:
                min_addr = body.getMinAddress()
                max_addr = body.getMaxAddress()
                if min_addr is not None and max_addr is not None:
                    try:
                        body_contains = (
                            min_addr.getOffset() <= addr.getOffset() <= max_addr.getOffset()
                        )
                    except Exception:
                        body_contains = False
            if body_contains:
                containing = current_function
                self._debug_print(
                    f"Local target {addr} falling back to current function '{current_function.getName()}'"
                )
        except Exception:
            containing = current_function
            self._debug_print(
                f"Local target {addr} falling back to current function "
                f"'{current_function.getName()}' after body check failure"
            )
    if containing is None and current_function is not None:
        containing = current_function
        self._debug_print(
            f"Local target {addr} using current function '{current_function.getName()}' as fallback"
        )
    if containing is None:
        self._debug_print(f"Local target resolution failed: no containing function for 0x{address_value:x}")
        self._local_target_cache[cache_key] = None
        return None

    from scripts.function_tracer_pcode.ghidra.decompilation_broker import (
        INLINE_REGION_SOURCE_CONTRACT,
        decompile_within_deadline,
    )
    with stage_region("decompile"):
        results = decompile_within_deadline(
            self, containing, 60, None,
            source_contract_id=INLINE_REGION_SOURCE_CONTRACT,
            semantic_owner="subordinate",
        )
    if not results.decompileCompleted():
        self._debug_print(
            f"Local target resolution failed: decompilation incomplete for 0x{address_value:x}"
        )
        self._local_target_cache[cache_key] = None
        return None
    high_function = results.getHighFunction()
    if high_function is None:
        self._debug_print(f"Local target resolution failed: HighFunction unavailable for 0x{address_value:x}")
        self._local_target_cache[cache_key] = None
        return None

    try:
        local_parameters = self._collect_parameters(high_function)
    except Exception:
        local_parameters = []
    bound_parameter_values = self._bound_parameter_values_from_call_args(
        args,
        local_parameters,
    )
    bound_parameter_storage_values = self._bound_parameter_storage_values_from_call_args(
        args,
        local_parameters,
    )
    tracer = self._make_tracer(
        high_function,
        bound_parameter_values=bound_parameter_values,
        bound_parameter_storage_values=bound_parameter_storage_values,
    )
    tracer.record_deferred_call = self._make_deferred_call_recorder(containing)
    expanded = self._expand_linear_code_target(addr, tracer, containing)
    if expanded:
        try:
            expanded = self._specialize_local_target_expansions(expanded, tracer, args, call_site)
        except OperandDerivationRefused as refusal:
            # Issue #281: 引数へ置き換えた派生が ref を保てない、または memory 読み出しを caller の時間軸へ
            # 移せない。置き換え前の値は callee の parameter・時間軸を指すので使えない: 展開をまるごとやめる
            # （他の失敗と同じく None を cache する）
            self._debug_print(f"Local target expansion skipped: {refusal}")
            expanded = None
    self._local_target_cache[cache_key] = expanded
    return expanded


def _impl__local_target_cache_key(
    self,
    address_value: int,
    args: List[Expression],
    call_site: Optional[CallSite] = None,
) -> Tuple[object, ...]:
    return (
        "local_target",
        int(address_value),
        # 展開の結果は呼び出し位置に依る（memory 読み出しを caller の時間軸へ移す: Issue #281）
        None if call_site is None else call_site.read_order_key,
        tuple(
            arg.structural_key(budget=256)
            for arg in (args or [])
            if arg is not None
        ),
    )


def _impl__specialize_local_target_expansions(
    self,
    expanded: List[Any],
    tracer: PcodeTracer,
    args: List[Expression],
    call_site: Optional[CallSite] = None,
) -> List[Any]:
    if not expanded:
        return expanded
    # Issue #281: 展開した code の memory 読み出しは、その code の op の時間軸の上にある。caller の呼び出し
    # 位置へ移すには「読み出しより前に書き込みが無い」が要るが、code target の effect 要約は無い（書き込みが
    # 分からない）ので、memory を読む展開は `CallBoundaryRefused` になる（呼び出し側が展開をやめる）
    site = call_site if call_site is not None else CallSite(None)
    timeline = CalleeTimeline.unknown()
    expanded = [
        item.__class__(
            value=import_callee_expression(item.value, site, timeline),
            conditions=[import_callee_condition(cond, site, timeline) for cond in (item.conditions or [])],
        )
        for item in expanded
    ]
    if not getattr(tracer, "_parameter_descriptors", None):
        return expanded
    if not args:
        return expanded
    owner_scope: Dict[str, Optional[int]] = {}
    get_owner_scope = getattr(tracer, "get_parameter_owner_scope", None)
    if callable(get_owner_scope):
        try:
            maybe_scope = get_owner_scope() or {}
        except Exception:
            maybe_scope = {}
        if isinstance(maybe_scope, dict):
            owner_scope = maybe_scope

    callee_params = [
        {
            "name": descriptor.name,
            "index": descriptor.index,
            "size": descriptor.size_bytes,
            "data_type": descriptor.data_type,
            "data_type_obj": descriptor.data_type_obj,
            "is_signed": descriptor.is_signed,
            "storage": descriptor.storage_info,
            **owner_scope,
        }
        for descriptor in getattr(tracer, "_parameter_descriptors", [])
    ]
    if not callee_params:
        return expanded

    replacements = _build_parameter_replacements(callee_params, args)
    specialized: List[Any] = []
    for item in expanded:
        value = substitute_expression(item.value, replacements, callee_params)
        conditions = [
            substitute_condition(cond, replacements, callee_params)
            for cond in (item.conditions or [])
        ]
        specialized.append(
            item.__class__(
                value=value,
                conditions=conditions,
            )
        )
    return specialized


def _impl__expand_linear_code_target(self, addr, tracer, current_function=None):
    from scripts.function_tracer_pcode.semantics.transform.expander import ExpandedValue

    instruction = self._get_instruction_with_fallback(addr)
    if instruction is None:
        self._debug_print(f"Local target resolution failed: no instruction at {addr}")
        return None

    self._debug_print(f"Attempting linear local target expansion from {addr}")
    max_steps = 16
    visited_offsets: Set[int] = set()
    local_values: Dict[Tuple[str, int, int], Expression] = {}
    local_storages: Dict[Tuple[str, int, int], Any] = {}
    local_memory: Dict[Tuple[StructuralKey, int], Expression] = {}

    for _ in range(max_steps):
        typed_instruction = cast(Any, instruction)
        try:
            current_offset = typed_instruction.getAddress().getOffset()
        except Exception:
            current_offset = None
        if current_offset is not None:
            if current_offset in visited_offsets:
                self._debug_print(
                    f"Local target resolution aborted at {typed_instruction.getAddress()}: cycle detected"
                )
                return None
            visited_offsets.add(current_offset)

        try:
            pcode_ops = typed_instruction.getPcode()
        except Exception:
            self._debug_print(f"Local target resolution failed: unable to get pcode at {typed_instruction.getAddress()}")
            return None

        branch_target = None
        for pcode_op in pcode_ops:
            mnemonic = pcode_op.getMnemonic()
            if mnemonic == "RETURN":
                value = self._resolve_local_return_expression(
                    pcode_op,
                    tracer,
                    local_values,
                    local_storages,
                    local_memory,
                    current_function,
                )
                if self._debug_available():
                    self._debug_print(
                        f"Resolved local target {typed_instruction.getAddress()} "
                        f"to return expression {summarize_expression(value)}"
                    )
                return [ExpandedValue(value=value, conditions=[])]

            if mnemonic == "STORE":
                self._apply_local_store_effect(
                    pcode_op,
                    tracer,
                    local_values,
                    local_storages,
                    local_memory,
                )
                continue

            if mnemonic == "BRANCH":
                branch_target = self._resolve_local_branch_target(instruction)
                if branch_target is None:
                    self._debug_print(
                        f"Local target resolution aborted at {typed_instruction.getAddress()}: "
                        "unresolved BRANCH target"
                    )
                    return None
                continue

            if mnemonic in {"CALL", "CALLIND", "CBRANCH", "BRANCHIND", "MULTIEQUAL"}:
                self._debug_print(
                    f"Local target resolution aborted at {typed_instruction.getAddress()}: unsupported {mnemonic}"
                )
                return None

            output = getattr(pcode_op, "getOutput", lambda: None)()
            if output is not None:
                value = self._evaluate_local_pcode_expression(
                    pcode_op,
                    tracer,
                    local_values,
                    local_storages,
                    local_memory,
                )
                if value is not None:
                    output_key = self._local_varnode_key(output)
                    local_values[output_key] = value
                    try:
                        local_storages[output_key] = tracer._get_storage_info_from_varnode(output)
                    except Exception:
                        pass

        if branch_target is not None:
            self._debug_print(
                f"Local target {typed_instruction.getAddress()} following BRANCH to {branch_target}"
            )
            instruction = self._get_instruction_with_fallback(branch_target)
            if instruction is None:
                self._debug_print(
                    f"Local target resolution failed: no instruction at branch target {branch_target}"
                )
                return None
            continue

        next_instruction = typed_instruction.getNext()
        if next_instruction is None:
            break
        instruction = next_instruction

    self._debug_print(f"Local target resolution failed: no RETURN found from {addr}")
    return None


def _impl__get_implicit_return_target_storages(
    self,
    function,
    tracer: PcodeTracer,
) -> List[StorageInfo]:
    target_storages: List[StorageInfo] = []
    for return_varnode in self._get_current_prototype_return_varnodes():
        storage = tracer._get_storage_info_from_varnode(return_varnode)
        if storage is not None:
            target_storages.append(storage)
    for return_varnode in self._get_function_return_varnodes(function):
        storage = tracer._get_storage_info_from_varnode(return_varnode)
        if storage is not None:
            target_storages.append(storage)

    if target_storages:
        return self._deduplicate_storage_infos(target_storages)

    fallback = self._infer_abi_return_storages()
    if self.debug and fallback:
        names = [storage.base_register_name or storage.register_name or "?" for storage in fallback]
        self._debug_print(
            f"Using ABI fallback return storages: {names}"
        )
    return fallback


def _impl__resolve_local_branch_target(self, instruction):
    try:
        flows = instruction.getFlows()
    except Exception:
        flows = None
    if flows:
        try:
            if len(flows) == 1 and flows[0] is not None:
                return flows[0]
        except Exception:
            pass

    try:
        fallthrough = instruction.getFallThrough()
    except Exception:
        fallthrough = None
    return fallthrough


def _impl__get_or_analyze_call_target(
    self,
    target,
    active_functions: Set[Tuple[Any, ...]],
    minimum_param_count: int = 0,
    args: Optional[Sequence[Expression]] = None,
) -> Optional[FunctionReturnAnalysis]:
    target_ref = self._coerce_runtime_target_ref(target)
    callee = self._resolve_target_function(target_ref)
    if callee is None:
        return None

    bound_parameter_values, bound_parameter_storage_values = (
        self._bound_parameter_maps_for_target_args(target_ref, args)
    )
    cache_key = self._analysis_scope_key(
        callee,
        bound_parameter_values,
        bound_parameter_storage_values,
    )
    generic_cache_key = self._function_cache_key(callee)
    cached = self._call_analysis_cache.get(cache_key)
    if cached is not None and len(getattr(cached, "parameters", []) or []) >= minimum_param_count:
        return cached

    analysis = self.analyze_function(
        callee,
        timeout=60,
        active_functions=self._extend_active_functions(active_functions, target_ref),
        bound_parameter_values=bound_parameter_values,
        bound_parameter_storage_values=bound_parameter_storage_values,
    )
    if cached is None:
        self._call_analysis_cache[cache_key] = analysis
        if generic_cache_key is not None and not bound_parameter_values and not bound_parameter_storage_values:
            self._call_analysis_cache[generic_cache_key] = analysis
        return analysis
    if analysis is None:
        return cached
    if len(getattr(analysis, "parameters", []) or []) >= len(getattr(cached, "parameters", []) or []):
        self._call_analysis_cache[cache_key] = analysis
        if generic_cache_key is not None and not bound_parameter_values and not bound_parameter_storage_values:
            self._call_analysis_cache[generic_cache_key] = analysis
        return analysis
    return cached


def _impl__call_summary_is_safe(
    self,
    value: Expression,
    conditions: List[Condition],
    args: List[Expression],
) -> bool:
    if (
        self._expression_contains_unknown_or_call(value)
        and not self._expression_unknowns_are_deferred_call_refs(value)
    ):
        return False
    if not self._expression_references_only_allowed_objects(value, args):
        return False

    for cond in conditions:
        if self._expression_contains_unknown_or_call(cond.expression):
            return False
        if not self._expression_references_only_allowed_objects(cond.expression, args):
            return False

    return True


def _impl__expression_unknowns_are_deferred_call_refs(self, expr: Optional[Expression]) -> bool:
    if expr is None:
        return True
    if expr.expr_type == ExpressionType.UNKNOWN:
        runtime_ref = getattr(expr, "runtime_ref", None)
        return getattr(runtime_ref, "deferred_call_ref", None) is not None
    if expr.expr_type == ExpressionType.CALL:
        return False
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and not self._expression_unknowns_are_deferred_call_refs(cond.expression):
                return False
            if not self._expression_unknowns_are_deferred_call_refs(value):
                return False
        return True
    for operand in getattr(expr, "operands", []) or []:
        if not self._expression_unknowns_are_deferred_call_refs(operand):
            return False
    return True


def _impl__expression_contains_unknown_or_call(self, expr: Optional[Expression]) -> bool:
    if expr is None:
        return False

    if expr.expr_type == ExpressionType.UNKNOWN:
        return True
    if expr.expr_type == ExpressionType.CALL:
        return True

    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and self._expression_contains_unknown_or_call(cond.expression):
                return True
            if self._expression_contains_unknown_or_call(value):
                return True
        return False

    for operand in getattr(expr, "operands", []) or []:
        if self._expression_contains_unknown_or_call(operand):
            return True

    return False


def _impl__specialize_call_analysis(
    self,
    analysis: FunctionReturnAnalysis,
    args: List[Expression],
    call_site: Optional[CallSite] = None,
    *,
    substitute_parameters: bool = True,
) -> FunctionReturnAnalysis:
    """callee の解析を caller の呼び出し位置の値にする。

    1. memory 読み出しを caller の時間軸へ移す（Issue #281: `call_boundary`。callee の parameter の言葉のまま
       行う。移せなければ `CallBoundaryRefused`）。
    2. callee の parameter を引数へ置き換える（`substitute_parameters`。引数で特殊化済みの callee では行わない）。
    """
    site = call_site if call_site is not None else CallSite(None)
    timeline = CalleeTimeline.from_effect_summary(
        getattr(analysis, "effect_summary", None),
        analysis.parameters,
    )
    replacements = (
        _build_parameter_replacements(analysis.parameters, args)
        if substitute_parameters
        else {}
    )

    def _specialize(expr: Optional[Expression]) -> Optional[Expression]:
        imported = import_callee_expression(expr, site, timeline)
        if imported is None or not substitute_parameters:
            return imported
        return substitute_expression(imported, replacements, analysis.parameters)

    def _specialize_condition(cond: Condition) -> Condition:
        imported = import_callee_condition(cond, site, timeline)
        if not substitute_parameters:
            return imported
        return substitute_condition(imported, replacements, analysis.parameters)

    specialized_deferred_calls: Dict[Tuple[object, ...], DeferredCallInfo] = {}
    original_to_specialized: Dict[Tuple[object, ...], DeferredCallInfo] = {}

    for info in (analysis.deferred_calls or {}).values():
        specialized_info = DeferredCallInfo(
            placeholder_name=info.placeholder_name,
            target_ref=info.target_ref,
            arguments=[_specialize(arg) for arg in (info.arguments or [])],
            call_target_expr=(
                _specialize(info.call_target_expr)
                if info.call_target_expr is not None
                else None
            ),
            deferred_call_ref=info.deferred_call_ref,
            call_argument_recovery_status=getattr(
                info,
                "call_argument_recovery_status",
                CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
            ),
            call_argument_recovery_reason=getattr(
                info,
                "call_argument_recovery_reason",
                None,
            ),
            effect_class=getattr(info, "effect_class", None),
            match_evidence=getattr(info, "match_evidence", None),
            domain_policy=getattr(info, "domain_policy", None),
            abi_return_width_bits=getattr(info, "abi_return_width_bits", None),
            abi_return_type_policy=getattr(info, "abi_return_type_policy", None),
            call_site_multiplicity=getattr(info, "call_site_multiplicity", None),
            call_model_candidate=getattr(info, "call_model_candidate", None),
        )
        specialized_deferred_calls[info.deferred_call_ref.stable_key()] = specialized_info
        original_to_specialized[info.deferred_call_ref.stable_key()] = specialized_info

    for info in specialized_deferred_calls.values():
        info.arguments = [
            self._rewrite_deferred_runtime_refs_in_expression(arg, original_to_specialized)
            for arg in (info.arguments or [])
        ]
        if info.call_target_expr is not None:
            rewritten_target_expr = self._rewrite_deferred_runtime_refs_in_expression(
                info.call_target_expr,
                original_to_specialized,
            )
            info.call_target_expr = self._normalize_call_target_expression(
                rewritten_target_expr,
            )

    specialized_returns: List[ReturnInfo] = []
    for ret in analysis.returns:
        specialized_value = _specialize(ret.value)
        specialized_value = self._rewrite_deferred_runtime_refs_in_expression(
            specialized_value,
            original_to_specialized,
        )
        specialized_conditions = [
            Condition(
                self._rewrite_deferred_runtime_refs_in_expression(
                    _specialize_condition(cond).expression,
                    original_to_specialized,
                ),
                cond.negated,
            )
            for cond in ret.conditions
        ]
        specialized_returns.append(
            ReturnInfo(
                address=ret.address,
                value=specialized_value,
                conditions=specialized_conditions,
                branch_index=ret.branch_index,
                pcode_identity=ret.pcode_identity,
                pcode_order=ret.pcode_order,
                pcode_time=ret.pcode_time,
                pcode_op_ref=getattr(ret, "pcode_op_ref", None),
                return_value_pcode_op_refs=tuple(
                    getattr(ret, "return_value_pcode_op_refs", ()) or ()
                ),
                return_kind=getattr(ret, "return_kind", "exact") or "exact",
                acceptance_status=getattr(ret, "acceptance_status", None),
                summary_candidate_id=getattr(ret, "summary_candidate_id", None),
                summary_candidate_source_key=getattr(
                    ret,
                    "summary_candidate_source_key",
                    None,
                ),
                summary_transition_evidence_key=getattr(
                    ret,
                    "summary_transition_evidence_key",
                    None,
                ),
                validation_blockers=tuple(
                    getattr(ret, "validation_blockers", ()) or ()
                ),
            )
        )

    return analysis.semantic_successor(
        parameters=[dict(param) for param in (analysis.parameters or [])],
        returns=specialized_returns,
        deferred_calls=specialized_deferred_calls,
    )


def _impl__merge_deferred_calls_into_current_analysis(
    self,
    deferred_calls: Optional[Dict[Tuple[object, ...], DeferredCallInfo]],
) -> None:
    if not deferred_calls:
        return

    for info in deferred_calls.values():
        if info is None or getattr(info, "deferred_call_ref", None) is None:
            continue
        deferred_key = info.deferred_call_ref.stable_key()
        if deferred_key in self._current_deferred_calls:
            existing = self._current_deferred_calls[deferred_key]
            merged_status, merged_reason = self._merge_call_argument_recovery_state(
                getattr(existing, "call_argument_recovery_status", None),
                getattr(existing, "call_argument_recovery_reason", None),
                getattr(info, "call_argument_recovery_status", None),
                getattr(info, "call_argument_recovery_reason", None),
            )
            existing.set_call_argument_recovery_state(
                merged_status,
                merged_reason,
            )
            continue

        cloned_target_expr = (
            self._normalize_call_target_expression(
                self._clone_expression(info.call_target_expr)
            )
            if info.call_target_expr is not None
            else None
        )
        self._current_deferred_calls[deferred_key] = DeferredCallInfo(
            placeholder_name=info.placeholder_name,
            target_ref=info.target_ref,
            arguments=[
                self._clone_expression(arg)
                for arg in (info.arguments or [])
            ],
            call_target_expr=cloned_target_expr,
                deferred_call_ref=info.deferred_call_ref,
                call_argument_recovery_status=getattr(
                    info,
                    "call_argument_recovery_status",
                    CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
                ),
                call_argument_recovery_reason=getattr(
                    info,
                    "call_argument_recovery_reason",
                    None,
                ),
                effect_class=getattr(info, "effect_class", None),
                match_evidence=getattr(info, "match_evidence", None),
                domain_policy=getattr(info, "domain_policy", None),
                abi_return_width_bits=getattr(info, "abi_return_width_bits", None),
                abi_return_type_policy=getattr(info, "abi_return_type_policy", None),
                call_site_multiplicity=getattr(info, "call_site_multiplicity", None),
                call_model_candidate=getattr(info, "call_model_candidate", None),
            )


def _impl__merge_call_argument_recovery_state(
    existing_status: Optional[str],
    existing_reason: Optional[str],
    incoming_status: Optional[str],
    incoming_reason: Optional[str],
) -> Tuple[str, Optional[str]]:
    rank = {
        CallArgumentEvidence.RECOVERY_COMPLETE: 0,
        CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL: 1,
        CallArgumentEvidence.RECOVERY_INCONCLUSIVE: 2,
    }

    def normalize_status(status: Optional[str]) -> str:
        value = str(status or CallArgumentEvidence.RECOVERY_INCONCLUSIVE)
        return value if value in rank else CallArgumentEvidence.RECOVERY_INCONCLUSIVE

    existing_norm = normalize_status(existing_status)
    incoming_norm = normalize_status(incoming_status)
    existing_rank = rank[existing_norm]
    incoming_rank = rank[incoming_norm]

    if incoming_rank > existing_rank:
        return incoming_norm, incoming_reason or existing_reason
    if existing_rank > incoming_rank:
        return existing_norm, existing_reason
    if (existing_reason is None) and (incoming_reason is not None):
        return incoming_norm, incoming_reason
    return existing_norm, existing_reason


def _impl__normalize_call_target_expression(
    self,
    expr: Optional[Expression],
) -> Optional[Expression]:
    if expr is None:
        return None

    if expr.expr_type == ExpressionType.PHI and expr.value:
        rebuilt_branches = []
        changed = False
        for cond, value in expr.value:
            rewritten_value = self._normalize_call_target_expression(value)
            changed = changed or (rewritten_value is not value)
            rebuilt_branches.append((cond, rewritten_value))
        if not changed:
            return expr
        rebuilt = Expression.phi(rebuilt_branches)
        rebuilt.size = expr.size
        return rebuilt

    if expr.expr_type == ExpressionType.CONSTANT:
        try:
            address_value = int(expr.value)
        except Exception:
            return expr

        if self._resolve_function_from_program_offset(address_value) is not None:
            return expr

        try:
            pointer_size = int(self.program.getDefaultPointerSize()) if self.program is not None else 0
        except Exception:
            pointer_size = int(expr.size or 0)
        if pointer_size <= 0:
            return expr

        loaded_value = self._read_memory_value(address_value, pointer_size)
        if loaded_value is None:
            return expr

        function = self._resolve_function_from_program_offset(loaded_value)
        if function is None:
            return expr

        return Expression.constant(
            loaded_value,
            size=max(expr.size or 0, pointer_size),
            runtime_ref=AddressValueRef(
                address_offset=loaded_value,
                source="readonly_call_target",
                display_hint=function.getName(),
                can_execute=True,
            ),
        )

    if not expr.operands:
        return expr

    rewritten_operands = [
        self._normalize_call_target_expression(operand)
        for operand in expr.operands
    ]
    if all(new is old for new, old in zip(rewritten_operands, expr.operands)):
        return expr
    return expr.clone_with(operands=rewritten_operands)


def _impl__rewrite_deferred_runtime_refs_in_expression(
    self,
    expr: Optional[Expression],
    deferred_mapping: Dict[Tuple[object, ...], DeferredCallInfo],
) -> Optional[Expression]:
    if expr is None or not deferred_mapping:
        return expr

    if expr.expr_type == ExpressionType.UNKNOWN:
        runtime_ref = getattr(expr, "runtime_ref", None)
        deferred_call_ref = getattr(runtime_ref, "deferred_call_ref", None)
        deferred_key = (
            deferred_call_ref.stable_key()
            if hasattr(deferred_call_ref, "stable_key")
            else None
        )
        replacement_info = deferred_mapping.get(deferred_key)
        if replacement_info is not None:
            return expr.clone_with(runtime_ref=replacement_info.unknown_ref)
        return expr

    if expr.expr_type == ExpressionType.PHI and expr.value:
        rebuilt_branches = []
        changed = False
        for cond, value in expr.value:
            rewritten_cond = None
            if cond is not None:
                rewritten_expr = self._rewrite_deferred_runtime_refs_in_expression(
                    cond.expression,
                    deferred_mapping,
                )
                rewritten_cond = cond if rewritten_expr is cond.expression else Condition(rewritten_expr, cond.negated)
                changed = changed or (rewritten_cond is not cond)
            rewritten_value = self._rewrite_deferred_runtime_refs_in_expression(
                value,
                deferred_mapping,
            )
            changed = changed or (rewritten_value is not value)
            rebuilt_branches.append((rewritten_cond, rewritten_value))
        if not changed:
            return expr
        rebuilt = Expression.phi(rebuilt_branches)
        rebuilt.size = expr.size
        return rebuilt

    if not expr.operands:
        return expr

    rewritten_operands = [
        self._rewrite_deferred_runtime_refs_in_expression(operand, deferred_mapping)
        for operand in expr.operands
    ]
    if all(new is old for new, old in zip(rewritten_operands, expr.operands)):
        return expr
    return expr.clone_with(operands=rewritten_operands)


def _impl__block_path_contains_noreturn_call(
    self,
    block_path,
    tracer: PcodeTracer,
    return_op,
) -> bool:
    for block_info in block_path:
        for pcode_op in getattr(block_info, "pcode_ops", []) or []:
            if self._pcode_ops_match(pcode_op, return_op):
                return False
            if self._is_noreturn_control_transfer_op(pcode_op, tracer):
                return True
    return False


def _impl__is_noreturn_call_op(self, pcode_op, tracer: PcodeTracer) -> bool:
    return self._is_noreturn_control_transfer_op(pcode_op, tracer)


def _impl__resolve_object_centric_call_targets(
    self,
    pcode_op,
    tracer: Optional[PcodeTracer],
) -> List[CallTargetRef]:
    return self._resolve_object_centric_transfer_targets(pcode_op, tracer)


def _impl__resolve_object_centric_transfer_targets(
    self,
    pcode_op,
    tracer: Optional[PcodeTracer],
) -> List[CallTargetRef]:
    if pcode_op is None or tracer is None:
        return []

    resolved: List[CallTargetRef] = []

    try:
        mnemonic = str(pcode_op.getMnemonic())
    except Exception:
        mnemonic = ""

    if mnemonic in {"CALL", "CALLIND"}:
        try:
            image_base = None
            if self.program is not None:
                image_base = self.program.getImageBase().getOffset()
            for target_ref, _conditions in resolve_call_targets(
                tracer,
                pcode_op,
                conditions=[],
                parameters=list(self._current_parameters or []),
                read_memory_value=self._read_memory_value if self.program is not None else None,
                image_base=image_base,
                debug=self.debug,
            ):
                if target_ref is not None:
                    resolved.append(target_ref)
        except Exception:
            pass
    elif mnemonic == "BRANCHIND":
        try:
            target_varnode = pcode_op.getInput(0)
        except Exception:
            target_varnode = None

        if target_varnode is not None:
            resolver = getattr(tracer, "resolve_call_target_ref", None)
            if callable(resolver):
                try:
                    direct_target = resolver(
                        target_varnode,
                        allow_containing=True,
                        allow_code_address=True,
                    )
                except Exception:
                    direct_target = None
                direct_target_ref = coerce_call_target_ref(direct_target)
                if direct_target_ref is not None:
                    resolved.append(direct_target_ref)

            try:
                target_expr = tracer.trace_varnode(target_varnode, use_cache=False)
            except Exception:
                target_expr = None
            if target_expr is not None:
                target_expr = self._concretize_readonly_loads(
                    target_expr,
                    [],
                    self._current_parameters,
                )
                for _branch_conditions, address_value in _enumerate_constant_expression_branches(target_expr):
                    target_function = self._resolve_function_from_program_offset(int(address_value))
                    if target_function is not None:
                        resolved.append(CallTargetRef.from_function(target_function))
                    else:
                        resolved.append(CallTargetRef.from_code_address(int(address_value)))

    if not resolved:
        fallback_target = _resolve_call_target_ref(tracer, pcode_op)
        if fallback_target is not None:
            resolved.append(fallback_target)

    deduped: List[CallTargetRef] = []
    seen_keys = set()
    for target_ref in resolved:
        stable_key = target_ref.stable_key()
        if stable_key in seen_keys:
            continue
        seen_keys.add(stable_key)
        deduped.append(target_ref)
    return deduped


def _impl__resolve_function_from_call_target_ref(
    self,
    target_ref: Optional[CallTargetRef],
):
    if target_ref is None or target_ref.is_unknown():
        return None

    function_obj = getattr(target_ref, "function_obj", None)
    if function_obj is not None:
        return function_obj

    if target_ref.entry_offset is not None:
        return self._resolve_function_from_program_offset(target_ref.entry_offset)

    if target_ref.address_offset is not None:
        return self._resolve_function_from_program_offset(target_ref.address_offset)

    return None


def _impl__find_terminal_call_before_return(
    self,
    return_op,
    condition_tracker: ConditionTracker,
    tracer: Optional[PcodeTracer] = None,
    current_function=None,
):
    """同一 basic block 内で wrapper return とみなせる末尾 CALL/CALLIND を探す。"""
    return_parent = getattr(return_op, "getParent", lambda: None)()
    return_block = condition_tracker.get_block_by_hash(return_parent)
    if return_block is None:
        return None

    linear_ops = self._collect_linear_ops_to_return([return_block], return_op)
    if not linear_ops:
        return None
    return self._find_terminal_call_from_linear_ops(
        linear_ops,
        return_op,
        tracer=tracer,
        condition_tracker=condition_tracker,
        current_function=current_function,
        block_path=[return_block],
        path_conditions=None,
    )


def _impl__recover_implicit_return_from_terminal_call(
    self,
    call_op,
    address: str,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    path_conditions: List[Condition],
    return_index: int,
    all_path_conditions: Optional[List[List[Condition]]] = None,
    active_functions: Optional[Set[Tuple[Any, ...]]] = None,
    current_function=None,
    site_metadata: Optional[Dict[str, Optional[object]]] = None,
) -> Optional[List[ReturnInfo]]:
    """`call foo(...); return;` 形式の wrapper を callee summary から復元する。"""
    from scripts.function_tracer_pcode.semantics.transform import ExpressionExpander

    expander = ExpressionExpander(
        tracer,
        condition_tracker,
        debug=self.debug,
        call_resolver=self._make_call_resolver(active_functions or set(), current_function),
        effect_summary=self._current_effect_summary,
        parameters=self._current_parameters,
        resolve_callee_parameters=self._get_freshest_callee_parameters,
        read_memory_value=self._read_memory_value,
        image_base=self.program.getImageBase().getOffset(),
        record_deferred_call=self._make_deferred_call_recorder(current_function),
        budget_sink=self._make_expansion_budget_sink(
            surface="call_wrapper",
            owner_scope_key=self._current_analysis_scope_key,
        ),
    )

    path_condition_sets = all_path_conditions or []
    if not path_condition_sets:
        path_condition_sets = [path_conditions] if path_conditions else [[]]

    expanded_values = []
    for conds in path_condition_sets:
        expanded_values.extend(
            expander._expand_call_operation(
                call_op,
                conds,
                depth=0,
                output_size=0,
            )
        )

    if not expanded_values:
        return None

    results = self._build_return_infos_from_expansions(
        address,
        expanded_values,
        return_index,
        site_metadata=site_metadata,
    )
    return results or None


def _impl__is_semantically_lossless_effect_sensitive_rewrite(
    self,
    original: Optional[Expression],
    rewritten: Optional[Expression],
    conditions: List[Condition],
    effect_summary: EffectSummary,
) -> bool:
    if original is None or rewritten is None:
        return False
    if not expression_contains_post_state_reads(rewritten):
        return False
    if not _expression_contains_observed_loads(original):
        return False
    rewritten_location = canonicalize_expr_read_location(
        rewritten,
        self._current_parameters,
    )
    if rewritten_location is not None:
        existing_effect_carrier = promote_effect_value_match_to_post_state_read(
            original,
            rewritten_location,
            conditions,
            effect_summary.effects,
            self._current_parameters,
            symbolic_post_state=True,
        )
        if existing_effect_carrier is not None:
            return False

    comparison_targets: List[Expression] = [original]
    if _expression_contains_observed_loads(original):
        observed_post_state = promote_observed_loads_to_post_state_reads(
            original,
            conditions,
            effect_summary.effects,
            self._current_parameters,
            symbolic_post_state=True,
        )
        if observed_post_state is not None:
            comparison_targets.append(observed_post_state)
            lowered_observed_post_state = lower_post_state_expression_for_smt(
                observed_post_state,
                conditions,
                effect_summary.effects,
                self._current_parameters,
            )
            if lowered_observed_post_state is not None:
                comparison_targets.append(lowered_observed_post_state)
        observed_rewritten = rewrite_observed_loads_from_effects(
            original,
            conditions,
            effect_summary.effects,
            self._current_parameters,
        )
        if observed_rewritten is not None:
            comparison_targets.append(observed_rewritten)

    lowered_rewritten = lower_post_state_expression_for_smt(
        rewritten,
        conditions,
        effect_summary.effects,
        self._current_parameters,
    )
    lowered_rewritten = lowered_rewritten if lowered_rewritten is not None else rewritten
    if expression_contains_post_state_reads(lowered_rewritten):
        return False

    for target in comparison_targets:
        lowered_target = lower_post_state_expression_for_smt(
            target,
            conditions,
            effect_summary.effects,
            self._current_parameters,
        )
        candidate = lowered_target if lowered_target is not None else target
        if _expressions_equivalent_under_conditions(
            lowered_rewritten,
            candidate,
            conditions,
            self._current_parameters,
        ):
            return True
    return False


def _impl__expression_contains_deferred_call_value(self, expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    if getattr(expr, "expr_type", None) == ExpressionType.UNKNOWN:
        runtime_ref = getattr(expr, "runtime_ref", None)
        if getattr(runtime_ref, "deferred_call_ref", None) is not None:
            return True
    if getattr(expr, "expr_type", None) == ExpressionType.PHI and getattr(expr, "value", None):
        for condition, value in expr.value or []:
            if condition is not None and self._expression_contains_deferred_call_value(condition.expression):
                return True
            if self._expression_contains_deferred_call_value(value):
                return True
        return False
    for operand in getattr(expr, "operands", None) or ():
        if self._expression_contains_deferred_call_value(operand):
            return True
    return False


def _impl__clear_resolved_call_effect_blockers(self, analysis: Optional[FunctionReturnAnalysis]) -> None:
    if analysis is None:
        return
    if getattr(analysis, "deferred_calls", None):
        return
    if any(
        self._expression_contains_deferred_call_value(getattr(ret, "value", None))
        or any(
            self._expression_contains_deferred_call_value(getattr(cond, "expression", None))
            for cond in (getattr(ret, "conditions", None) or [])
        )
        for ret in (getattr(analysis, "returns", None) or [])
    ):
        return
    blocking_notes = {
        "effect_call_argument_evidence",
        "effect_call_argument_evidence_incomplete",
    }
    effect_summary = getattr(analysis, "effect_summary", None)
    if effect_summary is not None and getattr(effect_summary, "call_argument_evidence", None):
        return
    if any(note in blocking_notes for note in getattr(analysis, "analysis_notes", []) or []):
        analysis.analysis_notes = [
            note
            for note in (analysis.analysis_notes or [])
            if note not in blocking_notes
        ]
        if "bounded_call_effect_resolved" not in analysis.analysis_notes:
            analysis.analysis_notes.append("bounded_call_effect_resolved")
