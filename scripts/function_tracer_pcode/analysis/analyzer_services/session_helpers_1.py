"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.analyzer``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    ANALYSIS_STATUS_DECOMPILATION_FAILED,
    ANALYSIS_STATUS_HIGH_FUNCTION_MISSING,
    AnalysisFailure,
    CallTargetRef,
    ComparisonSurface,
    Condition,
    ConditionNormalizer,
    ConditionSMTOracle,
    ConditionSimplifier,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    Mapping,
    PcodeOpRef,
    _SIGNED_COMPARE_TO_UNSIGNED,
    _UNSIGNED_COMPARE_TO_SIGNED,
    _expressions_equivalent,
    _iter_expression_nodes,
    attach_summary_return_acceptance_proof,
    cast,
    expression_contains_unsupported_smt_ops,
    expression_key_safe,
    hashlib,
    summarize_expression,
)
from ._api import (
    ConditionTracker,
    StructuralRecurrenceSummarizer,
    accept_summary_return_candidates,
)

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl__debug_print(self, msg: str, indent: int = 0):
    if self.debug:
        prefix = "  " * indent
        print(f"{prefix}[ReturnAnalyzer] {msg}")

def _impl__current_function_entry_address(self):
    if self._current_function_entry_address_value is not None:
        return self._current_function_entry_address_value
    prototype = self._current_function_prototype
    for getter_name in ("getFunction", "getFunctionDefinition"):
        getter = getattr(prototype, getter_name, None)
        if not callable(getter):
            continue
        try:
            function = getter()
        except Exception:
            function = None
        entry_getter = getattr(function, "getEntryPoint", None)
        if callable(entry_getter):
            try:
                return entry_getter()
            except Exception:
                return None
    return None

def _impl__function_entry_address(function):
    entry_getter = getattr(function, "getEntryPoint", None)
    if not callable(entry_getter):
        return None
    try:
        return entry_getter()
    except Exception:
        return None

def _impl__debug_expr_summary(self, expr: Optional[Expression], max_depth: int = 4) -> str:
    return summarize_expression(expr, max_depth=max_depth)

def _impl__debug_expr_identity_summary(
    self,
    expr: Optional[Expression],
    max_depth: int = 3,
) -> str:
    if expr is None:
        return "None"

    runtime_ref = getattr(expr, "runtime_ref", None)
    read_order_key = getattr(expr, "read_order_key", None)
    runtime_tag = type(runtime_ref).__name__ if runtime_ref is not None else "None"
    try:
        structural_key = expression_key_safe(
            expr,
            include_memory_read_order=True,
        )
    except Exception:
        structural_key = None
    return (
        f"{summarize_expression(expr, max_depth=max_depth)} "
        f"[type={expr.expr_type.name}, size={expr.size}, "
        f"read_order={read_order_key}, runtime_ref={runtime_tag}:{runtime_ref}, "
        f"structural={structural_key}]"
    )

def _impl__coerce_optional_int(self, value: object) -> Optional[int]:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    try:
        return int(cast(Any, value))
    except Exception:
        return None

def _impl__describe_pcode_site(
    self,
    pcode_op,
    fallback_address: Optional[str] = None,
    *,
    identity_prefix: Optional[str] = None,
) -> Dict[str, Optional[object]]:
    address = fallback_address or "unknown"
    pcode_identity: Optional[str] = None
    pcode_order: Optional[int] = None
    pcode_time: Optional[int] = None

    seq = getattr(pcode_op, "getSeqnum", lambda: None)() if pcode_op is not None else None
    if seq is not None:
        try:
            target = seq.getTarget()
            if target is not None:
                address = str(target)
        except Exception:
            target = None
        pcode_order = self._coerce_optional_int(getattr(seq, "getOrder", lambda: None)())
        pcode_time = self._coerce_optional_int(getattr(seq, "getTime", lambda: None)())

        if pcode_time is not None:
            pcode_identity = f"{address}:t{pcode_time}"
        elif pcode_order is not None:
            pcode_identity = f"{address}:o{pcode_order}"
        elif address:
            pcode_identity = address
    elif identity_prefix:
        pcode_identity = f"{identity_prefix}:{address}"

    return {
        "address": address,
        "pcode_identity": pcode_identity,
        "pcode_order": pcode_order,
        "pcode_time": pcode_time,
        "pcode_op_ref": PcodeOpRef.from_pcode_op(
            pcode_op,
            binary_id=self._binary_id,
            program_uid=self._program_identity(),
            function_entry=self._current_function_entry_address(),
        ),
    }

def _impl__pcode_op_identity_key(self, pcode_op) -> Optional[Tuple[Any, ...]]:
    if pcode_op is None:
        return None

    site = self._describe_pcode_site(pcode_op)
    output = getattr(pcode_op, "getOutput", lambda: None)()
    output_key = self._varnode_location_key(output)
    if output_key is None and output is not None:
        output_key = ("id", id(output))

    mnemonic = None
    try:
        mnemonic = str(pcode_op.getMnemonic())
    except Exception:
        mnemonic = None

    identity = (
        site.get("address"),
        site.get("pcode_time"),
        site.get("pcode_order"),
        mnemonic,
        output_key,
    )
    if identity[0] is None and identity[1] is None and identity[2] is None and identity[3] is None:
        return None
    return identity

def _impl__pcode_ops_match(self, lhs, rhs) -> bool:
    if lhs is rhs:
        return True
    lhs_key = self._pcode_op_identity_key(lhs)
    rhs_key = self._pcode_op_identity_key(rhs)
    if lhs_key is None or rhs_key is None:
        return False
    return lhs_key == rhs_key

def _impl__expression_contains_equivalent_subexpr(
    self,
    expr: Optional[Expression],
    target: Optional[Expression],
) -> bool:
    if expr is None or target is None:
        return False
    if _expressions_equivalent(expr, target):
        return True
    for operand in getattr(expr, "operands", []) or []:
        if self._expression_contains_equivalent_subexpr(operand, target):
            return True
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and self._expression_contains_equivalent_subexpr(cond.expression, target):
                return True
            if self._expression_contains_equivalent_subexpr(value, target):
                return True
    return False

def _impl__analysis_context(
    self,
    parameters: List[Dict],
    effect_summary: Optional[EffectSummary],
    function_prototype=None,
    function_entry_address=None,
):
    """Temporarily bind per-analysis state and restore the parent context on exit."""
    previous_parameters = self._current_parameters
    previous_effect_summary = self._current_effect_summary
    previous_deferred_calls = self._current_deferred_calls
    previous_function_prototype = self._current_function_prototype
    previous_function_entry_address = self._current_function_entry_address_value
    previous_noreturn_observations = self._current_noreturn_terminal_observations
    self._current_parameters = parameters
    self._current_effect_summary = effect_summary
    self._current_deferred_calls = {}
    self._current_function_prototype = function_prototype
    self._current_function_entry_address_value = function_entry_address
    self._current_noreturn_terminal_observations = []
    try:
        yield
    finally:
        self._current_parameters = previous_parameters
        self._current_effect_summary = previous_effect_summary
        self._current_deferred_calls = previous_deferred_calls
        self._current_function_prototype = previous_function_prototype
        self._current_function_entry_address_value = previous_function_entry_address
        self._current_noreturn_terminal_observations = previous_noreturn_observations

def _impl_dispose(self):
    if self._decompiler is not None:
        try:
            self._decompiler.dispose()
        except Exception as exc:
            exc_text = str(exc).lower()
            if "jvm is not running" not in exc_text and "java virtual machine is not running" not in exc_text:
                raise
        finally:
            self._decompiler = None

def _impl__condition_mentions_param(self, condition: Condition, param_name: str) -> bool:
    """条件が指定パラメータ変数を参照するか判定（to_string 非依存）。"""
    expression = condition.expression
    if expression is None:
        return False
    try:
        return param_name in expression.get_all_variables()
    except Exception:
        return False

def _impl__expression_is_zero_constant(self, expr: Optional[Expression]) -> bool:
    """式が 0 定数、または同値なゼロ表現か判定（to_string 非依存）。"""
    if expr is None:
        return False
    if expr.expr_type == ExpressionType.CONSTANT:
        try:
            return int(expr.value) == 0
        except Exception:
            return False
    if expr.expr_type == ExpressionType.LITERAL:
        try:
            return int(expr.value) == 0
        except Exception:
            return False
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_2COMP", "INT_NEGATE"}:
        if not expr.operands:
            return False
        return self._expression_is_zero_constant(expr.operands[0])
    return False

def _impl__expression_has_param(expr: Optional[Expression], param_name: str) -> bool:
    """式の内部に指定パラメータが含まれるかを判定。"""
    if expr is None:
        return False
    try:
        return param_name in expr.get_all_variables()
    except Exception:
        return False

def _impl__classify_param_condition(
    self,
    condition: Condition,
    param_name: str,
) -> Tuple[bool, bool, bool]:
    """
    条件を零・正・負チェックへ分類（display 文字列不使用）。

    戻り値: (has_zero_check, has_positive_check, has_negative_check)
    """
    decompose = self._decompose_comparison_condition(condition)
    if decompose is None:
        return False, False, False

    negated, op, left, right = decompose
    has_pos = False
    has_neg = False
    has_zero = False

    left_param = self._expression_has_param(left, param_name)
    right_param = self._expression_has_param(right, param_name)
    left_zero = self._expression_is_zero_constant(left)
    right_zero = self._expression_is_zero_constant(right)

    if op in {"INT_EQUAL", "INT_NOTEQUAL"}:
        if (left_zero and right_param) or (right_zero and left_param):
            has_zero = True
        return has_zero, has_pos, has_neg

    if not (
        (left_param and right_zero) or (right_param and left_zero)
    ):
        return has_zero, has_pos, has_neg

    relation_positive_on_zero = op in {"INT_LESSEQUAL", "INT_SLESSEQUAL", "INT_LESS", "INT_SLESS"}
    if not relation_positive_on_zero:
        return has_zero, has_pos, has_neg

    # op が param < 0 系の場合
    if left_param and right_zero:
        if op in {"INT_LESS", "INT_SLESS"}:
            # param < 0
            has_neg = not negated
            has_pos = negated
        elif op in {"INT_LESSEQUAL", "INT_SLESSEQUAL"}:
            # param <= 0
            has_neg = not negated
            has_pos = False
    # op が 0 < param 系の場合
    elif left_zero and right_param:
        if op in {"INT_LESS", "INT_SLESS"}:
            # 0 < param
            has_pos = not negated
            has_neg = negated
        elif op in {"INT_LESSEQUAL", "INT_SLESSEQUAL"}:
            # 0 <= param
            has_pos = not negated
            has_neg = False

    if op in {"INT_NOTEQUAL"} and (left_zero and right_param or right_zero and left_param):
        has_zero = True

    return has_zero, has_pos, has_neg

def _impl_analyze_function(
    self,
    function,
    timeout: int = 60,
    active_functions: Optional[Set[Tuple[Any, ...]]] = None,
    bound_parameter_values: Optional[Dict[int, Expression]] = None,
    bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]] = None,
) -> Optional[FunctionReturnAnalysis]:
     # デバッグフラグを ConditionSimplifier に伝播
    from ..condition import ConditionSimplifier
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
    self._return_path_entry_cache = {}
    current_active_key = analysis_scope_key

    self._debug_print("=" * 60)
    self._debug_print(f"Analyzing function: {function.getName()}")
    self._debug_print("=" * 60)

    decompiler = self._get_decompiler()
    results = decompiler.decompileFunction(function, timeout, None)

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
    from ..phi_resolver import PhiHandler

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
        )

        # 戻り値の型を取得
        return_type_obj, return_type = self._get_return_type_info(high_function)
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
            signedness_result=signedness_result,
            deferred_calls=dict(self._current_deferred_calls),
            effect_summary=effect_summary,
            program_is_big_endian=self._program_is_big_endian(),
            binary_id=self._binary_id,
        )
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

        result.deferred_calls = dict(self._current_deferred_calls)
        self._apply_effect_call_argument_evidence_to_deferred_calls(result)

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
        self._clear_resolved_call_effect_blockers(result)

        self._synchronize_parameters_with_referenced_parameter_expressions(result)
        self._repair_mixed_scalar_signedness(result)
        self._normalize_return_partition(result)
        self._mark_incomplete_control_flow(result)

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
                self._clear_resolved_call_effect_blockers(result)
                self._normalize_return_partition(result)
                self._mark_incomplete_control_flow(result)
        if (
            result.has_symbolic_post_state_reads()
            and "symbolic_post_state_reads" not in result.analysis_notes
        ):
            result.analysis_notes.append("symbolic_post_state_reads")

        self._apply_outcome_partition_summaries(
            function,
            high_function,
            result,
        )
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
            print(f"  Use --debug flag for detailed report")

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
    accepted = accept_summary_return_candidates(
        analysis,
        summary_returns,
        summary_note=summary_note,
        enable_completed_recovery_proofs=self.enable_completed_recovery_proofs,
    )
    if accepted.blockers:
        if self.debug:
            for candidate in accepted.candidates:
                ret = getattr(candidate, "return_info", None)
                conditions = [
                    getattr(cond, "to_string", lambda: repr(cond))()
                    for cond in (getattr(ret, "conditions", None) or [])
                ]
                value = getattr(getattr(ret, "value", None), "to_string", lambda: repr(getattr(ret, "value", None)))()
                print(
                    "Summary return candidate rejected/status="
                    f"{getattr(candidate, 'acceptance_status', None)} "
                    f"blockers={list(getattr(candidate, 'validation_blockers', ()) or ())} "
                    f"conditions={conditions} value={value}"
                )
        return analysis.with_summary_return_diagnostics(
            summary_return_candidates=accepted.candidates,
            blockers=tuple(accepted.blockers),
            reason=summary_note,
        )
    if not accepted.accepted_returns:
        return None
    accepted_view = analysis.with_accepted_return_partition(
        list(accepted.accepted_returns),
        summary_return_candidates=accepted.candidates,
        reason=summary_note,
    )
    attach_summary_return_acceptance_proof(
        accepted_view,
        candidates=accepted.candidates,
        accepted_returns=accepted.accepted_returns,
        summary_note=summary_note,
    )
    if summary_note not in accepted_view.analysis_notes:
        accepted_view.analysis_notes.append(summary_note)
    return accepted_view

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

def _impl__region_input_is_nondata_operand(mnemonic: str, input_index: int) -> bool:
    control_inputs = {
        "BRANCH": {0},
        "CBRANCH": {0},
        "BRANCHIND": {0},
        "CALL": {0},
        "CALLIND": {0},
        "CALLOTHER": {0},
        "RETURN": {0},
        "LOAD": {0},
        "STORE": {0},
    }
    return int(input_index) in control_inputs.get(str(mnemonic), set())

def _impl__region_address_is_code(self, address) -> bool:
    if address is None or self.program is None:
        return False
    try:
        manager = self.program.getFunctionManager()
        if manager.getFunctionContaining(address) is not None:
            return True
    except Exception:
        pass
    try:
        listing = self.program.getListing()
        if listing.getInstructionContaining(address) is not None:
            return True
    except Exception:
        pass
    try:
        block = self.program.getMemory().getBlock(address)
        if block is not None and bool(block.isExecute()):
            return True
    except Exception:
        pass
    return False

def _impl__region_parameter_index_for_location(
    location_key: Tuple[str, int, int],
    parameters: Sequence[Dict[str, Any]],
) -> Optional[int]:
    space_name, offset, size = location_key
    for ordinal, parameter in enumerate(parameters or ()):
        storage = parameter.get("storage") if isinstance(parameter, Mapping) else None
        if storage is None:
            continue
        storage_space = (
            storage.get("space_name")
            if isinstance(storage, Mapping)
            else getattr(storage, "space_name", None)
        )
        storage_offset = (
            storage.get("offset")
            if isinstance(storage, Mapping)
            else getattr(storage, "offset", None)
        )
        storage_size = (
            storage.get("size")
            if isinstance(storage, Mapping)
            else getattr(storage, "size", None)
        )
        try:
            if (
                str(storage_space) == str(space_name)
                and int(storage_offset) == int(offset)
                and int(storage_size) == int(size)
            ):
                return int(parameter.get("index", ordinal))
        except (TypeError, ValueError):
            continue
    return None

def _impl__region_live_in_key(
    self,
    varnode,
    *,
    mnemonic: str,
    input_index: int,
    parameters: Sequence[Dict[str, Any]],
) -> Tuple[Optional[Tuple[object, ...]], str]:
    if self._region_input_is_nondata_operand(mnemonic, input_index):
        return None, "excluded_nondata_operand"
    try:
        if bool(varnode.isConstant()) or varnode.getDef() is not None:
            return None, "excluded_not_live_in"
        address = varnode.getAddress()
    except Exception:
        return None, "incomplete"
    location_key = self._varnode_location_key(varnode)
    if location_key is None:
        return None, "incomplete"
    space_name = str(location_key[0]).lower()
    if space_name == "ram" and self._region_address_is_code(address):
        return None, "excluded_artifact_code_address"
    parameter_index = self._region_parameter_index_for_location(
        location_key,
        parameters,
    )
    if parameter_index is not None:
        return (
            "parameter_input",
            parameter_index,
            tuple(location_key),
        ), "included"
    if space_name == "register":
        category = "register_input"
    elif space_name in {"stack", "ram"}:
        category = "memory_input"
    else:
        return None, "incomplete"
    return (category, tuple(location_key)), "included"

def _impl__recursive_scc_certificate(
    self,
    function_key: Optional[Tuple[object, ...]],
) -> Tuple[bool, Optional[str], Tuple[Tuple[object, ...], ...]]:
    """Return a certificate only for a fully enumerated recursive SCC."""

    if function_key is None or function_key not in self._direct_call_graph:
        return False, None, ()
    graph = self._direct_call_graph
    index = 0
    stack: List[Tuple[object, ...]] = []
    on_stack: Set[Tuple[object, ...]] = set()
    indices: Dict[Tuple[object, ...], int] = {}
    lowlinks: Dict[Tuple[object, ...], int] = {}
    components: List[Tuple[Tuple[object, ...], ...]] = []

    def visit(node: Tuple[object, ...]) -> None:
        nonlocal index
        indices[node] = index
        lowlinks[node] = index
        index += 1
        stack.append(node)
        on_stack.add(node)
        for target in graph.get(node, set()):
            if target not in graph:
                continue
            if target not in indices:
                visit(target)
                lowlinks[node] = min(lowlinks[node], lowlinks[target])
            elif target in on_stack:
                lowlinks[node] = min(lowlinks[node], indices[target])
        if lowlinks[node] != indices[node]:
            return
        component: List[Tuple[object, ...]] = []
        while stack:
            member = stack.pop()
            on_stack.remove(member)
            component.append(member)
            if member == node:
                break
        components.append(tuple(component))

    for node in tuple(graph):
        if node not in indices:
            visit(node)
    component = next(
        (candidate for candidate in components if function_key in candidate),
        (),
    )
    recursive = len(component) > 1 or function_key in graph.get(function_key, set())
    complete = bool(component) and all(
        member in self._direct_call_graph_complete_nodes for member in component
    )
    if not recursive or not complete:
        return False, None, ()
    members = tuple(sorted(component, key=repr))
    identity = hashlib.sha256(repr(("call_graph_scc", members)).encode("utf-8")).hexdigest()
    return True, identity, members

def _impl__collect_java_or_python_iterable(value) -> Tuple[Tuple[Any, ...], bool]:
    if value is None:
        return (), False
    has_next = getattr(value, "hasNext", None)
    next_item = getattr(value, "next", None)
    items: List[Any] = []
    if callable(has_next) and callable(next_item):
        while True:
            try:
                has_item = has_next()
                if not isinstance(has_item, bool):
                    return tuple(items), False
                if not has_item:
                    break
                items.append(next_item())
            except Exception:
                return tuple(items), False
        return tuple(items), True
    try:
        iterator = iter(value)
    except TypeError:
        return (), False
    try:
        for item in iterator:
            items.append(item)
    except Exception:
        return tuple(items), False
    return tuple(items), True

def _impl__constant_expression_value(expr: Optional[Expression]) -> Optional[int]:
    if expr is None or getattr(expr, "expr_type", None) != ExpressionType.CONSTANT:
        return None
    try:
        return int(getattr(expr, "value", 0) or 0)
    except (TypeError, ValueError):
        return None

def _impl__strip_stack_protector_only_conditions(
    self,
    return_infos: List[ReturnInfo],
) -> List[ReturnInfo]:
    if not return_infos:
        return return_infos

    stripped_infos: List[ReturnInfo] = []
    changed = False

    for info in return_infos:
        if not info.conditions:
            stripped_infos.append(info)
            continue

        retained_conditions = [
            cond
            for cond in info.conditions
            if not self._condition_looks_like_stack_protector_guard(cond)
        ]
        if len(retained_conditions) == len(info.conditions):
            stripped_infos.append(info)
            continue

        changed = True
        if self.debug:
            removed_dump = [
                ConditionSimplifier.get_simplified_condition_string(cond)
                for cond in info.conditions
                if cond not in retained_conditions
            ]
            self._debug_print(
                "Dropped object-centric stack-protector guard conditions from "
                f"return case: {removed_dump}"
            )

        stripped_infos.append(
            self._make_return_info(
                address=info.address,
                value=info.value,
                conditions=retained_conditions,
                branch_index=info.branch_index,
                site_metadata=self._return_site_metadata_from_info(info),
            )
        )

    if not changed:
        return return_infos
    return stripped_infos

def _impl__synchronize_parameters_with_referenced_parameter_expressions(
    self,
    analysis: FunctionReturnAnalysis,
) -> None:
    parameters = [dict(param) for param in (analysis.parameters or [])]
    referenced = self._collect_referenced_parameter_descriptors(analysis.returns)
    changed = False

    for candidate in referenced:
        match_index = self._find_matching_parameter_descriptor_index(parameters, candidate)
        if match_index is None:
            parameters.append(candidate)
            changed = True
            continue

        merged = self._merge_parameter_descriptors(parameters[match_index], candidate)
        if merged != parameters[match_index]:
            parameters[match_index] = merged
            changed = True

    if not changed:
        return

    parameters.sort(key=lambda param: int(param.get("index", 1 << 20)))
    analysis.parameters = parameters
    self._current_parameters = parameters

def _impl__repair_mixed_scalar_signedness(
    self,
    analysis: FunctionReturnAnalysis,
) -> None:
    profiles = self._collect_scalar_signedness_profiles(analysis.returns)
    preferred: Dict[Tuple[StructuralKey, int], str] = {}
    for key, profile in profiles.items():
        signed_score = int(profile.get("signed", 0))
        unsigned_score = int(profile.get("unsigned", 0))
        if signed_score <= 0 or unsigned_score <= 0 or signed_score == unsigned_score:
            continue
        preferred[key] = "signed" if signed_score > unsigned_score else "unsigned"

    if not preferred:
        return

    repaired_returns: List[ReturnInfo] = []
    changed = False
    for info in analysis.returns or []:
        rewritten_value, value_changed = self._rewrite_expression_signedness(
            info.value,
            preferred,
        )
        rewritten_conditions: List[Condition] = []
        cond_changed = False
        for cond in info.conditions or []:
            rewritten_expr, expr_changed = self._rewrite_expression_signedness(
                cond.expression,
                preferred,
            )
            rewritten_conditions.append(Condition(rewritten_expr, cond.negated))
            cond_changed = cond_changed or expr_changed
        if value_changed or cond_changed:
            changed = True
            repaired_returns.append(
                self._make_return_info(
                    address=info.address,
                    value=rewritten_value,
                    conditions=rewritten_conditions,
                    branch_index=info.branch_index,
                    site_metadata=self._return_site_metadata_from_info(info),
                )
            )
        else:
            repaired_returns.append(info)

    if not changed:
        return

    analysis.returns = repaired_returns
    note = "object_centric_scalar_signedness_repair"
    if note not in analysis.analysis_notes:
        analysis.analysis_notes.append(note)

def _impl__collect_scalar_signedness_profiles(
    self,
    return_infos: List[ReturnInfo],
) -> Dict[Tuple[StructuralKey, int], Dict[str, int]]:
    profiles: Dict[Tuple[StructuralKey, int], Dict[str, int]] = {}

    def record_expr(expr: Optional[Expression]) -> None:
        if expr is None:
            return
        self._record_scalar_signedness_from_expression(expr, profiles)
        for operand in getattr(expr, "operands", []) or []:
            record_expr(operand)
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None:
                    record_expr(cond.expression)
                record_expr(value)

    for info in return_infos or []:
        record_expr(info.value)
        for cond in info.conditions or []:
            record_expr(cond.expression)

    return profiles

def _impl__record_scalar_signedness_from_expression(
    self,
    expr: Expression,
    profiles: Dict[Tuple[StructuralKey, int], Dict[str, int]],
) -> None:
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP:
        return
    if expr.operator not in set(_UNSIGNED_COMPARE_TO_SIGNED) | set(_SIGNED_COMPARE_TO_UNSIGNED):
        return

    fact = ConditionSimplifier.extract_scalar_constraint(Condition(expr, False))
    if fact is None:
        return

    profile = profiles.setdefault(fact.key, {"signed": 0, "unsigned": 0})
    if expr.operator in _SIGNED_COMPARE_TO_UNSIGNED:
        score = 2
        if fact.value is not None and int(fact.value) < 0:
            score += 2
        profile["signed"] += score
    else:
        profile["unsigned"] += 1

def _impl__collect_referenced_parameter_descriptors(
    self,
    return_infos: List[ReturnInfo],
) -> List[Dict]:
    discovered: Dict[str, Dict] = {}

    for return_info in return_infos or []:
        self._collect_parameter_descriptors_from_expression(return_info.value, discovered)
        for condition in return_info.conditions or []:
            self._collect_parameter_descriptors_from_expression(
                getattr(condition, "expression", None),
                discovered,
            )

    descriptors = list(discovered.values())
    descriptors.sort(key=lambda param: int(param.get("index", 1 << 20)))
    return descriptors

def _impl__collect_parameter_descriptors_from_expression(
    self,
    expr: Optional[Expression],
    discovered: Dict[str, Dict],
) -> None:
    if expr is None:
        return

    if expr.expr_type == ExpressionType.PARAMETER:
        descriptor = self._parameter_descriptor_from_expression(expr)
        key = self._parameter_descriptor_key(descriptor)
        existing = discovered.get(key)
        discovered[key] = self._merge_parameter_descriptors(existing, descriptor)
        return

    if expr.expr_type in {
        ExpressionType.BINARY_OP,
        ExpressionType.UNARY_OP,
        ExpressionType.CALL,
        ExpressionType.INTRINSIC,
        ExpressionType.MEMORY,
    }:
        for operand in expr.operands or []:
            self._collect_parameter_descriptors_from_expression(operand, discovered)
        return

    if expr.expr_type == ExpressionType.PHI and expr.value:
        for branch_condition, branch_value in expr.value:
            if branch_condition is not None:
                self._collect_parameter_descriptors_from_expression(
                    getattr(branch_condition, "expression", None),
                    discovered,
                )
            self._collect_parameter_descriptors_from_expression(branch_value, discovered)

def _impl__parameter_descriptor_from_expression(self, expr: Expression) -> Dict:
    index_value = expr.value if isinstance(expr.value, int) and expr.value >= 0 else -1

    descriptor = {
        "name": expr.name or (f"param_{index_value + 1}" if index_value >= 0 else None),
        "index": index_value,
        "size": expr.size or 0,
        "data_type": expr.data_type,
        "is_signed": True,
        "implicit_passthrough": True,
    }
    if expr.storage_info is not None:
        descriptor["storage"] = expr.storage_info.to_dict()
    return descriptor

def _impl__parameter_descriptor_key(self, descriptor: Dict) -> str:
    name = descriptor.get("name")
    if name:
        return f"name:{name}"
    index = descriptor.get("index")
    if isinstance(index, int) and index >= 0:
        return f"index:{index}"

    storage = descriptor.get("storage")
    if storage:
        base_name = storage.get("base_register_name") or storage.get("register_name") or storage.get("space_name")
        offset = int(storage.get("bit_offset_in_base", storage.get("offset", 0)) or 0)
        size_bits = int(storage.get("size_bits") or (storage.get("size", 0) * 8) or 0)
        return f"storage:{base_name}:{offset}:{size_bits}"
    return f"anonymous:{id(descriptor)}"

def _impl__find_matching_parameter_descriptor_index(
    self,
    parameters: List[Dict],
    candidate: Dict,
) -> Optional[int]:
    candidate_name = candidate.get("name")
    if candidate_name:
        for index, param in enumerate(parameters):
            if param.get("name") == candidate_name:
                return index

    candidate_index = candidate.get("index")
    if isinstance(candidate_index, int) and candidate_index >= 0:
        for index, param in enumerate(parameters):
            if int(param.get("index", -1)) == candidate_index:
                return index

    candidate_storage = candidate.get("storage")
    if candidate_storage:
        for index, param in enumerate(parameters):
            if self._parameter_storages_match_for_passthrough(
                param.get("storage"),
                candidate_storage,
            ):
                return index
    return None

def _impl__merge_parameter_descriptors(
    self,
    existing: Optional[Dict],
    candidate: Dict,
) -> Dict:
    if existing is None:
        return dict(candidate)

    merged = dict(existing)
    if not merged.get("name") and candidate.get("name"):
        merged["name"] = candidate.get("name")
    if int(merged.get("index", -1)) < 0 and int(candidate.get("index", -1)) >= 0:
        merged["index"] = candidate.get("index")
    if int(merged.get("size", 0) or 0) <= 0 and int(candidate.get("size", 0) or 0) > 0:
        merged["size"] = candidate.get("size")
    if not merged.get("data_type") and candidate.get("data_type"):
        merged["data_type"] = candidate.get("data_type")
    if not merged.get("storage") and candidate.get("storage"):
        merged["storage"] = candidate.get("storage")
    if candidate.get("implicit_passthrough"):
        merged["implicit_passthrough"] = True
    if "is_signed" not in merged and "is_signed" in candidate:
        merged["is_signed"] = candidate.get("is_signed")
    return merged

def _impl__condition_looks_like_stack_protector_guard(self, condition: Condition) -> bool:
    compared = self._extract_stack_protector_compare_pair(condition)
    if compared is None:
        return False
    left, right = compared
    return self._reads_share_stack_protector_probe(left, right)

def _impl__extract_stack_protector_compare_pair(
    self,
    condition: Optional[Condition],
) -> Optional[Tuple[Expression, Expression]]:
    if condition is None:
        return None

    decomposed = self._decompose_comparison_condition(condition)
    if decomposed is None:
        return None

    _negated, operator, left, right = decomposed
    if operator in {"INT_NOTEQUAL", "INT_EQUAL"}:
        if self._is_zero_constant(right):
            pair = self._extract_difference_pair(left)
            if pair is not None:
                return pair
        if self._is_zero_constant(left):
            pair = self._extract_difference_pair(right)
            if pair is not None:
                return pair
        return left, right
    return None

def _impl__extract_difference_pair(
    self,
    expr: Optional[Expression],
) -> Optional[Tuple[Expression, Expression]]:
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return None
    if expr.operator != "INT_SUB":
        return None
    return expr.operands[0], expr.operands[1]

def _impl__is_zero_constant(self, expr: Optional[Expression]) -> bool:
    return (
        expr is not None
        and expr.expr_type == ExpressionType.CONSTANT
        and int(expr.value) == 0
    )

def _impl__reads_share_stack_protector_probe(
    self,
    left: Expression,
    right: Expression,
) -> bool:
    left_probe = self._extract_stack_protector_memory_probe(left)
    right_probe = self._extract_stack_protector_memory_probe(right)
    if left_probe is None or right_probe is None:
        return False

    left_base_key, left_disp, left_deref_depth, left_size = left_probe
    right_base_key, right_disp, right_deref_depth, right_size = right_probe
    if left_size != right_size:
        return False
    if left_base_key != right_base_key or left_disp != right_disp:
        return False
    return {left_deref_depth, right_deref_depth} == {0, 1}

def _impl__extract_indirect_probe(
    self,
    expr: Optional[Expression],
) -> Optional[Tuple[StructuralKey, int, int]]:
    if expr is None:
        return None

    current = expr
    while (
        current.expr_type == ExpressionType.UNARY_OP
        and current.operator in {"INT_ZEXT", "INT_SEXT", "INT_2COMP"}
        and current.operands
    ):
        current = current.operands[0]

    if current.expr_type != ExpressionType.BINARY_OP or len(current.operands) != 2:
        return None
    if current.operator not in {"INDIRECT", "PTRADD", "PTRSUB", "INT_ADD"}:
        return None

    left, right = current.operands
    displacement = self._constant_int_value(right)
    base_expr = left
    if displacement is None:
        displacement = self._constant_int_value(left)
        base_expr = right
    if displacement is None:
        return None

    deref_depth = 0
    while base_expr.expr_type == ExpressionType.MEMORY and base_expr.operands:
        deref_depth += 1
        base_expr = base_expr.operands[0]

    return (
        ConditionNormalizer.expression_signature(
            base_expr,
            include_memory_read_order=False,
        ),
        displacement,
        deref_depth,
    )

def _impl__constant_int_value(self, expr: Optional[Expression]) -> Optional[int]:
    if expr is None or expr.expr_type != ExpressionType.CONSTANT:
        return None
    try:
        return int(expr.value)
    except (TypeError, ValueError):
        return None

def _impl__prove_single_guard_nonprogress_region_must_diverge(
    self,
    high_function,
    analysis: FunctionReturnAnalysis,
    *,
    divergence_guard: Condition,
    param: Expression,
) -> Optional[Dict[str, Any]]:
    if high_function is None or divergence_guard is None:
        return None
    if expression_contains_unsupported_smt_ops(getattr(divergence_guard, "expression", None)):
        self._debug_print("Outcome loop divergence proof declined: unsupported divergence guard")
        return None
    if not (
        self._conditions_equivalent([divergence_guard], [self._signed_positive_condition(param)])
        or self._condition_is_signed_positive_of_param(divergence_guard, param)
    ):
        self._debug_print("Outcome loop divergence proof declined: divergence guard is not param positive")
        return None

    blocks = list(self._iter_high_basic_blocks(high_function))
    if not blocks:
        self._debug_print("Outcome loop divergence proof declined: no high-function blocks")
        return None
    if not self._high_function_has_cfg_cycle(high_function):
        self._debug_print("Outcome loop divergence proof declined: no CFG cycle")
        return None

    tracer = None
    if self.program is not None:
        try:
            tracer = self._make_tracer(high_function)
        except Exception:
            tracer = None
    cyclic_sccs = self._high_function_cyclic_sccs(blocks)
    if not cyclic_sccs:
        self._debug_print("Outcome loop divergence proof declined: no cyclic SCC")
        return None

    for scc in cyclic_sccs:
        proof = self._prove_scc_must_diverge_under_guard(
            scc,
            all_blocks=blocks,
            divergence_guard=divergence_guard,
            param=param,
            tracer=tracer,
        )
        if proof is not None:
            cfg_blocks = tuple(sorted(
                (self._block_debug_key(block) for block in blocks), key=repr
            ))
            cfg_edges = tuple(sorted((
                (self._block_debug_key(block), self._block_debug_key(successor))
                for block in blocks
                for successor in self._block_successors(block)
            ), key=repr))
            proof.update(
                {
                    "proof_kind": "single_guard_nonprogress_must_diverge",
                    "candidate_rule": "side_effect_free_nonprogress_loop_guard_complement",
                    "guard": "param_positive",
                    "return_partition": "param_nonpositive_return_zero",
                    "cfg_applicability_surface": (cfg_blocks, cfg_edges),
                }
            )
            return proof
    return None

def _impl__prove_scc_must_diverge_under_guard(
    self,
    scc: Sequence[Any],
    *,
    all_blocks: Sequence[Any],
    divergence_guard: Condition,
    param: Expression,
    tracer: Optional[PcodeTracer],
) -> Optional[Dict[str, Any]]:
    scc_set = set(scc or ())
    scc_keys = {self._block_debug_key(block) for block in scc_set}
    if not scc_set:
        return None
    if any(self._block_has_return_op(block) for block in scc_set):
        self._debug_print("Outcome loop divergence proof declined: RETURN in candidate SCC")
        return None
    if any(self._block_writes_outcome_guard_state(block) for block in scc_set):
        self._debug_print("Outcome loop divergence proof declined: guard state write in SCC")
        return None
    if not self._scc_preserves_guard_dependencies(scc_set):
        self._debug_print("Outcome loop divergence proof declined: guard dependency is redefined in SCC")
        return None

    internal_guarded_continue = False
    internal_unconditional_continue = False
    exit_proofs = []
    for block in scc_set:
        for successor in self._block_successors(block):
            if self._block_debug_key(successor) in scc_keys:
                edge_condition = self._edge_condition_for_successor(block, successor, tracer)
                if edge_condition is None:
                    internal_unconditional_continue = True
                elif self._single_guard_condition_matches(edge_condition, divergence_guard, param):
                    internal_guarded_continue = True
                continue

            edge_condition = self._edge_condition_for_successor(block, successor, tracer)
            if edge_condition is None:
                self._debug_print("Outcome loop divergence proof declined: SCC exit without edge guard")
                return None
            if not self._single_guard_conditions_are_contradictory(divergence_guard, edge_condition, param):
                self._debug_print(
                    "Outcome loop divergence proof declined: SCC exit is feasible under divergence guard "
                    f"(divergence={divergence_guard.to_string()}, exit={edge_condition.to_string()})"
                )
                return None
            exit_proofs.append(
                {
                    "source": self._block_debug_key(block),
                    "target": self._block_debug_key(successor),
                    "guard_relation": "divergence_guard_and_exit_guard_unsat",
                }
            )

    entry_proofs = []
    has_guarded_entry = False
    has_unconditional_entry = False
    for block in all_blocks or ():
        if self._block_debug_key(block) in scc_keys:
            continue
        for successor in self._block_successors(block):
            if self._block_debug_key(successor) not in scc_keys:
                continue
            edge_condition = self._edge_condition_for_successor(block, successor, tracer)
            if edge_condition is None:
                if self._block_predecessor_count(block) != 0:
                    self._debug_print("Outcome loop divergence proof declined: unconditional SCC entry is not from function entry")
                    return None
                has_unconditional_entry = True
                entry_proofs.append(
                    {
                        "source": self._block_debug_key(block),
                        "target": self._block_debug_key(successor),
                        "guard_relation": "unconditional_entry_then_internal_guard",
                    }
                )
            elif self._single_guard_condition_matches(edge_condition, divergence_guard, param):
                has_guarded_entry = True
                entry_proofs.append(
                    {
                        "source": self._block_debug_key(block),
                        "target": self._block_debug_key(successor),
                        "guard_relation": "entry_guard_equivalent_to_divergence_guard",
                    }
                )
            else:
                self._debug_print(
                    "Outcome loop divergence proof declined: SCC entry guard does not match divergence guard "
                    f"(divergence={divergence_guard.to_string()}, entry={edge_condition.to_string()})"
                )
                return None

    if not has_guarded_entry and not has_unconditional_entry:
        self._debug_print("Outcome loop divergence proof declined: candidate SCC has no proved external entry")
        return None
    if has_guarded_entry:
        preservation_ok = internal_unconditional_continue or internal_guarded_continue
    elif has_unconditional_entry:
        preservation_ok = internal_guarded_continue
    else:
        preservation_ok = False
    if not preservation_ok:
        self._debug_print("Outcome loop divergence proof declined: no guarded/invariant-preserving continue edge")
        return None

    return {
        "scc_blocks": [self._block_debug_key(block) for block in scc_set],
        "entry_edges": entry_proofs,
        "exit_edges": exit_proofs,
        "side_effect_control_safety": {
            "forbidden_ops_absent": True,
            "return_ops_absent_in_scc": True,
            "guard_state_writes_absent": True,
        },
        "invariant_preservation": {
            "internal_guarded_continue": internal_guarded_continue,
            "internal_unconditional_continue": internal_unconditional_continue,
        },
    }

def _impl__high_function_cyclic_sccs(self, blocks: Sequence[Any]) -> List[Tuple[Any, ...]]:
    key_to_block = {self._block_debug_key(block): block for block in blocks or ()}
    block_keys = set(key_to_block)
    index_counter = 0
    stack: List[Any] = []
    on_stack: Set[Any] = set()
    indices: Dict[Any, int] = {}
    lowlinks: Dict[Any, int] = {}
    components: List[Tuple[Any, ...]] = []

    def strongconnect(block_key) -> None:
        nonlocal index_counter
        indices[block_key] = index_counter
        lowlinks[block_key] = index_counter
        index_counter += 1
        stack.append(block_key)
        on_stack.add(block_key)

        for successor in self._block_successors(key_to_block[block_key]):
            successor_key = self._block_debug_key(successor)
            if successor_key not in block_keys:
                continue
            if successor_key not in indices:
                strongconnect(successor_key)
                lowlinks[block_key] = min(lowlinks[block_key], lowlinks[successor_key])
            elif successor_key in on_stack:
                lowlinks[block_key] = min(lowlinks[block_key], indices[successor_key])

        if lowlinks[block_key] != indices[block_key]:
            return
        component = []
        while stack:
            current = stack.pop()
            on_stack.remove(current)
            component.append(current)
            if current == block_key:
                break
        component_set = set(component)
        if len(component) > 1 or any(
            self._block_debug_key(successor) in component_set
            for item in component
            for successor in self._block_successors(key_to_block[item])
        ):
            components.append(tuple(key_to_block[item] for item in component))

    for block in blocks or ():
        key = self._block_debug_key(block)
        if key not in indices:
            strongconnect(key)
    return components

def _impl__scc_preserves_guard_dependencies(self, scc_set: Set[Any]) -> bool:
    guard_dependency_keys: Set[Tuple[Any, ...]] = set()
    for block in scc_set:
        cbranch = self._first_high_block_cbranch(block)
        if cbranch is None:
            continue
        if getattr(cbranch, "condition_expr", None) is not None and not callable(getattr(cbranch, "getInput", None)):
            continue
        try:
            if int(getattr(cbranch, "getNumInputs", lambda: 0)() or 0) < 2:
                return False
            condition_varnode = cbranch.getInput(1)
        except Exception:
            return False
        if not self._collect_guard_dependency_varnodes(
            condition_varnode,
            guard_dependency_keys,
            is_root=True,
            seen=set(),
        ):
            return False

    if not guard_dependency_keys:
        return True

    for block in scc_set:
        for op in self._iter_high_block_ops(block):
            output = getattr(op, "getOutput", lambda: None)()
            if output is None:
                continue
            output_key = self._varnode_guard_dependency_key(output)
            if output_key in guard_dependency_keys:
                return False
    return True

def _impl__collect_guard_dependency_varnodes(
    self,
    varnode,
    guard_dependency_keys: Set[Tuple[Any, ...]],
    *,
    is_root: bool,
    seen: Set[Tuple[Any, ...]],
) -> bool:
    if varnode is None:
        return False
    key = self._varnode_guard_dependency_key(varnode)
    if key in seen:
        return True
    seen.add(key)

    is_constant = getattr(varnode, "isConstant", lambda: False)
    try:
        if callable(is_constant) and is_constant():
            return True
    except Exception:
        return False

    try:
        def_op = varnode.getDef()
    except Exception:
        return False
    if def_op is None:
        guard_dependency_keys.add(key)
        return True

    if not is_root:
        guard_dependency_keys.add(key)

    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    if mnemonic not in {
        "COPY",
        "CAST",
        "SUBPIECE",
        "INT_ZEXT",
        "INT_SEXT",
        "INT_EQUAL",
        "INT_NOTEQUAL",
        "INT_LESS",
        "INT_SLESS",
        "INT_LESSEQUAL",
        "INT_SLESSEQUAL",
        "BOOL_NEGATE",
        "BOOL_AND",
        "BOOL_OR",
        "BOOL_XOR",
    }:
        return False

    try:
        input_count = int(getattr(def_op, "getNumInputs", lambda: 0)() or 0)
    except Exception:
        return False
    for index in range(input_count):
        try:
            child = def_op.getInput(index)
        except Exception:
            return False
        if not self._collect_guard_dependency_varnodes(
            child,
            guard_dependency_keys,
            is_root=False,
            seen=seen,
        ):
            return False
    return True

def _impl__varnode_guard_dependency_key(self, varnode) -> Tuple[Any, ...]:
    try:
        address = varnode.getAddress()
        offset = getattr(address, "getOffset", lambda: None)()
        space = getattr(getattr(address, "getAddressSpace", lambda: None)(), "getName", lambda: None)()
        size = getattr(varnode, "getSize", lambda: None)()
        if offset is not None and size is not None:
            return ("varnode", space, int(offset), int(size))
    except Exception:
        pass
    return ("varnode_object", id(varnode))

def _impl__edge_condition_for_successor(
    self,
    block,
    successor,
    tracer: Optional[PcodeTracer],
) -> Optional[Condition]:
    edge_conditions = getattr(block, "_edge_conditions", None)
    if isinstance(edge_conditions, Mapping):
        for key in (successor, id(successor), self._block_debug_key(successor)):
            condition = edge_conditions.get(key)
            if condition is not None:
                return condition

    cbranch = self._first_high_block_cbranch(block)
    if cbranch is None:
        return None
    expr = getattr(cbranch, "condition_expr", None)
    if expr is None:
        if tracer is None:
            return None
        try:
            if int(getattr(cbranch, "getNumInputs", lambda: 0)() or 0) < 2:
                return None
            expr = tracer.trace_varnode(cbranch.getInput(1), use_cache=False)
        except Exception:
            return None
    if expr is None or expression_contains_unsupported_smt_ops(expr):
        return None

    true_out = getattr(block, "getTrueOut", lambda: None)()
    false_out = getattr(block, "getFalseOut", lambda: None)()
    if true_out is not None and self._same_high_block(true_out, successor):
        return Condition(expr, False)
    if false_out is not None and self._same_high_block(false_out, successor):
        return Condition(expr, True)
    relation = self._direct_cbranch_successor_relation(cbranch, block, successor)
    if relation == "true":
        return Condition(expr, False)
    if relation == "false":
        return Condition(expr, True)
    return None

def _impl__address_like_keys(
    self,
    value,
    *,
    default_space: Optional[str] = None,
) -> Set[Tuple[str, int]]:
    if value is None:
        return set()
    keys: Set[Tuple[str, int]] = set()
    try:
        is_constant = getattr(value, "isConstant", lambda: False)
        if callable(is_constant) and is_constant():
            address = getattr(value, "getAddress", lambda: None)()
            offset = None
            if address is not None:
                offset = getattr(address, "getOffset", lambda: None)()
            if offset is None:
                try:
                    offset = int(value)
                except Exception:
                    offset = None
            if default_space and offset is not None:
                keys.add((str(default_space), int(offset)))
            return keys
    except Exception:
        return set()
    try:
        offset = getattr(value, "getOffset", lambda: None)()
        if offset is not None:
            space_name = self._address_space_name(value)
            if space_name:
                keys.add((space_name, int(offset)))
    except Exception:
        pass
    try:
        address = getattr(value, "getAddress", lambda: None)()
        if address is not None and address is not value:
            keys.update(self._address_like_keys(address, default_space=default_space))
    except Exception:
        pass
    return keys

def _impl__address_space_name(self, address) -> Optional[str]:
    try:
        space = getattr(address, "getAddressSpace", lambda: None)()
        name = getattr(space, "getName", lambda: None)()
        if name is None:
            return None
        return str(name)
    except Exception:
        return None

def _impl__conditions_are_unsat(self, conditions: Sequence[Condition]) -> bool:
    return ConditionSMTOracle.conjunction_is_unsat(list(conditions or ())) is True

def _impl__single_guard_condition_matches(
    self,
    condition: Condition,
    divergence_guard: Condition,
    param: Expression,
) -> bool:
    return (
        condition.equals(divergence_guard)
        or self._conditions_equivalent([condition], [divergence_guard])
        or (
            self._condition_is_signed_positive_of_param(condition, param)
            and self._condition_is_signed_positive_of_param(divergence_guard, param)
        )
    )

def _impl__single_guard_conditions_are_contradictory(
    self,
    divergence_guard: Condition,
    edge_condition: Condition,
    param: Expression,
) -> bool:
    return (
        edge_condition.equals(divergence_guard.negate())
        or self._conditions_are_unsat([divergence_guard, edge_condition])
        or (
            self._condition_is_signed_positive_of_param(divergence_guard, param)
            and self._condition_is_signed_nonpositive_of_param(edge_condition, param)
        )
    )

def _impl__tuple_field_from_structural_proof(
    proof: Tuple[Any, ...],
    field_name: str,
) -> Tuple[Any, ...]:
    for item in proof or ():
        if isinstance(item, tuple) and len(item) == 2 and item[0] == field_name:
            value = item[1]
            return tuple(value) if isinstance(value, (tuple, list)) else (value,)
    return ()

def _impl__field_value_from_structural_proof(
    proof: Tuple[Any, ...],
    field_name: str,
) -> Any:
    for item in proof or ():
        if isinstance(item, tuple) and len(item) == 2 and item[0] == field_name:
            return item[1]
    return None

def _impl__condition_identity_key(condition: Condition) -> Tuple[Any, ...]:
    return (
        "condition",
        expression_key_safe(getattr(condition, "expression", None)),
        bool(getattr(condition, "negated", False)),
    )

def _impl__conditional_progress_guard_keys_from_structural_proof(
    self,
    proof: Tuple[Any, ...],
) -> Dict[int, Tuple[Any, ...]]:
    result: Dict[int, Tuple[Any, ...]] = {}
    for item in self._tuple_field_from_structural_proof(proof, "conditional_progress_guard_keys"):
        if not isinstance(item, tuple) or len(item) != 2:
            continue
        index, key = item
        if not isinstance(key, tuple):
            continue
        try:
            result[int(index)] = key
        except Exception:
            continue
    return result

def _impl__condition_for_identity_key(
    self,
    key: Tuple[Any, ...],
    conditions: Sequence[Condition],
) -> Optional[Condition]:
    if not isinstance(key, tuple):
        return None
    for condition in conditions or ():
        if condition is not None and self._condition_identity_key(condition) == key:
            return condition
    return None

def _impl__conditional_progress_guards_contradict_invariant(
    self,
    guard_keys: Dict[int, Tuple[Any, ...]],
    *,
    target_conditions: Sequence[Condition],
    invariant_conditions: Sequence[Condition],
) -> bool:
    if not guard_keys:
        return False
    for guard_key in guard_keys.values():
        guard = self._condition_for_identity_key(guard_key, target_conditions)
        if guard is None:
            return False
        try:
            if ConditionSMTOracle.conjunction_is_unsat([guard] + list(invariant_conditions or ())) is not True:
                return False
        except Exception:
            return False
    return True

def _impl__conditions_have_contradictory_pair(
    self,
    left: Sequence[Condition],
    right: Sequence[Condition],
) -> bool:
    for left_condition in left or ():
        if left_condition is None:
            continue
        for right_condition in right or ():
            if right_condition is None:
                continue
            if (
                left_condition.negate().equals(right_condition)
                or right_condition.negate().equals(left_condition)
                or ConditionNormalizer.are_equivalent(left_condition.negate(), right_condition)
                or ConditionNormalizer.are_equivalent(right_condition.negate(), left_condition)
            ):
                return True
            try:
                if ConditionSMTOracle.conjunction_is_unsat([left_condition, right_condition]) is True:
                    return True
            except Exception:
                continue
    return False

def _impl__varnodes_same_storage(self, left, right) -> bool:
    if left is None or right is None:
        return False
    try:
        left_addr = left.getAddress()
        right_addr = right.getAddress()
        left_space = left_addr.getAddressSpace().getName()
        right_space = right_addr.getAddressSpace().getName()
        return (
            left_space == right_space
            and int(left_addr.getOffset()) == int(right_addr.getOffset())
            and int(left.getSize()) == int(right.getSize())
        )
    except Exception:
        return False

def _impl__pcode_op_input_def_reaches_phi(
    self,
    op,
    target_phi_key: Tuple[Any, ...],
    *,
    max_depth: int,
) -> bool:
    seen: Set[int] = set()

    def visit_varnode(varnode, depth: int) -> bool:
        if varnode is None or depth > int(max_depth):
            return False
        marker = id(varnode)
        if marker in seen:
            return False
        seen.add(marker)
        try:
            def_op = varnode.getDef()
        except Exception:
            def_op = None
        if def_op is None:
            return False
        if self._pcode_op_stable_key(def_op) == target_phi_key:
            return True
        try:
            input_count = int(def_op.getNumInputs())
        except Exception:
            input_count = 0
        for index in range(input_count):
            try:
                if visit_varnode(def_op.getInput(index), depth + 1):
                    return True
            except Exception:
                continue
        return False

    try:
        input_count = int(op.getNumInputs())
    except Exception:
        input_count = 0
    for index in range(input_count):
        try:
            if visit_varnode(op.getInput(index), 0):
                return True
        except Exception:
            continue
    return False

def _impl__pcode_op_stable_key(self, op) -> Optional[Tuple[Any, ...]]:
    op_ref = PcodeOpRef.from_pcode_op(
        op,
        binary_id=self._binary_id,
        program_uid=self._program_identity(),
        function_entry=self._current_function_entry_address(),
    )
    if op_ref is None:
        return None
    try:
        return op_ref.stable_key()
    except Exception:
        return None

def _impl__phi_circular_origin_stable_keys(self, expr: Optional[Expression]) -> Set[Tuple[Any, ...]]:
    keys: Set[Tuple[Any, ...]] = set()
    for node in _iter_expression_nodes(expr):
        if getattr(node, "expr_type", None) != ExpressionType.UNKNOWN:
            continue
        if not self._expression_contains_phi_circular_marker(node):
            continue
        runtime_ref = getattr(node, "runtime_ref", None)
        origin_ref = getattr(runtime_ref, "origin_ref", None)
        stable_key = getattr(origin_ref, "stable_key", None)
        if callable(stable_key):
            try:
                key = stable_key()
            except Exception:
                key = None
            if isinstance(key, tuple):
                keys.add(key)
    return keys

def _impl__candidate_phi_origin_keys_from_summary_source_key(self, value) -> Set[Tuple[Any, ...]]:
    keys: Set[Tuple[Any, ...]] = set()
    if not isinstance(value, tuple):
        return keys
    for item in value:
        if (
            isinstance(item, tuple)
            and len(item) == 2
            and item[0] == "candidate_phi_origin_keys"
        ):
            raw_keys = item[1]
            for raw_key in tuple(raw_keys or ()):
                if isinstance(raw_key, tuple):
                    keys.add(raw_key)
            continue
        if isinstance(item, tuple):
            keys.update(self._candidate_phi_origin_keys_from_summary_source_key(item))
    return keys

def _impl__expression_is_placeholder_plus_one(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
) -> bool:
    return self._expression_is_placeholder_plus_constant(expr, placeholder, 1)

def _impl__expression_is_placeholder_minus_one(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
) -> bool:
    return self._expression_is_placeholder_plus_constant(expr, placeholder, -1)

def _impl__expression_is_placeholder_plus_one_under_conditions(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
    conditions: Sequence[Condition],
) -> bool:
    if self._expression_is_placeholder_plus_one(expr, placeholder):
        return True
    if self._expression_is_placeholder_plus_unit_condition(expr, placeholder, conditions):
        return True
    expected = Expression.binary_op(
        "INT_ADD",
        placeholder,
        Expression.constant(1, size=max(1, int(getattr(placeholder, "size", 0) or 4))),
    )
    expected.size = max(1, int(getattr(placeholder, "size", 0) or 4))
    return self._expressions_equal_under_conditions_smt(
        expr,
        expected,
        tuple(conditions or ()),
        getattr(self, "_current_parameters", ()) or (),
    )

def _impl__expression_is_placeholder_minus_one_under_conditions(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
    conditions: Sequence[Condition],
) -> bool:
    if self._expression_is_placeholder_minus_one(expr, placeholder):
        return True
    if self._expression_is_placeholder_minus_one_unit_condition(expr, placeholder, conditions):
        return True
    expected = Expression.binary_op(
        "INT_SUB",
        placeholder,
        Expression.constant(1, size=max(1, int(getattr(placeholder, "size", 0) or 4))),
    )
    expected.size = max(1, int(getattr(placeholder, "size", 0) or 4))
    return self._expressions_equal_under_conditions_smt(
        expr,
        expected,
        tuple(conditions or ()),
        getattr(self, "_current_parameters", ()) or (),
    )

def _impl__expression_is_placeholder_plus_zero_under_conditions(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
    conditions: Sequence[Condition],
) -> bool:
    current = self._strip_transparent_unary(expr)
    if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
        return False
    if getattr(current, "operator", None) not in {"INT_ADD", "INT_SUB"}:
        return False
    operands = tuple(getattr(current, "operands", ()) or ())
    if len(operands) != 2:
        return False
    left, right = operands
    if self._expressions_same_key(left, placeholder):
        delta = right
        if getattr(current, "operator", None) == "INT_ADD":
            return self._expression_is_zero_under_conditions(delta, conditions)
        return self._expression_is_zero_under_conditions(delta, conditions)
    if getattr(current, "operator", None) == "INT_ADD" and self._expressions_same_key(right, placeholder):
        return self._expression_is_zero_under_conditions(left, conditions)
    return False

def _impl__expression_is_zero_under_conditions(
    self,
    expr: Optional[Expression],
    conditions: Sequence[Condition],
) -> bool:
    if self._constant_int_value(expr) == 0:
        return True
    current = self._strip_transparent_unary(expr)
    if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
        return False
    as_condition = Condition(current, False)
    if self._conditions_imply(tuple(conditions or ()), (as_condition.negate(),)):
        return True
    operator = getattr(current, "operator", None)
    operands = tuple(getattr(current, "operands", ()) or ())
    if len(operands) != 2:
        return False
    if operator == "INT_SLESS":
        left, right = operands
        if self._constant_int_value(right) == 1 and getattr(left, "expr_type", None) == ExpressionType.PARAMETER:
            if any(
                self._condition_is_signed_positive_of_param(condition, left)
                for condition in conditions or ()
            ):
                return True
    if operator == "INT_SUB":
        left, right = operands
        if self._expression_is_one_under_conditions(left, conditions) and self._constant_int_value(right) == 1:
            return True
    return self._expressions_equal_under_conditions_smt(
        current,
        Expression.constant(0, size=max(1, int(getattr(current, "size", 0) or 4))),
        tuple(conditions or ()),
        getattr(self, "_current_parameters", ()) or (),
    )

def _impl__expression_is_placeholder_minus_one_unit_condition(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
    conditions: Sequence[Condition],
) -> bool:
    return self._placeholder_minus_one_unit_condition_guard_key(expr, placeholder, conditions) is not None

def _impl__placeholder_minus_one_unit_condition_guard_key(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
    conditions: Sequence[Condition],
) -> Optional[Tuple[Any, ...]]:
    current = self._strip_transparent_unary(expr)
    if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    if getattr(current, "operator", None) == "INT_ADD":
        operands = tuple(getattr(current, "operands", ()) or ())
        if len(operands) != 2:
            return None
        left, right = operands
        if self._expressions_same_key(left, placeholder):
            return self._negated_unit_condition_key_for_expression(right, conditions)
        if self._expressions_same_key(right, placeholder):
            return self._negated_unit_condition_key_for_expression(left, conditions)
        return None
    if getattr(current, "operator", None) != "INT_SUB":
        return None
    operands = tuple(getattr(current, "operands", ()) or ())
    if len(operands) != 2:
        return None
    if not self._expressions_same_key(operands[0], placeholder):
        return None
    return (
        self._unit_condition_key_for_expression(operands[1], conditions)
        or self._negated_unit_condition_key_for_expression(operands[1], conditions)
    )

def _impl__expression_is_placeholder_plus_unit_condition(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
    conditions: Sequence[Condition],
) -> bool:
    return self._placeholder_plus_unit_condition_guard_key(expr, placeholder, conditions) is not None

def _impl__placeholder_plus_unit_condition_guard_key(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
    conditions: Sequence[Condition],
) -> Optional[Tuple[Any, ...]]:
    current = self._strip_transparent_unary(expr)
    if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    if getattr(current, "operator", None) != "INT_ADD":
        return None
    operands = tuple(getattr(current, "operands", ()) or ())
    if len(operands) != 2:
        return None
    left, right = operands
    if self._expressions_same_key(left, placeholder):
        return self._unit_condition_key_for_expression(right, conditions)
    if self._expressions_same_key(right, placeholder):
        return self._unit_condition_key_for_expression(left, conditions)
    return None

def _impl__unit_condition_key_for_expression(
    self,
    expr: Optional[Expression],
    conditions: Sequence[Condition],
) -> Optional[Tuple[Any, ...]]:
    current = self._strip_transparent_unary(expr)
    if current is None:
        return None
    for condition in conditions or ():
        if condition is None:
            continue
        if self._expression_is_one_under_conditions(current, (condition,)):
            return self._condition_identity_key(condition)
    return None

def _impl__negated_unit_condition_key_for_expression(
    self,
    expr: Optional[Expression],
    conditions: Sequence[Condition],
) -> Optional[Tuple[Any, ...]]:
    current = self._strip_transparent_unary(expr)
    if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    if getattr(current, "operator", None) != "INT_SUB":
        return None
    operands = tuple(getattr(current, "operands", ()) or ())
    if len(operands) != 2 or self._constant_int_value(operands[1]) != 1:
        return None
    flag_expr = self._strip_transparent_unary(operands[0])
    if flag_expr is None:
        return None
    for condition in conditions or ():
        if condition is None:
            continue
        if self._expression_is_zero_under_conditions(flag_expr, (condition,)) and self._expression_is_one_under_conditions(
            flag_expr,
            (condition.negate(),),
        ):
            return self._condition_identity_key(condition)
    return None

def _impl__strip_transparent_unary(expr: Optional[Expression]) -> Optional[Expression]:
    current = expr
    while (
        current is not None
        and getattr(current, "expr_type", None) == ExpressionType.UNARY_OP
        and getattr(current, "operator", None) in {"COPY", "CAST", "SUBPIECE", "INT_ZEXT", "INT_SEXT"}
        and len(tuple(getattr(current, "operands", ()) or ())) == 1
    ):
        current = tuple(getattr(current, "operands", ()) or ())[0]
    return current

def _impl__expression_is_placeholder_plus_constant(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
    constant: int,
) -> bool:
    current = expr
    while (
        current is not None
        and getattr(current, "expr_type", None) == ExpressionType.UNARY_OP
        and getattr(current, "operator", None) in {"COPY", "CAST", "SUBPIECE", "INT_ZEXT", "INT_SEXT"}
        and len(tuple(getattr(current, "operands", ()) or ())) == 1
    ):
        current = tuple(getattr(current, "operands", ()) or ())[0]
    if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
        return False
    operands = tuple(getattr(current, "operands", ()) or ())
    if len(operands) != 2:
        return False
    operator = getattr(current, "operator", None)
    left, right = operands
    if operator == "INT_ADD":
        if self._expressions_same_key(left, placeholder) and self._constant_int_value(right) == constant:
            return True
        if self._expressions_same_key(right, placeholder) and self._constant_int_value(left) == constant:
            return True
        wrapped = self._constant_int_value(right)
        if self._expressions_same_key(left, placeholder) and wrapped is not None:
            return self._signed_unit_constant_matches(wrapped, constant, getattr(current, "size", None))
    if operator == "INT_SUB":
        if self._expressions_same_key(left, placeholder) and self._constant_int_value(right) == -constant:
            return True
    return False
