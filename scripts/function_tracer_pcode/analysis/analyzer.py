# -*- coding: utf-8 -*-
"""Return解析メインモジュール（符号性検出統合版）"""

import re
from contextlib import contextmanager
from typing import Iterable, List, Dict, Optional, Any, Set, Tuple, cast

from ..model.expression import Expression, ExpressionType, Condition
from ..model.storage import StorageInfo
from ..model.analysis import DeferredCallInfo, ReturnInfo, FunctionReturnAnalysis, SignednessResult
from ..config.settings import (
    BOUNDED_CALL_MAX_CASES,
    BOUNDED_CALL_REFINEMENT_ENABLED,
    BOUNDED_CALL_UNROLL_LIMIT,
)
from . import PcodeTracer
from .bounded_refinement import BoundedCallRefiner
from .condition import ConditionTracker, ConditionSimplifier, ConditionNormalizer
from .debug import summarize_expression
from .signedness import SignednessDetector
from .effect_summary import (
    EffectSummary,
    _expressions_equivalent,
    _expressions_equivalent_under_conditions,
    _enumerate_constant_expression_branches,
    _resolve_call_target_name,
    _reduce_expression_under_conditions,
    expression_contains_synthetic_location_reads,
    lower_post_state_expression_for_smt,
    normalize_post_state_expression,
    summarize_store_effects,
    substitute_condition,
    substitute_expression,
)
from .memory_resolver import concretize_readonly_loads
from .recurrence_summary import StructuralRecurrenceSummarizer


class ReturnAnalyzer:
    """関数のReturn値を解析"""

    _KNOWN_NORETURN_NAME_FRAGMENTS = (
        "stack_chk_fail",
        "fortify_fail",
        "assert_fail",
        "abort",
        "panic",
        "fatal",
    )
    _KNOWN_STACK_PROTECTOR_NAME_FRAGMENTS = (
        "stack_chk_guard",
        "stack_chk_fail",
        "fortify_fail",
    )
    
    def __init__(self, program, debug: bool = False):
        self.program = program
        self.debug = debug
        self._decompiler = None
        self._current_parameters: List[Dict] = []
        self._current_effect_summary: Optional[EffectSummary] = None
        self._effect_summary_cache: Dict[str, Any] = {}
        self._effect_summary_parameter_cache: Dict[str, List[Dict]] = {}
        self._call_analysis_cache: Dict[str, Optional[FunctionReturnAnalysis]] = {}
        self._local_target_cache: Dict[int, Optional[List[Any]]] = {}
        self._current_deferred_calls: Dict[str, DeferredCallInfo] = {}
        self._deferred_call_counter: int = 0
        self._analysis_in_progress: Dict[str, FunctionReturnAnalysis] = {}
        self._bounded_call_refinement_enabled = bool(BOUNDED_CALL_REFINEMENT_ENABLED)
        self._bounded_call_unroll_limit = int(BOUNDED_CALL_UNROLL_LIMIT)
        self._bounded_call_max_cases = int(BOUNDED_CALL_MAX_CASES)
        self._last_function_lookup_error: Optional[str] = None
        self._last_structured_reduction_failure: Optional[Dict[str, Any]] = None
    
    def _debug_print(self, msg: str, indent: int = 0):
        if self.debug:
            prefix = "  " * indent
            print(f"{prefix}[ReturnAnalyzer] {msg}")

    def _debug_expr_summary(self, expr: Optional[Expression], max_depth: int = 4) -> str:
        return summarize_expression(expr, max_depth=max_depth)

    def _record_structured_reduction_failure(
        self,
        body_lines: List[str],
        index: int,
        reason: str,
        detail: Optional[str] = None,
    ) -> None:
        if self._last_structured_reduction_failure is not None:
            return
        line = None
        if 0 <= index < len(body_lines):
            line = body_lines[index]
        self._last_structured_reduction_failure = {
            "index": index,
            "line": line,
            "reason": reason,
            "detail": detail,
        }

    def _expression_contains_equivalent_subexpr(
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

    @contextmanager
    def _analysis_context(self, parameters: List[Dict], effect_summary: Optional[EffectSummary]):
        """Temporarily bind per-analysis state and restore the parent context on exit."""
        previous_parameters = self._current_parameters
        previous_effect_summary = self._current_effect_summary
        previous_deferred_calls = self._current_deferred_calls
        self._current_parameters = parameters
        self._current_effect_summary = effect_summary
        self._current_deferred_calls = {}
        try:
            yield
        finally:
            self._current_parameters = previous_parameters
            self._current_effect_summary = previous_effect_summary
            self._current_deferred_calls = previous_deferred_calls
    
    def _get_decompiler(self):
        if self._decompiler is None:
            from ghidra.app.decompiler import DecompInterface # type: ignore[import]
            self._decompiler = DecompInterface()
            self._decompiler.openProgram(self.program)
        return self._decompiler

    @contextmanager
    def _program_transaction(self, description: str):
        start_transaction = getattr(self.program, "startTransaction", None)
        end_transaction = getattr(self.program, "endTransaction", None)
        if not callable(start_transaction) or not callable(end_transaction):
            yield
            return

        tx_id = start_transaction(description)
        try:
            yield
            end_transaction(tx_id, True)
        except Exception:
            end_transaction(tx_id, False)
            raise
    
    def dispose(self):
        if self._decompiler is not None:
            try:
                self._decompiler.dispose()
            except Exception as exc:
                exc_text = str(exc).lower()
                if "jvm is not running" not in exc_text and "java virtual machine is not running" not in exc_text:
                    raise
            finally:
                self._decompiler = None
    
    def _dump_return_infos(self, analysis: FunctionReturnAnalysis):
        """
        ReturnInfo一覧をダンプ（デバッグ用）
        
        各ReturnInfoについて以下を出力：
        - branch_index（分岐識別子）
        - address（アドレス）
        - value（式の文字列表現とSMT表現）
        - conditions（簡約後の条件リスト）
        """
        if not self.debug:
            return
        
        self._debug_print("=" * 60)
        self._debug_print(f"ReturnInfo dump for {analysis.function_name}")
        self._debug_print(f"Total return candidates: {len(analysis.returns)}")
        self._debug_print("=" * 60)
        
        for i, ret_info in enumerate(analysis.returns):
            self._debug_print(f"[{i}] branch_index={ret_info.branch_index}")
            self._debug_print(f"    address: {ret_info.address}", 1)
            
            # 値の文字列表現
            try:
                value_str = self._debug_expr_summary(ret_info.value)
                self._debug_print(f"    value: {value_str}", 1)
            except Exception as e:
                self._debug_print(f"    value: (error converting to string: {e})", 1)
            
            # SMT表現（エラー時はスキップ）- 引数なし
            try:
                smt_str = ret_info.value.to_smt()
                # 長すぎる場合は切り詰め
                if len(smt_str) > 300:
                    smt_str = smt_str[:300] + "..."
                self._debug_print(f"    smt: {smt_str}", 1)
            except Exception as e:
                self._debug_print(f"    smt: (error: {e})", 1)
            
            # 条件リスト（簡約版）
            if ret_info.conditions:
                try:
                    cond_strs = [ConditionSimplifier.get_simplified_condition_string(c) 
                                for c in ret_info.conditions]
                    self._debug_print(f"    conditions({len(ret_info.conditions)}): {cond_strs}", 1)
                except Exception as e:
                    self._debug_print(f"    conditions: (error: {e})", 1)
            else:
                self._debug_print(f"    conditions: (unconditional/always)", 1)
        
        self._debug_print("=" * 60)
        
        # 条件カバレッジの簡易チェック
        self._check_condition_coverage(analysis)
    
    def _check_condition_coverage(self, analysis: FunctionReturnAnalysis):
        """
        条件カバレッジの簡易チェック
        
        各パラメータについて、正・負・ゼロのケースが存在するかをヒューリスティックに確認
        """
        if not self.debug or not analysis.returns:
            return
        
        self._debug_print("Condition coverage check:")
        
        # パラメータ名を収集
        param_names = [p.get('name', f'param_{i}') for i, p in enumerate(analysis.parameters)]
        
        if not param_names:
            return
        
        # 各パラメータについて、どのような条件が存在するか確認
        for param_name in param_names:
            has_zero_check = False
            has_positive_check = False
            has_negative_check = False
            
            for ret_info in analysis.returns:
                for cond in ret_info.conditions:
                    cond_str = cond.expression.to_string()
                    
                    # パラメータが条件に含まれるか
                    if param_name in cond_str:
                        # ゼロチェック
                        if "== 0" in cond_str or "!= 0" in cond_str:
                            has_zero_check = True
                        
                        # 符号チェック
                        if "< 0" in cond_str or "<= 0" in cond_str:
                            has_negative_check = True
                        if "> 0" in cond_str or ">= 0" in cond_str:
                            has_positive_check = True
            
            coverage_info = []
            if has_zero_check:
                coverage_info.append("zero")
            if has_positive_check:
                coverage_info.append("positive")
            if has_negative_check:
                coverage_info.append("negative")
            
            if coverage_info:
                self._debug_print(f"  {param_name}: {', '.join(coverage_info)} checks found", 1)
            else:
                self._debug_print(f"  {param_name}: no explicit checks", 1)
    
    def analyze_function(
        self,
        function,
        timeout: int = 60,
        active_functions: Optional[Set[str]] = None,
    ) -> Optional[FunctionReturnAnalysis]:
         # デバッグフラグを ConditionSimplifier に伝播
        from .condition import ConditionSimplifier
        ConditionSimplifier.DEBUG = self.debug
        ConditionSimplifier.reset_debug_state()
        
        active_functions = set(active_functions or set())
        active_functions.add(function.getName())

        self._debug_print("=" * 60)
        self._debug_print(f"Analyzing function: {function.getName()}")
        self._debug_print("=" * 60)
        
        decompiler = self._get_decompiler()
        results = decompiler.decompileFunction(function, timeout, None)
        
        if not results.decompileCompleted():
            self._debug_print("Decompilation failed!")
            return None
        
        high_function = results.getHighFunction()
        if high_function is None:
            self._debug_print("HighFunction is None!")
            return None
        
        # Step 1: tracer作成
        tracer = PcodeTracer(self.program, high_function, debug=self.debug)

        parameters = self._collect_parameters(high_function)
        parameters = self._augment_parameters_with_implicit_passthrough(
            parameters,
            tracer,
            active_functions,
        )
        with self._analysis_context(parameters, None):
            # Step 2: condition_tracker作成（まだビルドしない）
            condition_tracker = ConditionTracker(tracer)

            # Step 3: phi_handler作成 → tracerに注入
            from .phi_resolver import PhiHandler
            phi_handler = PhiHandler(tracer, condition_tracker)
            tracer.phi_handler = phi_handler

            # Step 4: ブロック情報構築（phi_handler準備後）
            condition_tracker.build()

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
            effect_summary = self._build_effect_summary(
                function,
                high_function,
                tracer,
                condition_tracker,
                parameters,
                active_functions={function.getName()},
            )
            self._current_effect_summary = effect_summary

            # 戻り値の型を取得
            return_type = self._get_return_type(high_function)
            self._debug_print(f"Return type: {return_type}")

            # === Phase 1: 符号性検出 ===
            signedness_result = self._detect_signedness(high_function)
            if signedness_result:
                self._debug_print(f"Inferred signedness: {signedness_result.signedness}")
                if self.debug:
                    self._debug_print(f"Evidence summary: {signedness_result.evidence_summary}")
                    self._debug_print(f"Opcode counts: {signedness_result.opcode_counts}")

            return_infos = []
            return_ops = tracer.find_return_ops()

            self._debug_print(f"Found {len(return_ops)} RETURN operations")

            for i, return_op in enumerate(return_ops):
                self._debug_print(f"--- Analyzing RETURN #{i + 1} ---")
                infos = self._analyze_return_op(
                    return_op,
                    tracer,
                    condition_tracker,
                    i,
                    current_function=function,
                    active_functions=active_functions,
                )
                return_infos.extend(infos)

            result = FunctionReturnAnalysis(
                function_name=function.getName(),
                entry_point=str(function.getEntryPoint()),
                parameters=parameters,
                returns=return_infos,
                return_type=return_type,
                signedness_result=signedness_result,
                deferred_calls=dict(self._current_deferred_calls),
                effect_summary=effect_summary,
            )
            result.unknown_event_count = len(tracer.unknown_tracker.events)
            result.unknown_event_reasons = sorted(
                {
                    getattr(event, "reason_str", None) or getattr(event.reason, "value", "unknown")
                    for event in tracer.unknown_tracker.events
                }
            )

            if (
                return_type
                and return_type.strip().lower() == "void"
                and effect_summary.synthetic_expr is not None
                and not effect_summary.has_unsupported_call
            ):
                result.returns = [
                    ReturnInfo(
                        address=str(function.getEntryPoint()),
                        conditions=[],
                        branch_index=0,
                        value=effect_summary.synthetic_expr,
                    )
                ]

            recovered_returns = self._recover_switch_like_returns_from_decompiler(
                results,
                result,
            )
            if recovered_returns is not None:
                result.returns = recovered_returns
                result.recovered_from_decompiler = True
                result.analysis_notes.append("switch_like_return_recovery")
            else:
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
                    result.recovered_from_decompiler = True
                    result.analysis_notes.append("call_wrapper_return_recovery")
                else:
                    recovered_returns = self._recover_counted_scalar_reduction_from_decompiler(
                        results,
                        result,
                    )
                    if recovered_returns is not None:
                        result.returns = recovered_returns
                        result.recovered_from_decompiler = True
                        result.analysis_notes.append("counted_scalar_reduction_recovery")

            summary = self._apply_structural_recurrence_summary(
                function,
                high_function,
                result,
                tracer,
            )
            if summary is not None:
                result.returns = summary[0]
                result.analysis_notes.append(summary[1])

            self._analysis_in_progress[function.getName()] = result
            try:
                self._apply_bounded_call_refinement(
                    result,
                    active_functions,
                    function.getName(),
                )
            finally:
                self._analysis_in_progress.pop(function.getName(), None)

            self._synchronize_parameters_with_referenced_parameter_expressions(result)
            result.returns = self._strip_stack_protector_only_conditions(result.returns)
            if (
                result.has_symbolic_post_state_reads()
                and "symbolic_post_state_reads" not in result.analysis_notes
            ):
                result.analysis_notes.append("symbolic_post_state_reads")
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

            return result

    def _apply_structural_recurrence_summary(
        self,
        function,
        high_function,
        analysis: FunctionReturnAnalysis,
        tracer: PcodeTracer,
    ) -> Optional[Tuple[List[ReturnInfo], str]]:
        if analysis is None or not analysis.returns:
            return None

        should_try = analysis.has_unresolved_return_value() or any(
            reason in {"call_out_of_scope", "max_depth_exceeded", "phi_no_valid_branch", "phi_circular"}
            for reason in getattr(analysis, "unknown_event_reasons", [])
        )
        if not should_try and getattr(analysis, "effect_summary", None) is not None:
            should_try = bool(
                getattr(analysis.effect_summary, "effects", None)
                and len(getattr(analysis, "returns", []) or []) >= 2
            )
        if not should_try:
            return None

        summarizer = StructuralRecurrenceSummarizer(tracer, debug=self.debug)
        return summarizer.try_summarize_function(function, high_function, analysis)

    def _strip_stack_protector_only_conditions(
        self,
        return_infos: List[ReturnInfo],
    ) -> List[ReturnInfo]:
        if len(return_infos) != 1:
            return return_infos

        only_return = return_infos[0]
        if not only_return.conditions:
            return return_infos
        if not all(self._condition_looks_like_stack_protector_guard(cond) for cond in only_return.conditions):
            return return_infos

        if self.debug:
            cond_dump = [
                ConditionSimplifier.get_simplified_condition_string(cond)
                for cond in only_return.conditions
            ]
            self._debug_print(
                "Dropped stack-protector-only return conditions from the sole surviving return case: "
                f"{cond_dump}"
            )

        return [
            ReturnInfo(
                address=only_return.address,
                value=only_return.value,
                conditions=[],
                branch_index=only_return.branch_index,
            )
        ]

    def _synchronize_parameters_with_referenced_parameter_expressions(
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

    def _collect_referenced_parameter_descriptors(
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

    def _collect_parameter_descriptors_from_expression(
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

    def _parameter_descriptor_from_expression(self, expr: Expression) -> Dict:
        index_value = expr.value if isinstance(expr.value, int) else -1
        if index_value < 0 and expr.name:
            match = re.fullmatch(r"param_(\d+)", expr.name)
            if match:
                index_value = int(match.group(1)) - 1

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

    def _parameter_descriptor_key(self, descriptor: Dict) -> str:
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

    def _find_matching_parameter_descriptor_index(
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

    def _merge_parameter_descriptors(
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

    def _condition_looks_like_stack_protector_guard(self, condition: Condition) -> bool:
        names = sorted(condition.get_all_variables())
        if names:
            return all(self._name_looks_stack_protector_artifact(name) for name in names)
        text = condition.to_string().lower()
        return any(fragment in text for fragment in self._KNOWN_STACK_PROTECTOR_NAME_FRAGMENTS)

    def _name_looks_stack_protector_artifact(self, name: Optional[str]) -> bool:
        if not name:
            return False
        normalized = str(name).lower()
        for prefix in ("ptr_", "thunk_", "__imp_"):
            if normalized.startswith(prefix):
                normalized = normalized[len(prefix):]
        normalized = re.sub(r"_[0-9a-f]+$", "", normalized)
        normalized = normalized.lstrip("_")
        return any(fragment in normalized for fragment in self._KNOWN_STACK_PROTECTOR_NAME_FRAGMENTS)

    def _mark_incomplete_control_flow(self, analysis: FunctionReturnAnalysis) -> None:
        """後段で保守的に扱うべき不完全な制御フロー要約を記録する。"""
        reasons = []

        if analysis.has_unknown_return():
            reasons.append("unknown_return")
        if analysis.has_overlapping_unconditional_returns():
            reasons.append("overlapping_unconditional_returns")
        if (
            analysis.has_unresolved_return_value()
            and any(
                reason in {"call_out_of_scope", "callind_out_of_scope"}
                for reason in analysis.unknown_event_reasons
            )
        ):
            reasons.append("indirect_control_flow_unresolved")

        if analysis.recovered_from_decompiler:
            reasons = [reason for reason in reasons if reason == "unknown_return"]

        seen = set(analysis.analysis_notes)
        for reason in reasons:
            if reason not in seen:
                analysis.analysis_notes.append(reason)
                seen.add(reason)
        analysis.incomplete_control_flow = bool(reasons)

    def _make_deferred_call_recorder(self, target_function_name: str):
        def record_call(target_name: str, args: List[Expression]) -> str:
            placeholder_name = f"call_out_of_scope:{target_name}#{self._deferred_call_counter}"
            self._deferred_call_counter += 1
            cloned_args = [self._clone_expression(arg) for arg in args]
            self._current_deferred_calls[placeholder_name] = DeferredCallInfo(
                placeholder_name=placeholder_name,
                target_name=target_name,
                arguments=cloned_args,
            )
            if self.debug:
                arg_dump = ", ".join(arg.to_string() for arg in cloned_args)
                self._debug_print(
                    f"Recorded deferred call in '{target_function_name}': "
                    f"{placeholder_name} -> {target_name}([{arg_dump}])"
                )
            return placeholder_name

        return record_call

    def _apply_bounded_call_refinement(
        self,
        analysis: FunctionReturnAnalysis,
        active_functions: Set[str],
        current_function_name: str,
    ) -> None:
        if (
            not self._bounded_call_refinement_enabled
            or analysis is None
            or not analysis.deferred_calls
            or self._bounded_call_unroll_limit <= 0
        ):
            return

        def provide_analysis(function_name: str) -> Optional[FunctionReturnAnalysis]:
            if function_name == current_function_name:
                return analysis
            in_progress = self._analysis_in_progress.get(function_name)
            if in_progress is not None:
                return in_progress
            if function_name in active_functions:
                return None
            return self._get_or_analyze_call_target(function_name, active_functions)

        refiner = BoundedCallRefiner(
            provide_analysis,
            max_unroll=self._bounded_call_unroll_limit,
            max_cases=self._bounded_call_max_cases,
            debug=self.debug,
        )
        changed = refiner.refine_analysis(analysis)
        if changed:
            self._debug_print(
                f"Applied bounded call refinement to '{analysis.function_name}' "
                f"(remaining deferred calls={len(analysis.deferred_calls)})"
            )

    def _recover_switch_like_returns_from_decompiler(
        self,
        decompile_results,
        analysis: FunctionReturnAnalysis,
    ) -> Optional[List[ReturnInfo]]:
        """decompiler の structured switch を補助的に return case へ復元する。"""
        if not self._should_attempt_switch_recovery(analysis):
            if self.debug:
                self._debug_print(
                    "Switch-like recovery skipped: analysis does not look incomplete"
                )
            return None
        if self.debug:
            self._debug_print(
                "Attempting switch-like recovery from decompiler text "
                f"(returns={len(analysis.returns)}, "
                f"unconditional={analysis.count_unconditional_returns()}, "
                f"unknown_reasons={analysis.unknown_event_reasons})"
            )

        c_text = self._get_decompiled_c_text(decompile_results)
        if not c_text:
            if self.debug:
                self._debug_print("Switch-like recovery failed: decompiler C text unavailable")
            return None
        if self.debug:
            preview_lines = [line.rstrip() for line in c_text.splitlines() if line.strip()][:12]
            if preview_lines:
                self._debug_print("Decompiler preview for switch-like recovery:")
                for line in preview_lines:
                    self._debug_print(line, indent=1)

        recovered = self._parse_switch_returns_from_c_text(
            c_text,
            analysis.parameters,
            analysis.return_type,
            analysis.entry_point,
        )
        if recovered and self.debug:
            self._debug_print(
                f"Recovered {len(recovered)} switch-like return cases from decompiler text"
            )
        elif self.debug:
            self._debug_print("Switch-like recovery failed: parser did not match decompiler text")
        return recovered

    def _recover_call_wrapper_returns(
        self,
        decompile_results,
        analysis: FunctionReturnAnalysis,
        current_function,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        return_ops: List[Any],
        active_functions: Optional[Set[str]] = None,
    ) -> Optional[List[ReturnInfo]]:
        """wrapper らしい unknown return を P-code 優先で復元し、必要なら decompiler へフォールバックする。"""
        if not self._analysis_needs_wrapper_recovery(analysis):
            return None

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

        return self._recover_call_wrapper_returns_from_decompiler(
            decompile_results,
            analysis,
            current_function,
            active_functions or set(),
        )

    def _recover_call_wrapper_returns_from_pcode(
        self,
        analysis: FunctionReturnAnalysis,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        return_ops: List[Any],
        current_function,
        active_functions: Set[str],
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

            seq = getattr(return_op, "getSeqnum", lambda: None)()
            address = str(seq.getTarget()) if seq else analysis.entry_point
            return_results: List[ReturnInfo] = []

            for path_index, (block_path, path_conditions) in enumerate(path_entries):
                terminal_call = self._find_terminal_call_on_block_path(block_path, return_op)
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

    def _recover_call_wrapper_returns_from_decompiler(
        self,
        decompile_results,
        analysis: FunctionReturnAnalysis,
        current_function,
        active_functions: Optional[Set[str]] = None,
    ) -> Optional[List[ReturnInfo]]:
        """decompiler の `callee(args); return;` 形式を戻り値 wrapper として補助復元する。"""
        if not self._analysis_needs_wrapper_recovery(analysis):
            return None

        c_text = self._get_decompiled_c_text(decompile_results)
        if not c_text:
            return None
        wrapper_parameters = self._merge_wrapper_parameters_from_c_text(
            analysis.parameters,
            c_text,
        )
        if self.debug:
            self._debug_print(
                "Attempting call-wrapper recovery from decompiler text "
                f"(returns={len(analysis.returns)}, unknown_reasons={analysis.unknown_event_reasons})"
            )
        recovered_structured = self._recover_structured_call_wrapper_from_c_text(
            c_text,
            wrapper_parameters,
            analysis.entry_point,
            current_function,
            active_functions or set(),
        )
        if recovered_structured is not None:
            if self.debug:
                self._debug_print(
                    f"Call-wrapper recovery reconstructed {len(recovered_structured)} return case(s) "
                    "from structured wrapper body"
                )
            return recovered_structured
        if self.debug:
            self._debug_print("Call-wrapper structured recovery did not match decompiler text")

        recovered_chain = self._recover_straightline_call_chain_from_c_text(
            c_text,
            wrapper_parameters,
            analysis.entry_point,
            current_function,
            active_functions or set(),
        )
        if recovered_chain is not None:
            if self.debug:
                self._debug_print(
                    f"Call-wrapper recovery reconstructed {len(recovered_chain)} return case(s) "
                    "from straight-line call chain"
                )
            return recovered_chain
        if self.debug:
            self._debug_print("Call-wrapper straight-line recovery did not match decompiler text")

        recovered = self._parse_call_wrapper_from_c_text(
            c_text,
            wrapper_parameters,
        )
        if recovered is None:
            if self.debug:
                self._debug_print("Call-wrapper recovery failed: parser did not match decompiler text")
            return None

        callee_name, args = recovered
        if self.debug:
            arg_preview = [arg.to_string() for arg in args]
            self._debug_print(
                f"Call-wrapper recovery matched callee '{callee_name}' with args {arg_preview}"
            )

        expanded = self._resolve_call_expansions(
            callee_name,
            args,
            active_functions or set(),
            current_function=current_function,
        )
        if not expanded:
            if self.debug:
                self._debug_print(
                    f"Call-wrapper recovery failed: no safe call summary available for '{callee_name}'"
                )
            return None

        return self._build_return_infos_from_expansions(
            analysis.entry_point,
            expanded,
            0,
        )

    def _recover_counted_scalar_reduction_from_decompiler(
        self,
        decompile_results,
        analysis: FunctionReturnAnalysis,
    ) -> Optional[List[ReturnInfo]]:
        c_text = self._get_decompiled_c_text(decompile_results)
        if not c_text:
            if self.debug:
                self._debug_print(
                    "Counted reduction recovery skipped: decompiler C text unavailable"
                )
            return None
        if not self._should_attempt_counted_scalar_reduction_recovery(analysis, c_text):
            if self.debug:
                self._debug_print(
                    "Counted reduction recovery skipped: analysis does not look incomplete"
                )
            return None
        if self.debug:
            preview_lines = [line.rstrip() for line in c_text.splitlines() if line.strip()][:40]
            if preview_lines:
                self._debug_print("Decompiler preview for counted reduction recovery:")
                for line in preview_lines:
                    self._debug_print(line, indent=1)
        if self.debug:
            self._debug_print(
                "Attempting counted reduction recovery from decompiler text "
                f"(returns={len(analysis.returns)}, unknown_reasons={analysis.unknown_event_reasons})"
            )

        recovered = self._parse_counted_reduction_from_c_text(
            c_text,
            analysis.parameters,
            analysis.entry_point,
        )
        if recovered and self.debug:
            self._debug_print(
                f"Counted reduction recovery reconstructed {len(recovered)} return case(s) "
                "from structured loop body"
            )
        if recovered is not None and not self._validate_counted_scalar_reduction_recovery(analysis, recovered):
            if self.debug:
                self._debug_print(
                    "Counted reduction recovery rejected after bounded semantic validation "
                    "against the original summary"
                )
            return None
        return recovered

    def _should_attempt_counted_scalar_reduction_recovery(
        self,
        analysis: Optional[FunctionReturnAnalysis],
        c_text: Optional[str] = None,
    ) -> bool:
        """保守的に counted reduction recovery を起動するべきか判定する。"""
        if analysis is None or not analysis.parameters or not analysis.returns:
            return False
        if str(analysis.return_type or "").strip().lower() == "void":
            return False
        if analysis.recovered_from_decompiler:
            return False
        if c_text is not None and not self._decompiled_text_looks_structured_summary_friendly(c_text):
            return False

        loop_like_text = self._decompiled_text_looks_loop_like(c_text or "")

        # 元の summary が十分に具体化できているケースを decompiler 式で上書きすると、
        # UB 境界や signed/unsigned の表現差で不要な SAT を作りやすい。
        if analysis.has_unknown_return() or analysis.has_unresolved_return_value():
            return True
        if analysis.has_symbolic_post_state_reads() or analysis.has_overlapping_unconditional_returns():
            return True
        if self._analysis_has_ambiguous_condition_region_returns(analysis):
            return True

        # ケース爆発や deeply-nested 分岐は loop summary recovery の恩恵が大きい。
        if len(analysis.returns) > 8:
            return True
        if loop_like_text and len(analysis.returns) >= 4 and any(len(ret.conditions or []) >= 3 for ret in analysis.returns):
            return True
        if c_text is not None and self._analysis_has_suspicious_peeled_loop_cases(analysis):
            return True
        if (
            c_text is not None
            and 2 <= len(analysis.returns) <= 6
            and analysis.count_unconditional_returns() == 0
            and any(len(ret.conditions or []) >= 2 for ret in analysis.returns)
        ):
            return True

        return False

    def _decompiled_text_looks_loop_like(self, c_text: str) -> bool:
        body = c_text or ""
        return any(marker in body for marker in ("for (", "for(", "while (", "while(", "do {", "do{"))

    def _decompiled_text_looks_structured_summary_friendly(self, c_text: str) -> bool:
        body = c_text or ""
        return any(
            marker in body
            for marker in ("if (", "if(", "return ", "for (", "for(", "while (", "while(", "do {", "do{")
        )

    def _analysis_has_suspicious_peeled_loop_cases(
        self,
        analysis: FunctionReturnAnalysis,
    ) -> bool:
        parameters = analysis.parameters or []
        param_names = {
            str(param.get("name"))
            for param in parameters
            if param.get("name")
        }
        if not param_names and not parameters:
            return False

        for ret in analysis.returns or []:
            for cond in ret.conditions or []:
                if self._condition_expr_looks_like_parameter_peeling(
                    getattr(cond, "expression", None),
                    parameters,
                ):
                    return True
                cond_text = cond.to_string()
                if not any(param_name in cond_text for param_name in param_names):
                    continue
                if self._condition_text_looks_like_parameter_peeling(cond_text, param_names):
                    return True
        return False

    def _condition_expr_looks_like_parameter_peeling(
        self,
        expr: Optional[Expression],
        parameters: List[Dict],
    ) -> bool:
        if expr is None:
            return False
        param_names = {
            str(param.get("name"))
            for param in parameters
            if param.get("name")
        }
        if not param_names:
            return False

        if expr.expr_type == ExpressionType.PARAMETER and expr.name in param_names:
            return False

        if expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
            value = int(expr.value)
            if value in {-1, 0, 1, 0xFFFFFFFF, 0x7FFFFFFF, 0x80000000}:
                return True
            return False

        if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
            return self._condition_expr_looks_like_parameter_peeling(expr.operands[0], parameters)

        if expr.expr_type != ExpressionType.BINARY_OP or not expr.operands:
            return False

        operator = expr.operator
        if operator in {"INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", "INT_SLESS", "INT_LESSEQUAL", "INT_SLESSEQUAL"}:
            return any(
                self._condition_expr_looks_like_parameter_peeling(operand, parameters)
                for operand in expr.operands
            )

        if operator in {"INT_ADD", "INT_SUB"} and len(expr.operands) == 2:
            left, right = expr.operands
            if (
                left.expr_type == ExpressionType.PARAMETER
                and left.name in param_names
                and right.expr_type == ExpressionType.CONSTANT
                and isinstance(right.value, int)
                and abs(int(right.value)) == 1
            ):
                return True
            if (
                right.expr_type == ExpressionType.PARAMETER
                and right.name in param_names
                and left.expr_type == ExpressionType.CONSTANT
                and isinstance(left.value, int)
                and abs(int(left.value)) == 1
            ):
                return True
            return any(
                self._condition_expr_looks_like_parameter_peeling(operand, parameters)
                for operand in expr.operands
            )

        return any(
            self._condition_expr_looks_like_parameter_peeling(operand, parameters)
            for operand in expr.operands
        )

    def _condition_text_looks_like_parameter_peeling(
        self,
        cond_text: str,
        param_names: Set[str],
    ) -> bool:
        text = str(cond_text or "")
        if not text:
            return False

        comparison_tokens = ("==", "!=", "<", "<=", ">", ">=")
        if not any(token in text for token in comparison_tokens):
            return False

        small_constant_markers = (
            " 0",
            " 1",
            "-1",
            "4294967295",
            "2147483647",
            "2147483648",
        )
        if any(marker in text for marker in small_constant_markers):
            return True

        for param_name in param_names:
            if re.search(rf"\b{re.escape(param_name)}\b\s*[+\-]\s*1\b", text):
                return True
            if re.search(rf"\b{re.escape(param_name)}\b.*4294967295", text):
                return True
            if re.search(rf"4294967295.*\b{re.escape(param_name)}\b", text):
                return True

        return False

    def _validate_counted_scalar_reduction_recovery(
        self,
        analysis: FunctionReturnAnalysis,
        recovered: List[ReturnInfo],
    ) -> bool:
        samples = self._build_counted_recovery_validation_samples(analysis.parameters or [])
        checked = 0
        recovered_defined = 0

        for env in samples:
            original_value = self._evaluate_return_summary_under_environment(analysis.returns or [], env)
            recovered_value = self._evaluate_return_summary_under_environment(recovered, env)
            if recovered_value is not None:
                recovered_defined += 1
            if original_value is None:
                continue
            if recovered_value is None or recovered_value != original_value:
                if self.debug:
                    self._debug_print(
                        "Counted reduction recovery validation mismatch: "
                        f"env={env}, original={original_value}, recovered={recovered_value}"
                    )
                return False
            checked += 1

        minimum_checked = 4 if len(samples) >= 4 else len(samples)
        if checked >= minimum_checked:
            return True

        if self._may_accept_fragment_backed_self_consistent_recovery(analysis, recovered):
            if self.debug:
                self._debug_print(
                    "Counted reduction recovery accepted via self-consistent sampled coverage "
                    f"(checked={checked}, recovered_defined={recovered_defined}, samples={len(samples)})"
                )
            return recovered_defined >= minimum_checked and recovered_defined == len(samples)

        if self.debug:
            self._debug_print(
                "Counted reduction recovery validation insufficient overlap: "
                f"checked={checked}, recovered_defined={recovered_defined}, samples={len(samples)}"
            )
        return False

    def _may_accept_fragment_backed_self_consistent_recovery(
        self,
        analysis: FunctionReturnAnalysis,
        recovered: List[ReturnInfo],
    ) -> bool:
        if analysis is None:
            return False
        if any(self._expression_contains_unresolved_value(ret.value) for ret in recovered):
            return False
        if not self._analysis_has_suspicious_peeled_loop_cases(analysis):
            return False
        if not any(self._return_info_mentions_parameter_fragment(ret) for ret in recovered):
            return False
        return True

    def _return_info_mentions_parameter_fragment(self, ret: ReturnInfo) -> bool:
        for condition in ret.conditions or []:
            if self._expression_mentions_parameter_fragment(condition.expression):
                return True
        return self._expression_mentions_parameter_fragment(ret.value)

    def _expression_mentions_parameter_fragment(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        if expr.expr_type == ExpressionType.VARIABLE and self._looks_like_wrapper_fragment_temp_name(expr.name or ""):
            return True
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None and self._expression_mentions_parameter_fragment(cond.expression):
                    return True
                if self._expression_mentions_parameter_fragment(value):
                    return True
            return False
        return any(self._expression_mentions_parameter_fragment(operand) for operand in expr.operands or [])

    def _build_counted_recovery_validation_samples(
        self,
        parameters: List[Dict],
    ) -> List[Dict[str, int]]:
        scalar_params = [
            param for param in (parameters or [])
            if param.get("name") and int(param.get("size", 4) or 4) <= 8
        ]
        if not scalar_params:
            return []

        candidate_values_per_param: List[Tuple[str, List[int]]] = []
        for param in scalar_params[:2]:
            name = str(param.get("name"))
            size_bytes = max(1, int(param.get("size", 4) or 4))
            bit_width = size_bytes * 8
            is_signed = bool(param.get("is_signed", True))
            values = [0, 1, 2, 3, 4, 7, 8]
            if is_signed:
                values.extend([-1, -2])
                if bit_width >= 2:
                    values.extend([-(1 << (bit_width - 1)), (1 << (bit_width - 1)) - 1])
            values.append((1 << bit_width) - 1)

            deduped: List[int] = []
            seen = set()
            for value in values:
                masked = self._mask_bitvector_value(value, bit_width)
                if masked in seen:
                    continue
                seen.add(masked)
                deduped.append(value)
            candidate_values_per_param.append((name, deduped[:10]))

        samples: List[Dict[str, int]] = []
        if len(candidate_values_per_param) == 1:
            param_name, values = candidate_values_per_param[0]
            for value in values:
                samples.append({param_name: value})
            return samples

        first_name, first_values = candidate_values_per_param[0]
        second_name, second_values = candidate_values_per_param[1]
        for first in first_values:
            for second in second_values:
                samples.append({first_name: first, second_name: second})
        return samples

    def _evaluate_return_summary_under_environment(
        self,
        returns: List[ReturnInfo],
        env: Dict[str, int],
    ) -> Optional[int]:
        augmented_env = self._augment_validation_environment_with_fragments(returns, env)
        matched_values: List[int] = []
        for ret in returns:
            cond_truths: List[bool] = []
            for cond in ret.conditions or []:
                cond_value = self._evaluate_expression_under_environment(cond.expression, augmented_env)
                if cond_value is None:
                    cond_truths = []
                    break
                truth = cond_value != 0
                cond_truths.append((not truth) if cond.negated else truth)
            if ret.conditions and not cond_truths:
                continue
            if not all(cond_truths):
                continue
            value = self._evaluate_expression_under_environment(ret.value, augmented_env)
            if value is None:
                continue
            matched_values.append(value)

        if not matched_values:
            return None
        if any(value != matched_values[0] for value in matched_values[1:]):
            return None
        return matched_values[0]

    def _augment_validation_environment_with_fragments(
        self,
        returns: List[ReturnInfo],
        env: Dict[str, int],
    ) -> Dict[str, int]:
        augmented_env = dict(env)
        fragment_bindings: Dict[str, Tuple[str, int]] = {}
        for ret in returns:
            for condition in ret.conditions or []:
                self._collect_parameter_fragment_bindings(condition.expression, fragment_bindings)
            self._collect_parameter_fragment_bindings(ret.value, fragment_bindings)

        if not fragment_bindings:
            return augmented_env

        param_info = {
            str(param.get("name")): param
            for param in (self._current_parameters or [])
            if param.get("name")
        }
        for fragment_name, (param_name, fragment_bits) in fragment_bindings.items():
            if fragment_name in augmented_env or param_name not in augmented_env:
                continue
            param = param_info.get(param_name, {})
            param_bits = max(1, int(param.get("size", 4) or 4) * 8)
            source_value = self._mask_bitvector_value(int(augmented_env[param_name]), param_bits)
            is_signed = bool(param.get("is_signed", True))
            extended = self._to_signed_bitvector(source_value, param_bits) if is_signed else source_value
            augmented_env[fragment_name] = self._mask_bitvector_value(extended >> param_bits, fragment_bits)
        return augmented_env

    def _collect_parameter_fragment_bindings(
        self,
        expr: Optional[Expression],
        bindings: Dict[str, Tuple[str, int]],
    ) -> None:
        if expr is None:
            return
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None:
                    self._collect_parameter_fragment_bindings(cond.expression, bindings)
                self._collect_parameter_fragment_bindings(value, bindings)
            return
        if (
            expr.expr_type == ExpressionType.BINARY_OP
            and expr.operator == "PIECE"
            and len(expr.operands) == 2
        ):
            high_expr, low_expr = expr.operands
            if (
                high_expr.expr_type == ExpressionType.VARIABLE
                and high_expr.name
                and low_expr.expr_type == ExpressionType.PARAMETER
                and low_expr.name
            ):
                bindings.setdefault(
                    high_expr.name,
                    (low_expr.name, max(1, int(getattr(high_expr, "size", 0) or 4) * 8)),
                )
        for operand in expr.operands or []:
            self._collect_parameter_fragment_bindings(operand, bindings)

    def _evaluate_expression_under_environment(
        self,
        expr: Optional[Expression],
        env: Dict[str, int],
    ) -> Optional[int]:
        if expr is None:
            return None

        expr_type = expr.expr_type
        bit_width = max(1, int(getattr(expr, "size", 0) or 4) * 8)
        if expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
            return self._mask_bitvector_value(int(expr.value), bit_width)
        if expr_type in {ExpressionType.PARAMETER, ExpressionType.VARIABLE} and expr.name:
            if expr.name not in env:
                return None
            return self._mask_bitvector_value(int(env[expr.name]), bit_width)
        if expr_type == ExpressionType.UNARY_OP and expr.operands:
            operand = self._evaluate_expression_under_environment(expr.operands[0], env)
            if operand is None:
                return None
            if expr.operator == "INT_2COMP":
                return self._mask_bitvector_value(-self._to_signed_bitvector(operand, bit_width), bit_width)
            if expr.operator == "INT_NEGATE":
                return self._mask_bitvector_value(~operand, bit_width)
            if expr.operator == "BOOL_NEGATE":
                return 0 if operand != 0 else 1
            if expr.operator in {"INT_ZEXT", "INT_SEXT", "COPY"}:
                return self._mask_bitvector_value(operand, bit_width)
            return None
        if expr_type == ExpressionType.PHI and expr.value:
            for condition, value in expr.value:
                if condition is not None:
                    cond_value = self._evaluate_expression_under_environment(condition.expression, env)
                    if cond_value is None:
                        continue
                    truth = cond_value != 0
                    if condition.negated:
                        truth = not truth
                    if not truth:
                        continue
                resolved_value = self._evaluate_expression_under_environment(value, env)
                if resolved_value is not None:
                    return self._mask_bitvector_value(resolved_value, bit_width)
            return None
        if expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None

        left = self._evaluate_expression_under_environment(expr.operands[0], env)
        right = self._evaluate_expression_under_environment(expr.operands[1], env)
        if left is None or right is None:
            return None

        operator = expr.operator
        if operator == "INT_ADD":
            return self._mask_bitvector_value(left + right, bit_width)
        if operator == "INT_SUB":
            return self._mask_bitvector_value(left - right, bit_width)
        if operator == "INT_MULT":
            return self._mask_bitvector_value(left * right, bit_width)
        if operator == "INT_AND":
            return self._mask_bitvector_value(left & right, bit_width)
        if operator == "INT_OR":
            return self._mask_bitvector_value(left | right, bit_width)
        if operator == "INT_XOR":
            return self._mask_bitvector_value(left ^ right, bit_width)
        if operator == "INT_LEFT":
            return self._mask_bitvector_value(left << self._mask_shift_amount(right), bit_width)
        if operator == "INT_RIGHT":
            return self._mask_bitvector_value(left >> self._mask_shift_amount(right), bit_width)
        if operator == "INT_SRIGHT":
            signed_left = self._to_signed_bitvector(left, bit_width)
            return self._mask_bitvector_value(signed_left >> self._mask_shift_amount(right), bit_width)
        if operator == "INT_DIV":
            if right == 0:
                return None
            return self._mask_bitvector_value(left // right, bit_width)
        if operator == "INT_SDIV":
            divisor = self._to_signed_bitvector(right, bit_width)
            if divisor == 0:
                return None
            dividend = self._to_signed_bitvector(left, bit_width)
            return self._mask_bitvector_value(int(dividend / divisor), bit_width)
        if operator == "INT_REM":
            if right == 0:
                return None
            return self._mask_bitvector_value(left % right, bit_width)
        if operator == "INT_SREM":
            divisor = self._to_signed_bitvector(right, bit_width)
            if divisor == 0:
                return None
            dividend = self._to_signed_bitvector(left, bit_width)
            quotient = int(dividend / divisor)
            return self._mask_bitvector_value(dividend - quotient * divisor, bit_width)
        if operator in {"INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", "INT_LESSEQUAL", "INT_SLESS", "INT_SLESSEQUAL"}:
            return self._evaluate_bitvector_comparison(operator, left, right, bit_width)
        if operator == "BOOL_AND":
            return 1 if (left != 0 and right != 0) else 0
        if operator == "BOOL_OR":
            return 1 if (left != 0 or right != 0) else 0
        if operator == "BOOL_XOR":
            return 1 if ((left != 0) ^ (right != 0)) else 0
        if operator == "SUBPIECE":
            shift_bits = self._mask_bitvector_value(right, bit_width) * 8
            output_bits = max(1, int(getattr(expr, "size", 0) or 4) * 8)
            return self._mask_bitvector_value(left >> shift_bits, output_bits)
        if operator == "PIECE":
            low_bits = max(1, int(getattr(expr.operands[1], "size", 0) or 4) * 8)
            return self._mask_bitvector_value((left << low_bits) | self._mask_bitvector_value(right, low_bits), bit_width)
        return None

    def _evaluate_bitvector_comparison(
        self,
        operator: Optional[str],
        left: int,
        right: int,
        bit_width: int,
    ) -> int:
        if operator == "INT_EQUAL":
            return 1 if left == right else 0
        if operator == "INT_NOTEQUAL":
            return 1 if left != right else 0
        if operator == "INT_LESS":
            return 1 if left < right else 0
        if operator == "INT_LESSEQUAL":
            return 1 if left <= right else 0

        left_signed = self._to_signed_bitvector(left, bit_width)
        right_signed = self._to_signed_bitvector(right, bit_width)
        if operator == "INT_SLESS":
            return 1 if left_signed < right_signed else 0
        if operator == "INT_SLESSEQUAL":
            return 1 if left_signed <= right_signed else 0
        return 0

    def _mask_shift_amount(self, value: int) -> int:
        return max(0, int(value))

    def _mask_bitvector_value(self, value: int, bit_width: int) -> int:
        mask = (1 << bit_width) - 1
        return int(value) & mask

    def _to_signed_bitvector(self, value: int, bit_width: int) -> int:
        masked = self._mask_bitvector_value(value, bit_width)
        sign_bit = 1 << (bit_width - 1)
        return masked - (1 << bit_width) if masked & sign_bit else masked

    def _find_terminal_call_on_block_path(
        self,
        block_path: List[Any],
        return_op,
    ):
        """block path 上で RETURN に至る直前の wrapper 候補 CALL/CALLIND を探す。"""
        linear_ops = []
        for block_info in block_path:
            for pcode_op in getattr(block_info, "pcode_ops", []) or []:
                linear_ops.append(pcode_op)
                if pcode_op is return_op:
                    break
            if linear_ops and linear_ops[-1] is return_op:
                break

        if not linear_ops or linear_ops[-1] is not return_op:
            return None

        terminal_index = None
        for index, pcode_op in enumerate(linear_ops[:-1]):
            if pcode_op.getMnemonic() in {"CALL", "CALLIND"}:
                terminal_index = index

        if terminal_index is None:
            return None

        for pcode_op in linear_ops[terminal_index + 1:-1]:
            if not self._is_wrapper_passthrough_pcode_op(pcode_op):
                return None

        return linear_ops[terminal_index]

    def _is_wrapper_passthrough_pcode_op(self, pcode_op) -> bool:
        """terminal CALL の後ろに許容できる op だけを通す。"""
        mnemonic = pcode_op.getMnemonic()
        return mnemonic in {
            "BRANCH",
            "CBRANCH",
            "BRANCHIND",
            "MULTIEQUAL",
            "COPY",
            "CAST",
            "INT_ZEXT",
            "INT_SEXT",
            "SUBPIECE",
        }

    def _recover_structured_call_wrapper_from_c_text(
        self,
        c_text: str,
        parameters: List[Dict],
        address: str,
        current_function,
        active_functions: Set[str],
        initial_bindings: Optional[Dict[str, Expression]] = None,
    ) -> Optional[List[ReturnInfo]]:
        from ..transform.expander import ExpandedValue

        body_lines = self._extract_structured_wrapper_body_lines(c_text)
        if not body_lines:
            return None

        seeded_bindings = {
            name: self._clone_expression(expr)
            for name, expr in (initial_bindings or {}).items()
        }

        next_index, live_states, terminated_states, ok = self._execute_structured_wrapper_block(
            body_lines,
            0,
            [(seeded_bindings, [], None)],
            parameters,
            active_functions,
            current_function,
        )
        if not ok or next_index != len(body_lines) or live_states:
            return None

        expanded_values = []
        for _bindings, conditions, last_call in terminated_states:
            if last_call is None:
                return None
            simplified = ConditionSimplifier.simplify_conditions(conditions)
            if ConditionSimplifier.is_contradiction(simplified):
                continue
            expanded_values.append(ExpandedValue(self._clone_expression(last_call), simplified))

        if not expanded_values:
            return None

        return self._build_return_infos_from_expansions(address, expanded_values, 0)

    def _recover_straightline_call_chain_from_c_text(
        self,
        c_text: str,
        parameters: List[Dict],
        address: str,
        current_function,
        active_functions: Set[str],
        initial_bindings: Optional[Dict[str, Expression]] = None,
    ) -> Optional[List[ReturnInfo]]:
        from ..transform.expander import ExpandedValue

        structured_body_lines = self._extract_structured_wrapper_body_lines(c_text)
        if structured_body_lines and self._has_structured_control_flow_markers(structured_body_lines):
            return None

        statements = self._extract_wrapper_body_statements(c_text)
        if not statements:
            return None

        states: List[Tuple[Dict[str, Expression], List[Condition], Optional[Expression]]] = [
            (
                {
                    name: self._clone_expression(expr)
                    for name, expr in (initial_bindings or {}).items()
                },
                [],
                None,
            )
        ]

        for index, statement in enumerate(statements):
            return_expr = self._parse_wrapper_return_statement(
                statement,
                parameters,
                states,
                active_functions=active_functions,
                current_function=current_function,
            )
            if return_expr is not None:
                if index != len(statements) - 1:
                    return None
                states = return_expr
                break

            if self._is_wrapper_declaration_line(statement):
                continue

            parsed_call = self._parse_wrapper_call_statement(statement)
            if parsed_call is not None:
                target_name, callee_spec, arg_blob = parsed_call
                next_states = self._expand_wrapper_call_states(
                    states,
                    target_name,
                    callee_spec,
                    arg_blob,
                    parameters,
                    active_functions,
                    current_function,
                    assign_to_last_call=target_name is None,
                )
                if next_states is None:
                    return None
                states = next_states
                continue

            simple_assign = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.+)\s*;", statement)
            if simple_assign:
                target_name = simple_assign.group(1)
                expr_text = simple_assign.group(2)
                next_states = []
                for bindings, conditions, _last_call in states:
                    parsed_expr = self._parse_wrapper_argument_expr(
                        expr_text,
                        parameters,
                        fallback_index=0,
                        local_bindings=bindings,
                    )
                    if parsed_expr is None:
                        return None
                    new_bindings = dict(bindings)
                    new_bindings[target_name] = self._clone_expression(parsed_expr)
                    next_states.append((new_bindings, list(conditions), None))
                states = next_states
                continue

            parsed_store = self._parse_wrapper_store_statement(statement)
            if parsed_store is not None:
                lhs_text, rhs_text = parsed_store
                next_states = []
                for bindings, conditions, last_call in states:
                    parsed_expr = self._parse_wrapper_argument_expr(
                        rhs_text,
                        parameters,
                        fallback_index=0,
                        local_bindings=bindings,
                    )
                    if parsed_expr is None:
                        return None
                    new_bindings = dict(bindings)
                    self._record_wrapper_store_binding(
                        new_bindings,
                        lhs_text,
                        parsed_expr,
                        parameters,
                    )
                    next_states.append((new_bindings, list(conditions), last_call))
                states = next_states
                continue

            return None

        expanded_values = []
        for _bindings, conditions, last_call in states:
            if last_call is None:
                continue
            simplified_conds = ConditionSimplifier.simplify_conditions(conditions)
            if ConditionSimplifier.is_contradiction(simplified_conds):
                continue
            expanded_values.append(ExpandedValue(last_call, simplified_conds))

        if not expanded_values:
            return None

        return self._build_return_infos_from_expansions(address, expanded_values, 0)

    def _execute_structured_wrapper_block(
        self,
        body_lines: List[str],
        start_index: int,
        states: List[Tuple[Dict[str, Expression], List[Condition], Optional[Expression]]],
        parameters: List[Dict],
        active_functions: Set[str],
        current_function,
        stop_on_closing_brace: bool = False,
    ) -> Tuple[
        int,
        List[Tuple[Dict[str, Expression], List[Condition], Optional[Expression]]],
        List[Tuple[Dict[str, Expression], List[Condition], Optional[Expression]]],
        bool,
    ]:
        live_states = [
            (dict(bindings), list(conditions), last_call)
            for bindings, conditions, last_call in states
        ]
        terminated_states: List[Tuple[Dict[str, Expression], List[Condition], Optional[Expression]]] = []
        index = start_index

        while index < len(body_lines):
            line = body_lines[index]

            if line == "}":
                if stop_on_closing_brace:
                    return index + 1, live_states, terminated_states, True
                return index, live_states, terminated_states, False

            if line == "{":
                return index, live_states, terminated_states, False

            if not live_states:
                next_index = len(body_lines)
                if stop_on_closing_brace:
                    next_index = self._advance_to_structured_block_exit(body_lines, index)
                return next_index, [], terminated_states, True

            if self._is_wrapper_declaration_line(line):
                index += 1
                continue

            if line == "return;":
                if not live_states or any(last_call is None for _bindings, _conditions, last_call in live_states):
                    return index, live_states, terminated_states, False
                terminated_states.extend(
                    (dict(bindings), list(conditions), self._clone_expression(cast(Expression, last_call)))
                    for bindings, conditions, last_call in live_states
                )
                next_index = index + 1
                if stop_on_closing_brace:
                    next_index = self._advance_to_structured_block_exit(body_lines, next_index)
                return next_index, [], terminated_states, True

            return_expr = self._parse_wrapper_return_statement(
                line,
                parameters,
                live_states,
                active_functions=active_functions,
                current_function=current_function,
            )
            if return_expr is not None:
                terminated_states.extend(return_expr)
                next_index = index + 1
                if stop_on_closing_brace:
                    next_index = self._advance_to_structured_block_exit(body_lines, next_index)
                return next_index, [], terminated_states, True

            if_match = re.fullmatch(r"if\s*\((.+)\)\s*(\{)?", line)
            if if_match:
                next_index, live_states, branch_terminated, ok = self._execute_structured_wrapper_if(
                    body_lines,
                    index,
                    live_states,
                    if_match.group(1).strip(),
                    bool(if_match.group(2)),
                    parameters,
                    active_functions,
                    current_function,
                )
                if not ok:
                    return index, live_states, terminated_states, False
                terminated_states.extend(branch_terminated)
                index = next_index
                continue

            parsed_call = self._parse_wrapper_call_statement(line)
            if parsed_call is not None:
                target_name, callee_spec, arg_blob = parsed_call
                live_states = self._expand_wrapper_call_states(
                    live_states,
                    target_name,
                    callee_spec,
                    arg_blob,
                    parameters,
                    active_functions,
                    current_function,
                    assign_to_last_call=target_name is None,
                )
                if live_states is None:
                    return index, [], terminated_states, False
                index += 1
                continue

            simple_assign = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.+)\s*;", line)
            if simple_assign:
                target_name = simple_assign.group(1)
                expr_text = simple_assign.group(2)
                next_states = []
                for bindings, conditions, _last_call in live_states:
                    parsed_expr = self._parse_wrapper_argument_expr(
                        expr_text,
                        parameters,
                        fallback_index=0,
                        local_bindings=bindings,
                    )
                    if parsed_expr is None:
                        return index, [], terminated_states, False
                    new_bindings = dict(bindings)
                    new_bindings[target_name] = self._clone_expression(parsed_expr)
                    next_states.append((new_bindings, list(conditions), None))
                live_states = next_states
                index += 1
                continue

            parsed_store = self._parse_wrapper_store_statement(line)
            if parsed_store is not None:
                lhs_text, rhs_text = parsed_store
                next_states = []
                for bindings, conditions, last_call in live_states:
                    parsed_expr = self._parse_wrapper_argument_expr(
                        rhs_text,
                        parameters,
                        fallback_index=0,
                        local_bindings=bindings,
                    )
                    if parsed_expr is None:
                        return index, [], terminated_states, False
                    new_bindings = dict(bindings)
                    self._record_wrapper_store_binding(
                        new_bindings,
                        lhs_text,
                        parsed_expr,
                        parameters,
                    )
                    next_states.append((new_bindings, list(conditions), last_call))
                live_states = next_states
                index += 1
                continue

            return index, live_states, terminated_states, False

        return index, live_states, terminated_states, True

    def _advance_to_structured_block_exit(
        self,
        body_lines: List[str],
        start_index: int,
    ) -> int:
        depth = 0
        index = start_index
        while index < len(body_lines):
            line = body_lines[index]
            for char in line:
                if char == "{":
                    depth += 1
                elif char == "}":
                    if depth == 0:
                        return index + 1
                    depth -= 1
            index += 1
        return start_index

    def _parse_wrapper_return_statement(
        self,
        statement: str,
        parameters: List[Dict],
        states: List[Tuple[Dict[str, Expression], List[Condition], Optional[Expression]]],
        active_functions: Optional[Set[str]] = None,
        current_function=None,
    ) -> Optional[List[Tuple[Dict[str, Expression], List[Condition], Optional[Expression]]]]:
        line = statement.strip()
        if line == "return;":
            return [
                (dict(bindings), list(conditions), self._clone_expression(last_call))
                for bindings, conditions, last_call in states
                if last_call is not None
            ] or None

        return_match = re.fullmatch(r"return\s+(.+)\s*;", line)
        if return_match is None:
            return None

        expr_text = return_match.group(1).strip()
        parsed_call = self._parse_wrapper_call_expr(expr_text)
        if parsed_call is not None:
            callee_spec, arg_blob = parsed_call
            return self._expand_wrapper_return_call_states(
                states,
                callee_spec,
                arg_blob,
                parameters,
                active_functions or set(),
                current_function,
            )

        terminated_states = []
        for bindings, conditions, _last_call in states:
            parsed_expr = self._parse_wrapper_argument_expr(
                expr_text,
                parameters,
                fallback_index=0,
                local_bindings=bindings,
            )
            if parsed_expr is None:
                return None
            terminated_states.append(
                (dict(bindings), list(conditions), self._clone_expression(parsed_expr))
            )
        return terminated_states or None

    def _execute_structured_wrapper_if(
        self,
        body_lines: List[str],
        if_index: int,
        states: List[Tuple[Dict[str, Expression], List[Condition], Optional[Expression]]],
        condition_text: str,
        header_has_brace: bool,
        parameters: List[Dict],
        active_functions: Set[str],
        current_function,
    ) -> Tuple[
        int,
        List[Tuple[Dict[str, Expression], List[Condition], Optional[Expression]]],
        List[Tuple[Dict[str, Expression], List[Condition], Optional[Expression]]],
        bool,
    ]:
        then_start = if_index + 1
        if not header_has_brace:
            if then_start >= len(body_lines) or body_lines[then_start] != "{":
                return if_index, states, [], False
            then_start += 1

        then_inputs = []
        else_inputs = []
        for bindings, conditions, last_call in states:
            ok_then, refined_then = self._refine_wrapper_state_conditions(
                conditions,
                condition_text,
                parameters,
                bindings,
                negated=False,
            )
            if not ok_then:
                self._record_structured_reduction_failure(body_lines, if_index, "if_then_condition_refinement_failed")
                return if_index, states, [], False
            if refined_then is not None:
                then_inputs.append((dict(bindings), refined_then, last_call))

            ok_else, refined_else = self._refine_wrapper_state_conditions(
                conditions,
                condition_text,
                parameters,
                bindings,
                negated=True,
            )
            if not ok_else:
                self._record_structured_reduction_failure(body_lines, if_index, "if_else_condition_refinement_failed")
                return if_index, states, [], False
            if refined_else is not None:
                else_inputs.append((dict(bindings), refined_else, last_call))

        next_index, then_live, then_terminated, ok = self._execute_structured_wrapper_block(
            body_lines,
            then_start,
            then_inputs,
            parameters,
            active_functions,
            current_function,
            stop_on_closing_brace=True,
        )
        if not ok:
            self._record_structured_reduction_failure(body_lines, then_start, "if_then_block_execution_failed")
            return if_index, states, [], False

        all_terminated = list(then_terminated)
        merged_live = list(then_live)

        if next_index < len(body_lines):
            next_index, else_live, else_terminated, ok = self._execute_structured_wrapper_else_clause(
                body_lines,
                next_index,
                else_inputs,
                parameters,
                active_functions,
                current_function,
            )
            if not ok:
                self._record_structured_reduction_failure(body_lines, next_index, "if_else_block_execution_failed")
                return if_index, states, [], False
            merged_live.extend(else_live)
            all_terminated.extend(else_terminated)
        elif else_inputs:
            merged_live.extend(else_inputs)

        return next_index, merged_live, all_terminated, True

    def _execute_structured_wrapper_else_clause(
        self,
        body_lines: List[str],
        next_index: int,
        else_inputs: List[Tuple[Dict[str, Expression], List[Condition], Optional[Expression]]],
        parameters: List[Dict],
        active_functions: Set[str],
        current_function,
    ) -> Tuple[
        int,
        List[Tuple[Dict[str, Expression], List[Condition], Optional[Expression]]],
        List[Tuple[Dict[str, Expression], List[Condition], Optional[Expression]]],
        bool,
    ]:
        line = body_lines[next_index]
        else_match = re.fullmatch(r"else\s*(\{)?", line)
        if else_match:
            else_start = next_index + 1
            if not else_match.group(1):
                if else_start >= len(body_lines) or body_lines[else_start] != "{":
                    return next_index, [], [], False
                else_start += 1

            next_index, else_live, else_terminated, ok = self._execute_structured_wrapper_block(
                body_lines,
                else_start,
                else_inputs,
                parameters,
                active_functions,
                current_function,
                stop_on_closing_brace=True,
            )
            return next_index, else_live, else_terminated, ok

        else_if_match = re.fullmatch(r"else\s+if\s*\((.+)\)\s*(\{)?", line)
        if else_if_match:
            return self._execute_structured_wrapper_if(
                body_lines,
                next_index,
                else_inputs,
                else_if_match.group(1).strip(),
                bool(else_if_match.group(2)),
                parameters,
                active_functions,
                current_function,
            )

        return next_index, list(else_inputs), [], True

    def _refine_wrapper_state_conditions(
        self,
        existing_conditions: List[Condition],
        condition_text: str,
        parameters: List[Dict],
        local_bindings: Dict[str, Expression],
        negated: bool = False,
    ) -> Tuple[bool, Optional[List[Condition]]]:
        condition_expr = self._parse_wrapper_condition_expr(
            condition_text,
            parameters,
            local_bindings,
        )
        if condition_expr is None:
            return False, None

        constant_truth = self._evaluate_wrapper_boolean_constant(condition_expr)
        if constant_truth is not None:
            branch_taken = not constant_truth if negated else constant_truth
            return True, list(existing_conditions) if branch_taken else None

        known_env = self._collect_wrapper_known_constant_bindings(existing_conditions)
        known_env.update(self._collect_wrapper_known_local_bindings(local_bindings))
        if known_env:
            known_truth_value = self._evaluate_expression_under_environment(condition_expr, known_env)
            if known_truth_value is not None:
                branch_taken = (known_truth_value == 0) if negated else (known_truth_value != 0)
                return True, list(existing_conditions) if branch_taken else None

        refined_condition = Condition(condition_expr, negated=negated)
        if self._wrapper_condition_conflicts_with_existing(existing_conditions, refined_condition):
            return True, None

        simplified = ConditionSimplifier.simplify_conditions(
            list(existing_conditions) + [refined_condition]
        )
        if ConditionSimplifier.is_contradiction(simplified):
            return True, None
        if self._wrapper_conditions_contradict_under_known_constants(simplified):
            return True, None
        return True, simplified

    def _collect_wrapper_known_local_bindings(
        self,
        local_bindings: Dict[str, Expression],
    ) -> Dict[str, int]:
        env: Dict[str, int] = {}
        for name, expr in (local_bindings or {}).items():
            if not name or expr is None:
                continue
            value = self._evaluate_wrapper_constant(expr)
            if value is not None:
                env[name] = value
                if expr.expr_type == ExpressionType.VARIABLE and expr.name:
                    env[expr.name] = value
                continue
            if self._resolve_expression_to_named_wrapper_target(expr) is not None:
                env[name] = 1
                if expr.expr_type == ExpressionType.VARIABLE and expr.name:
                    env[expr.name] = 1
        return env

    def _wrapper_condition_conflicts_with_existing(
        self,
        existing_conditions: List[Condition],
        new_condition: Condition,
    ) -> bool:
        for existing in existing_conditions:
            if ConditionSimplifier.are_contradictory_conditions(existing, new_condition):
                return True

            if existing.negated == new_condition.negated:
                continue

            existing_positive = Condition(self._clone_expression(existing.expression), False)
            new_positive = Condition(self._clone_expression(new_condition.expression), False)
            if ConditionSimplifier.are_equivalent_conditions(existing_positive, new_positive):
                return True
            if (
                ConditionSimplifier.get_simplified_condition_string(existing_positive)
                == ConditionSimplifier.get_simplified_condition_string(new_positive)
            ):
                return True
            if existing_positive.to_string() == new_positive.to_string():
                return True
        return False

    def _wrapper_conditions_contradict_under_known_constants(
        self,
        conditions: List[Condition],
    ) -> bool:
        env = self._collect_wrapper_known_constant_bindings(conditions)
        if not env:
            return False

        for condition in conditions:
            cond_value = self._evaluate_expression_under_environment(condition.expression, env)
            if cond_value is None:
                continue
            truth = cond_value != 0
            if condition.negated:
                truth = not truth
            if not truth:
                return True
        return False

    def _collect_wrapper_known_constant_bindings(
        self,
        conditions: List[Condition],
    ) -> Dict[str, int]:
        env: Dict[str, int] = {}
        for condition in conditions:
            name, value = self._extract_wrapper_known_constant_binding(condition)
            if name is None or value is None:
                continue
            existing = env.get(name)
            if existing is not None and existing != value:
                return {name: value, **env}
            env[name] = value
        return env

    def _extract_wrapper_known_constant_binding(
        self,
        condition: Condition,
    ) -> Tuple[Optional[str], Optional[int]]:
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None, None

        operator = expr.operator
        if condition.negated and operator == "INT_NOTEQUAL":
            operator = "INT_EQUAL"
        elif condition.negated and operator == "INT_EQUAL":
            return None, None
        elif not condition.negated and operator != "INT_EQUAL":
            return None, None
        elif condition.negated:
            return None, None

        left, right = expr.operands
        if left.expr_type in {ExpressionType.PARAMETER, ExpressionType.VARIABLE} and left.name:
            right_value = self._evaluate_wrapper_constant(right)
            if right_value is not None:
                return left.name, right_value
        if right.expr_type in {ExpressionType.PARAMETER, ExpressionType.VARIABLE} and right.name:
            left_value = self._evaluate_wrapper_constant(left)
            if left_value is not None:
                return right.name, left_value
        return None, None

    def _evaluate_wrapper_boolean_constant(self, expr: Optional[Expression]) -> Optional[bool]:
        if expr is None:
            return None

        if expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
            return bool(int(expr.value))

        if expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "BOOL_NEGATE" and expr.operands:
            operand = self._evaluate_wrapper_boolean_constant(expr.operands[0])
            return None if operand is None else (not operand)

        if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None

        left_value = self._evaluate_wrapper_constant(expr.operands[0])
        right_value = self._evaluate_wrapper_constant(expr.operands[1])
        if left_value is None or right_value is None:
            return None

        operator = expr.operator
        if operator == "INT_EQUAL":
            return left_value == right_value
        if operator == "INT_NOTEQUAL":
            return left_value != right_value
        if operator == "INT_LESS":
            return left_value < right_value
        if operator == "INT_LESSEQUAL":
            return left_value <= right_value
        if operator == "INT_SLESS":
            return self._to_signed_wrapper_value(left_value, expr.operands[0].get_bit_width()) < self._to_signed_wrapper_value(
                right_value,
                expr.operands[1].get_bit_width(),
            )
        if operator == "INT_SLESSEQUAL":
            return self._to_signed_wrapper_value(left_value, expr.operands[0].get_bit_width()) <= self._to_signed_wrapper_value(
                right_value,
                expr.operands[1].get_bit_width(),
            )
        if operator == "BOOL_AND":
            return bool(left_value) and bool(right_value)
        if operator == "BOOL_OR":
            return bool(left_value) or bool(right_value)
        if operator == "BOOL_XOR":
            return bool(left_value) ^ bool(right_value)
        return None

    def _evaluate_wrapper_constant(self, expr: Optional[Expression]) -> Optional[int]:
        if expr is None:
            return None
        if expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
            return int(expr.value)
        if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
            operand_value = self._evaluate_wrapper_constant(expr.operands[0])
            if operand_value is None:
                return None
            if expr.operator in {"INT_2COMP", "INT_NEGATE"}:
                return -operand_value
        if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands or []) == 2:
            left_value = self._evaluate_wrapper_constant(expr.operands[0])
            right_value = self._evaluate_wrapper_constant(expr.operands[1])
            if left_value is None or right_value is None:
                return None
            operator = expr.operator
            if operator == "INT_ADD":
                return left_value + right_value
            if operator == "INT_SUB":
                return left_value - right_value
            if operator == "INT_MULT":
                return left_value * right_value
            if operator == "INT_AND":
                return left_value & right_value
            if operator == "INT_OR":
                return left_value | right_value
            if operator == "INT_XOR":
                return left_value ^ right_value
        if expr.expr_type == ExpressionType.VARIABLE and expr.name:
            match = re.fullmatch(r"ADDR_([0-9a-fA-F]+)", expr.name)
            if match:
                return int(match.group(1), 16)
            pointer_target = self._resolve_pointer_symbol_wrapper_target(expr.name)
            if pointer_target is not None:
                try:
                    resolved = self._find_function_by_name(pointer_target)
                except Exception:
                    resolved = None
                if resolved is not None:
                    try:
                        return int(resolved.getEntryPoint().getOffset())
                    except Exception:
                        return 1
                return 1
            resolved_name = self._resolve_named_wrapper_target(expr.name)
            if resolved_name is not None:
                return 1
        return None

    def _to_signed_wrapper_value(self, value: int, bit_width: int) -> int:
        width = max(1, int(bit_width or 1))
        mask = (1 << width) - 1
        value &= mask
        sign_bit = 1 << (width - 1)
        if value & sign_bit:
            return value - (1 << width)
        return value

    def _parse_wrapper_condition_expr(
        self,
        text: str,
        parameters: List[Dict],
        local_bindings: Optional[Dict[str, Expression]] = None,
    ) -> Optional[Expression]:
        operand = self._parse_wrapper_expr(
            text,
            parameters,
            fallback_index=0,
            local_bindings=local_bindings,
        )
        if operand is None:
            return None

        if self._is_wrapper_boolean_expr(operand):
            return operand

        return Expression.binary_op(
            "INT_NOTEQUAL",
            operand,
            Expression.constant(0, max(1, operand.size or 4)),
        )

    def _split_top_level_binary(
        self,
        text: str,
        operator: str,
    ) -> Optional[Tuple[str, str]]:
        depth = 0
        index = 0
        while index <= len(text) - len(operator):
            char = text[index]
            if char == "(":
                depth += 1
                index += 1
                continue
            if char == ")":
                depth -= 1
                if depth < 0:
                    return None
                index += 1
                continue
            if depth == 0 and text.startswith(operator, index):
                left = text[:index].strip()
                right = text[index + len(operator):].strip()
                if not left or not right:
                    return None
                return left, right
            index += 1
        return None

    def _split_top_level_binary_any(
        self,
        text: str,
        operators: Tuple[str, ...],
    ) -> Optional[Tuple[str, str, str]]:
        depth = 0
        candidates = sorted(operators, key=len, reverse=True)
        for index in range(len(text) - 1, -1, -1):
            char = text[index]
            if char == ")":
                depth += 1
                continue
            if char == "(":
                depth -= 1
                if depth < 0:
                    return None
                continue
            if depth != 0:
                continue

            for operator in candidates:
                op_start = index - len(operator) + 1
                if op_start < 0 or text[op_start:index + 1] != operator:
                    continue
                if self._binary_operator_token_is_ambiguous(text, op_start, operator):
                    continue
                if operator in {"+", "-"} and self._is_unary_operator_position(text, op_start):
                    continue
                left = text[:op_start].strip()
                right = text[index + 1:].strip()
                if not left or not right:
                    return None
                return left, operator, right
        return None

    def _binary_operator_token_is_ambiguous(
        self,
        text: str,
        op_start: int,
        operator: str,
    ) -> bool:
        if operator not in {"<", ">"}:
            return False
        before = text[op_start - 1] if op_start > 0 else ""
        after_index = op_start + len(operator)
        after = text[after_index] if after_index < len(text) else ""
        return before == operator or after == operator

    def _is_unary_operator_position(self, text: str, index: int) -> bool:
        if index <= 0:
            return True
        prev = text[index - 1]
        return prev in "(,+-*/%<>=!&|^"

    def _is_wrapper_boolean_expr(self, expr: Expression) -> bool:
        if expr.expr_type == ExpressionType.UNARY_OP:
            return expr.operator == "BOOL_NEGATE"
        if expr.expr_type != ExpressionType.BINARY_OP:
            return False
        return expr.operator in {
            "INT_EQUAL",
            "INT_NOTEQUAL",
            "INT_LESS",
            "INT_SLESS",
            "INT_LESSEQUAL",
            "INT_SLESSEQUAL",
            "BOOL_AND",
            "BOOL_OR",
            "BOOL_XOR",
        }

    def _build_wrapper_compare_expr(
        self,
        operator: str,
        left_expr: Expression,
        right_expr: Expression,
        parameters: List[Dict],
    ) -> Expression:
        if left_expr.expr_type == ExpressionType.CONSTANT and right_expr.size:
            left_expr = Expression.constant(left_expr.value, max(1, right_expr.size))
        if right_expr.expr_type == ExpressionType.CONSTANT and left_expr.size:
            right_expr = Expression.constant(right_expr.value, max(1, left_expr.size))

        if operator == "==":
            return Expression.binary_op("INT_EQUAL", left_expr, right_expr)
        if operator == "!=":
            return Expression.binary_op("INT_NOTEQUAL", left_expr, right_expr)

        prefer_signed = self._wrapper_expr_prefers_signed_compare(left_expr, parameters)
        prefer_signed = prefer_signed or self._wrapper_expr_prefers_signed_compare(right_expr, parameters)
        less_op = "INT_SLESS" if prefer_signed else "INT_LESS"
        less_equal_op = "INT_SLESSEQUAL" if prefer_signed else "INT_LESSEQUAL"
        if operator == "<":
            return Expression.binary_op(less_op, left_expr, right_expr)
        if operator == "<=":
            return Expression.binary_op(less_equal_op, left_expr, right_expr)
        if operator == ">":
            return Expression.binary_op(less_op, right_expr, left_expr)
        return Expression.binary_op(less_equal_op, right_expr, left_expr)

    def _infer_wrapper_constant_size(
        self,
        expr_text: str,
        parameters: List[Dict],
        fallback_index: int,
    ) -> int:
        literal = expr_text.strip()
        negative = literal.startswith("-")
        if negative:
            literal = literal[1:].strip()
        if literal.lower().startswith("0x"):
            hex_digits = len(literal[2:])
            if hex_digits <= 2:
                return 1
            if hex_digits <= 4:
                return 2
            if hex_digits <= 8:
                return 4
            return 8
        if 0 <= fallback_index < len(parameters):
            return max(1, parameters[fallback_index].get("size", 4))
        try:
            value = int(expr_text, 0)
        except ValueError:
            return 4
        if -(1 << 31) <= value <= ((1 << 32) - 1):
            return 4
        return 8

    def _infer_size_from_wrapper_type_name(self, type_text: Optional[str]) -> int:
        type_lower = str(type_text or "").strip().lower()
        if not type_lower:
            return 4
        if "*" in type_lower:
            try:
                return int(self.program.getDefaultPointerSize()) if self.program is not None else 8
            except Exception:
                return 8
        undefined_match = re.search(r"undefined(\d+)", type_lower)
        if undefined_match:
            try:
                return max(1, int(undefined_match.group(1)))
            except ValueError:
                return 4
        if "bool" in type_lower or "char" in type_lower:
            return 1
        if "short" in type_lower:
            return 2
        if "long long" in type_lower or "__int64" in type_lower:
            return 8
        if "long" in type_lower:
            return 8
        if "int" in type_lower:
            return 4
        return 4

    def _parse_wrapper_concat_expr(
        self,
        expr_text: str,
        parameters: List[Dict],
        fallback_index: int,
        local_bindings: Optional[Dict[str, Expression]] = None,
    ) -> Optional[Expression]:
        match = re.fullmatch(r"CONCAT[0-9]+\((.+)\)", expr_text)
        if match is None:
            return None
        args = self._split_call_arguments(match.group(1).strip())
        if args is None or len(args) != 2:
            return None
        left_expr = self._parse_wrapper_expr(args[0], parameters, fallback_index, local_bindings)
        right_expr = self._parse_wrapper_expr(args[1], parameters, fallback_index, local_bindings)
        if left_expr is None or right_expr is None:
            return None
        piece = Expression.binary_op("PIECE", left_expr, right_expr)
        piece.size = max(1, (left_expr.size or 0) + (right_expr.size or 0))
        return piece

    def _parse_wrapper_expr(
        self,
        text: str,
        parameters: List[Dict],
        fallback_index: int,
        local_bindings: Optional[Dict[str, Expression]] = None,
    ) -> Optional[Expression]:
        def finalize(result: Optional[Expression]) -> Optional[Expression]:
            for cast_type in reversed(cast_types):
                result = self._apply_wrapper_cast(result, cast_type, parameters)
                if result is None:
                    return None
            return result

        expr_text = self._strip_outer_parentheses(text.strip())
        cast_types: List[str] = []
        previous = None
        while expr_text != previous:
            previous = expr_text
            cast_match = re.match(r"^\(\s*([A-Za-z_][A-Za-z0-9_\s\*]*)\s*\)\s*(.+)$", expr_text)
            if cast_match:
                cast_remainder = cast_match.group(2).strip()
                if not self._can_strip_leading_wrapper_cast(cast_remainder):
                    break
                cast_types.append(cast_match.group(1).strip())
                expr_text = self._strip_outer_parentheses(cast_remainder)
        expr_text = re.sub(
            r"\+\s*-(?=(?:0x[0-9a-fA-F]+|\d+)\b)",
            "- ",
            expr_text,
        )

        if not expr_text:
            return None

        if local_bindings and expr_text in local_bindings:
            return finalize(self._clone_expression(local_bindings[expr_text]))

        concat_expr = self._parse_wrapper_concat_expr(
            expr_text,
            parameters,
            fallback_index,
            local_bindings,
        )
        if concat_expr is not None:
            return finalize(concat_expr)

        split = self._split_top_level_binary_any(expr_text, ("||",))
        if split is not None:
            left_text, _operator, right_text = split
            left_expr = self._parse_wrapper_expr(left_text, parameters, fallback_index, local_bindings)
            right_expr = self._parse_wrapper_expr(right_text, parameters, fallback_index, local_bindings)
            if left_expr is None or right_expr is None:
                return None
            return finalize(Expression.binary_op("BOOL_OR", left_expr, right_expr))

        split = self._split_top_level_binary_any(expr_text, ("&&",))
        if split is not None:
            left_text, _operator, right_text = split
            left_expr = self._parse_wrapper_expr(left_text, parameters, fallback_index, local_bindings)
            right_expr = self._parse_wrapper_expr(right_text, parameters, fallback_index, local_bindings)
            if left_expr is None or right_expr is None:
                return None
            return finalize(Expression.binary_op("BOOL_AND", left_expr, right_expr))

        split = self._split_top_level_binary_any(expr_text, ("|",))
        if split is not None:
            left_text, _operator, right_text = split
            left_expr = self._parse_wrapper_expr(left_text, parameters, fallback_index, local_bindings)
            right_expr = self._parse_wrapper_expr(right_text, parameters, fallback_index, local_bindings)
            if left_expr is None or right_expr is None:
                return None
            return finalize(Expression.binary_op("INT_OR", left_expr, right_expr))

        split = self._split_top_level_binary_any(expr_text, ("^",))
        if split is not None:
            left_text, _operator, right_text = split
            left_expr = self._parse_wrapper_expr(left_text, parameters, fallback_index, local_bindings)
            right_expr = self._parse_wrapper_expr(right_text, parameters, fallback_index, local_bindings)
            if left_expr is None or right_expr is None:
                return None
            return finalize(Expression.binary_op("INT_XOR", left_expr, right_expr))

        split = self._split_top_level_binary_any(expr_text, ("&",))
        if split is not None:
            left_text, _operator, right_text = split
            left_expr = self._parse_wrapper_expr(left_text, parameters, fallback_index, local_bindings)
            right_expr = self._parse_wrapper_expr(right_text, parameters, fallback_index, local_bindings)
            if left_expr is None or right_expr is None:
                return None
            return finalize(Expression.binary_op("INT_AND", left_expr, right_expr))

        split = self._split_top_level_binary_any(expr_text, ("==", "!=", "<=", ">=", "<", ">"))
        if split is not None:
            left_text, operator, right_text = split
            left_expr = self._parse_wrapper_expr(left_text, parameters, fallback_index, local_bindings)
            right_expr = self._parse_wrapper_expr(right_text, parameters, fallback_index, local_bindings)
            if left_expr is None or right_expr is None:
                return None
            return finalize(self._build_wrapper_compare_expr(operator, left_expr, right_expr, parameters))

        split = self._split_top_level_binary_any(expr_text, ("<<", ">>"))
        if split is not None:
            left_text, operator, right_text = split
            left_expr = self._parse_wrapper_expr(left_text, parameters, fallback_index, local_bindings)
            right_expr = self._parse_wrapper_expr(right_text, parameters, fallback_index, local_bindings)
            if left_expr is None or right_expr is None:
                return None
            if operator == "<<":
                return finalize(Expression.binary_op("INT_LEFT", left_expr, right_expr))
            shift_op = (
                "INT_SRIGHT"
                if self._wrapper_expr_prefers_signed_compare(left_expr, parameters)
                else "INT_RIGHT"
            )
            return finalize(Expression.binary_op(shift_op, left_expr, right_expr))

        split = self._split_top_level_binary_any(expr_text, ("+", "-"))
        if split is not None:
            left_text, operator, right_text = split
            left_expr = self._parse_wrapper_expr(left_text, parameters, fallback_index, local_bindings)
            right_expr = self._parse_wrapper_expr(right_text, parameters, fallback_index, local_bindings)
            if left_expr is None or right_expr is None:
                return None
            return finalize(Expression.binary_op("INT_ADD" if operator == "+" else "INT_SUB", left_expr, right_expr))

        split = self._split_top_level_binary_any(expr_text, ("*", "/", "%"))
        if split is not None:
            left_text, operator, right_text = split
            left_expr = self._parse_wrapper_expr(left_text, parameters, fallback_index, local_bindings)
            right_expr = self._parse_wrapper_expr(right_text, parameters, fallback_index, local_bindings)
            if left_expr is None or right_expr is None:
                return None
            if operator == "*":
                return finalize(Expression.binary_op("INT_MULT", left_expr, right_expr))
            if operator == "/":
                division_op = (
                    "INT_SDIV"
                    if self._wrapper_expr_prefers_signed_compare(left_expr, parameters)
                    else "INT_DIV"
                )
                return finalize(Expression.binary_op(division_op, left_expr, right_expr))
            remainder_op = (
                "INT_SREM"
                if self._wrapper_expr_prefers_signed_compare(left_expr, parameters)
                else "INT_REM"
            )
            return finalize(Expression.binary_op(remainder_op, left_expr, right_expr))

        if expr_text.startswith("!"):
            operand = self._parse_wrapper_expr(
                expr_text[1:].strip(),
                parameters,
                fallback_index,
                local_bindings,
            )
            if operand is None:
                return None
            if self._is_wrapper_boolean_expr(operand):
                return finalize(Expression.unary_op("BOOL_NEGATE", operand))
            return finalize(Expression.binary_op(
                "INT_EQUAL",
                operand,
                Expression.constant(0, max(1, operand.size or 4)),
            ))

        if expr_text.startswith("+"):
            return finalize(
                self._parse_wrapper_expr(expr_text[1:].strip(), parameters, fallback_index, local_bindings)
            )

        if expr_text.startswith("&"):
            operand = self._parse_wrapper_expr(
                expr_text[1:].strip(),
                parameters,
                fallback_index,
                local_bindings,
            )
            if operand is None:
                return None
            return finalize(operand)

        if expr_text.startswith("*"):
            operand = self._parse_wrapper_expr(
                expr_text[1:].strip(),
                parameters,
                fallback_index,
                local_bindings,
            )
            if operand is None:
                return None
            if local_bindings:
                binding_key = self._wrapper_memory_binding_key(operand)
                if binding_key in local_bindings:
                    return finalize(self._clone_expression(local_bindings[binding_key]))
            pointer_size = max(1, operand.size or 8)
            return finalize(Expression.memory(operand, size=pointer_size))

        if expr_text.startswith("-") and not re.fullmatch(r"-?(?:0x[0-9a-fA-F]+|\d+)", expr_text):
            operand = self._parse_wrapper_expr(
                expr_text[1:].strip(),
                parameters,
                fallback_index,
                local_bindings,
            )
            if operand is None:
                return None
            return finalize(Expression.binary_op(
                "INT_SUB",
                Expression.constant(0, max(1, operand.size or 4)),
                operand,
            ))

        for index, param in enumerate(parameters):
            if expr_text == param.get("name"):
                return finalize(Expression.parameter(
                    expr_text,
                    index=index,
                    data_type=param.get("data_type"),
                    size=param.get("size", 4),
                    storage_info=self._coerce_wrapper_storage_info(param.get("storage")),
                ))

        const_match = re.fullmatch(r"(-?(?:0x[0-9a-fA-F]+|\d+))", expr_text)
        if const_match:
            value = int(const_match.group(1), 0)
            size = self._infer_wrapper_constant_size(expr_text, parameters, fallback_index)
            return finalize(Expression.constant(value, size=size))

        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", expr_text):
            resolved_name = self._resolve_named_wrapper_target(expr_text)
            if resolved_name is not None or expr_text.startswith(("PTR_", "DAT_", "LAB_", "ADDR_")):
                return finalize(Expression.variable(expr_text, size=8))
            if self._looks_like_decompiler_temp_name(expr_text):
                return finalize(Expression.variable(expr_text, size=4))

        return None

    def _can_strip_leading_wrapper_cast(self, remainder_text: str) -> bool:
        text = str(remainder_text or "").strip()
        if not text:
            return False

        if text.startswith("("):
            depth = 0
            for index, char in enumerate(text):
                if char == "(":
                    depth += 1
                elif char == ")":
                    depth -= 1
                    if depth == 0:
                        return index == len(text) - 1
            return False

        if self._split_top_level_binary_any(
            text,
            ("||", "&&", "|", "^", "&", "==", "!=", "<=", ">=", "<", ">", "<<", ">>", "+", "-", "*", "/", "%"),
        ) is not None:
            return False
        return True

    def _apply_wrapper_cast(
        self,
        expr: Optional[Expression],
        type_text: str,
        parameters: List[Dict],
    ) -> Optional[Expression]:
        if expr is None:
            return None

        target_size = self._infer_size_from_wrapper_type_name(type_text)
        if target_size <= 0:
            return expr

        source_size = max(1, int(getattr(expr, "size", 0) or 4))
        target_type = type_text.strip()
        target_signedness = self._signedness_from_wrapper_type_name(target_type)

        if target_size > source_size:
            source_signedness = self._infer_wrapper_expr_signedness(expr, parameters)
            extend_signed = source_signedness is True
            if source_signedness is None and target_signedness is True:
                extend_signed = True
            widened = Expression.unary_op("INT_SEXT" if extend_signed else "INT_ZEXT", expr)
            widened.size = target_size
            widened.data_type = target_type
            return widened

        if target_size < source_size:
            narrowed = Expression.binary_op("SUBPIECE", expr, Expression.constant(0, 4))
            narrowed.size = target_size
            narrowed.data_type = target_type
            return narrowed

        expr.data_type = target_type
        return expr

    def _wrapper_expr_prefers_signed_compare(
        self,
        expr: Expression,
        parameters: List[Dict],
    ) -> bool:
        signedness = self._infer_wrapper_expr_signedness(expr, parameters)
        return signedness is True

    def _infer_wrapper_expr_signedness(
        self,
        expr: Optional[Expression],
        parameters: List[Dict],
    ) -> Optional[bool]:
        if expr is None:
            return None

        expr_type_signedness = self._signedness_from_wrapper_type_name(expr.data_type)
        if expr_type_signedness is not None:
            return expr_type_signedness

        if expr.expr_type == ExpressionType.PARAMETER and expr.name:
            for param in parameters:
                if expr.name != param.get("name"):
                    continue
                if "is_signed" in param:
                    return bool(param.get("is_signed"))
                param_type_signedness = self._signedness_from_wrapper_type_name(param.get("data_type"))
                if param_type_signedness is not None:
                    return param_type_signedness
                return None

        if expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
            return True if int(expr.value) < 0 else None

        if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
            return self._infer_wrapper_expr_signedness(expr.operands[0], parameters)

        if expr.expr_type == ExpressionType.BINARY_OP and expr.operands:
            if expr.operator == "PIECE" and len(expr.operands) == 2:
                high_expr, low_expr = expr.operands
                low_signedness = self._infer_wrapper_expr_signedness(low_expr, parameters)
                if (
                    high_expr.expr_type == ExpressionType.VARIABLE
                    and high_expr.name
                    and self._looks_like_wrapper_fragment_temp_name(high_expr.name)
                ):
                    return low_signedness

            if expr.operator in {
                "INT_EQUAL",
                "INT_NOTEQUAL",
                "INT_LESS",
                "INT_SLESS",
                "INT_LESSEQUAL",
                "INT_SLESSEQUAL",
                "BOOL_AND",
                "BOOL_OR",
                "BOOL_XOR",
            }:
                return None

            operand_signedness = {
                value
                for value in (
                    self._infer_wrapper_expr_signedness(operand, parameters)
                    for operand in expr.operands
                )
                if value is not None
            }
            if len(operand_signedness) == 1:
                return operand_signedness.pop()

        return None

    def _signedness_from_wrapper_type_name(self, data_type: Optional[str]) -> Optional[bool]:
        type_lower = str(data_type or "").lower()
        if not type_lower:
            return None
        if "unsigned" in type_lower or type_lower.startswith("u"):
            return False
        if any(token in type_lower for token in ("int", "long", "short", "char")):
            return True
        return None

    def _extract_wrapper_body_statements(self, c_text: str) -> Optional[List[str]]:
        body_lines = self._extract_structured_wrapper_body_lines(c_text)
        if body_lines is None:
            return None

        statements = [
            line
            for line in body_lines
            if line not in {"{", "}"} and not line.endswith("{")
        ]
        return statements or None

    def _extract_structured_wrapper_body_lines(self, c_text: str) -> Optional[List[str]]:
        lines = self._normalize_wrapper_c_lines(c_text)
        if not lines:
            return None

        body_lines: List[str] = []
        body_started = False
        body_depth = 0
        for line in lines:
            if not body_started:
                if line == "{":
                    body_started = True
                    body_depth = 1
                    continue
                if self._looks_like_wrapper_header_line(line) and line.endswith("{"):
                    body_started = True
                    body_depth = 1
                continue

            if line == "}" and body_depth == 1:
                return body_lines

            body_lines.append(line)
            body_depth += line.count("{") - line.count("}")
            if body_depth <= 0:
                return None

        return None

    def _parse_counted_reduction_from_c_text(
        self,
        c_text: str,
        parameters: List[Dict],
        address: str,
    ) -> Optional[List[ReturnInfo]]:
        from ..transform.expander import ExpandedValue

        body_lines = self._extract_structured_wrapper_body_lines(c_text)
        if not body_lines:
            return None

        self._last_structured_reduction_failure = None
        next_index, live_states, returned_states, ok = self._execute_structured_reduction_block(
            body_lines,
            0,
            [({}, [], set())],
            parameters,
        )
        if not ok or next_index != len(body_lines) or live_states or not returned_states:
            if self.debug:
                failure_line = None
                if 0 <= next_index < len(body_lines):
                    failure_line = body_lines[next_index]
                failure_reason = None
                failure_detail_line = None
                failure_detail = None
                if self._last_structured_reduction_failure is not None:
                    failure_reason = self._last_structured_reduction_failure.get("reason")
                    failure_detail_line = self._last_structured_reduction_failure.get("line")
                    failure_detail = self._last_structured_reduction_failure.get("detail")
                self._debug_print(
                    "Counted reduction recovery failed while executing structured body "
                    f"(ok={ok}, next_index={next_index}, live_states={len(live_states)}, "
                    f"returned_states={len(returned_states)}, failure_line={failure_line!r})"
                )
                if failure_reason is not None:
                    self._debug_print(
                        "Structured reduction inner failure: "
                        f"reason={failure_reason}, line={failure_detail_line!r}, detail={failure_detail!r}"
                    )
            return None

        expanded_values = []
        for _bindings, conditions, return_expr, _nonnegative_vars in returned_states:
            simplified = ConditionSimplifier.simplify_conditions(list(conditions))
            if ConditionSimplifier.is_contradiction(simplified):
                continue
            expanded_values.append(ExpandedValue(return_expr, simplified))

        if not expanded_values:
            return None
        return self._build_return_infos_from_expansions(address, expanded_values, 0)

    def _execute_structured_reduction_block(
        self,
        body_lines: List[str],
        start_index: int,
        states: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]],
        parameters: List[Dict],
        stop_on_closing_brace: bool = False,
    ) -> Tuple[
        int,
        List[Tuple[Dict[str, Expression], List[Condition], Set[str]]],
        List[Tuple[Dict[str, Expression], List[Condition], Expression, Set[str]]],
        bool,
    ]:
        live_states = [
            (dict(bindings), list(conditions), set(nonnegative_vars))
            for bindings, conditions, nonnegative_vars in states
        ]
        returned_states: List[Tuple[Dict[str, Expression], List[Condition], Expression, Set[str]]] = []
        index = start_index

        while index < len(body_lines):
            line = body_lines[index]

            if line == "}":
                if stop_on_closing_brace:
                    return index + 1, live_states, returned_states, True
                return index, live_states, returned_states, False

            if line == "{":
                index += 1
                continue

            if not live_states:
                next_index = index
                if stop_on_closing_brace:
                    next_index = self._advance_to_structured_block_exit(body_lines, index)
                return next_index, [], returned_states, True

            updated_states = self._apply_structured_reduction_declaration(
                line,
                live_states,
                parameters,
            )
            if updated_states is not None:
                live_states = updated_states
                index += 1
                continue

            add_assign = self._parse_structured_reduction_add_assign(line)
            if add_assign is not None:
                updated_states = self._apply_structured_reduction_add_assign(
                    add_assign,
                    live_states,
                    parameters,
                )
                if updated_states is None:
                    return index, live_states, returned_states, False
                live_states = updated_states
                index += 1
                continue

            increment_assign = self._parse_structured_reduction_increment(line)
            if increment_assign is not None:
                updated_states = self._apply_structured_reduction_add_assign(
                    increment_assign,
                    live_states,
                    parameters,
                )
                if updated_states is None:
                    return index, live_states, returned_states, False
                live_states = updated_states
                index += 1
                continue

            simple_assign = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.+)\s*;", line)
            if simple_assign is not None:
                updated_states = self._apply_structured_reduction_assignment(
                    simple_assign.group(1),
                    simple_assign.group(2),
                    live_states,
                    parameters,
                )
                if updated_states is None:
                    return index, live_states, returned_states, False
                live_states = updated_states
                index += 1
                continue

            if line.startswith("while ") or line.startswith("while("):
                next_index, loop_states, ok = self._execute_structured_reduction_while(
                    body_lines,
                    index,
                    live_states,
                    parameters,
                )
                if not ok:
                    self._record_structured_reduction_failure(body_lines, index, "while_loop_recovery_failed")
                    return index, live_states, returned_states, False
                live_states = loop_states
                index = next_index
                continue

            if line == "do {" or line == "do{" or line == "do":
                next_index, loop_states, ok = self._execute_structured_reduction_do_while(
                    body_lines,
                    index,
                    live_states,
                    parameters,
                )
                if not ok:
                    self._record_structured_reduction_failure(body_lines, index, "do_while_recovery_failed")
                    return index, live_states, returned_states, False
                live_states = loop_states
                index = next_index
                continue

            if line.startswith("for ") or line.startswith("for("):
                next_index, loop_states, ok = self._execute_structured_reduction_for(
                    body_lines,
                    index,
                    live_states,
                    parameters,
                )
                if not ok:
                    self._record_structured_reduction_failure(body_lines, index, "for_loop_recovery_failed")
                    return index, live_states, returned_states, False
                live_states = loop_states
                index = next_index
                continue

            if_match = re.fullmatch(r"if\s*\((.+)\)\s*(\{)?", line)
            if if_match is not None:
                next_index, branch_live_states, branch_returned, ok = self._execute_structured_reduction_if(
                    body_lines,
                    index,
                    live_states,
                    if_match.group(1).strip(),
                    bool(if_match.group(2)),
                    parameters,
                )
                if not ok:
                    self._record_structured_reduction_failure(body_lines, index, "if_branch_recovery_failed")
                    return index, live_states, returned_states, False
                live_states = branch_live_states
                returned_states.extend(branch_returned)
                index = next_index
                continue

            return_match = re.fullmatch(r"return\s+(.+)\s*;", line)
            if return_match is not None:
                expr_text = return_match.group(1).strip()
                for bindings, conditions, nonnegative_vars in live_states:
                    return_expr = self._parse_wrapper_expr(
                        expr_text,
                        parameters,
                        fallback_index=0,
                        local_bindings=bindings,
                    )
                    if return_expr is None:
                        self._record_structured_reduction_failure(body_lines, index, "return_expr_parse_failed")
                        return index, live_states, returned_states, False
                    returned_states.append(
                        (
                            dict(bindings),
                            list(conditions),
                            self._clone_expression(return_expr),
                            set(nonnegative_vars),
                        )
                    )
                next_index = index + 1
                if stop_on_closing_brace:
                    next_index = self._advance_to_structured_block_exit(body_lines, next_index)
                return next_index, [], returned_states, True

            self._record_structured_reduction_failure(body_lines, index, "unsupported_statement")
            return index, live_states, returned_states, False

        return index, live_states, returned_states, True

    def _execute_structured_reduction_if(
        self,
        body_lines: List[str],
        if_index: int,
        states: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]],
        condition_text: str,
        header_has_brace: bool,
        parameters: List[Dict],
    ) -> Tuple[
        int,
        List[Tuple[Dict[str, Expression], List[Condition], Set[str]]],
        List[Tuple[Dict[str, Expression], List[Condition], Expression, Set[str]]],
        bool,
    ]:
        then_start = if_index + 1
        if not header_has_brace:
            if then_start >= len(body_lines) or body_lines[then_start] != "{":
                return if_index, states, [], False
            then_start += 1

        then_inputs: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]] = []
        else_inputs: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]] = []
        for bindings, conditions, nonnegative_vars in states:
            ok_then, refined_then = self._refine_wrapper_state_conditions(
                conditions,
                condition_text,
                parameters,
                bindings,
                negated=False,
            )
            if not ok_then:
                return if_index, states, [], False
            if refined_then is not None:
                then_inputs.append((dict(bindings), refined_then, set(nonnegative_vars)))

            ok_else, refined_else = self._refine_wrapper_state_conditions(
                conditions,
                condition_text,
                parameters,
                bindings,
                negated=True,
            )
            if not ok_else:
                return if_index, states, [], False
            if refined_else is not None:
                else_inputs.append((dict(bindings), refined_else, set(nonnegative_vars)))

        next_index, then_live, then_returned, ok = self._execute_structured_reduction_block(
            body_lines,
            then_start,
            then_inputs,
            parameters,
            stop_on_closing_brace=True,
        )
        if not ok:
            return if_index, states, [], False

        merged_live = list(then_live)
        merged_returned = list(then_returned)

        if next_index < len(body_lines):
            next_index, else_live, else_returned, ok = self._execute_structured_reduction_else_clause(
                body_lines,
                next_index,
                else_inputs,
                parameters,
            )
            if not ok:
                return if_index, states, [], False
            merged_live.extend(else_live)
            merged_returned.extend(else_returned)
        elif else_inputs:
            merged_live.extend(else_inputs)

        return next_index, merged_live, merged_returned, True

    def _execute_structured_reduction_else_clause(
        self,
        body_lines: List[str],
        next_index: int,
        else_inputs: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]],
        parameters: List[Dict],
    ) -> Tuple[
        int,
        List[Tuple[Dict[str, Expression], List[Condition], Set[str]]],
        List[Tuple[Dict[str, Expression], List[Condition], Expression, Set[str]]],
        bool,
    ]:
        line = body_lines[next_index]
        else_match = re.fullmatch(r"else\s*(\{)?", line)
        if else_match:
            else_start = next_index + 1
            if not else_match.group(1):
                if else_start >= len(body_lines) or body_lines[else_start] != "{":
                    return next_index, [], [], False
                else_start += 1

            next_index, else_live, else_returned, ok = self._execute_structured_reduction_block(
                body_lines,
                else_start,
                else_inputs,
                parameters,
                stop_on_closing_brace=True,
            )
            return next_index, else_live, else_returned, ok

        else_if_match = re.fullmatch(r"else\s+if\s*\((.+)\)\s*(\{)?", line)
        if else_if_match:
            return self._execute_structured_reduction_if(
                body_lines,
                next_index,
                else_inputs,
                else_if_match.group(1).strip(),
                bool(else_if_match.group(2)),
                parameters,
            )

        return next_index, list(else_inputs), [], True

    def _apply_structured_reduction_declaration(
        self,
        line: str,
        states: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]],
        parameters: List[Dict],
    ) -> Optional[List[Tuple[Dict[str, Expression], List[Condition], Set[str]]]]:
        leading_token = line.split(None, 1)[0] if line.split() else ""
        if leading_token in {"return", "for", "if", "else", "while", "switch"}:
            return None

        decl_init = re.fullmatch(
            r"[A-Za-z_][A-Za-z0-9_\s\*]*\s+([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.+)\s*;",
            line,
        )
        if decl_init is not None:
            return self._apply_structured_reduction_assignment(
                decl_init.group(1),
                decl_init.group(2),
                states,
                parameters,
            )

        decl_match = re.fullmatch(
            r"([A-Za-z_][A-Za-z0-9_\s\*]*)\s+([A-Za-z_][A-Za-z0-9_]*)\s*;",
            line,
        )
        if decl_match is not None:
            type_text = decl_match.group(1).strip()
            name = decl_match.group(2).strip()
            size = self._infer_size_from_wrapper_type_name(type_text)
            if self._looks_like_wrapper_fragment_temp_name(name) or size > 4:
                declared_expr = Expression.variable(
                    name,
                    data_type=type_text,
                    size=size,
                )
                next_states = []
                for bindings, conditions, nonnegative_vars in states:
                    new_bindings = dict(bindings)
                    new_bindings.setdefault(name, self._clone_expression(declared_expr))
                    next_states.append((new_bindings, list(conditions), set(nonnegative_vars)))
                return next_states
            return [
                (dict(bindings), list(conditions), set(nonnegative_vars))
                for bindings, conditions, nonnegative_vars in states
            ]
        return None

    def _apply_structured_reduction_assignment(
        self,
        target_name: str,
        expr_text: str,
        states: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]],
        parameters: List[Dict],
    ) -> Optional[List[Tuple[Dict[str, Expression], List[Condition], Set[str]]]]:
        next_states = []
        for bindings, conditions, nonnegative_vars in states:
            parsed_expr = self._parse_wrapper_expr(
                expr_text,
                parameters,
                fallback_index=0,
                local_bindings=bindings,
            )
            if parsed_expr is None:
                return None
            previous_expr = bindings.get(target_name)
            if previous_expr is not None:
                if not parsed_expr.data_type and previous_expr.data_type:
                    parsed_expr.data_type = previous_expr.data_type
                if (getattr(parsed_expr, "size", 0) or 0) <= 0 and (getattr(previous_expr, "size", 0) or 0) > 0:
                    parsed_expr.size = previous_expr.size
            new_bindings = dict(bindings)
            new_bindings[target_name] = self._clone_expression(parsed_expr)
            next_states.append((new_bindings, list(conditions), set(nonnegative_vars)))
        return next_states

    def _parse_structured_reduction_add_assign(self, line: str) -> Optional[Tuple[str, str]]:
        match = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_]*)\s*\+=\s*(.+)\s*;", line)
        if match is None:
            return None
        return match.group(1), match.group(2)

    def _parse_structured_reduction_increment(self, line: str) -> Optional[Tuple[str, str]]:
        post = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_]*)\s*\+\+\s*;", line)
        if post is not None:
            return post.group(1), "1"
        pre = re.fullmatch(r"\+\+\s*([A-Za-z_][A-Za-z0-9_]*)\s*;", line)
        if pre is not None:
            return pre.group(1), "1"
        return None

    def _apply_structured_reduction_add_assign(
        self,
        add_assign: Tuple[str, str],
        states: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]],
        parameters: List[Dict],
    ) -> Optional[List[Tuple[Dict[str, Expression], List[Condition], Set[str]]]]:
        target_name, expr_text = add_assign
        next_states = []
        for bindings, conditions, nonnegative_vars in states:
            current_value = bindings.get(target_name)
            if current_value is None:
                return None
            delta_expr = self._parse_wrapper_expr(
                expr_text,
                parameters,
                fallback_index=0,
                local_bindings=bindings,
            )
            if delta_expr is None:
                return None
            updated_value = Expression.binary_op(
                "INT_ADD",
                self._clone_expression(current_value),
                delta_expr,
            )
            updated_value.size = max(
                getattr(current_value, "size", 0) or 0,
                getattr(delta_expr, "size", 0) or 0,
                4,
            )
            new_bindings = dict(bindings)
            new_bindings[target_name] = updated_value
            next_states.append((new_bindings, list(conditions), set(nonnegative_vars)))
        return next_states

    def _execute_structured_reduction_while(
        self,
        body_lines: List[str],
        while_index: int,
        states: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]],
        parameters: List[Dict],
    ) -> Tuple[int, List[Tuple[Dict[str, Expression], List[Condition], Set[str]]], bool]:
        parsed = self._parse_structured_reduction_while_header(body_lines[while_index])
        if parsed is None or parsed["trailing"]:
            return while_index, states, False

        body_start = while_index + 1
        if not parsed["header_has_brace"]:
            if body_start >= len(body_lines) or body_lines[body_start] != "{":
                return while_index, states, False
            body_start += 1

        next_states: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]] = []
        for bindings, conditions, nonnegative_vars in states:
            loop_spec = self._infer_structured_reduction_loop_from_condition(
                parsed["condition_text"],
                bindings,
                parameters,
            )
            if loop_spec is None:
                if self.debug:
                    self._debug_print(
                        "Structured reduction while-loop recovery failed: "
                        f"unsupported condition '{parsed['condition_text']}'"
                    )
                return while_index, states, False

            positive_cond = loop_spec["positive_cond"]
            positive_cond_expr = getattr(positive_cond, "expression", None)
            if positive_cond_expr is None:
                return while_index, states, False

            zero_conditions = ConditionSimplifier.simplify_conditions(
                list(conditions) + [Condition(self._clone_expression(positive_cond_expr), True)]
            )
            if not ConditionSimplifier.is_contradiction(zero_conditions):
                next_states.append((dict(bindings), zero_conditions, set(nonnegative_vars)))

            positive_conditions = ConditionSimplifier.simplify_conditions(list(conditions) + [positive_cond])
            if ConditionSimplifier.is_contradiction(positive_conditions):
                continue

            loop_bindings = dict(bindings)
            loop_bindings[loop_spec["counter_name"]] = Expression.variable(
                loop_spec["counter_name"],
                size=max(1, loop_spec["start_expr"].size or 4),
            )
            loop_nonnegative_vars = set(nonnegative_vars)
            start_lower_bound = self._structured_expr_lower_bound(
                loop_spec["start_expr"],
                loop_nonnegative_vars,
            )
            if start_lower_bound is not None and start_lower_bound >= 0:
                loop_nonnegative_vars.add(loop_spec["counter_name"])

            body_index, body_live_states, body_returned, ok = self._execute_structured_reduction_block(
                body_lines,
                body_start,
                [(loop_bindings, positive_conditions, loop_nonnegative_vars)],
                parameters,
                stop_on_closing_brace=True,
            )
            if not ok or body_returned or not body_live_states:
                return while_index, states, False
            counter_step = self._structured_loop_counter_step(
                body_live_states[0][0].get(loop_spec["counter_name"]),
                loop_spec["counter_name"],
            )
            if counter_step is None or not self._structured_counter_step_matches_allowed(
                counter_step,
                loop_spec["allowed_steps"],
            ):
                return while_index, states, False
            if not all(
                self._structured_loop_counter_step(
                    body_bindings.get(loop_spec["counter_name"]),
                    loop_spec["counter_name"],
                )
                == counter_step
                for body_bindings, _body_conditions, _body_nonnegative_vars in body_live_states
            ):
                return while_index, states, False

            positive_proved = self._structured_condition_constant_truth(
                positive_cond,
                loop_nonnegative_vars,
            ) is True
            summarized = self._summarize_structured_reduction_loop_cases(
                bindings,
                body_live_states,
                loop_spec["counter_name"],
                loop_spec["start_expr"],
                loop_spec["limit_expr"],
                parameters,
                loop_nonnegative_vars,
                require_invariant_conditions=not positive_proved,
                counter_step=counter_step,
            )
            if summarized is None:
                symbolic_loop_bindings = self._build_symbolic_structured_loop_bindings(
                    bindings,
                    counter_name=loop_spec["counter_name"],
                )
                symbolic_body_index, symbolic_body_live_states, symbolic_body_returned, symbolic_ok = self._execute_structured_reduction_block(
                    body_lines,
                    body_start,
                    [(symbolic_loop_bindings, positive_conditions, loop_nonnegative_vars)],
                    parameters,
                    stop_on_closing_brace=True,
                )
                if (
                    symbolic_ok
                    and not symbolic_body_returned
                    and symbolic_body_live_states
                    and symbolic_body_index == body_index
                ):
                    summarized = self._summarize_structured_reduction_loop_cases(
                        bindings,
                        body_live_states,
                        loop_spec["counter_name"],
                        loop_spec["start_expr"],
                        loop_spec["limit_expr"],
                        parameters,
                        loop_nonnegative_vars,
                        require_invariant_conditions=not positive_proved,
                        counter_step=counter_step,
                        recurrence_base_bindings=symbolic_loop_bindings,
                        recurrence_body_states=symbolic_body_live_states,
                    )
            if summarized is None:
                return while_index, states, False
            next_states.extend(summarized)

        loop_end = self._advance_to_structured_block_exit(body_lines, body_start)
        return loop_end, next_states, True

    def _execute_structured_reduction_do_while(
        self,
        body_lines: List[str],
        do_index: int,
        states: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]],
        parameters: List[Dict],
    ) -> Tuple[int, List[Tuple[Dict[str, Expression], List[Condition], Set[str]]], bool]:
        body_start = do_index + 1
        if body_lines[do_index] not in {"do {", "do{"}:
            if body_start >= len(body_lines) or body_lines[body_start] != "{":
                return do_index, states, False
            body_start += 1

        next_states: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]] = []
        trailing_index: Optional[int] = None
        trailing: Optional[Dict[str, Any]] = None
        loop_condition_alias_name: Optional[str] = None

        for initial_bindings, initial_conditions, initial_nonnegative_vars in states:
            first_pass_index, first_pass_live, first_pass_returned, ok = self._execute_structured_reduction_block(
                body_lines,
                body_start,
                [(dict(initial_bindings), list(initial_conditions), set(initial_nonnegative_vars))],
                parameters,
                stop_on_closing_brace=True,
            )
            if not ok or first_pass_returned:
                self._record_structured_reduction_failure(body_lines, body_start, "do_while_first_pass_failed")
                return do_index, states, False
            if first_pass_index >= len(body_lines):
                self._record_structured_reduction_failure(body_lines, do_index, "do_while_missing_trailing_condition")
                return do_index, states, False
            if trailing_index is None:
                trailing_index = first_pass_index
                trailing = self._parse_structured_reduction_while_header(body_lines[first_pass_index])
                if trailing is None or not trailing["trailing"]:
                    self._record_structured_reduction_failure(body_lines, first_pass_index, "do_while_invalid_trailing_header")
                    return do_index, states, False
                alias_match = re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", trailing["condition_text"])
                if alias_match:
                    loop_condition_alias_name = alias_match.group(0)
            elif first_pass_index != trailing_index:
                return do_index, states, False

            symbolic_first_pass_live: Optional[List[Tuple[Dict[str, Expression], List[Condition], Set[str]]]] = None
            symbolic_first_pass_index: Optional[int] = None
            for index, (bindings, conditions, nonnegative_vars) in enumerate(first_pass_live):
                loop_spec = self._infer_structured_reduction_loop_from_condition(
                    cast(Dict[str, Any], trailing)["condition_text"],
                    bindings,
                    parameters,
                )
                if loop_spec is None:
                    symbolic_initial_bindings = self._build_symbolic_structured_loop_bindings(
                        initial_bindings,
                        counter_name="",
                    )
                    symbolic_initial_state = [
                        (symbolic_initial_bindings, list(initial_conditions), set(initial_nonnegative_vars))
                    ]
                    symbolic_first_pass_index, symbolic_first_pass_live, symbolic_first_pass_returned, symbolic_ok = self._execute_structured_reduction_block(
                        body_lines,
                        body_start,
                        symbolic_initial_state,
                        parameters,
                        stop_on_closing_brace=True,
                    )
                    if (
                        not symbolic_ok
                        or symbolic_first_pass_returned
                        or symbolic_first_pass_index != first_pass_index
                        or symbolic_first_pass_live is None
                        or index >= len(symbolic_first_pass_live)
                    ):
                        if self.debug:
                            self._debug_print(
                                "Structured reduction do-while recovery failed: "
                                f"unsupported trailing condition '{cast(Dict[str, Any], trailing)['condition_text']}'"
                            )
                        self._record_structured_reduction_failure(body_lines, first_pass_index, "do_while_trailing_condition_unsupported")
                        return do_index, states, False
                    loop_spec = self._infer_structured_reduction_loop_from_condition(
                        cast(Dict[str, Any], trailing)["condition_text"],
                        symbolic_first_pass_live[index][0],
                        parameters,
                    )
                    if loop_spec is None:
                        if self.debug:
                            self._debug_print(
                                "Structured reduction do-while recovery failed: "
                                f"unsupported trailing condition '{cast(Dict[str, Any], trailing)['condition_text']}'"
                            )
                        return do_index, states, False
                    concrete_start_expr = bindings.get(loop_spec["counter_name"])
                    if concrete_start_expr is None:
                        self._record_structured_reduction_failure(body_lines, body_start, "do_while_missing_concrete_start_expr")
                        return do_index, states, False
                    reparsed = None
                    if loop_condition_alias_name:
                        alias_expr = symbolic_first_pass_live[index][0].get(loop_condition_alias_name)
                        counter_step_hint = self._structured_concrete_counter_step_hint(
                            initial_bindings.get(loop_spec["counter_name"]),
                            concrete_start_expr,
                        )
                        reparsed = self._derive_structured_do_while_alias_loop_condition(
                            loop_spec["counter_name"],
                            concrete_start_expr,
                            alias_expr,
                            counter_step_hint=counter_step_hint,
                        )
                    if reparsed is None:
                        reparsed = self._parse_structured_reduction_loop_condition(
                            loop_spec["counter_name"],
                            cast(Dict[str, Any], trailing)["condition_text"],
                            parameters,
                            symbolic_first_pass_live[index][0],
                            concrete_start_expr,
                        )
                    if reparsed is None:
                        self._record_structured_reduction_failure(body_lines, first_pass_index, "do_while_reparse_condition_failed")
                        return do_index, states, False
                    concrete_limit_expr, concrete_positive_cond = reparsed
                    loop_spec = dict(loop_spec)
                    loop_spec["start_expr"] = concrete_start_expr
                    loop_spec["limit_expr"] = concrete_limit_expr
                    loop_spec["positive_cond"] = concrete_positive_cond

                positive_cond = loop_spec["positive_cond"]
                positive_cond_expr = getattr(positive_cond, "expression", None)
                if positive_cond_expr is None:
                    self._record_structured_reduction_failure(body_lines, first_pass_index, "do_while_missing_positive_condition")
                    return do_index, states, False

                done_conditions = ConditionSimplifier.simplify_conditions(
                    list(conditions) + [self._make_structured_negative_condition(positive_cond)]
                )
                if not ConditionSimplifier.is_contradiction(done_conditions):
                    next_states.append((dict(bindings), done_conditions, set(nonnegative_vars)))

                continue_conditions = ConditionSimplifier.simplify_conditions(list(conditions) + [positive_cond])
                if ConditionSimplifier.is_contradiction(continue_conditions):
                    continue

                loop_bindings = dict(bindings)
                loop_bindings[loop_spec["counter_name"]] = Expression.variable(
                    loop_spec["counter_name"],
                    size=max(1, loop_spec["start_expr"].size or 4),
                )
                loop_carried_names = set(initial_bindings.keys())
                loop_carried_names.add(loop_spec["counter_name"])
                ignored_change_names = {
                    name
                    for name in bindings.keys()
                    if name not in loop_carried_names
                }
                if loop_condition_alias_name:
                    ignored_change_names.add(loop_condition_alias_name)
                loop_nonnegative_vars = set(nonnegative_vars)
                start_lower_bound = self._structured_expr_lower_bound(
                    loop_spec["start_expr"],
                    loop_nonnegative_vars,
                )
                if start_lower_bound is not None and start_lower_bound >= 0:
                    loop_nonnegative_vars.add(loop_spec["counter_name"])

                body_index, body_live_states, body_returned, ok = self._execute_structured_reduction_block(
                    body_lines,
                    body_start,
                    [(loop_bindings, continue_conditions, loop_nonnegative_vars)],
                    parameters,
                    stop_on_closing_brace=True,
                )
                if not ok or body_returned or not body_live_states:
                    self._record_structured_reduction_failure(body_lines, body_start, "do_while_body_execution_failed")
                    return do_index, states, False
                counter_step = self._structured_loop_counter_step(
                    body_live_states[0][0].get(loop_spec["counter_name"]),
                    loop_spec["counter_name"],
                )
                if counter_step is None or not self._structured_counter_step_matches_allowed(
                    counter_step,
                    loop_spec["allowed_steps"],
                ):
                    self._record_structured_reduction_failure(body_lines, body_start, "do_while_counter_step_unsupported")
                    return do_index, states, False
                if not all(
                    self._structured_loop_counter_step(
                        body_bindings.get(loop_spec["counter_name"]),
                        loop_spec["counter_name"],
                    )
                    == counter_step
                    for body_bindings, _body_conditions, _body_nonnegative_vars in body_live_states
                ):
                    self._record_structured_reduction_failure(body_lines, body_start, "do_while_counter_step_inconsistent")
                    return do_index, states, False

                positive_proved = self._structured_condition_constant_truth(
                    positive_cond,
                    loop_nonnegative_vars,
                ) is True
                summarized = self._summarize_structured_reduction_loop_cases(
                    bindings,
                    body_live_states,
                    loop_spec["counter_name"],
                    loop_spec["start_expr"],
                    loop_spec["limit_expr"],
                    parameters,
                    loop_nonnegative_vars,
                    require_invariant_conditions=not positive_proved,
                    counter_step=counter_step,
                    ignored_change_names=ignored_change_names,
                )
                if summarized is None:
                    symbolic_loop_bindings = self._build_symbolic_structured_loop_bindings(
                        bindings,
                        counter_name=loop_spec["counter_name"],
                        symbolic_names=loop_carried_names,
                    )
                    symbolic_body_index, symbolic_body_live_states, symbolic_body_returned, symbolic_ok = self._execute_structured_reduction_block(
                        body_lines,
                        body_start,
                        [(symbolic_loop_bindings, continue_conditions, loop_nonnegative_vars)],
                        parameters,
                        stop_on_closing_brace=True,
                    )
                    if (
                        symbolic_ok
                        and not symbolic_body_returned
                        and symbolic_body_live_states
                        and symbolic_body_index == body_index
                    ):
                        summarized = self._summarize_structured_reduction_loop_cases(
                            bindings,
                            body_live_states,
                            loop_spec["counter_name"],
                            loop_spec["start_expr"],
                            loop_spec["limit_expr"],
                            parameters,
                            loop_nonnegative_vars,
                            require_invariant_conditions=not positive_proved,
                            counter_step=counter_step,
                            recurrence_base_bindings=symbolic_loop_bindings,
                            recurrence_body_states=symbolic_body_live_states,
                            ignored_change_names=ignored_change_names,
                        )
                if summarized is None:
                    self._record_structured_reduction_failure(body_lines, body_start, "do_while_loop_summary_failed")
                    return do_index, states, False
                if loop_condition_alias_name:
                    summarized = self._set_structured_loop_condition_alias_exit_value(
                        summarized,
                        bindings,
                        loop_condition_alias_name,
                    )
                next_states.extend(summarized)

        if trailing_index is None:
            return do_index, states, False
        return trailing_index + 1, next_states, True

    def _derive_structured_do_while_alias_loop_condition(
        self,
        counter_name: str,
        current_start_expr: Expression,
        alias_expr: Optional[Expression],
        counter_step_hint: Optional[int] = None,
    ) -> Optional[Tuple[Expression, Condition]]:
        if alias_expr is None or alias_expr.expr_type != ExpressionType.BINARY_OP or len(alias_expr.operands) != 2:
            return None

        left_expr, right_expr = alias_expr.operands
        if left_expr.name == counter_name and left_expr.expr_type in {ExpressionType.VARIABLE, ExpressionType.PARAMETER}:
            if alias_expr.operator in {"INT_NOTEQUAL", "INT_SLESS", "INT_LESS"}:
                if alias_expr.operator == "INT_NOTEQUAL" and counter_step_hint is not None and counter_step_hint < 0:
                    return (
                        self._clone_expression(right_expr),
                        Condition(
                            Expression.binary_op(
                                "INT_SLESS",
                                self._clone_expression(right_expr),
                                self._clone_expression(current_start_expr),
                            ),
                            False,
                        ),
                    )
                limit_plus_one = Expression.binary_op(
                    "INT_ADD",
                    self._clone_expression(right_expr),
                    Expression.constant(1, max(1, right_expr.size or 4)),
                )
                limit_plus_one.size = max(1, right_expr.size or 4)
                return (
                    limit_plus_one,
                    Condition(
                        Expression.binary_op(
                            "INT_SLESS",
                            self._clone_expression(current_start_expr),
                            limit_plus_one,
                        ),
                        False,
                    ),
                )
        if right_expr.name == counter_name and right_expr.expr_type in {ExpressionType.VARIABLE, ExpressionType.PARAMETER}:
            if alias_expr.operator in {"INT_NOTEQUAL", "INT_SLESS", "INT_LESS"}:
                if alias_expr.operator == "INT_NOTEQUAL" and counter_step_hint is not None and counter_step_hint < 0:
                    return (
                        self._clone_expression(left_expr),
                        Condition(
                            Expression.binary_op(
                                "INT_SLESS",
                                self._clone_expression(left_expr),
                                self._clone_expression(current_start_expr),
                            ),
                            False,
                        ),
                    )
                limit_plus_one = Expression.binary_op(
                    "INT_ADD",
                    self._clone_expression(left_expr),
                    Expression.constant(1, max(1, left_expr.size or 4)),
                )
                limit_plus_one.size = max(1, left_expr.size or 4)
                return (
                    limit_plus_one,
                    Condition(
                        Expression.binary_op(
                            "INT_SLESS",
                            self._clone_expression(current_start_expr),
                            limit_plus_one,
                        ),
                        False,
                    ),
                )
        return None

    def _structured_concrete_counter_step_hint(
        self,
        before_expr: Optional[Expression],
        after_expr: Optional[Expression],
    ) -> Optional[int]:
        if before_expr is None or after_expr is None:
            return None
        delta = self._structured_extract_additive_delta(after_expr, before_expr)
        if delta is None:
            normalized_after = self._structured_strip_counter_casts(after_expr)
            normalized_before = self._structured_strip_counter_casts(before_expr)
            if normalized_after is None or normalized_before is None:
                return None
            delta = self._structured_extract_additive_delta(normalized_after, normalized_before)
        if delta is None:
            return None
        delta_value = self._evaluate_wrapper_constant(delta)
        if delta_value is None:
            return None
        delta_size = max(
            1,
            getattr(delta, "size", 0) or getattr(after_expr, "size", 0) or getattr(before_expr, "size", 0) or 4,
        )
        signed_delta = self._to_signed_wrapper_value(int(delta_value), delta_size * 8)
        return signed_delta if signed_delta != 0 else None

    def _set_structured_loop_condition_alias_exit_value(
        self,
        states: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]],
        reference_bindings: Dict[str, Expression],
        alias_name: str,
    ) -> List[Tuple[Dict[str, Expression], List[Condition], Set[str]]]:
        alias_expr = reference_bindings.get(alias_name)
        alias_size = max(1, getattr(alias_expr, "size", 0) or 1)
        false_expr = Expression.constant(0, alias_size)
        updated: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]] = []
        for bindings, conditions, nonnegative_vars in states:
            new_bindings = dict(bindings)
            if alias_name in reference_bindings or alias_name in bindings:
                new_bindings[alias_name] = false_expr
            updated.append((new_bindings, conditions, nonnegative_vars))
        return updated

    def _execute_structured_reduction_for(
        self,
        body_lines: List[str],
        for_index: int,
        states: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]],
        parameters: List[Dict],
    ) -> Tuple[int, List[Tuple[Dict[str, Expression], List[Condition], Set[str]]], bool]:
        header = body_lines[for_index]
        parsed = self._parse_structured_reduction_for_header(header, states, parameters)
        if parsed is None:
            return for_index, states, False

        counter_name = parsed["counter_name"]
        start_expr = parsed["start_expr"]
        limit_expr = parsed["limit_expr"]
        positive_cond = parsed["positive_cond"]
        counter_step = parsed["counter_step"]
        positive_cond_expr = getattr(positive_cond, "expression", None)
        if positive_cond_expr is None:
            return for_index, states, False

        body_start = for_index + 1
        if not parsed["header_has_brace"]:
            if body_start >= len(body_lines) or body_lines[body_start] != "{":
                return for_index, states, False
            body_start += 1

        next_states: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]] = []
        for bindings, conditions, nonnegative_vars in states:
            zero_conditions = ConditionSimplifier.simplify_conditions(
                list(conditions) + [Condition(self._clone_expression(positive_cond_expr), True)]
            )
            if not ConditionSimplifier.is_contradiction(zero_conditions):
                next_states.append((dict(bindings), zero_conditions, set(nonnegative_vars)))

            positive_conditions = ConditionSimplifier.simplify_conditions(
                list(conditions) + [positive_cond]
            )
            if ConditionSimplifier.is_contradiction(positive_conditions):
                continue

            loop_var_size = max(
                getattr(start_expr, "size", 0) or 0,
                getattr(limit_expr, "size", 0) or 0,
                4,
            )
            loop_bindings = dict(bindings)
            loop_bindings[counter_name] = Expression.variable(counter_name, size=loop_var_size)
            loop_nonnegative_vars = set(nonnegative_vars)
            start_lower_bound = self._structured_expr_lower_bound(
                start_expr,
                loop_nonnegative_vars,
            )
            if start_lower_bound is not None and start_lower_bound >= 0:
                loop_nonnegative_vars.add(counter_name)

            body_index, body_live_states, body_returned, ok = self._execute_structured_reduction_block(
                body_lines,
                body_start,
                [(loop_bindings, positive_conditions, loop_nonnegative_vars)],
                parameters,
                stop_on_closing_brace=True,
            )
            if not ok or body_returned or not body_live_states:
                return for_index, states, False

            positive_proved = self._structured_condition_constant_truth(
                positive_cond,
                loop_nonnegative_vars,
            ) is True

            summarized = self._summarize_structured_reduction_loop_cases(
                bindings,
                body_live_states,
                counter_name,
                start_expr,
                limit_expr,
                parameters,
                loop_nonnegative_vars,
                require_invariant_conditions=not positive_proved,
                counter_step=counter_step,
            )
            if summarized is None:
                symbolic_loop_bindings = self._build_symbolic_structured_loop_bindings(
                    bindings,
                    counter_name=counter_name,
                )
                symbolic_body_index, symbolic_body_live_states, symbolic_body_returned, symbolic_ok = self._execute_structured_reduction_block(
                    body_lines,
                    body_start,
                    [(symbolic_loop_bindings, positive_conditions, loop_nonnegative_vars)],
                    parameters,
                    stop_on_closing_brace=True,
                )
                if (
                    symbolic_ok
                    and not symbolic_body_returned
                    and symbolic_body_live_states
                    and symbolic_body_index == body_index
                ):
                    summarized = self._summarize_structured_reduction_loop_cases(
                        bindings,
                        body_live_states,
                        counter_name,
                        start_expr,
                        limit_expr,
                        parameters,
                        loop_nonnegative_vars,
                        require_invariant_conditions=not positive_proved,
                        counter_step=counter_step,
                        recurrence_base_bindings=symbolic_loop_bindings,
                        recurrence_body_states=symbolic_body_live_states,
                    )
            if summarized is None:
                return for_index, states, False
            next_states.extend(summarized)

        loop_end = self._advance_to_structured_block_exit(body_lines, body_start)
        return loop_end, next_states, True

    def _parse_structured_reduction_while_header(
        self,
        line: str,
    ) -> Optional[Dict[str, Any]]:
        trailing = re.fullmatch(r"while\s*\((.+)\)\s*;", line)
        if trailing is not None:
            return {
                "condition_text": trailing.group(1).strip(),
                "header_has_brace": False,
                "trailing": True,
            }

        header = re.fullmatch(r"while\s*\((.+)\)\s*(\{)?", line)
        if header is None:
            return None
        return {
            "condition_text": header.group(1).strip(),
            "header_has_brace": bool(header.group(2)),
            "trailing": False,
        }

    def _infer_structured_reduction_loop_from_condition(
        self,
        condition_text: str,
        bindings: Dict[str, Expression],
        parameters: List[Dict],
    ) -> Optional[Dict[str, Any]]:
        matches: List[Dict[str, Any]] = []
        for counter_name, start_expr in bindings.items():
            parsed = self._parse_structured_reduction_loop_condition(
                counter_name,
                condition_text,
                parameters,
                bindings,
                start_expr,
            )
            if parsed is None:
                continue
            matches.append(
                {
                    "counter_name": counter_name,
                    "start_expr": start_expr,
                    "limit_expr": parsed["limit_expr"],
                    "positive_cond": parsed["positive_cond"],
                    "allowed_steps": set(parsed["allowed_steps"]),
                }
            )

        if len(matches) != 1:
            return None
        return matches[0]

    def _structured_loop_counter_step(
        self,
        expr: Optional[Expression],
        counter_name: str,
    ) -> Optional[int]:
        if expr is None:
            return None
        counter_expr = Expression.variable(counter_name, size=max(1, expr.size or 4))
        delta = self._structured_extract_additive_delta(expr, counter_expr)
        if delta is None:
            normalized_expr = self._structured_strip_counter_casts(expr)
            normalized_counter = self._structured_strip_counter_casts(counter_expr)
            if normalized_expr is not None and normalized_counter is not None:
                delta = self._structured_extract_additive_delta(normalized_expr, normalized_counter)
        if delta is None:
            return None
        delta_value = self._evaluate_wrapper_constant(delta)
        if delta_value is None:
            return None
        delta_size = max(1, getattr(delta, "size", 0) or getattr(expr, "size", 0) or 4)
        signed_delta = self._to_signed_wrapper_value(int(delta_value), delta_size * 8)
        return signed_delta if signed_delta != 0 else None

    def _structured_counter_step_matches_allowed(
        self,
        counter_step: int,
        allowed_steps: Set[int],
    ) -> bool:
        if counter_step == 0:
            return False
        if counter_step > 0:
            return any(step > 0 for step in allowed_steps)
        return any(step < 0 for step in allowed_steps)

    def _structured_strip_counter_casts(
        self,
        expr: Optional[Expression],
    ) -> Optional[Expression]:
        if expr is None:
            return None
        current = expr
        while True:
            if current.expr_type == ExpressionType.UNARY_OP and current.operator in {"INT_SEXT", "INT_ZEXT", "COPY"} and current.operands:
                current = current.operands[0]
                continue
            if (
                current.expr_type == ExpressionType.BINARY_OP
                and current.operator == "SUBPIECE"
                and len(current.operands) == 2
                and current.operands[1].expr_type == ExpressionType.CONSTANT
                and int(current.operands[1].value) == 0
            ):
                current = current.operands[0]
                continue
            return current

    def _parse_structured_reduction_for_header(
        self,
        line: str,
        states: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]],
        parameters: List[Dict],
    ) -> Optional[Dict[str, Any]]:
        match = re.fullmatch(r"for\s*\((.+);(.+);(.+)\)\s*(\{)?", line)
        if match is None or not states:
            return None

        init_text = match.group(1).strip()
        cond_text = match.group(2).strip()
        step_text = match.group(3).strip()
        header_has_brace = bool(match.group(4))

        init_match = re.fullmatch(
            r"(?:[A-Za-z_][A-Za-z0-9_\s\*]*\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.+)",
            init_text,
        )
        if init_match is None:
            return None
        counter_name = init_match.group(1)
        sample_bindings = states[0][0]
        start_expr = self._parse_wrapper_expr(
            init_match.group(2).strip(),
            parameters,
            fallback_index=0,
            local_bindings=sample_bindings,
        )
        if start_expr is None:
            return None

        parsed_cond = self._parse_structured_reduction_loop_condition(
            counter_name,
            cond_text,
            parameters,
            sample_bindings,
            start_expr,
        )
        if parsed_cond is None:
            return None
        counter_step = self._structured_reduction_parse_unit_step(step_text, counter_name)
        if counter_step is None or not self._structured_counter_step_matches_allowed(
            counter_step,
            parsed_cond["allowed_steps"],
        ):
            return None

        return {
            "counter_name": counter_name,
            "start_expr": start_expr,
            "limit_expr": parsed_cond["limit_expr"],
            "positive_cond": parsed_cond["positive_cond"],
            "allowed_steps": parsed_cond["allowed_steps"],
            "counter_step": counter_step,
            "header_has_brace": header_has_brace,
        }

    def _parse_structured_reduction_loop_condition(
        self,
        counter_name: str,
        cond_text: str,
        parameters: List[Dict],
        bindings: Dict[str, Expression],
        start_expr: Expression,
    ) -> Optional[Dict[str, Any]]:
        match = re.fullmatch(r"(.+?)(<=|<|>=|>|==|!=)(.+)", cond_text)
        if match is not None:
            left_text = match.group(1).strip()
            operator = match.group(2)
            right_text = match.group(3).strip()

            left_is_counter = left_text == counter_name
            right_is_counter = right_text == counter_name

            left_expr = None if left_is_counter else self._parse_wrapper_expr(
                left_text,
                parameters,
                fallback_index=0,
                local_bindings=bindings,
            )
            right_expr = None if right_is_counter else self._parse_wrapper_expr(
                right_text,
                parameters,
                fallback_index=0,
                local_bindings=bindings,
            )

            parsed = self._parse_structured_reduction_loop_condition_expr(
                counter_name,
                start_expr,
                operator,
                left_expr,
                right_expr,
                left_is_counter=left_is_counter,
                right_is_counter=right_is_counter,
            )
            if parsed is not None:
                return parsed

        condition_expr = self._parse_wrapper_expr(
            cond_text,
            parameters,
            fallback_index=0,
            local_bindings=bindings,
        )
        if condition_expr is None:
            return None
        return self._parse_structured_reduction_loop_condition_from_expression(
            counter_name,
            start_expr,
            condition_expr,
        )

    def _parse_structured_reduction_loop_condition_expr(
        self,
        counter_name: str,
        start_expr: Expression,
        operator: str,
        left_expr: Optional[Expression],
        right_expr: Optional[Expression],
        *,
        left_is_counter: bool,
        right_is_counter: bool,
    ) -> Optional[Dict[str, Any]]:
        if left_is_counter and right_expr is not None:
            if operator == "<":
                return {
                    "limit_expr": right_expr,
                    "positive_cond": self._make_structured_positive_condition(
                        "INT_SLESS",
                        start_expr,
                        right_expr,
                    ),
                    "allowed_steps": {1},
                }
            if operator == "<=":
                plus_one = Expression.binary_op(
                    "INT_ADD",
                    right_expr,
                    Expression.constant(1, max(1, right_expr.size or 4)),
                )
                plus_one.size = max(1, right_expr.size or 4)
                return {
                    "limit_expr": plus_one,
                    "positive_cond": self._make_structured_positive_condition(
                        "INT_SLESSEQUAL",
                        start_expr,
                        right_expr,
                    ),
                    "allowed_steps": {1},
                }
            if operator == ">":
                return {
                    "limit_expr": right_expr,
                    "positive_cond": self._make_structured_positive_condition(
                        "INT_SLESS",
                        right_expr,
                        start_expr,
                    ),
                    "allowed_steps": {-1},
                }
            if operator == ">=":
                minus_one = Expression.binary_op(
                    "INT_SUB",
                    right_expr,
                    Expression.constant(1, max(1, right_expr.size or 4)),
                )
                minus_one.size = max(1, right_expr.size or 4)
                return {
                    "limit_expr": minus_one,
                    "positive_cond": self._make_structured_positive_condition(
                        "INT_SLESSEQUAL",
                        right_expr,
                        start_expr,
                    ),
                    "allowed_steps": {-1},
                }
            if operator == "!=":
                return {
                    "limit_expr": right_expr,
                    "positive_cond": Condition(Expression.binary_op("INT_NOTEQUAL", start_expr, right_expr), False),
                    "allowed_steps": {-1, 1},
                }
        if right_is_counter and left_expr is not None:
            if operator == ">":
                return {
                    "limit_expr": left_expr,
                    "positive_cond": self._make_structured_positive_condition(
                        "INT_SLESS",
                        start_expr,
                        left_expr,
                    ),
                    "allowed_steps": {1},
                }
            if operator == ">=":
                plus_one = Expression.binary_op(
                    "INT_ADD",
                    left_expr,
                    Expression.constant(1, max(1, left_expr.size or 4)),
                )
                plus_one.size = max(1, left_expr.size or 4)
                return {
                    "limit_expr": plus_one,
                    "positive_cond": self._make_structured_positive_condition(
                        "INT_SLESSEQUAL",
                        start_expr,
                        left_expr,
                    ),
                    "allowed_steps": {1},
                }
            if operator == "<":
                return {
                    "limit_expr": left_expr,
                    "positive_cond": self._make_structured_positive_condition(
                        "INT_SLESS",
                        left_expr,
                        start_expr,
                    ),
                    "allowed_steps": {-1},
                }
            if operator == "<=":
                minus_one = Expression.binary_op(
                    "INT_SUB",
                    left_expr,
                    Expression.constant(1, max(1, left_expr.size or 4)),
                )
                minus_one.size = max(1, left_expr.size or 4)
                return {
                    "limit_expr": minus_one,
                    "positive_cond": self._make_structured_positive_condition(
                        "INT_SLESSEQUAL",
                        left_expr,
                        start_expr,
                    ),
                    "allowed_steps": {-1},
                }
            if operator == "!=":
                return {
                    "limit_expr": left_expr,
                    "positive_cond": Condition(Expression.binary_op("INT_NOTEQUAL", start_expr, left_expr), False),
                    "allowed_steps": {-1, 1},
                }
        return None

    def _make_structured_positive_condition(
        self,
        operator: str,
        left_expr: Expression,
        right_expr: Expression,
    ) -> Condition:
        expr = Expression.binary_op(operator, left_expr, right_expr)
        normalized = self._normalize_structured_loop_condition_expr(expr)
        return Condition(normalized if normalized is not None else expr, False)

    def _make_structured_negative_condition(
        self,
        condition: Condition,
    ) -> Condition:
        expr = getattr(condition, "expression", None)
        if expr is not None and expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
            complemented_operator = {
                "INT_SLESS": "INT_SLESSEQUAL",
                "INT_SLESSEQUAL": "INT_SLESS",
                "INT_LESS": "INT_LESSEQUAL",
                "INT_LESSEQUAL": "INT_LESS",
                "INT_EQUAL": "INT_NOTEQUAL",
                "INT_NOTEQUAL": "INT_EQUAL",
            }.get(expr.operator)
            if complemented_operator is not None:
                complemented = Expression.binary_op(
                    complemented_operator,
                    self._clone_expression(expr.operands[1]),
                    self._clone_expression(expr.operands[0]),
                )
                normalized = self._normalize_structured_loop_condition_expr(complemented)
                return Condition(normalized if normalized is not None else complemented, False)
        return Condition(self._clone_expression(condition.expression), True)

    def _parse_structured_reduction_loop_condition_from_expression(
        self,
        counter_name: str,
        start_expr: Expression,
        condition_expr: Expression,
    ) -> Optional[Dict[str, Any]]:
        expr = condition_expr
        if expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "BOOL_NEGATE" and expr.operands:
            inner = self._parse_structured_reduction_loop_condition_from_expression(
                counter_name,
                start_expr,
                expr.operands[0],
            )
            if inner is None:
                return None
            return {
                "limit_expr": inner["limit_expr"],
                "positive_cond": Condition(
                    self._clone_expression(inner["positive_cond"].expression),
                    negated=not inner["positive_cond"].negated,
                ),
                "allowed_steps": set(inner["allowed_steps"]),
            }

        if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None
        if expr.operator not in {"INT_SLESS", "INT_SLESSEQUAL", "INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", "INT_LESSEQUAL"}:
            return None

        left_expr, right_expr = expr.operands
        left_is_counter = left_expr.name == counter_name and left_expr.expr_type in {ExpressionType.VARIABLE, ExpressionType.PARAMETER}
        right_is_counter = right_expr.name == counter_name and right_expr.expr_type in {ExpressionType.VARIABLE, ExpressionType.PARAMETER}

        operator_map = {
            "INT_SLESS": "<",
            "INT_LESS": "<",
            "INT_SLESSEQUAL": "<=",
            "INT_LESSEQUAL": "<=",
            "INT_NOTEQUAL": "!=",
            "INT_EQUAL": "==",
        }
        operator = operator_map.get(expr.operator)
        if operator is None:
            return None
        return self._parse_structured_reduction_loop_condition_expr(
            counter_name,
            start_expr,
            operator,
            None if left_is_counter else left_expr,
            None if right_is_counter else right_expr,
            left_is_counter=left_is_counter,
            right_is_counter=right_is_counter,
        )

    def _structured_reduction_parse_unit_step(self, step_text: str, counter_name: str) -> Optional[int]:
        normalized = step_text.replace(" ", "")
        positive = {
            f"{counter_name}++",
            f"++{counter_name}",
            f"{counter_name}+={1}",
            f"{counter_name}={counter_name}+1",
            f"{counter_name}=1+{counter_name}",
        }
        if normalized in positive:
            return 1
        negative = {
            f"{counter_name}--",
            f"--{counter_name}",
            f"{counter_name}-={1}",
            f"{counter_name}={counter_name}-1",
        }
        if normalized in negative:
            return -1
        literal_pattern = r"(?:0x[0-9a-fA-F]+|\d+)"
        plus_assign = re.fullmatch(rf"{re.escape(counter_name)}\+=({literal_pattern})", normalized)
        if plus_assign is not None:
            return int(plus_assign.group(1), 0)
        minus_assign = re.fullmatch(rf"{re.escape(counter_name)}-=({literal_pattern})", normalized)
        if minus_assign is not None:
            return -int(minus_assign.group(1), 0)
        plus_update = re.fullmatch(
            rf"{re.escape(counter_name)}={re.escape(counter_name)}\+({literal_pattern})",
            normalized,
        )
        if plus_update is not None:
            return int(plus_update.group(1), 0)
        plus_update_commuted = re.fullmatch(
            rf"{re.escape(counter_name)}=({literal_pattern})\+{re.escape(counter_name)}",
            normalized,
        )
        if plus_update_commuted is not None:
            return int(plus_update_commuted.group(1), 0)
        minus_update = re.fullmatch(
            rf"{re.escape(counter_name)}={re.escape(counter_name)}-({literal_pattern})",
            normalized,
        )
        if minus_update is not None:
            return -int(minus_update.group(1), 0)
        return None

    def _summarize_structured_reduction_loop_cases(
        self,
        base_bindings: Dict[str, Expression],
        body_states: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]],
        counter_name: str,
        start_expr: Expression,
        limit_expr: Expression,
        parameters: List[Dict],
        nonnegative_vars: Set[str],
        require_invariant_conditions: bool,
        counter_step: int = 1,
        recurrence_base_bindings: Optional[Dict[str, Expression]] = None,
        recurrence_body_states: Optional[List[Tuple[Dict[str, Expression], List[Condition], Set[str]]]] = None,
        ignored_change_names: Optional[Set[str]] = None,
    ) -> Optional[List[Tuple[Dict[str, Expression], List[Condition], Set[str]]]]:
        summarized: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]] = []
        changed_union: Set[str] = set()
        recurrence_base = recurrence_base_bindings or base_bindings
        recurrence_states = recurrence_body_states or body_states
        ignored_names = set(ignored_change_names or set())
        if len(recurrence_states) != len(body_states):
            self._last_structured_reduction_failure = {
                "index": -1,
                "line": None,
                "reason": "do_while_loop_summary_failed",
                "detail": (
                    "recurrence_state_length_mismatch:"
                    f"{len(recurrence_states)}!={len(body_states)}"
                ),
            }
            return None

        for recurrence_bindings, _body_conditions, _body_nonnegative_vars in recurrence_states:
            changed_union.update(
                name
                for name, value in recurrence_bindings.items()
                if name != counter_name
                and name not in ignored_names
                and name in recurrence_base
                and (
                    not _expressions_equivalent(value, recurrence_base[name])
                )
            )
        if len(changed_union) > 1:
            if recurrence_body_states is None or recurrence_base_bindings is None:
                self._last_structured_reduction_failure = {
                    "index": -1,
                    "line": None,
                    "reason": "do_while_loop_summary_failed",
                    "detail": f"multi_var_without_symbolic_recurrence:{sorted(changed_union)}",
                }
                return None
            return self._summarize_structured_reduction_multi_var_cases(
                base_bindings,
                body_states,
                counter_name,
                start_expr,
                limit_expr,
                parameters,
                require_invariant_conditions,
                counter_step,
                recurrence_base,
                recurrence_states,
                ignored_names,
            )
        acc_name = next(iter(changed_union)) if changed_union else None

        for (body_bindings, body_conditions, body_nonnegative_vars), (recurrence_bindings, _, _) in zip(
            body_states,
            recurrence_states,
        ):
            rewritten_conditions = self._rewrite_structured_reduction_conditions_for_counter(
                body_conditions,
                counter_name,
                body_nonnegative_vars,
                require_invariant=require_invariant_conditions,
                counter_replacement=start_expr,
            )
            if rewritten_conditions is None:
                self._last_structured_reduction_failure = {
                    "index": -1,
                    "line": None,
                    "reason": "do_while_loop_summary_failed",
                    "detail": f"condition_rewrite_failed:{counter_name}",
                }
                return None

            new_bindings = dict(base_bindings)
            if acc_name is not None:
                before_value = base_bindings.get(acc_name)
                after_value = recurrence_bindings.get(acc_name, recurrence_base.get(acc_name))
                if before_value is None or after_value is None:
                    self._last_structured_reduction_failure = {
                        "index": -1,
                        "line": None,
                        "reason": "do_while_loop_summary_failed",
                        "detail": f"missing_acc_binding:{acc_name}",
                    }
                    return None

                delta_expr = self._structured_extract_additive_delta(
                    after_value,
                    recurrence_base[acc_name],
                )
                if delta_expr is None:
                    self._last_structured_reduction_failure = {
                        "index": -1,
                        "line": None,
                        "reason": "do_while_loop_summary_failed",
                        "detail": f"delta_extraction_failed:{acc_name}",
                    }
                    return None
                if (
                    rewritten_conditions == []
                    and delta_expr.expr_type == ExpressionType.CONSTANT
                    and int(delta_expr.value) == 0
                ):
                    continue

                summed_delta = self._structured_sum_expression_over_counter(
                    delta_expr,
                    counter_name,
                    start_expr,
                    limit_expr,
                    parameters,
                    counter_step=counter_step,
                )
                if summed_delta is None:
                    self._last_structured_reduction_failure = {
                        "index": -1,
                        "line": None,
                        "reason": "do_while_loop_summary_failed",
                        "detail": f"delta_summation_failed:{acc_name}",
                    }
                    return None

                updated_value = Expression.binary_op(
                    "INT_ADD",
                    self._clone_expression(before_value),
                    self._structured_materialize_symbolic_loop_names(
                        summed_delta,
                        base_bindings,
                        recurrence_base,
                        exclude_names={counter_name},
                    ),
                )
                updated_value.size = max(
                    getattr(before_value, "size", 0) or 0,
                    getattr(summed_delta, "size", 0) or 0,
                    4,
                )
                new_bindings[acc_name] = updated_value
            summarized.append((new_bindings, rewritten_conditions, set(body_nonnegative_vars)))

        return summarized

    def _build_symbolic_structured_loop_bindings(
        self,
        bindings: Dict[str, Expression],
        counter_name: str,
        symbolic_names: Optional[Set[str]] = None,
    ) -> Dict[str, Expression]:
        symbolic: Dict[str, Expression] = {}
        for name, value in bindings.items():
            size = max(1, getattr(value, "size", 0) or 4)
            should_symbolize = (
                name == counter_name
                or (
                    re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name or "")
                    and (
                        symbolic_names is None
                        or name in symbolic_names
                    )
                )
            )
            if should_symbolize:
                symbolic[name] = Expression.variable(name, size=size)
            else:
                symbolic[name] = self._clone_expression(value)
        return symbolic

    def _summarize_structured_reduction_multi_var_cases(
        self,
        base_bindings: Dict[str, Expression],
        body_states: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]],
        counter_name: str,
        start_expr: Expression,
        limit_expr: Expression,
        parameters: List[Dict],
        require_invariant_conditions: bool,
        counter_step: int,
        recurrence_base_bindings: Dict[str, Expression],
        recurrence_body_states: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]],
        ignored_change_names: Set[str],
    ) -> Optional[List[Tuple[Dict[str, Expression], List[Condition], Set[str]]]]:
        summarized: List[Tuple[Dict[str, Expression], List[Condition], Set[str]]] = []

        for (body_bindings, body_conditions, body_nonnegative_vars), (recurrence_bindings, _, _) in zip(
            body_states,
            recurrence_body_states,
        ):
            rewritten_conditions = self._rewrite_structured_reduction_conditions_for_counter(
                body_conditions,
                counter_name,
                body_nonnegative_vars,
                require_invariant=require_invariant_conditions,
                counter_replacement=start_expr,
            )
            if rewritten_conditions is None:
                self._last_structured_reduction_failure = {
                    "index": -1,
                    "line": None,
                    "reason": "do_while_loop_summary_failed",
                    "detail": f"multi_var_condition_rewrite_failed:{counter_name}",
                }
                return None

            changed_names = [
                name
                for name, before_value in recurrence_base_bindings.items()
                if name != counter_name
                and name not in ignored_change_names
                and name in recurrence_bindings
                and not _expressions_equivalent(recurrence_bindings[name], before_value)
            ]
            if not changed_names:
                summarized.append((dict(base_bindings), rewritten_conditions, set(body_nonnegative_vars)))
                continue

            base_replacements = {
                name: self._clone_expression(expr)
                for name, expr in base_bindings.items()
                if name not in changed_names
            }
            current_value_exprs: Dict[str, Expression] = {}
            final_value_exprs: Dict[str, Expression] = {}
            pending = set(changed_names)

            while pending:
                progress = False
                for name in list(pending):
                    before_symbolic = recurrence_base_bindings.get(name)
                    after_symbolic = recurrence_bindings.get(name)
                    before_concrete = base_bindings.get(name)
                    if before_symbolic is None or after_symbolic is None or before_concrete is None:
                        self._last_structured_reduction_failure = {
                            "index": -1,
                            "line": None,
                            "reason": "do_while_loop_summary_failed",
                            "detail": f"multi_var_missing_binding:{name}",
                        }
                        return None

                    delta_expr = self._structured_extract_additive_delta(after_symbolic, before_symbolic)
                    if delta_expr is None:
                        continue

                    unresolved = [
                        other
                        for other in pending
                        if other != name and self._expression_mentions_name(delta_expr, other)
                    ]
                    if unresolved:
                        continue

                    substituted_delta = self._structured_replace_named_subexpressions(
                        delta_expr,
                        {
                            **base_replacements,
                            **current_value_exprs,
                        },
                    )
                    current_counter_expr = Expression.variable(
                        counter_name,
                        size=max(1, getattr(start_expr, "size", 0) or getattr(limit_expr, "size", 0) or 4),
                    )
                    prefix_sum = self._structured_sum_expression_over_counter(
                        substituted_delta,
                        counter_name,
                        start_expr,
                        current_counter_expr,
                        parameters,
                        counter_step=counter_step,
                    )
                    final_sum = self._structured_sum_expression_over_counter(
                        substituted_delta,
                        counter_name,
                        start_expr,
                        limit_expr,
                        parameters,
                        counter_step=counter_step,
                    )
                    if prefix_sum is None or final_sum is None:
                        continue

                    current_expr = Expression.binary_op(
                        "INT_ADD",
                        self._clone_expression(before_concrete),
                        prefix_sum,
                    )
                    current_expr.size = max(
                        getattr(before_concrete, "size", 0) or 0,
                        getattr(prefix_sum, "size", 0) or 0,
                        4,
                    )
                    final_expr = Expression.binary_op(
                        "INT_ADD",
                        self._clone_expression(before_concrete),
                        final_sum,
                    )
                    final_expr.size = max(
                        getattr(before_concrete, "size", 0) or 0,
                        getattr(final_sum, "size", 0) or 0,
                        4,
                    )
                    current_value_exprs[name] = current_expr
                    final_value_exprs[name] = final_expr
                    pending.remove(name)
                    progress = True

                if not progress:
                    self._last_structured_reduction_failure = {
                        "index": -1,
                        "line": None,
                        "reason": "do_while_loop_summary_failed",
                        "detail": f"multi_var_stalled:{sorted(pending)}",
                    }
                    return None

            new_bindings = dict(base_bindings)
            for name, final_expr in final_value_exprs.items():
                new_bindings[name] = final_expr
            summarized.append((new_bindings, rewritten_conditions, set(body_nonnegative_vars)))

        return summarized

    def _structured_replace_named_subexpressions(
        self,
        expr: Optional[Expression],
        replacements: Dict[str, Expression],
    ) -> Optional[Expression]:
        if expr is None:
            return None
        if expr.name and expr.name in replacements:
            return self._clone_expression(replacements[expr.name])
        if expr.expr_type == ExpressionType.PHI and expr.value:
            replaced_branches = []
            for cond, value in expr.value:
                replaced_cond = None
                if cond is not None:
                    cond_expr = self._structured_replace_named_subexpressions(cond.expression, replacements)
                    if cond_expr is None:
                        return None
                    replaced_cond = Condition(cond_expr, negated=cond.negated)
                replaced_value = self._structured_replace_named_subexpressions(value, replacements)
                if replaced_value is None:
                    return None
                replaced_branches.append((replaced_cond, replaced_value))
            return Expression.phi(replaced_branches)
        if not expr.operands:
            return self._clone_expression(expr)
        replaced_operands = [
            self._structured_replace_named_subexpressions(operand, replacements)
            for operand in expr.operands
        ]
        if any(operand is None for operand in replaced_operands):
            return None
        rebuilt = Expression(
            expr_type=expr.expr_type,
            name=expr.name,
            value=expr.value,
            operator=expr.operator,
            operands=cast(List[Expression], replaced_operands),
            data_type=expr.data_type,
            size=expr.size,
            storage_info=expr.storage_info,
        )
        return rebuilt

    def _structured_materialize_symbolic_loop_names(
        self,
        expr: Optional[Expression],
        concrete_bindings: Dict[str, Expression],
        symbolic_bindings: Dict[str, Expression],
        exclude_names: Optional[Set[str]] = None,
    ) -> Optional[Expression]:
        replacements = {
            name: self._clone_expression(concrete_bindings[name])
            for name in symbolic_bindings
            if name in concrete_bindings and name not in (exclude_names or set())
        }
        return self._structured_replace_named_subexpressions(expr, replacements)

    def _rewrite_structured_reduction_conditions_for_counter(
        self,
        conditions: List[Condition],
        counter_name: str,
        nonnegative_vars: Set[str],
        require_invariant: bool,
        counter_replacement: Optional[Expression] = None,
    ) -> Optional[List[Condition]]:
        rewritten: List[Condition] = []
        for condition in ConditionSimplifier.simplify_conditions(list(conditions)):
            truth = self._structured_condition_constant_truth(condition, nonnegative_vars)
            if truth is True:
                continue
            if truth is False:
                return []
            rewritten_condition = condition
            did_replace_counter = False
            if require_invariant and self._expression_mentions_name(condition.expression, counter_name):
                if counter_replacement is None:
                    return None
                if not self._expression_contains_equivalent_subexpr(
                    condition.expression,
                    counter_replacement,
                ):
                    replaced_expr = self._structured_replace_named_subexpressions(
                        condition.expression,
                        {counter_name: counter_replacement},
                    )
                    if replaced_expr is None:
                        return None
                    rewritten_condition = Condition(replaced_expr, negated=condition.negated)
                    did_replace_counter = True
            if did_replace_counter:
                normalized_expr = self._normalize_structured_loop_condition_expr(
                    rewritten_condition.expression
                )
                if normalized_expr is not None:
                    rewritten_condition = Condition(normalized_expr, negated=rewritten_condition.negated)
            rewritten.append(rewritten_condition)
        if ConditionSimplifier.is_contradiction(rewritten):
            return []
        return rewritten

    def _normalize_structured_loop_condition_expr(
        self,
        expr: Optional[Expression],
    ) -> Optional[Expression]:
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return expr
        if expr.operator not in {
            "INT_SLESS",
            "INT_SLESSEQUAL",
            "INT_LESS",
            "INT_LESSEQUAL",
        }:
            return expr

        left_terms = self._structured_flatten_add_terms(expr.operands[0])
        right_terms = self._structured_flatten_add_terms(expr.operands[1])
        remaining_left = list(left_terms)
        remaining_right = list(right_terms)

        changed = False
        for left_index, (left_sign, left_term) in enumerate(list(remaining_left)):
            matched_index = None
            for right_index, (right_sign, right_term) in enumerate(remaining_right):
                if left_sign != right_sign:
                    continue
                if not _expressions_equivalent(left_term, right_term):
                    continue
                matched_index = right_index
                break
            if matched_index is None:
                continue
            del remaining_right[matched_index]
            for candidate_index, candidate in enumerate(remaining_left):
                if candidate[0] == left_sign and _expressions_equivalent(candidate[1], left_term):
                    del remaining_left[candidate_index]
                    break
            changed = True

        if not changed:
            return expr

        rebuilt_left = self._structured_sum_terms(
            [self._structured_scale_expression(term, sign) for sign, term in remaining_left]
        )
        rebuilt_right = self._structured_sum_terms(
            [self._structured_scale_expression(term, sign) for sign, term in remaining_right]
        )
        if rebuilt_left is None or rebuilt_right is None:
            return expr
        rebuilt = Expression.binary_op(
            expr.operator,
            rebuilt_left,
            rebuilt_right,
        )
        rebuilt.size = expr.size
        return rebuilt

    def _structured_condition_constant_truth(
        self,
        condition: Condition,
        nonnegative_vars: Set[str],
    ) -> Optional[bool]:
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None

        operator = expr.operator
        if operator not in {"INT_SLESS", "INT_SLESSEQUAL", "INT_EQUAL", "INT_NOTEQUAL"}:
            return None

        diff_lower, diff_upper = self._structured_difference_bounds(
            expr.operands[1],
            expr.operands[0],
            nonnegative_vars,
        )
        result: Optional[bool] = None
        if operator == "INT_SLESS":
            if diff_lower is not None and diff_lower >= 1:
                result = True
            elif diff_upper is not None and diff_upper <= 0:
                result = False
        elif operator == "INT_SLESSEQUAL":
            if diff_lower is not None and diff_lower >= 0:
                result = True
            elif diff_upper is not None and diff_upper <= -1:
                result = False
        elif operator == "INT_EQUAL":
            if diff_lower is not None and diff_upper is not None and diff_lower == 0 and diff_upper == 0:
                result = True
            elif diff_lower is not None and diff_lower > 0:
                result = False
            elif diff_upper is not None and diff_upper < 0:
                result = False
        elif operator == "INT_NOTEQUAL":
            equal_truth = self._structured_condition_constant_truth(
                Condition(Expression.binary_op("INT_EQUAL", expr.operands[0], expr.operands[1]), False),
                nonnegative_vars,
            )
            if equal_truth is True:
                result = False
            elif equal_truth is False:
                result = True

        if result is None:
            return None
        return not result if condition.negated else result

    def _structured_difference_bounds(
        self,
        left: Expression,
        right: Expression,
        nonnegative_vars: Set[str],
    ) -> Tuple[Optional[int], Optional[int]]:
        left_lower = self._structured_expr_lower_bound(left, nonnegative_vars)
        left_upper = self._structured_expr_upper_bound(left, nonnegative_vars)
        right_lower = self._structured_expr_lower_bound(right, nonnegative_vars)
        right_upper = self._structured_expr_upper_bound(right, nonnegative_vars)

        lower = None if left_lower is None or right_upper is None else left_lower - right_upper
        upper = None if left_upper is None or right_lower is None else left_upper - right_lower
        return lower, upper

    def _structured_expr_lower_bound(
        self,
        expr: Optional[Expression],
        nonnegative_vars: Set[str],
    ) -> Optional[int]:
        if expr is None:
            return None
        if expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
            return int(expr.value)
        if expr.expr_type == ExpressionType.VARIABLE and expr.name in nonnegative_vars:
            return 0
        if expr.expr_type == ExpressionType.PARAMETER and expr.name in nonnegative_vars:
            return 0
        if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
            left, right = expr.operands
            if expr.operator == "INT_ADD":
                left_bound = self._structured_expr_lower_bound(left, nonnegative_vars)
                right_bound = self._structured_expr_lower_bound(right, nonnegative_vars)
                if left_bound is None or right_bound is None:
                    return None
                return left_bound + right_bound
            if expr.operator == "INT_SUB":
                left_bound = self._structured_expr_lower_bound(left, nonnegative_vars)
                right_bound = self._structured_expr_upper_bound(right, nonnegative_vars)
                if left_bound is None or right_bound is None:
                    return None
                return left_bound - right_bound
            if expr.operator == "INT_MULT":
                left_const = self._evaluate_wrapper_constant(left)
                right_const = self._evaluate_wrapper_constant(right)
                if left_const is not None:
                    right_bound = self._structured_expr_lower_bound(right, nonnegative_vars)
                    if right_bound is not None and left_const >= 0:
                        return left_const * right_bound
                if right_const is not None:
                    left_bound = self._structured_expr_lower_bound(left, nonnegative_vars)
                    if left_bound is not None and right_const >= 0:
                        return right_const * left_bound
        return None

    def _structured_expr_upper_bound(
        self,
        expr: Optional[Expression],
        nonnegative_vars: Set[str],
    ) -> Optional[int]:
        if expr is None:
            return None
        if expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
            return int(expr.value)
        if expr.expr_type == ExpressionType.VARIABLE and expr.name in nonnegative_vars:
            return None
        if expr.expr_type == ExpressionType.PARAMETER and expr.name in nonnegative_vars:
            return None
        if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
            left, right = expr.operands
            if expr.operator == "INT_ADD":
                left_bound = self._structured_expr_upper_bound(left, nonnegative_vars)
                right_bound = self._structured_expr_upper_bound(right, nonnegative_vars)
                if left_bound is None or right_bound is None:
                    return None
                return left_bound + right_bound
            if expr.operator == "INT_SUB":
                left_bound = self._structured_expr_upper_bound(left, nonnegative_vars)
                right_bound = self._structured_expr_lower_bound(right, nonnegative_vars)
                if left_bound is None or right_bound is None:
                    return None
                return left_bound - right_bound
            if expr.operator == "INT_MULT":
                left_const = self._evaluate_wrapper_constant(left)
                right_const = self._evaluate_wrapper_constant(right)
                if left_const is not None:
                    right_bound = self._structured_expr_upper_bound(right, nonnegative_vars)
                    if right_bound is not None and left_const >= 0:
                        return left_const * right_bound
                if right_const is not None:
                    left_bound = self._structured_expr_upper_bound(left, nonnegative_vars)
                    if left_bound is not None and right_const >= 0:
                        return right_const * left_bound
        return None

    def _structured_extract_additive_delta(
        self,
        expr: Expression,
        base_expr: Expression,
    ) -> Optional[Expression]:
        expr_terms = self._structured_flatten_add_terms(expr)
        base_terms = self._structured_flatten_add_terms(base_expr)
        remaining = list(expr_terms)
        for sign, term in base_terms:
            matched = False
            for index, (candidate_sign, candidate_term) in enumerate(remaining):
                if sign != candidate_sign:
                    continue
                if not _expressions_equivalent(candidate_term, term):
                    continue
                del remaining[index]
                matched = True
                break
            if not matched:
                return None
        return self._structured_sum_terms(
            [self._structured_scale_expression(term, sign) for sign, term in remaining]
        )

    def _structured_flatten_add_terms(
        self,
        expr: Expression,
        sign: int = 1,
    ) -> List[Tuple[int, Expression]]:
        normalized_expr = self._structured_strip_counter_casts(expr)
        if normalized_expr is not None:
            expr = normalized_expr
        if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_ADD" and len(expr.operands) == 2:
            return self._structured_flatten_add_terms(expr.operands[0], sign) + self._structured_flatten_add_terms(
                expr.operands[1],
                sign,
            )
        if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_SUB" and len(expr.operands) == 2:
            return self._structured_flatten_add_terms(expr.operands[0], sign) + self._structured_flatten_add_terms(
                expr.operands[1],
                -sign,
            )
        if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_2COMP", "INT_NEGATE"} and expr.operands:
            return self._structured_flatten_add_terms(expr.operands[0], -sign)
        return [(sign, expr)]

    def _structured_scale_expression(
        self,
        expr: Optional[Expression],
        factor: int,
    ) -> Optional[Expression]:
        if expr is None or factor == 0:
            return None
        if factor == 1:
            return expr
        if factor == -1:
            negated = Expression.unary_op("INT_2COMP", expr)
            negated.size = expr.size
            return negated
        scaled = Expression.binary_op(
            "INT_MULT",
            Expression.constant(factor, max(1, expr.size or 4)),
            expr,
        )
        scaled.size = expr.size
        return scaled

    def _structured_sum_terms(
        self,
        terms: List[Optional[Expression]],
    ) -> Optional[Expression]:
        normalized = [term for term in terms if term is not None]
        if not normalized:
            return Expression.constant(0, 4)
        total = normalized[0]
        for term in normalized[1:]:
            total = Expression.binary_op("INT_ADD", total, term)
            total.size = max(
                getattr(total, "size", 0) or 0,
                getattr(term, "size", 0) or 0,
                4,
            )
        return total

    def _structured_sum_expression_over_counter(
        self,
        expr: Expression,
        counter_name: str,
        start_expr: Expression,
        limit_expr: Expression,
        parameters: List[Dict],
        counter_step: int = 1,
    ) -> Optional[Expression]:
        coeff_expr, bias_expr = self._structured_extract_symbolic_affine(expr, counter_name)
        if coeff_expr is None or bias_expr is None:
            return None

        size = max(
            getattr(expr, "size", 0) or 0,
            getattr(start_expr, "size", 0) or 0,
            getattr(limit_expr, "size", 0) or 0,
            4,
        )
        trip_count = self._structured_loop_trip_count_expr(
            start_expr,
            limit_expr,
            counter_step,
            size,
        )
        if trip_count is None:
            return None
        triangular = self._structured_exact_triangular(trip_count, size)

        lead_term = Expression.binary_op(
            "INT_MULT",
            self._clone_expression(trip_count),
            self._clone_expression(start_expr),
        )
        if counter_step == 1:
            sum_counter = Expression.binary_op("INT_ADD", lead_term, triangular)
        elif counter_step == -1:
            sum_counter = Expression.binary_op("INT_SUB", lead_term, triangular)
        else:
            step_term = Expression.binary_op(
                "INT_MULT",
                Expression.constant(counter_step, size),
                triangular,
            )
            step_term.size = size
            sum_counter = Expression.binary_op("INT_ADD", lead_term, step_term)
        sum_counter.size = size

        terms = []
        coeff_is_zero = coeff_expr.expr_type == ExpressionType.CONSTANT and int(coeff_expr.value) == 0
        bias_is_zero = bias_expr.expr_type == ExpressionType.CONSTANT and int(bias_expr.value) == 0
        if not coeff_is_zero:
            coeff_term = Expression.binary_op("INT_MULT", coeff_expr, sum_counter)
            coeff_term.size = size
            terms.append(coeff_term)
        if not bias_is_zero:
            bias_term = Expression.binary_op("INT_MULT", bias_expr, trip_count)
            bias_term.size = size
            terms.append(bias_term)
        return self._structured_sum_terms(terms)

    def _structured_loop_trip_count_expr(
        self,
        start_expr: Expression,
        limit_expr: Expression,
        counter_step: int,
        size: int,
    ) -> Optional[Expression]:
        if counter_step > 0:
            distance = Expression.binary_op(
                "INT_SUB",
                self._clone_expression(limit_expr),
                self._clone_expression(start_expr),
            )
        else:
            distance = Expression.binary_op(
                "INT_SUB",
                self._clone_expression(start_expr),
                self._clone_expression(limit_expr),
            )
        distance.size = size
        step_magnitude = abs(int(counter_step))
        if step_magnitude == 1:
            return distance
        return self._structured_exact_divide_by_constant(distance, step_magnitude, size)

    def _structured_exact_divide_by_constant(
        self,
        expr: Expression,
        divisor: int,
        size: int,
    ) -> Optional[Expression]:
        if divisor <= 0:
            return None
        if divisor == 1:
            cloned = self._clone_expression(expr)
            cloned.size = size
            return cloned
        if expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
            value = int(expr.value)
            if value % divisor != 0:
                return None
            return Expression.constant(value // divisor, size)
        if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
            if expr.operator in {"COPY", "INT_SEXT", "INT_ZEXT"}:
                return self._structured_exact_divide_by_constant(expr.operands[0], divisor, size)
        if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
            left_expr, right_expr = expr.operands
            if expr.operator in {"INT_ADD", "INT_SUB"}:
                left_div = self._structured_exact_divide_by_constant(left_expr, divisor, size)
                right_div = self._structured_exact_divide_by_constant(right_expr, divisor, size)
                if left_div is not None and right_div is not None:
                    divided = Expression.binary_op(expr.operator, left_div, right_div)
                    divided.size = size
                    return divided
            if expr.operator == "INT_MULT":
                left_const = self._evaluate_wrapper_constant(left_expr)
                right_const = self._evaluate_wrapper_constant(right_expr)
                if left_const is not None and left_const % divisor == 0:
                    divided = Expression.binary_op(
                        "INT_MULT",
                        Expression.constant(left_const // divisor, size),
                        self._clone_expression(right_expr),
                    )
                    divided.size = size
                    return divided
                if right_const is not None and right_const % divisor == 0:
                    divided = Expression.binary_op(
                        "INT_MULT",
                        self._clone_expression(left_expr),
                        Expression.constant(right_const // divisor, size),
                    )
                    divided.size = size
                    return divided
            if expr.operator == "INT_LEFT":
                shift_value = self._evaluate_wrapper_constant(right_expr)
                if shift_value is not None and shift_value >= 0 and divisor & (divisor - 1) == 0:
                    divisor_shift = divisor.bit_length() - 1
                    if int(shift_value) >= divisor_shift:
                        remaining_shift = int(shift_value) - divisor_shift
                        if remaining_shift == 0:
                            divided = self._clone_expression(left_expr)
                            divided.size = size
                            return divided
                        divided = Expression.binary_op(
                            "INT_LEFT",
                            self._clone_expression(left_expr),
                            Expression.constant(remaining_shift, max(1, right_expr.size or 4)),
                        )
                        divided.size = size
                        return divided
            if expr.operator == "INT_AND" and divisor & (divisor - 1) == 0:
                mask_value = self._evaluate_wrapper_constant(right_expr)
                if mask_value is not None and (int(mask_value) & (divisor - 1)) == 0:
                    shift_bits = divisor.bit_length() - 1
                    divided = Expression.binary_op(
                        "INT_RIGHT",
                        self._clone_expression(expr),
                        Expression.constant(shift_bits, max(1, right_expr.size or 4)),
                    )
                    divided.size = size
                    return divided
        return None

    def _structured_exact_triangular(
        self,
        expr: Expression,
        size: int,
    ) -> Expression:
        one = Expression.constant(1, size)
        zero = Expression.constant(0, size)
        shift_amount = Expression.constant(1, size)
        parity = Expression.binary_op("INT_AND", self._clone_expression(expr), one)
        parity.size = size
        expr_minus_one = Expression.binary_op("INT_SUB", self._clone_expression(expr), one)
        expr_minus_one.size = size
        even_half = Expression.binary_op("INT_RIGHT", self._clone_expression(expr), shift_amount)
        even_half.size = size
        odd_half = Expression.binary_op("INT_RIGHT", self._clone_expression(expr_minus_one), shift_amount)
        odd_half.size = size
        even_value = Expression.binary_op("INT_MULT", even_half, self._clone_expression(expr_minus_one))
        even_value.size = size
        odd_value = Expression.binary_op("INT_MULT", self._clone_expression(expr), odd_half)
        odd_value.size = size
        even_condition = Condition(Expression.binary_op("INT_EQUAL", parity, zero), False)
        odd_condition = Condition(Expression.binary_op("INT_EQUAL", parity, zero), True)
        triangular = Expression.phi([
            (even_condition, even_value),
            (odd_condition, odd_value),
        ])
        triangular.size = size
        return triangular

    def _structured_extract_symbolic_affine(
        self,
        expr: Expression,
        counter_name: str,
    ) -> Tuple[Optional[Expression], Optional[Expression]]:
        size = max(1, expr.size or 4)
        if expr.expr_type == ExpressionType.VARIABLE and expr.name == counter_name:
            return Expression.constant(1, size), Expression.constant(0, size)
        if not self._expression_mentions_variable_name(expr, counter_name):
            return Expression.constant(0, size), self._clone_expression(expr)
        if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_2COMP", "INT_NEGATE"} and expr.operands:
            coeff, bias = self._structured_extract_symbolic_affine(expr.operands[0], counter_name)
            if coeff is None or bias is None:
                return None, None
            return self._structured_negate_expression(coeff), self._structured_negate_expression(bias)
        if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None, None

        left_coeff, left_bias = self._structured_extract_symbolic_affine(expr.operands[0], counter_name)
        right_coeff, right_bias = self._structured_extract_symbolic_affine(expr.operands[1], counter_name)
        if expr.operator == "INT_ADD":
            return (
                self._structured_sum_terms([left_coeff, right_coeff]),
                self._structured_sum_terms([left_bias, right_bias]),
            )
        if expr.operator == "INT_SUB":
            return (
                self._structured_sum_terms([left_coeff, self._structured_negate_expression(right_coeff)]),
                self._structured_sum_terms([left_bias, self._structured_negate_expression(right_bias)]),
            )
        if expr.operator == "INT_MULT":
            left_depends = self._expression_mentions_variable_name(expr.operands[0], counter_name)
            right_depends = self._expression_mentions_variable_name(expr.operands[1], counter_name)
            if left_depends and right_depends:
                return None, None
            if left_coeff is None or left_bias is None or right_coeff is None or right_bias is None:
                return None, None
            if left_depends:
                factor = right_bias
                return (
                    self._structured_multiply_independent_expressions(left_coeff, factor),
                    self._structured_multiply_independent_expressions(left_bias, factor),
                )
            if right_depends:
                factor = left_bias
                return (
                    self._structured_multiply_independent_expressions(right_coeff, factor),
                    self._structured_multiply_independent_expressions(right_bias, factor),
                )
        return None, None

    def _structured_negate_expression(self, expr: Optional[Expression]) -> Optional[Expression]:
        if expr is None:
            return None
        if expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
            return Expression.constant(-int(expr.value), max(1, expr.size or 4))
        negated = Expression.unary_op("INT_2COMP", expr)
        negated.size = expr.size
        return negated

    def _structured_multiply_independent_expressions(
        self,
        left: Optional[Expression],
        right: Optional[Expression],
    ) -> Optional[Expression]:
        if left is None or right is None:
            return None
        if left.expr_type == ExpressionType.CONSTANT and int(left.value) == 0:
            return Expression.constant(0, max(1, right.size or 4))
        if right.expr_type == ExpressionType.CONSTANT and int(right.value) == 0:
            return Expression.constant(0, max(1, left.size or 4))
        if left.expr_type == ExpressionType.CONSTANT and int(left.value) == 1:
            return right
        if right.expr_type == ExpressionType.CONSTANT and int(right.value) == 1:
            return left
        product = Expression.binary_op("INT_MULT", left, right)
        product.size = max(
            getattr(left, "size", 0) or 0,
            getattr(right, "size", 0) or 0,
            4,
        )
        return product

    def _expression_mentions_name(self, expr: Optional[Expression], target_name: str) -> bool:
        if expr is None:
            return False
        if expr.name == target_name:
            return True
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None and self._expression_mentions_name(cond.expression, target_name):
                    return True
                if self._expression_mentions_name(value, target_name):
                    return True
            return False
        return any(self._expression_mentions_name(operand, target_name) for operand in expr.operands or [])

    def _expression_mentions_variable_name(self, expr: Optional[Expression], target_name: str) -> bool:
        if expr is None:
            return False
        if expr.expr_type == ExpressionType.VARIABLE and expr.name == target_name:
            return True
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None and self._expression_mentions_variable_name(cond.expression, target_name):
                    return True
                if self._expression_mentions_variable_name(value, target_name):
                    return True
            return False
        return any(self._expression_mentions_variable_name(operand, target_name) for operand in expr.operands or [])

    def _normalize_wrapper_c_lines(self, c_text: str) -> List[str]:
        normalized: List[str] = []
        pending: Optional[str] = None
        for raw_line in c_text.splitlines():
            line = re.sub(r"/\*.*?\*/", "", raw_line)
            line = line.split("//", 1)[0].strip()
            if not line:
                continue
            split_transition = self._split_wrapper_control_transition_line(line)
            pieces = split_transition if split_transition is not None else [line]
            for piece in pieces:
                if pending:
                    pending = f"{pending} {piece.strip()}".strip()
                else:
                    pending = piece.strip()
                if self._is_complete_wrapper_c_statement(pending):
                    normalized.append(pending)
                    pending = None
        if pending:
            normalized.append(pending)
        return normalized

    def _is_complete_wrapper_c_statement(self, line: str) -> bool:
        stripped = line.strip()
        if not stripped:
            return False
        if stripped in {"{", "}"}:
            return True
        if self._wrapper_c_delimiter_balance(stripped) != 0:
            return False
        if stripped.endswith((";", "{", "}")):
            return True
        if stripped in {"do", "else"}:
            return False
        return False

    def _wrapper_c_delimiter_balance(self, text: str) -> int:
        depth = 0
        for char in text:
            if char in "([":
                depth += 1
            elif char in ")]":
                depth -= 1
        return depth

    def _split_wrapper_control_transition_line(self, line: str) -> Optional[List[str]]:
        else_if_match = re.fullmatch(r"\}\s*else\s+if\s*\((.+)\)\s*\{", line)
        if else_if_match:
            return ["}", f"else if ({else_if_match.group(1).strip()}) {{"]
        if re.fullmatch(r"\}\s*else\s*\{", line):
            return ["}", "else {"]
        while_match = re.fullmatch(r"\}\s*while\s*\((.+)\)\s*;", line)
        if while_match:
            return ["}", f"while ({while_match.group(1).strip()});"]
        return None

    def _looks_like_wrapper_header_line(self, line: str) -> bool:
        return bool(
            re.match(
                r"^[A-Za-z_][A-Za-z0-9_\s\*]*\s+[A-Za-z_][A-Za-z0-9_]*\s*\(.*\)\s*\{?$",
                line.strip(),
            )
        )

    def _has_structured_control_flow_markers(self, body_lines: List[str]) -> bool:
        markers = ("if ", "if(", "else", "switch", "while", "for", "do ")
        return any(line.startswith(markers) for line in body_lines)

    def _is_wrapper_declaration_line(self, line: str) -> bool:
        if not line.endswith(";"):
            return False
        if "=" in line or "(" in line or ")" in line:
            return False
        tokens = line[:-1].split()
        if tokens and tokens[0] in {"return", "break", "continue", "goto", "case", "default"}:
            return False
        return len(tokens) >= 2

    def _expand_wrapper_call_states(
        self,
        states: List[Tuple[Dict[str, Expression], List[Condition], Optional[Expression]]],
        target_name: Optional[str],
        callee_spec: str,
        arg_blob: str,
        parameters: List[Dict],
        active_functions: Set[str],
        current_function,
        assign_to_last_call: bool,
    ) -> Optional[List[Tuple[Dict[str, Expression], List[Condition], Optional[Expression]]]]:
        arg_texts = self._split_call_arguments(arg_blob) if arg_blob else []
        if arg_texts is None:
            return None

        next_states: List[Tuple[Dict[str, Expression], List[Condition], Optional[Expression]]] = []
        for bindings, conditions, _last_call in states:
            parsed_args: List[Expression] = []
            for arg_index, arg_text in enumerate(arg_texts):
                parsed_arg = self._parse_wrapper_argument_expr(
                    arg_text,
                    parameters,
                    fallback_index=arg_index,
                    local_bindings=bindings,
                )
                if parsed_arg is None:
                    return None
                parsed_args.append(parsed_arg)

            expanded = self._resolve_wrapper_call_target(
                callee_spec,
                parsed_args,
                conditions,
                parameters,
                bindings,
                active_functions,
                current_function,
            )
            if not expanded:
                if self.debug:
                    arg_preview = [arg.to_string() for arg in parsed_args]
                    self._debug_print(
                        "Call-wrapper nested expansion failed: "
                        f"callee='{callee_spec}', args={arg_preview}"
                    )
                return None

            for ev in expanded:
                merged_conditions = ConditionSimplifier.simplify_conditions(
                    list(conditions) + list(ev.conditions)
                )
                if ConditionSimplifier.is_contradiction(merged_conditions):
                    continue
                new_bindings = dict(bindings)
                cloned_value = self._clone_expression(ev.value)
                last_call_value = None
                if target_name is not None:
                    new_bindings[target_name] = cloned_value
                if assign_to_last_call:
                    last_call_value = cloned_value
                next_states.append((new_bindings, merged_conditions, last_call_value))

        return next_states or None

    def _expand_wrapper_return_call_states(
        self,
        states: List[Tuple[Dict[str, Expression], List[Condition], Optional[Expression]]],
        callee_spec: str,
        arg_blob: str,
        parameters: List[Dict],
        active_functions: Set[str],
        current_function,
    ) -> Optional[List[Tuple[Dict[str, Expression], List[Condition], Optional[Expression]]]]:
        arg_texts = self._split_call_arguments(arg_blob) if arg_blob else []
        if arg_texts is None:
            return None

        terminated_states: List[Tuple[Dict[str, Expression], List[Condition], Optional[Expression]]] = []
        for bindings, conditions, _last_call in states:
            parsed_args: List[Expression] = []
            for arg_index, arg_text in enumerate(arg_texts):
                parsed_arg = self._parse_wrapper_argument_expr(
                    arg_text,
                    parameters,
                    fallback_index=arg_index,
                    local_bindings=bindings,
                )
                if parsed_arg is None:
                    return None
                parsed_args.append(parsed_arg)

            expanded = self._resolve_wrapper_call_target(
                callee_spec,
                parsed_args,
                conditions,
                parameters,
                bindings,
                active_functions,
                current_function,
            )
            if not expanded:
                if self.debug:
                    arg_preview = [arg.to_string() for arg in parsed_args]
                    self._debug_print(
                        "Return-call wrapper expansion failed: "
                        f"callee='{callee_spec}', args={arg_preview}"
                    )
                return None

            for ev in expanded:
                merged_conditions = ConditionSimplifier.simplify_conditions(
                    list(conditions) + list(ev.conditions)
                )
                if ConditionSimplifier.is_contradiction(merged_conditions):
                    continue
                terminated_states.append(
                    (
                        dict(bindings),
                        merged_conditions,
                        self._clone_expression(ev.value),
                    )
                )

        return terminated_states or None

    def _resolve_wrapper_call_target(
        self,
        callee_spec: str,
        args: List[Expression],
        conditions: List[Condition],
        parameters: List[Dict],
        local_bindings: Dict[str, Expression],
        active_functions: Set[str],
        current_function,
    ):
        normalized_spec = self._normalize_wrapper_callee_spec(callee_spec)
        direct_name = None
        if self._should_attempt_direct_wrapper_name_resolution(
            normalized_spec,
            parameters,
            local_bindings,
        ):
            direct_name = self._resolve_named_wrapper_target(normalized_spec)
        if direct_name is not None:
            augmented_args = self._augment_wrapper_call_args_with_implicit_passthrough(
                direct_name,
                args,
                parameters,
                active_functions,
            )
            return self._resolve_call_expansions(
                direct_name,
                augmented_args,
                active_functions,
                current_function=current_function,
            )

        callee_expr = self._parse_wrapper_argument_expr(
            normalized_spec,
            parameters,
            fallback_index=0,
            local_bindings=local_bindings,
        )
        if callee_expr is None:
            return None
        return self._resolve_indirect_wrapper_call_expansions(
            callee_expr,
            args,
            conditions,
            parameters,
            active_functions,
            current_function,
        )

    def _resolve_indirect_wrapper_call_expansions(
        self,
        callee_expr: Expression,
        args: List[Expression],
        conditions: List[Condition],
        parameters: List[Dict],
        active_functions: Set[str],
        current_function,
    ):
        from ..transform.expander import ExpandedValue

        resolved_targets = self._resolve_wrapper_indirect_call_targets(
            callee_expr,
            conditions,
            parameters,
        )
        if not resolved_targets:
            return None

        expanded = []
        for target_name, target_conditions in resolved_targets:
            augmented_args = self._augment_wrapper_call_args_with_implicit_passthrough(
                target_name,
                args,
                parameters,
                active_functions,
            )
            resolved = self._resolve_call_expansions(
                target_name,
                augmented_args,
                active_functions,
                current_function=current_function,
            )
            if not resolved:
                return None
            for ev in resolved:
                merged_conditions = ConditionSimplifier.simplify_conditions(
                    list(target_conditions) + list(ev.conditions)
                )
                if ConditionSimplifier.is_contradiction(merged_conditions):
                    continue
                expanded.append(
                    ExpandedValue(
                        value=self._clone_expression(ev.value),
                        conditions=merged_conditions,
                    )
                )
        return expanded or None

    def _augment_wrapper_call_args_with_implicit_passthrough(
        self,
        function_name: str,
        args: List[Expression],
        current_parameters: List[Dict],
        active_functions: Set[str],
    ) -> List[Expression]:
        try:
            callee_analysis = self._get_or_analyze_call_target(
                function_name,
                active_functions,
                minimum_param_count=len(args) + 1,
            )
        except Exception:
            return list(args)
        if callee_analysis is None:
            return list(args)

        callee_parameters = list(getattr(callee_analysis, "parameters", None) or [])
        if len(args) >= len(callee_parameters):
            return list(args)

        explicit_param_names = {
            arg.name
            for arg in args
            if getattr(arg, "expr_type", None) == ExpressionType.PARAMETER and arg.name
        }

        augmented_args = list(args)
        for callee_param in callee_parameters[len(args):]:
            matched_param = self._find_implicit_passthrough_parameter(
                callee_param,
                current_parameters,
                explicit_param_names,
            )
            if matched_param is None:
                return list(args)
            param_name = matched_param.get("name")
            if not param_name:
                return list(args)
            explicit_param_names.add(param_name)
            augmented_args.append(
                Expression.parameter(
                    param_name,
                    index=int(matched_param.get("index", len(augmented_args))),
                    data_type=matched_param.get("data_type"),
                    size=matched_param.get("size", callee_param.get("size", 4)),
                    storage_info=self._coerce_wrapper_storage_info(matched_param.get("storage")),
                )
            )

        return augmented_args

    def _find_implicit_passthrough_parameter(
        self,
        callee_param: Dict,
        current_parameters: List[Dict],
        used_param_names: Set[str],
    ) -> Optional[Dict]:
        callee_storage = callee_param.get("storage") or {}
        candidates = []
        for param in current_parameters or []:
            name = param.get("name")
            if not name or name in used_param_names:
                continue
            if not self._parameter_storages_match_for_passthrough(
                param.get("storage"),
                callee_storage,
            ):
                continue
            candidates.append(param)

        if not candidates:
            overlap_candidates = []
            for param in current_parameters or []:
                name = param.get("name")
                if not name or name in used_param_names:
                    continue
                if not self._parameter_storages_overlap_for_passthrough(
                    param.get("storage"),
                    callee_storage,
                ):
                    continue
                overlap_candidates.append(param)
            if overlap_candidates:
                overlap_candidates.sort(key=lambda param: int(param.get("index", 1 << 20)))
                return overlap_candidates[0]

            named = self._find_implicit_passthrough_parameter_by_name_or_index(
                callee_param,
                current_parameters,
                used_param_names,
            )
            if named is not None:
                return named
            return None

        candidates.sort(key=lambda param: int(param.get("index", 1 << 20)))
        return candidates[0]

    def _find_implicit_passthrough_parameter_by_name_or_index(
        self,
        callee_param: Dict,
        current_parameters: List[Dict],
        used_param_names: Set[str],
    ) -> Optional[Dict]:
        callee_name = callee_param.get("name")
        callee_index = int(callee_param.get("index", -1))

        if callee_name:
            for param in current_parameters or []:
                name = param.get("name")
                if not name or name in used_param_names:
                    continue
                if name != callee_name:
                    continue
                param_index = int(param.get("index", -1))
                if callee_index >= 0 and param_index >= 0 and param_index != callee_index:
                    continue
                return param

        if callee_index >= 0:
            for param in current_parameters or []:
                name = param.get("name")
                if not name or name in used_param_names:
                    continue
                if int(param.get("index", -1)) != callee_index:
                    continue
                return param

        return None

    def _parameter_storages_match_for_passthrough(
        self,
        caller_storage: Optional[Dict],
        callee_storage: Optional[Dict],
    ) -> bool:
        caller = caller_storage or {}
        callee = callee_storage or {}
        if not caller.get("is_register") or not callee.get("is_register"):
            return False

        caller_base = (caller.get("base_register_name") or caller.get("register_name") or "").lower()
        callee_base = (callee.get("base_register_name") or callee.get("register_name") or "").lower()
        if not caller_base or caller_base != callee_base:
            return False

        caller_offset = int(caller.get("bit_offset_in_base", 0))
        callee_offset = int(callee.get("bit_offset_in_base", 0))
        if caller_offset != callee_offset:
            return False

        caller_bits = int(caller.get("size_bits") or (caller.get("size", 0) * 8))
        callee_bits = int(callee.get("size_bits") or (callee.get("size", 0) * 8))
        return caller_bits == callee_bits and caller_bits > 0

    def _parameter_storages_overlap_for_passthrough(
        self,
        caller_storage: Optional[Dict],
        callee_storage: Optional[Dict],
    ) -> bool:
        caller = self._coerce_wrapper_storage_info(caller_storage)
        callee = self._coerce_wrapper_storage_info(callee_storage)
        if caller is None or callee is None:
            return False
        if not caller.is_register or not callee.is_register:
            return False
        try:
            return (
                caller.shares_base_register_with(callee)
                and caller.bit_range_overlaps_with(callee)
            )
        except Exception:
            return False

    def _coerce_wrapper_storage_info(self, storage: Optional[object]) -> Optional[StorageInfo]:
        if storage is None:
            return None
        if isinstance(storage, StorageInfo):
            return storage
        if isinstance(storage, dict):
            try:
                return StorageInfo(
                    is_register=bool(storage.get("is_register", False)),
                    space_name=str(storage.get("space_name", "")),
                    offset=int(storage.get("offset", 0)),
                    size=int(storage.get("size", 0)),
                    size_bits=int(storage.get("size_bits", 0)),
                    register_name=storage.get("register_name"),
                    base_register_name=storage.get("base_register_name"),
                    base_register_offset=int(storage.get("base_register_offset", 0)),
                    base_register_size=int(storage.get("base_register_size", 0)),
                    base_register_size_bits=int(storage.get("base_register_size_bits", 0)),
                    bit_offset_in_base=int(storage.get("bit_offset_in_base", 0)),
                )
            except Exception:
                return None
        return None

    def _parameter_descriptor_quality(self, parameters: Optional[List[Dict]]) -> Tuple[int, int, int, int]:
        params = list(parameters or [])
        return (
            len(params),
            sum(1 for param in params if param.get("storage")),
            sum(1 for param in params if param.get("data_type")),
            sum(1 for param in params if int(param.get("size", 0) or 0) > 0),
        )

    def _choose_richer_parameter_descriptors(
        self,
        cached_parameters: Optional[List[Dict]],
        fresh_parameters: Optional[List[Dict]],
    ) -> List[Dict]:
        cached = list(cached_parameters or [])
        fresh = list(fresh_parameters or [])
        if self._parameter_descriptor_quality(fresh) > self._parameter_descriptor_quality(cached):
            return fresh
        return cached

    def _get_freshest_callee_parameters(self, function_name: str) -> List[Dict]:
        callee = self._find_function_by_name(function_name)
        if callee is None:
            return []

        callee_key = str(callee.getEntryPoint())
        cached_parameters = self._effect_summary_parameter_cache.get(callee_key)

        results = self._decompile_function(callee, timeout=60)
        if results is None:
            return list(cached_parameters or [])

        callee_high = results.getHighFunction()
        if callee_high is None:
            return list(cached_parameters or [])

        fresh_parameters = self._collect_parameters(callee_high)
        merged_parameters = self._choose_richer_parameter_descriptors(
            cached_parameters,
            fresh_parameters,
        )
        self._effect_summary_parameter_cache[callee_key] = list(merged_parameters)
        return list(merged_parameters)

    def _augment_parameters_with_implicit_passthrough(
        self,
        parameters: List[Dict],
        tracer: Any,
        active_functions: Set[str],
    ) -> List[Dict]:
        augmented = [dict(param) for param in (parameters or [])]
        changed = False

        try:
            pcode_ops = list(tracer.get_all_pcode_ops())
        except Exception:
            return augmented

        for op in pcode_ops:
            try:
                if op.getMnemonic() not in {"CALL", "CALLIND"} or op.getNumInputs() < 1:
                    continue
            except Exception:
                continue

            target_name = _resolve_call_target_name(tracer, op)
            if not target_name or target_name == "UNKNOWN_FUNC" or target_name in active_functions:
                continue

            explicit_count = max(0, int(op.getNumInputs()) - 1)
            callee_parameters = self._get_freshest_callee_parameters(target_name)
            if len(callee_parameters) <= explicit_count:
                continue

            for callee_param in callee_parameters[explicit_count:]:
                callee_storage = self._coerce_wrapper_storage_info(callee_param.get("storage"))
                if callee_storage is None or not callee_storage.is_register:
                    continue
                if any(
                    self._parameter_storages_overlap_for_passthrough(
                        existing.get("storage"),
                        callee_param.get("storage"),
                    )
                    for existing in augmented
                ):
                    continue
                if not self._should_synthesize_implicit_passthrough_for_call(
                    tracer,
                    op,
                    callee_storage,
                ):
                    continue
                augmented.append(
                    self._synthesize_implicit_passthrough_parameter(
                        augmented,
                        callee_param,
                        callee_storage,
                    )
                )
                changed = True

        if changed:
            augmented.sort(key=lambda param: int(param.get("index", 1 << 20)))
        return augmented

    def _should_synthesize_implicit_passthrough_for_call(
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

    def _is_passthrough_storage_live_in_for_call(
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

    def _has_non_parameter_symbol_for_storage(
        self,
        tracer: PcodeTracer,
        target_storage: StorageInfo,
    ) -> bool:
        high_function = getattr(tracer, "high_function", None)
        if high_function is None:
            return False
        try:
            local_map = high_function.getLocalSymbolMap()
        except Exception:
            return False
        if local_map is None:
            return False

        for sym in local_map.getSymbols() or []:
            try:
                if sym.isParameter():
                    continue
            except Exception:
                continue
            candidate_storage = self._coerce_wrapper_storage_info(self._get_storage_info(sym))
            if candidate_storage is None or not candidate_storage.is_register:
                continue
            try:
                same_base = candidate_storage.shares_base_register_with(target_storage)
                overlaps = candidate_storage.bit_range_overlaps_with(target_storage)
            except Exception:
                same_base = False
                overlaps = False
            if same_base and overlaps:
                return True
        return False

    def _coerce_order_key(self, value: object) -> Optional[int]:
        if value is None:
            return None
        if isinstance(value, bool):
            return int(value)
        if isinstance(value, int):
            return value
        try:
            return int(cast(Any, value))
        except Exception:
            return None

    def _synthesize_implicit_passthrough_parameter(
        self,
        current_parameters: List[Dict],
        callee_param: Dict,
        callee_storage: StorageInfo,
    ) -> Dict:
        used_names = {param.get("name") for param in current_parameters if param.get("name")}
        next_index = max((int(param.get("index", -1)) for param in current_parameters), default=-1) + 1
        suggested_name = callee_param.get("name") or f"param_{next_index + 1}"
        if suggested_name in used_names:
            suggested_name = f"param_{next_index + 1}"

        return {
            "name": suggested_name,
            "index": next_index,
            "size": callee_param.get("size") or callee_storage.size or 0,
            "data_type": callee_param.get("data_type"),
            "data_type_obj": callee_param.get("data_type_obj"),
            "is_signed": callee_param.get("is_signed", True),
            "storage": callee_storage.to_dict(),
            "implicit_passthrough": True,
        }

    def _resolve_wrapper_indirect_call_targets(
        self,
        callee_expr: Optional[Expression],
        conditions: List[Condition],
        parameters: List[Dict],
    ) -> List[Tuple[str, List[Condition]]]:
        if callee_expr is None:
            return []

        direct_name = self._resolve_expression_to_named_wrapper_target(callee_expr)
        if direct_name is not None:
            simplified = ConditionSimplifier.simplify_conditions(list(conditions))
            if ConditionSimplifier.is_contradiction(simplified):
                return []
            return [(direct_name, simplified)]

        rewritten = callee_expr
        try:
            image_base = self.program.getImageBase().getOffset()
        except Exception:
            image_base = None

        try:
            rewritten = concretize_readonly_loads(
                callee_expr,
                list(conditions or []),
                list(parameters or []),
                self._read_memory_value,
                image_base=image_base,
                debug=self.debug,
            )
        except Exception:
            rewritten = callee_expr

        if rewritten.expr_type == ExpressionType.PHI and rewritten.value:
            resolved: List[Tuple[str, List[Condition]]] = []
            for branch_cond, branch_value in rewritten.value:
                branch_conditions = list(conditions)
                if branch_cond is not None:
                    branch_conditions.append(branch_cond)
                resolved.extend(
                    self._resolve_wrapper_indirect_call_targets(
                        branch_value,
                        branch_conditions,
                        parameters,
                    )
                )
            return self._deduplicate_wrapper_targets(resolved)

        resolved: List[Tuple[str, List[Condition]]] = []
        for branch_conditions, address_value in _enumerate_constant_expression_branches(rewritten):
            target_name = self._lookup_program_function_name_by_value(address_value)
            if target_name is None:
                target_name = f"ADDR_{address_value:x}"
            merged_conditions = ConditionSimplifier.simplify_conditions(
                list(conditions) + list(branch_conditions)
            )
            if ConditionSimplifier.is_contradiction(merged_conditions):
                continue
            resolved.append((target_name, merged_conditions))
        return self._deduplicate_wrapper_targets(resolved)

    def _should_attempt_direct_wrapper_name_resolution(
        self,
        name: str,
        parameters: List[Dict],
        local_bindings: Dict[str, Expression],
    ) -> bool:
        if not name or name in local_bindings:
            return False
        if any(name == param.get("name") for param in (parameters or []) if param.get("name")):
            return False
        if name.startswith(("PTR_", "DAT_", "LAB_")):
            return False
        return True

    def _normalize_wrapper_callee_spec(self, callee_spec: str) -> str:
        spec = self._strip_wrapper_callee_casts(callee_spec)
        if spec.startswith("*"):
            spec = self._strip_wrapper_callee_casts(spec[1:].strip())
        return spec

    def _strip_wrapper_callee_casts(self, text: str) -> str:
        expr_text = self._strip_outer_parentheses(text.strip())
        previous = None
        while expr_text != previous:
            previous = expr_text
            expr_text = self._strip_outer_parentheses(expr_text)
            cast_match = re.match(r"^\(\s*[A-Za-z_][A-Za-z0-9_\s\*]*\s*\)\s*(.+)$", expr_text)
            if cast_match:
                expr_text = cast_match.group(1).strip()
        return self._strip_outer_parentheses(expr_text)

    def _deduplicate_wrapper_targets(
        self,
        targets: List[Tuple[str, List[Condition]]],
    ) -> List[Tuple[str, List[Condition]]]:
        deduped: List[Tuple[str, List[Condition]]] = []
        seen = set()
        for target_name, conditions in targets:
            key = (target_name, tuple(cond.to_string() for cond in conditions))
            if key in seen:
                continue
            seen.add(key)
            deduped.append((target_name, conditions))
        return deduped

    def _resolve_expression_to_named_wrapper_target(
        self,
        expr: Expression,
    ) -> Optional[str]:
        if expr.expr_type == ExpressionType.PARAMETER:
            return None
        if expr.expr_type == ExpressionType.VARIABLE and expr.name:
            if expr.name.startswith(("PTR_", "DAT_", "LAB_")):
                return self._resolve_pointer_symbol_wrapper_target(expr.name)
            return self._resolve_named_wrapper_target(expr.name)
        return None

    def _resolve_named_wrapper_target(self, name: Optional[str]) -> Optional[str]:
        if not name:
            return None
        if self._looks_like_decompiler_parameter_name(name):
            return None
        if name.startswith("ADDR_"):
            return name
        pointer_target = self._resolve_pointer_symbol_wrapper_target(name)
        if pointer_target is not None:
            return pointer_target
        try:
            resolved = self._find_function_by_name(name)
        except Exception:
            resolved = None
        if resolved is not None:
            return name
        if re.fullmatch(r"(?:thunk_)?FUN_[0-9a-fA-F]+", name):
            return name
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name) and not self._looks_like_decompiler_temp_name(name):
            return name
        return None

    def _looks_like_decompiler_parameter_name(self, name: Optional[str]) -> bool:
        return bool(re.fullmatch(r"(?:param|arg)_?\d+", name or ""))

    def _resolve_pointer_symbol_wrapper_target(self, name: Optional[str]) -> Optional[str]:
        if not name or not name.startswith(("PTR_", "DAT_", "LAB_")):
            return None

        match = re.fullmatch(r"(?:PTR|DAT|LAB)_([A-Za-z_][A-Za-z0-9_]*)_[0-9A-Fa-f]+", name)
        if match is None:
            return None

        candidate = match.group(1)
        try:
            resolved = self._find_function_by_name(candidate)
        except Exception:
            resolved = None
        if resolved is not None:
            return candidate
        if re.fullmatch(r"(?:thunk_)?FUN_[0-9a-fA-F]+", candidate):
            return candidate
        return None

    def _looks_like_decompiler_temp_name(self, name: str) -> bool:
        candidate = name or ""
        if re.fullmatch(r"(?:[A-Za-z]{1,4}Var\d+|local_[0-9A-Fa-f]+)", candidate):
            return True
        return bool(
            re.fullmatch(
                r"(?:UNRECOVERED|extraout|unaff|in)_[A-Za-z0-9_]+",
                candidate,
            )
        )

    def _looks_like_wrapper_fragment_temp_name(self, name: str) -> bool:
        candidate = name or ""
        return bool(
            re.fullmatch(
                r"(?:UNRECOVERED|extraout|unaff|in)_[A-Za-z0-9_]+",
                candidate,
            )
        )

    def _lookup_program_function_name_by_value(self, address_value: int) -> Optional[str]:
        try:
            default_space = self.program.getAddressFactory().getDefaultAddressSpace()
            addr = default_space.getAddress(address_value)
            manager = self.program.getFunctionManager()
            func = manager.getFunctionAt(addr)
            if func is None:
                func = manager.getFunctionContaining(addr)
            if func is not None:
                return func.getName()
        except Exception:
            return None
        return None

    def _should_attempt_switch_recovery(self, analysis: FunctionReturnAnalysis) -> bool:
        if analysis.recovered_from_decompiler:
            return False
        if analysis.has_unknown_return():
            return True
        if analysis.has_overlapping_unconditional_returns():
            return True
        if self._analysis_has_ambiguous_condition_region_returns(analysis):
            return True
        return any(
            reason in {"call_out_of_scope", "callind_out_of_scope"}
            for reason in analysis.unknown_event_reasons
        )

    def _parse_call_wrapper_from_c_text(
        self,
        c_text: str,
        parameters: List[Dict],
    ) -> Optional[Tuple[str, List[Expression]]]:
        """`callee(args); return;` だけの単純 wrapper を解析する。"""
        lines = []
        for raw_line in c_text.splitlines():
            line = raw_line.split("//", 1)[0].strip()
            if line:
                lines.append(line)
        if not lines:
            return None

        body_lines = [
            line
            for line in lines
            if line not in {"{", "}"} and not line.endswith("{")
        ]
        if len(body_lines) < 3:
            return None

        call_line = None
        return_seen = False
        for line in body_lines[1:]:
            if line == "return;":
                return_seen = True
                continue
            if return_seen:
                return None
            if call_line is not None:
                return None
            call_line = line

        if call_line is None or not return_seen:
            return None

        parsed_call = self._parse_wrapper_call_statement(call_line)
        if parsed_call is None:
            return None
        target_name, callee_name, arg_blob = parsed_call
        resolved_callee_name = self._resolve_named_wrapper_target(
            self._normalize_wrapper_callee_spec(callee_name)
        )
        if target_name is not None or resolved_callee_name is None:
            return None
        if not arg_blob:
            return resolved_callee_name, []

        arg_texts = self._split_call_arguments(arg_blob)
        if arg_texts is None:
            return None

        parsed_args: List[Expression] = []
        for index, arg_text in enumerate(arg_texts):
            parsed = self._parse_wrapper_argument_expr(arg_text, parameters, index)
            if parsed is None:
                return None
            parsed_args.append(parsed)
        return resolved_callee_name, parsed_args

    def _split_call_arguments(self, arg_blob: str) -> Optional[List[str]]:
        parts: List[str] = []
        current: List[str] = []
        depth = 0
        for char in arg_blob:
            if char == "," and depth == 0:
                part = "".join(current).strip()
                if not part:
                    return None
                parts.append(part)
                current = []
                continue
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth < 0:
                    return None
            current.append(char)
        if depth != 0:
            return None
        tail = "".join(current).strip()
        if tail:
            parts.append(tail)
        return parts or None

    def _parse_wrapper_call_statement(
        self,
        statement: str,
    ) -> Optional[Tuple[Optional[str], str, str]]:
        stripped = statement.strip()
        if not stripped.endswith(";"):
            return None
        stripped = stripped[:-1].strip()
        if not stripped:
            return None

        target_name = None
        assign_match = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.+)", stripped)
        if assign_match:
            target_name = assign_match.group(1)
            stripped = assign_match.group(2).strip()

        if not stripped.endswith(")"):
            return None
        open_index = self._find_outer_call_open_paren(stripped)
        if open_index is None:
            return None

        callee_spec = stripped[:open_index].strip()
        arg_blob = stripped[open_index + 1:-1].strip()
        if not callee_spec:
            return None
        return target_name, callee_spec, arg_blob

    def _parse_wrapper_call_expr(
        self,
        expr_text: str,
    ) -> Optional[Tuple[str, str]]:
        stripped = self._strip_outer_parentheses(expr_text.strip())
        if not stripped or not stripped.endswith(")"):
            return None
        open_index = self._find_outer_call_open_paren(stripped)
        if open_index is None:
            return None
        callee_spec = stripped[:open_index].strip()
        arg_blob = stripped[open_index + 1:-1].strip()
        if not callee_spec:
            return None
        return callee_spec, arg_blob

    def _parse_wrapper_store_statement(
        self,
        statement: str,
    ) -> Optional[Tuple[str, str]]:
        stripped = statement.strip()
        if not stripped.endswith(";"):
            return None
        stripped = stripped[:-1].strip()
        if not stripped:
            return None

        assign_match = re.fullmatch(r"(\*.+?)\s*=\s*(.+)", stripped)
        if assign_match is None:
            return None

        lhs_text = assign_match.group(1).strip()
        rhs_text = assign_match.group(2).strip()
        if not lhs_text.startswith("*") or not rhs_text:
            return None
        return lhs_text, rhs_text

    def _find_outer_call_open_paren(self, text: str) -> Optional[int]:
        depth = 0
        for index in range(len(text) - 1, -1, -1):
            char = text[index]
            if char == ")":
                depth += 1
                continue
            if char == "(":
                depth -= 1
                if depth == 0:
                    return index
                if depth < 0:
                    return None
        return None

    def _parse_wrapper_argument_expr(
        self,
        text: str,
        parameters: List[Dict],
        fallback_index: int,
        local_bindings: Optional[Dict[str, Expression]] = None,
    ) -> Optional[Expression]:
        return self._parse_wrapper_expr(
            text,
            parameters,
            fallback_index=fallback_index,
            local_bindings=local_bindings,
        )

    def _analysis_needs_wrapper_recovery(
        self,
        analysis: Optional[FunctionReturnAnalysis],
    ) -> bool:
        if analysis is None:
            return False
        if analysis.has_unknown_return():
            return True
        if analysis.has_unresolved_return_value():
            return True
        return any(
            reason in {"call_out_of_scope", "callind_out_of_scope"}
            for reason in getattr(analysis, "unknown_event_reasons", [])
        )

    def _wrapper_memory_binding_key(self, operand: Expression) -> str:
        return f"*{operand.to_string()}"

    def _record_wrapper_store_binding(
        self,
        bindings: Dict[str, Expression],
        lhs_text: str,
        value_expr: Expression,
        parameters: List[Dict],
    ) -> None:
        normalized_lhs = self._strip_outer_parentheses(lhs_text.strip())
        bindings[normalized_lhs] = self._clone_expression(value_expr)

        lhs_expr = self._parse_wrapper_argument_expr(
            normalized_lhs,
            parameters,
            fallback_index=0,
            local_bindings=None,
        )
        if (
            lhs_expr is None
            or lhs_expr.expr_type != ExpressionType.MEMORY
            or not lhs_expr.operands
        ):
            return

        bindings[self._wrapper_memory_binding_key(lhs_expr.operands[0])] = self._clone_expression(value_expr)

    def _get_decompiled_c_text(self, decompile_results) -> Optional[str]:
        """DecompileResults から C テキストを安全に取得する。"""
        if decompile_results is None:
            return None

        try:
            decompiled = decompile_results.getDecompiledFunction()
            if decompiled is not None:
                c_text = decompiled.getC()
                if c_text:
                    return str(c_text)
        except Exception:
            pass

        for attr_name in ("getC", "getDecompiledFunction"):
            try:
                candidate = getattr(decompile_results, attr_name, None)
                if candidate is None:
                    continue
                value = candidate()
                if isinstance(value, str) and value.strip():
                    return value
            except Exception:
                continue

        return None

    def _parse_switch_returns_from_c_text(
        self,
        c_text: str,
        parameters: List[Dict],
        return_type: Optional[str],
        address: str,
    ) -> Optional[List[ReturnInfo]]:
        """単純な switch-return 形式を ReturnInfo 群へ変換する。"""
        lines = [line.rstrip() for line in c_text.splitlines()]
        switch_blocks = self._extract_switch_blocks_with_spans(lines)
        if len(switch_blocks) != 1:
            if self.debug:
                self._debug_print(
                    f"Switch-like parser aborted: expected 1 switch block, found {len(switch_blocks)}"
                )
            return None

        subject_raw, block_lines, _start_index, end_index = switch_blocks[0]
        subject_expr = self._parse_switch_subject_expr(subject_raw, parameters)
        if subject_expr is None:
            if self.debug:
                self._debug_print(
                    f"Switch-like parser aborted: unsupported switch subject '{subject_raw}'"
                )
            return None

        parsed_arms = self._parse_switch_arms(block_lines)
        if parsed_arms is None:
            shared_return_name = self._find_shared_return_variable(lines[end_index + 1:])
            if self.debug:
                if shared_return_name:
                    self._debug_print(
                        "Direct switch-return parse failed; "
                        f"retrying shared-return variable mode with '{shared_return_name}'"
                    )
                else:
                    self._debug_print(
                        "Switch-like parser aborted: no direct return arms and no shared return variable"
                    )
            if not shared_return_name:
                return None
            parsed_arms = self._parse_switch_assignment_arms(block_lines, shared_return_name)
            if parsed_arms is None:
                if self.debug:
                    self._debug_print(
                        "Switch-like parser aborted: shared-return assignment arms unsupported"
                    )
                return None

        case_values = []
        return_size = self._get_return_size_bytes(return_type)
        recovered: List[ReturnInfo] = []

        branch_index = 0
        for labels, return_value, is_default in parsed_arms:
            if is_default:
                conditions: List[Condition] = []
                if not case_values:
                    continue
                for case_value in case_values:
                    conditions.append(
                        Condition(
                            Expression.binary_op(
                                "INT_NOTEQUAL",
                                self._clone_expression(subject_expr),
                                Expression.constant(case_value, size=subject_expr.size or return_size),
                            ),
                            False,
                        )
                    )
                value_expr = Expression.constant(return_value, size=return_size)
                recovered.append(
                    ReturnInfo(
                        address=address,
                        value=value_expr,
                        conditions=conditions,
                        branch_index=branch_index,
                    )
                )
                branch_index += 1
                continue

            for label in labels:
                case_values.append(label)
                conditions = [
                    Condition(
                        Expression.binary_op(
                            "INT_EQUAL",
                            self._clone_expression(subject_expr),
                            Expression.constant(label, size=subject_expr.size or return_size),
                        ),
                        False,
                    )
                ]
                value_expr = Expression.constant(return_value, size=return_size)
                recovered.append(
                    ReturnInfo(
                        address=address,
                        value=value_expr,
                        conditions=conditions,
                        branch_index=branch_index,
                    )
                )
                branch_index += 1

        if len(recovered) < 2:
            if self.debug:
                self._debug_print(
                    f"Switch-like parser aborted: recovered only {len(recovered)} case(s)"
                )
            return None
        return recovered

    def _extract_switch_blocks(self, c_text: str) -> List[Tuple[str, List[str]]]:
        """decompiler C テキストから switch ブロックを抽出する。"""
        return [
            (subject, block_lines)
            for subject, block_lines, _start_index, _end_index
            in self._extract_switch_blocks_with_spans([line.rstrip() for line in c_text.splitlines()])
        ]

    def _extract_switch_blocks_with_spans(
        self,
        lines: List[str],
    ) -> List[Tuple[str, List[str], int, int]]:
        """decompiler C テキストから switch ブロックを抽出し、行範囲も返す。"""
        blocks: List[Tuple[str, List[str], int, int]] = []
        current_subject: Optional[str] = None
        pending_subject: Optional[str] = None
        current_lines: List[str] = []
        brace_depth = 0
        start_index = -1

        for index, raw_line in enumerate(lines):
            line = raw_line.strip()
            if current_subject is None:
                match = re.search(r"\bswitch\s*\((.+)\)\s*\{", line)
                if match:
                    current_subject = match.group(1).strip()
                    brace_depth = line.count("{") - line.count("}")
                    current_lines = []
                    start_index = index
                    continue
                match = re.search(r"\bswitch\s*\((.+)\)\s*$", line)
                if match:
                    pending_subject = match.group(1).strip()
                    continue
                if pending_subject is not None and line == "{":
                    current_subject = pending_subject
                    pending_subject = None
                    brace_depth = 1
                    current_lines = []
                    start_index = index
                continue

            brace_depth += line.count("{")
            brace_depth -= line.count("}")
            current_lines.append(line)
            if brace_depth <= 0:
                blocks.append((current_subject, current_lines[:-1], start_index, index))
                current_subject = None
                current_lines = []
                start_index = -1

        return blocks

    def _parse_switch_arms(
        self,
        block_lines: List[str],
    ) -> Optional[List[Tuple[List[int], int, bool]]]:
        """switch ブロック本体から case/default -> constant return を抽出する。"""
        arms: List[Tuple[List[int], int, bool]] = []
        pending_labels: List[int] = []
        pending_default = False

        for raw_line in block_lines:
            line = raw_line.strip()
            if not line or line in {"{", "}"}:
                continue

            line = line.split("//", 1)[0].strip()
            if not line:
                continue

            while True:
                case_match = re.match(r"case\s+(-?(?:0x[0-9a-fA-F]+|\d+))\s*:\s*(.*)", line)
                if case_match:
                    pending_labels.append(int(case_match.group(1), 0))
                    line = case_match.group(2).strip()
                    if not line:
                        break
                    continue

                default_match = re.match(r"default\s*:\s*(.*)", line)
                if default_match:
                    pending_default = True
                    line = default_match.group(1).strip()
                    if not line:
                        break
                    continue
                break

            if not line:
                continue

            if line.startswith("break;"):
                pending_labels = []
                pending_default = False
                continue

            return_match = re.match(r"return\s+(-?(?:0x[0-9a-fA-F]+|\d+))\s*;", line)
            if return_match and (pending_labels or pending_default):
                arms.append(
                    (
                        list(pending_labels),
                        int(return_match.group(1), 0),
                        pending_default,
                    )
                )
                pending_labels = []
                pending_default = False
                continue

            return None

        return arms or None

    def _find_shared_return_variable(self, suffix_lines: List[str]) -> Optional[str]:
        """switch 後の `return var;` から共有 return 変数名を取得する。"""
        for raw_line in suffix_lines:
            line = raw_line.strip()
            if not line:
                continue
            line = line.split("//", 1)[0].strip()
            if not line:
                continue
            return_match = re.match(r"return\s+([A-Za-z_][A-Za-z0-9_]*)\s*;", line)
            if return_match:
                return return_match.group(1)
            if line.startswith("}"):
                break
        return None

    def _parse_switch_assignment_arms(
        self,
        block_lines: List[str],
        target_name: str,
    ) -> Optional[List[Tuple[List[int], int, bool]]]:
        """`case: tmp = CONST; break;` + `return tmp;` 形式を抽出する。"""
        arms: List[Tuple[List[int], int, bool]] = []
        pending_labels: List[int] = []
        pending_default = False
        pending_value: Optional[int] = None

        for raw_line in block_lines:
            line = raw_line.strip()
            if not line or line in {"{", "}"}:
                continue

            line = line.split("//", 1)[0].strip()
            if not line:
                continue

            while True:
                case_match = re.match(r"case\s+(-?(?:0x[0-9a-fA-F]+|\d+))\s*:\s*(.*)", line)
                if case_match:
                    if pending_value is not None and (pending_labels or pending_default):
                        return None
                    pending_labels.append(int(case_match.group(1), 0))
                    line = case_match.group(2).strip()
                    if not line:
                        break
                    continue

                default_match = re.match(r"default\s*:\s*(.*)", line)
                if default_match:
                    if pending_value is not None and (pending_labels or pending_default):
                        return None
                    pending_default = True
                    line = default_match.group(1).strip()
                    if not line:
                        break
                    continue
                break

            if not line:
                continue

            assign_match = re.match(
                rf"{re.escape(target_name)}\s*=\s*(-?(?:0x[0-9a-fA-F]+|\d+))\s*;",
                line,
            )
            if assign_match and (pending_labels or pending_default):
                pending_value = int(assign_match.group(1), 0)
                continue

            return_match = re.match(r"return\s+(-?(?:0x[0-9a-fA-F]+|\d+))\s*;", line)
            if return_match and (pending_labels or pending_default):
                pending_value = int(return_match.group(1), 0)
                arms.append((list(pending_labels), pending_value, pending_default))
                pending_labels = []
                pending_default = False
                pending_value = None
                continue

            if line.startswith("break;"):
                if pending_value is None or not (pending_labels or pending_default):
                    pending_labels = []
                    pending_default = False
                    pending_value = None
                    continue
                arms.append((list(pending_labels), pending_value, pending_default))
                pending_labels = []
                pending_default = False
                pending_value = None
                continue

            return None

        if pending_value is not None and (pending_labels or pending_default):
            arms.append((list(pending_labels), pending_value, pending_default))

        return arms or None

    def _parse_switch_subject_expr(
        self,
        subject_raw: str,
        parameters: List[Dict],
    ) -> Optional[Expression]:
        """switch 対象式を parameter/variable の範囲で復元する。"""
        subject = subject_raw.strip()
        previous = None
        while subject != previous:
            previous = subject
            subject = self._strip_outer_parentheses(subject)
            cast_match = re.match(r"^\(\s*[A-Za-z_][A-Za-z0-9_\s\*]*\s*\)\s*(.+)$", subject)
            if cast_match:
                subject = cast_match.group(1).strip()

        for index, param in enumerate(parameters):
            param_name = param.get("name")
            if param_name and subject == param_name:
                size = param.get("size", 4)
                return Expression.parameter(
                    param_name,
                    index=index,
                    data_type=param.get("data_type"),
                    size=size,
                )

        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", subject):
            return Expression.variable(subject, size=4)

        return None

    def _strip_outer_parentheses(self, text: str) -> str:
        text = text.strip()
        while text.startswith("(") and text.endswith(")"):
            depth = 0
            valid = True
            for index, char in enumerate(text):
                if char == "(":
                    depth += 1
                elif char == ")":
                    depth -= 1
                    if depth == 0 and index != len(text) - 1:
                        valid = False
                        break
            if not valid or depth != 0:
                break
            text = text[1:-1].strip()
        return text

    def _get_return_size_bytes(self, return_type: Optional[str]) -> int:
        type_lower = (return_type or "").lower().strip()
        if "undefined8" in type_lower or "long" in type_lower:
            return 8
        if "undefined2" in type_lower or "short" in type_lower:
            return 2
        if "undefined1" in type_lower or "char" in type_lower:
            return 1
        return 4

    def _clone_expression(self, expr: Expression) -> Expression:
        if expr.expr_type == ExpressionType.PARAMETER:
            return Expression.parameter(
                expr.name or "",
                index=expr.value if isinstance(expr.value, int) else -1,
                data_type=expr.data_type,
                size=expr.size or 4,
                storage_info=expr.storage_info,
            )
        if expr.expr_type == ExpressionType.VARIABLE:
            return Expression.variable(
                expr.name or "",
                data_type=expr.data_type,
                size=expr.size or 4,
                storage_info=expr.storage_info,
            )
        return Expression(
            expr.expr_type,
            value=expr.value,
            operator=expr.operator,
            operands=[self._clone_expression(op) for op in expr.operands],
            size=expr.size,
            name=expr.name,
            data_type=expr.data_type,
            storage_info=expr.storage_info,
        )

    def _build_effect_summary(
        self,
        function,
        high_function,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        parameters: List[Dict],
        active_functions: set,
    ):
        cache_key = str(function.getEntryPoint())
        self._effect_summary_parameter_cache[cache_key] = list(parameters)
        cached = self._effect_summary_cache.get(cache_key)
        if cached is not None:
            return cached

        def summarize_call(function_name: str, args):
            if function_name in active_functions:
                return None
            callee = self._find_function_by_name(function_name)
            if callee is None:
                return None
            callee_key = str(callee.getEntryPoint())
            cached_callee = self._effect_summary_cache.get(callee_key)
            if cached_callee is not None:
                return cached_callee

            decompiler = self._get_decompiler()
            results = decompiler.decompileFunction(callee, 60, None)
            if not results.decompileCompleted():
                return None
            callee_high = results.getHighFunction()
            if callee_high is None:
                return None

            callee_tracer = PcodeTracer(self.program, callee_high, debug=self.debug)
            callee_tracker = ConditionTracker(callee_tracer)
            from .phi_resolver import PhiHandler

            callee_phi_handler = PhiHandler(callee_tracer, callee_tracker)
            callee_tracer.phi_handler = callee_phi_handler
            callee_tracker.build()
            callee_parameters = self._collect_parameters(callee_high)
            self._effect_summary_parameter_cache[callee_key] = list(callee_parameters)
            image_base = None
            try:
                image_base = self.program.getImageBase().getOffset()
            except Exception:
                image_base = None
            callee_tracker.refine_branch_conditions(
                call_resolver=self._make_call_resolver(active_functions | {function_name}, callee),
                parameters=callee_parameters,
                resolve_callee_parameters=self._get_freshest_callee_parameters,
                read_memory_value=self._read_memory_value,
                image_base=image_base,
            )
            summary = self._build_effect_summary(
                callee,
                callee_high,
                callee_tracer,
                callee_tracker,
                callee_parameters,
                active_functions | {function_name},
            )
            return summary

        def resolve_callee_parameters(function_name: str):
            return self._get_freshest_callee_parameters(function_name)

        current_function_name = function.getName()
        summary = summarize_store_effects(
            condition_tracker.block_by_index.values(),
            tracer,
            condition_tracker,
            parameters,
            direct_call_summary=summarize_call,
            direct_call_expander=self._make_call_resolver(active_functions | {current_function_name}, function),
            resolve_callee_parameters=resolve_callee_parameters,
            debug=self.debug,
        )
        self._effect_summary_cache[cache_key] = summary
        return summary

    def _make_call_resolver(self, active_functions: Set[str], current_function=None):
        def resolve_call(function_name: str, args):
            return self._resolve_call_expansions(function_name, args, active_functions, current_function)

        return resolve_call

    def _resolve_call_expansions(
        self,
        function_name: str,
        args: List[Expression],
        active_functions: Set[str],
        current_function=None,
    ):
        from ..transform.expander import ExpandedValue

        local_address = self._parse_local_target_address(function_name)
        if local_address is not None:
            return self._resolve_local_code_target_expansions(local_address, active_functions, current_function)

        if function_name in active_functions:
            self._debug_print(f"Skipping recursive call expansion for '{function_name}'")
            return None

        analysis = self._get_or_analyze_call_target(function_name, active_functions)
        if analysis is None:
            expanded = self._resolve_call_expansions_from_decompiler(
                function_name,
                args,
                active_functions,
                current_function=current_function,
                analysis=None,
            )
            if expanded is not None:
                return expanded
            self._debug_print(f"Call expansion skipped for '{function_name}': analysis unavailable")
            return None
        if not self._is_call_return_summary_allowed(analysis, args):
            expanded = self._resolve_call_expansions_from_decompiler(
                function_name,
                args,
                active_functions,
                current_function=current_function,
                analysis=analysis,
            )
            if expanded is not None:
                return expanded
            self._debug_print(
                f"Call expansion skipped for '{function_name}': "
                "summary not safe enough for inlining"
            )
            return None

        param_names = [
            name
            for param in analysis.parameters
            for name in [param.get("name")]
            if isinstance(name, str) and name
        ]
        if len(args) < len(param_names):
            self._debug_print(
                f"Call expansion skipped for '{function_name}': "
                f"expected {len(param_names)} args, got {len(args)}"
            )
            return None

        replacements: Dict[str, Expression] = dict(zip(param_names, args))
        allowed_names: Set[str] = set()
        for arg in args:
            allowed_names.update(arg.get_all_variables())

        expanded = []
        for ret in analysis.returns:
            value = substitute_expression(ret.value, replacements)
            conditions = [
                substitute_condition(cond, replacements)
                for cond in ret.conditions
            ]

            if not self._call_summary_is_safe(value, conditions, allowed_names):
                self._debug_print(
                    f"Call expansion rejected for '{function_name}': "
                    "callee summary references unresolved symbols"
                )
                return None

            expanded.append(
                ExpandedValue(
                    value=value,
                    conditions=ConditionSimplifier.simplify_conditions(conditions),
                )
            )

        return expanded

    def _resolve_call_expansions_from_decompiler(
        self,
        function_name: str,
        args: List[Expression],
        active_functions: Set[str],
        current_function=None,
        analysis: Optional[FunctionReturnAnalysis] = None,
    ):
        from ..transform.expander import ExpandedValue

        callee = self._find_function_by_name(function_name)
        if callee is None:
            return None

        decompile_results = self._decompile_function(callee, timeout=60)
        if decompile_results is None:
            return None
        c_text = self._get_decompiled_c_text(decompile_results)
        if not c_text:
            return None

        callee_analysis = analysis
        if callee_analysis is None:
            callee_analysis = self._get_or_analyze_call_target(function_name, active_functions)

        parameters = self._merge_wrapper_parameters_from_c_text(
            list(getattr(callee_analysis, "parameters", None) or []),
            c_text,
        )
        initial_bindings = self._build_wrapper_initial_bindings(parameters, args)
        nested_active = set(active_functions)
        nested_active.add(function_name)
        address = (
            getattr(callee_analysis, "entry_point", None)
            or str(callee.getEntryPoint())
        )

        recovered = self._recover_structured_call_wrapper_from_c_text(
            c_text,
            parameters,
            address,
            callee,
            nested_active,
            initial_bindings=initial_bindings,
        )
        if recovered is None:
            recovered = self._recover_straightline_call_chain_from_c_text(
                c_text,
                parameters,
                address,
                callee,
                nested_active,
                initial_bindings=initial_bindings,
            )
        if recovered is None:
            return None

        return [
            ExpandedValue(
                value=self._clone_expression(ret.value),
                conditions=ConditionSimplifier.simplify_conditions(list(ret.conditions)),
            )
            for ret in recovered
        ]

    def _decompile_function(self, function, timeout: int = 60):
        try:
            decompiler = self._get_decompiler()
            results = decompiler.decompileFunction(function, timeout, None)
            if not results.decompileCompleted():
                return None
            return results
        except Exception:
            return None

    def _build_wrapper_initial_bindings(
        self,
        parameters: List[Dict],
        args: List[Expression],
    ) -> Dict[str, Expression]:
        bindings: Dict[str, Expression] = {}
        for param, arg in zip(parameters, args):
            name = param.get("name")
            if not name:
                continue
            bindings[name] = self._clone_expression(arg)
        return bindings

    def _merge_wrapper_parameters_from_c_text(
        self,
        parameters: List[Dict],
        c_text: str,
    ) -> List[Dict]:
        merged = [dict(param) for param in (parameters or [])]
        by_name = {
            param.get("name"): param
            for param in merged
            if param.get("name")
        }

        header_line = next(
            (
                line
                for line in self._normalize_wrapper_c_lines(c_text)
                if self._looks_like_wrapper_header_line(line)
            ),
            "",
        )
        header_match = re.match(
            r"^[A-Za-z_][A-Za-z0-9_\s\*]*\s+[A-Za-z_][A-Za-z0-9_]*\s*\((.*)\)\s*\{?$",
            header_line,
        )
        if not header_match:
            return merged

        param_blob = header_match.group(1).strip()
        if not param_blob or param_blob == "void":
            return merged

        param_texts = self._split_call_arguments(param_blob)
        if param_texts is None:
            return merged

        for index, raw_param in enumerate(param_texts):
            param_text = self._strip_outer_parentheses(raw_param.strip())
            if not param_text:
                continue
            name_match = re.search(r"([A-Za-z_][A-Za-z0-9_]*)$", param_text)
            if not name_match:
                continue
            name = name_match.group(1)
            data_type = param_text[:name_match.start()].strip() or None
            target = by_name.get(name)
            inferred_size = self._infer_c_text_param_size(data_type)
            if target is None:
                target = {
                    "name": name,
                    "index": index,
                    "size": inferred_size,
                }
                if data_type:
                    target["data_type"] = data_type
                merged.append(target)
                by_name[name] = target
                continue
            target.setdefault("index", index)
            if data_type and not target.get("data_type"):
                target["data_type"] = data_type
            if not target.get("size"):
                target["size"] = inferred_size

        merged.sort(key=lambda param: int(param.get("index", 1 << 20)))
        return merged

    def _infer_c_text_param_size(self, data_type: Optional[str]) -> int:
        type_lower = str(data_type or "").lower()
        if "*" in type_lower:
            return 8
        if any(token in type_lower for token in ("undefined8", "ulong", "uint64", "long long", "int64")):
            return 8
        return 4

    def _parse_local_target_address(self, function_name: str) -> Optional[int]:
        match = re.fullmatch(r"ADDR_([0-9a-fA-F]+)", function_name or "")
        if not match:
            return None
        try:
            return int(match.group(1), 16)
        except Exception:
            return None

    def _resolve_local_code_target_expansions(
        self,
        address_value: int,
        active_functions: Set[str],
        current_function=None,
    ):
        from ..transform.expander import ExpandedValue

        if address_value in self._local_target_cache:
            return self._local_target_cache[address_value]

        try:
            default_space = self.program.getAddressFactory().getDefaultAddressSpace()
            addr = default_space.getAddress(address_value)
        except Exception:
            self._debug_print(f"Local target resolution failed: invalid address 0x{address_value:x}")
            self._local_target_cache[address_value] = None
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
            self._local_target_cache[address_value] = None
            return None

        decompiler = self._get_decompiler()
        results = decompiler.decompileFunction(containing, 60, None)
        if not results.decompileCompleted():
            self._debug_print(
                f"Local target resolution failed: decompilation incomplete for 0x{address_value:x}"
            )
            self._local_target_cache[address_value] = None
            return None
        high_function = results.getHighFunction()
        if high_function is None:
            self._debug_print(f"Local target resolution failed: HighFunction unavailable for 0x{address_value:x}")
            self._local_target_cache[address_value] = None
            return None

        tracer = PcodeTracer(self.program, high_function, debug=self.debug)
        expanded = self._expand_linear_code_target(addr, tracer, containing)
        self._local_target_cache[address_value] = expanded
        return expanded

    def _expand_linear_code_target(self, addr, tracer, current_function=None):
        from ..transform.expander import ExpandedValue

        instruction = self._get_instruction_with_fallback(addr)
        if instruction is None:
            self._debug_print(f"Local target resolution failed: no instruction at {addr}")
            return None

        self._debug_print(f"Attempting linear local target expansion from {addr}")
        max_steps = 16
        visited_offsets: Set[int] = set()
        local_values: Dict[Tuple[str, int, int], Expression] = {}
        local_storages: Dict[Tuple[str, int, int], Any] = {}
        local_memory: Dict[Tuple[str, int], Expression] = {}

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
                    self._debug_print(
                        f"Resolved local target {typed_instruction.getAddress()} to return expression {value.to_string()}"
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

    def _local_varnode_key(self, varnode) -> Tuple[str, int, int]:
        try:
            addr = varnode.getAddress()
            return (addr.getAddressSpace().getName(), int(varnode.getOffset()), int(varnode.getSize()))
        except Exception:
            return ("synthetic", id(varnode), int(getattr(varnode, "getSize", lambda: 0)()))

    def _local_memory_key(self, addr_expr: Expression, size: int) -> Tuple[str, int]:
        return (addr_expr.to_string(), int(size))

    def _evaluate_local_varnode_expression(
        self,
        varnode,
        tracer,
        local_values: Dict[Tuple[str, int, int], Expression],
        local_storages: Dict[Tuple[str, int, int], Any],
        local_memory: Dict[Tuple[str, int], Expression],
        visiting: Optional[Set[int]] = None,
    ) -> Expression:
        if varnode is None:
            return Expression.unknown("local_none")

        key = self._local_varnode_key(varnode)
        cached = local_values.get(key)
        if cached is not None:
            return cached

        aliased = self._lookup_local_alias_expression(varnode, tracer, local_values, local_storages)
        if aliased is not None:
            local_values[key] = aliased
            return aliased

        is_constant = getattr(varnode, "isConstant", None)
        if callable(is_constant) and is_constant():
            return Expression.constant(varnode.getOffset(), varnode.getSize())

        if visiting is None:
            visiting = set()
        marker = id(varnode)
        if marker in visiting:
            return Expression.unknown("local_cycle")
        visiting.add(marker)
        try:
            get_def = getattr(varnode, "getDef", None)
            def_op = get_def() if callable(get_def) else None
            if def_op is not None:
                evaluated = self._evaluate_local_pcode_expression(
                    def_op,
                    tracer,
                    local_values,
                    local_storages,
                    local_memory,
                    visiting,
                )
                if evaluated is not None:
                    local_values[key] = evaluated
                    return evaluated
        finally:
            visiting.discard(marker)

        return tracer.trace_varnode(varnode, use_cache=False)

    def _evaluate_local_pcode_expression(
        self,
        pcode_op,
        tracer,
        local_values: Dict[Tuple[str, int, int], Expression],
        local_storages: Dict[Tuple[str, int, int], Any],
        local_memory: Dict[Tuple[str, int], Expression],
        visiting: Optional[Set[int]] = None,
    ) -> Optional[Expression]:
        mnemonic = pcode_op.getMnemonic()

        def _input(index: int) -> Expression:
            return self._evaluate_local_varnode_expression(
                pcode_op.getInput(index),
                tracer,
                local_values,
                local_storages,
                local_memory,
                visiting,
            )

        if mnemonic in {"COPY", "CAST"} and pcode_op.getNumInputs() >= 1:
            expr = _input(0)
            output = pcode_op.getOutput()
            if output is not None:
                expr = self._clone_expression(expr)
                expr.size = output.getSize()
            return expr

        binary_ops = {
            "INT_ADD", "INT_SUB", "INT_MULT", "INT_DIV", "INT_SDIV",
            "INT_REM", "INT_SREM", "INT_AND", "INT_OR", "INT_XOR",
            "INT_LEFT", "INT_RIGHT", "INT_SRIGHT",
            "INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", "INT_SLESS",
            "INT_LESSEQUAL", "INT_SLESSEQUAL",
            "FLOAT_ADD", "FLOAT_SUB", "FLOAT_MULT", "FLOAT_DIV",
            "FLOAT_EQUAL", "FLOAT_NOTEQUAL", "FLOAT_LESS", "FLOAT_LESSEQUAL",
            "BOOL_AND", "BOOL_OR", "BOOL_XOR", "PIECE", "SUBPIECE",
            "PTRADD", "PTRSUB",
        }
        if mnemonic in binary_ops and pcode_op.getNumInputs() >= 2:
            if mnemonic == "PTRADD" and pcode_op.getNumInputs() >= 3:
                base = _input(0)
                index = _input(1)
                element_size = _input(2)
                return Expression.binary_op(
                    "INT_ADD",
                    base,
                    Expression.binary_op("INT_MULT", index, element_size),
                )
            return Expression.binary_op(mnemonic, _input(0), _input(1))

        unary_ops = {
            "INT_NEGATE", "INT_2COMP", "BOOL_NEGATE", "INT_ZEXT", "INT_SEXT",
            "FLOAT_NEG", "FLOAT_ABS", "FLOAT_SQRT",
            "TRUNC", "FLOAT_FLOAT2FLOAT", "FLOAT_INT2FLOAT", "FLOAT_CEIL", "FLOAT_FLOOR",
            "POPCOUNT", "LZCOUNT",
        }
        if mnemonic in unary_ops and pcode_op.getNumInputs() >= 1:
            expr = Expression.unary_op(mnemonic, _input(0))
            output = pcode_op.getOutput()
            if output is not None:
                expr.size = output.getSize()
            return expr

        if mnemonic == "LOAD" and pcode_op.getNumInputs() >= 2:
            output = pcode_op.getOutput()
            size = output.getSize() if output is not None else 4
            addr_expr = _input(1)
            cached = local_memory.get(self._local_memory_key(addr_expr, size))
            if cached is not None:
                return cached
            return Expression.memory(addr_expr, size)

        return None

    def _apply_local_store_effect(
        self,
        pcode_op,
        tracer,
        local_values: Dict[Tuple[str, int, int], Expression],
        local_storages: Dict[Tuple[str, int, int], Any],
        local_memory: Dict[Tuple[str, int], Expression],
    ) -> None:
        if pcode_op.getNumInputs() < 3:
            return
        addr_expr = self._evaluate_local_varnode_expression(
            pcode_op.getInput(1),
            tracer,
            local_values,
            local_storages,
            local_memory,
        )
        value_expr = self._evaluate_local_varnode_expression(
            pcode_op.getInput(2),
            tracer,
            local_values,
            local_storages,
            local_memory,
        )
        size = pcode_op.getInput(2).getSize()
        local_memory[self._local_memory_key(addr_expr, size)] = value_expr

    def _resolve_local_return_expression(
        self,
        pcode_op,
        tracer,
        local_values: Dict[Tuple[str, int, int], Expression],
        local_storages: Dict[Tuple[str, int, int], Any],
        local_memory: Dict[Tuple[str, int], Expression],
        current_function=None,
    ) -> Expression:
        if pcode_op.getNumInputs() >= 2:
            return self._evaluate_local_varnode_expression(
                pcode_op.getInput(1),
                tracer,
                local_values,
                local_storages,
                local_memory,
            )

        for return_varnode in self._get_function_return_varnodes(current_function):
            expr = self._evaluate_local_varnode_expression(
                return_varnode,
                tracer,
                local_values,
                local_storages,
                local_memory,
            )
            if expr is not None and expr.expr_type != ExpressionType.UNKNOWN:
                self._debug_print(
                    f"Local target RETURN without explicit value; using return storage {return_varnode}"
                )
                return expr

        self._debug_print("Local target RETURN without explicit value; defaulting to 0")
        return Expression.constant(0, 1)

    def _lookup_local_alias_expression(
        self,
        varnode,
        tracer,
        local_values: Dict[Tuple[str, int, int], Expression],
        local_storages: Dict[Tuple[str, int, int], Any],
    ) -> Optional[Expression]:
        try:
            target_storage = tracer._get_storage_info_from_varnode(varnode)
        except Exception:
            return None
        if target_storage is None or not getattr(target_storage, "is_register", False):
            return None

        for key, candidate_storage in local_storages.items():
            if candidate_storage is None:
                continue
            try:
                same_base = candidate_storage.shares_base_register_with(target_storage)
                overlaps = candidate_storage.bit_range_overlaps_with(target_storage)
            except Exception:
                continue
            if not same_base or not overlaps:
                continue
            candidate_expr = local_values.get(key)
            if candidate_expr is None:
                continue
            aliased = self._clone_expression(candidate_expr)
            aliased.size = target_storage.size
            self._debug_print(
                "Local alias resolution: "
                f"{getattr(candidate_storage, 'register_name', None)} -> "
                f"{getattr(target_storage, 'register_name', None)} as {aliased.to_string()}"
            )
            return aliased
        return None

    def _get_function_return_varnodes(self, function) -> List[Any]:
        if function is None:
            return []
        try:
            return_var = function.getReturn()
            if return_var is None:
                return []
            storage = return_var.getVariableStorage()
            if storage is None:
                return []
            get_varnodes = getattr(storage, "getVarnodes", None)
            if callable(get_varnodes):
                raw_varnodes = cast(Iterable[Any], get_varnodes())
                return [vn for vn in raw_varnodes if vn is not None]
        except Exception:
            return []
        return []

    def _infer_abi_return_storages(self) -> List[StorageInfo]:
        """関数シグネチャが void に潰れていても使える保守的な返り値レジスタ候補。"""
        try:
            lang = self.program.getLanguage() if self.program is not None else None
            lang_id = str(lang.getLanguageID()) if lang is not None else ""
            processor = str(lang.getProcessor()) if lang is not None else ""
            pointer_size = int(self.program.getDefaultPointerSize()) if self.program is not None else 8
        except Exception:
            lang_id = ""
            processor = ""
            pointer_size = 8

        arch_tag = f"{lang_id} {processor}".upper()
        base_bits = max(pointer_size * 8, 32)

        def _reg(base_name: str) -> StorageInfo:
            return StorageInfo(
                is_register=True,
                space_name="register",
                size=max(base_bits // 8, 4),
                size_bits=base_bits,
                register_name=base_name,
                base_register_name=base_name,
                base_register_size=max(base_bits // 8, 4),
                base_register_size_bits=base_bits,
                bit_offset_in_base=0,
            )

        if "MIPS" in arch_tag:
            return [_reg("v0")]
        if "AARCH64" in arch_tag or "ARM:LE:64" in arch_tag or "ARM:BE:64" in arch_tag:
            return [_reg("x0")]
        if "ARM" in arch_tag:
            return [_reg("r0")]
        if "X86" in arch_tag and "64" in arch_tag:
            return [_reg("rax")]
        if "X86" in arch_tag or "IA-32" in arch_tag:
            return [_reg("eax")]
        return []

    def _get_implicit_return_target_storages(
        self,
        function,
        tracer: PcodeTracer,
    ) -> List[StorageInfo]:
        target_storages: List[StorageInfo] = []
        for return_varnode in self._get_function_return_varnodes(function):
            storage = tracer._get_storage_info_from_varnode(return_varnode)
            if storage is not None:
                target_storages.append(storage)

        if target_storages:
            return target_storages

        fallback = self._infer_abi_return_storages()
        if self.debug and fallback:
            names = [storage.base_register_name or storage.register_name or "?" for storage in fallback]
            self._debug_print(
                f"Using ABI fallback return storages: {names}"
            )
        return fallback

    def _get_instruction_with_fallback(self, addr):
        listing = self.program.getListing()
        instruction = listing.getInstructionAt(addr)
        if instruction is not None:
            return instruction

        containing_instruction = getattr(listing, "getInstructionContaining", None)
        if callable(containing_instruction):
            instruction = containing_instruction(addr)
            if instruction is not None:
                return instruction

        if self._attempt_disassemble_at(addr):
            instruction = listing.getInstructionAt(addr)
            if instruction is not None:
                return instruction
            if callable(containing_instruction):
                instruction = containing_instruction(addr)
                if instruction is not None:
                    return instruction

        return None

    def _attempt_disassemble_at(self, addr) -> bool:
        try:
            from ghidra.app.cmd.disassemble import DisassembleCommand  # type: ignore[import]
        except Exception:
            self._debug_print(f"Local target disassembly unavailable at {addr}: import failed")
            return False

        try:
            command = DisassembleCommand(addr, None, True)
        except TypeError:
            try:
                command = DisassembleCommand(addr, None)
            except Exception as exc:
                self._debug_print(f"Local target disassembly setup failed at {addr}: {exc}")
                return False
        except Exception as exc:
            self._debug_print(f"Local target disassembly setup failed at {addr}: {exc}")
            return False

        try:
            with self._program_transaction(f"Disassemble local target {addr}"):
                applied = command.applyTo(self.program)
        except Exception as exc:
            self._debug_print(f"Local target disassembly failed at {addr}: {exc}")
            return False

        if applied:
            self._debug_print(f"Local target disassembly materialized instructions at {addr}")
        else:
            self._debug_print(f"Local target disassembly produced no instructions at {addr}")
        return bool(applied)

    def _resolve_local_branch_target(self, instruction):
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

    def _get_or_analyze_call_target(
        self,
        function_name: str,
        active_functions: Set[str],
        minimum_param_count: int = 0,
    ) -> Optional[FunctionReturnAnalysis]:
        callee = self._find_function_by_name(function_name)
        if callee is None:
            return None

        cache_key = str(callee.getEntryPoint())
        cached = self._call_analysis_cache.get(cache_key)
        if cached is not None and len(getattr(cached, "parameters", []) or []) >= minimum_param_count:
            return cached

        analysis = self.analyze_function(
            callee,
            timeout=60,
            active_functions=active_functions | {function_name},
        )
        if cached is None:
            self._call_analysis_cache[cache_key] = analysis
            return analysis
        if analysis is None:
            return cached
        if len(getattr(analysis, "parameters", []) or []) >= len(getattr(cached, "parameters", []) or []):
            self._call_analysis_cache[cache_key] = analysis
            return analysis
        return cached

    def _is_call_return_summary_allowed(
        self,
        analysis: FunctionReturnAnalysis,
        args: List[Expression],
    ) -> bool:
        if analysis is None or not analysis.returns:
            return False
        # 一時的な unknown event が残っていても、最終的な return summary が
        # 完全に解決済みなら call 展開には利用できる。ここでは最終 summary の
        # 安全性に直接効くシグナルだけを除外条件に使う。
        if analysis.has_unknown_return() or analysis.has_overlapping_unconditional_returns():
            return False

        param_names = {
            name
            for param in analysis.parameters
            for name in [param.get("name")]
            if isinstance(name, str) and name
        }
        allowed_names: Set[str] = set()
        for arg in args:
            allowed_names.update(arg.get_all_variables())

        for ret in analysis.returns:
            if self._expression_contains_unknown_or_call(ret.value):
                return False
            if not self._expression_uses_only_allowed_names(ret.value, param_names, allowed_names):
                return False
            for cond in ret.conditions:
                if self._expression_contains_unknown_or_call(cond.expression):
                    return False
                if not self._expression_uses_only_allowed_names(cond.expression, param_names, allowed_names):
                    return False

        return True

    def _call_summary_is_safe(
        self,
        value: Expression,
        conditions: List[Condition],
        allowed_names: Set[str],
    ) -> bool:
        if self._expression_contains_unknown_or_call(value):
            return False
        if not self._expression_uses_only_allowed_names(value, set(), allowed_names):
            return False

        for cond in conditions:
            if self._expression_contains_unknown_or_call(cond.expression):
                return False
            if not self._expression_uses_only_allowed_names(cond.expression, set(), allowed_names):
                return False

        return True

    def _expression_contains_unknown_or_call(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False

        if expr.expr_type in (ExpressionType.UNKNOWN, ExpressionType.CALL):
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

    def _expression_contains_phi(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        if expr.expr_type == ExpressionType.PHI:
            return True
        for operand in getattr(expr, "operands", []) or []:
            if self._expression_contains_phi(operand):
                return True
        return False

    def _expression_uses_only_allowed_names(
        self,
        expr: Optional[Expression],
        local_param_names: Set[str],
        allowed_names: Set[str],
    ) -> bool:
        if expr is None:
            return True
        referenced = expr.get_all_variables()
        return referenced.issubset(local_param_names | allowed_names)
    
    def _detect_signedness(self, high_function) -> Optional[SignednessResult]:
        """
        Phase 1: P-code証拠から符号性を推定
        
        Args:
            high_function: GhidraのHighFunctionオブジェクト
        
        Returns:
            SignednessResult: 推定結果（エラー時はNone）
        """
        try:
            detector = SignednessDetector(high_function, debug=self.debug)
            evidence = detector.detect()
            return SignednessResult.from_evidence(evidence)
        except Exception as e:
            self._debug_print(f"Signedness detection failed: {e}")
            return None
    
    def _get_return_type(self, high_function) -> Optional[str]:
        """戻り値の型を取得"""
        try:
            func_proto = high_function.getFunctionPrototype()
            if func_proto:
                ret_type = func_proto.getReturnType()
                if ret_type:
                    return str(ret_type)
        except Exception as e:
            self._debug_print(f"Failed to get return type: {e}")
        return None
    
    def _collect_parameters(self, high_function) -> List[Dict]:
        """パラメータ情報を収集（ストレージ情報付き）"""
        params = []
        local_map = high_function.getLocalSymbolMap()
        
        if local_map:
            for sym in local_map.getSymbols():
                if sym.isParameter():
                    data_type = sym.getDataType()
                    param_info = {
                        "name": sym.getName(),
                        "data_type": str(data_type) if data_type else None,
                        "data_type_obj": data_type,
                        "size": sym.getSize(),
                        "is_signed": self._is_signed_type(data_type),
                        "storage": self._get_storage_info(sym),
                    }
                    try:
                        param_info["index"] = sym.getCategoryIndex()
                    except:
                        param_info["index"] = -1
                    
                    if self.debug:
                        self._debug_print(f"Parameter '{sym.getName()}': "
                                         f"type={param_info['data_type']}, "
                                         f"signed={param_info['is_signed']}, "
                                         f"storage={param_info['storage']}")
                    
                    params.append(param_info)
        
        params.sort(key=lambda x: x.get("index", -1))
        return params
    
    def _is_signed_type(self, data_type) -> bool:
        """データ型が符号付きかどうかを判定"""
        if data_type is None:
            return True
        
        type_name = str(data_type).lower()
        
        # 明示的に unsigned の場合
        if "unsigned" in type_name or type_name.startswith("u"):
            return False
        
        # uint, ulong, uchar 等
        unsigned_patterns = ["uint", "ulong", "uchar", "ushort", "ubyte", 
                             "size_t", "uintptr"]
        for pattern in unsigned_patterns:
            if pattern in type_name:
                return False
        
        # pointer型は符号なし
        if "*" in type_name or "ptr" in type_name:
            return False
        
        return True
    
    def _get_storage_info(self, sym) -> Optional[Dict]:
        """シンボルのストレージ情報を取得"""
        try:
            storage = sym.getStorage()
            if storage is None:
                return None
            
            # Varnodeリストを取得
            raw_varnodes = getattr(storage, "getVarnodes", lambda: [])()
            varnodes = [vn for vn in cast(Iterable[Any], raw_varnodes) if vn is not None]
            if not varnodes:
                return None
            
            first_vn = varnodes[0]
            addr = first_vn.getAddress()
            space = addr.getAddressSpace()
            
            storage_info = {
                "is_register": space.isRegisterSpace(),
                "offset": first_vn.getOffset(),
                "size": first_vn.getSize(),
                "size_bits": first_vn.getSize() * 8,
                "space_name": space.getName(),
            }
            
            if space.isRegisterSpace():
                # レジスタ情報を取得
                reg = self.program.getRegister(addr, first_vn.getSize())
                if reg:
                    storage_info["register_name"] = reg.getName()
                    
                    # 親レジスタ情報
                    base_reg = reg.getBaseRegister()
                    if base_reg and base_reg != reg:
                        storage_info["base_register_name"] = base_reg.getName()
                        storage_info["base_register_size"] = base_reg.getBitLength() // 8
                        storage_info["base_register_size_bits"] = base_reg.getBitLength()
                        # パラメータのビットオフセット（親レジスタ内での位置）
                        byte_offset_in_base = reg.getOffset() - base_reg.getOffset()
                        storage_info["bit_offset_in_base"] = byte_offset_in_base * 8
                    else:
                        # 親レジスタと同じ場合
                        storage_info["base_register_name"] = reg.getName()
                        storage_info["base_register_size"] = reg.getBitLength() // 8
                        storage_info["base_register_size_bits"] = reg.getBitLength()
                        storage_info["bit_offset_in_base"] = 0
            
            return storage_info
        except Exception as e:
            if self.debug:
                self._debug_print(f"Failed to get storage info: {e}")
            return None
    
    def _analyze_return_op(
        self,
        return_op,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        return_index: int,
        current_function,
        active_functions: Set[str],
    ) -> List[ReturnInfo]:
        """単一のRETURNを解析"""
        seq = return_op.getSeqnum()
        address = str(seq.getTarget()) if seq else "unknown"
        
        num_inputs = return_op.getNumInputs()
        self._debug_print(f"RETURN at {address}, inputs: {num_inputs}")

        raw_path_entries = None
        get_block_paths = getattr(condition_tracker, "get_all_valid_block_paths_to_return", None)
        if callable(get_block_paths):
            raw_path_entries = get_block_paths(return_op)

        path_entries = self._coerce_block_path_entries(raw_path_entries)
        if path_entries:
            path_entries = self._filter_noreturn_return_path_entries(
                path_entries,
                tracer,
                return_op,
            )
            if not path_entries:
                if self.debug:
                    self._debug_print(
                        "All RETURN path variants were pruned as noreturn/unreachable; skipping RETURN"
                    )
                return []
            all_valid_path_conditions = [list(conditions) for _blocks, conditions in path_entries]
            path_conditions = list(all_valid_path_conditions[0]) if all_valid_path_conditions else []
        else:
            # Fall back to the pre-existing condition-only API if block paths are unavailable.
            path_conditions = condition_tracker.get_path_conditions_to_return(return_op)
            all_valid_path_conditions = condition_tracker.get_all_valid_paths_to_return(return_op)

        if self.debug and path_conditions:
            cond_strs = [ConditionSimplifier.get_simplified_condition_string(c) for c in path_conditions]
            self._debug_print(f"Path conditions to RETURN: {cond_strs}")
        if self.debug and len(all_valid_path_conditions) > 1:
            self._debug_print(
                f"RETURN has {len(all_valid_path_conditions)} valid path variants",
            )
        
        if num_inputs >= 2:
            return_varnode = return_op.getInput(1)
            return self._analyze_return_value(
                return_varnode,
                address,
                tracer,
                condition_tracker,
                path_conditions,
                return_index,
                all_path_conditions=all_valid_path_conditions,
                active_functions=active_functions,
                current_function=current_function,
            )
        else:
            implicit_results = self._analyze_implicit_return_value(
                return_op,
                address,
                tracer,
                condition_tracker,
                path_conditions,
                return_index,
                all_path_conditions=all_valid_path_conditions,
                path_entries=path_entries,
                active_functions=active_functions,
                current_function=current_function,
            )
            if implicit_results is not None:
                return implicit_results
            # void return
            simplified_conds = ConditionSimplifier.simplify_conditions(path_conditions)
            return [ReturnInfo(
                address=address,
                value=Expression.unknown("void"),
                conditions=simplified_conds,
                branch_index=return_index
            )]

    def _coerce_block_path_entries(self, path_entries) -> Optional[List[Tuple[List[Any], List[Condition]]]]:
        if not isinstance(path_entries, (list, tuple)):
            return None

        normalized: List[Tuple[List[Any], List[Condition]]] = []
        for entry in path_entries:
            if not isinstance(entry, (list, tuple)) or len(entry) != 2:
                return None
            block_path, conditions = entry
            if not isinstance(block_path, (list, tuple)):
                return None
            if not isinstance(conditions, (list, tuple)):
                return None
            normalized.append((list(block_path), list(conditions)))
        return normalized

    def _filter_noreturn_return_path_entries(
        self,
        path_entries,
        tracer: PcodeTracer,
        return_op,
    ):
        if not path_entries:
            return path_entries

        filtered = []
        for block_path, conditions in path_entries:
            if self._block_path_contains_noreturn_call(block_path, tracer, return_op):
                if self.debug:
                    cond_strs = [
                        ConditionSimplifier.get_simplified_condition_string(c)
                        for c in conditions
                    ]
                    block_indexes = [getattr(block, "index", "?") for block in block_path]
                    self._debug_print(
                        "Pruned RETURN path that contains a noreturn call: "
                        f"blocks={block_indexes}, conditions={cond_strs}"
                    )
                continue
            filtered.append((block_path, conditions))

        return filtered

    def _block_path_contains_noreturn_call(
        self,
        block_path,
        tracer: PcodeTracer,
        return_op,
    ) -> bool:
        for block_info in block_path:
            for pcode_op in getattr(block_info, "pcode_ops", []) or []:
                if pcode_op is return_op:
                    return False
                if self._is_noreturn_call_op(pcode_op, tracer):
                    return True
        return False

    def _is_noreturn_call_op(self, pcode_op, tracer: PcodeTracer) -> bool:
        if pcode_op is None or pcode_op.getMnemonic() not in {"CALL", "CALLIND"}:
            return False

        for candidate_name in self._collect_call_target_candidate_names(pcode_op, tracer):
            if self._name_looks_noreturn(candidate_name):
                return True

        resolved_name = _resolve_call_target_name(tracer, pcode_op)
        if not resolved_name:
            return False

        try:
            function_manager = self.program.getFunctionManager() if self.program is not None else None
            if function_manager is not None:
                for func in function_manager.getFunctions(True):
                    if func.getName() != resolved_name:
                        continue
                    for attr_name in ("hasNoReturn", "isNoReturn", "getNoReturn"):
                        attr = getattr(func, attr_name, None)
                        if callable(attr):
                            try:
                                if bool(attr()):
                                    return True
                            except Exception:
                                continue
        except Exception:
            pass

        return self._name_looks_noreturn(resolved_name)

    def _collect_call_target_candidate_names(
        self,
        pcode_op,
        tracer: PcodeTracer,
    ) -> List[str]:
        names: List[str] = []
        if pcode_op is None or pcode_op.getNumInputs() < 1:
            return names

        def _append_name(candidate) -> None:
            if not candidate:
                return
            candidate_str = str(candidate)
            if candidate_str and candidate_str not in names:
                names.append(candidate_str)

        try:
            target_varnode = pcode_op.getInput(0)
        except Exception:
            return names

        _append_name(tracer._get_function_name(target_varnode))

        try:
            high_var = target_varnode.getHigh()
            if high_var is not None:
                _append_name(high_var.getName())
                symbol = high_var.getSymbol()
                if symbol is not None:
                    _append_name(symbol.getName())
        except Exception:
            pass

        try:
            traced_target = tracer.trace_varnode(target_varnode, use_cache=False)
            _append_name(getattr(traced_target, "name", None))
        except Exception:
            pass

        return names

    def _name_looks_noreturn(self, name: Optional[str]) -> bool:
        if not name:
            return False
        normalized = str(name).lower()
        for prefix in ("ptr_", "thunk_", "__imp_"):
            if normalized.startswith(prefix):
                normalized = normalized[len(prefix):]
        normalized = re.sub(r"_[0-9a-f]+$", "", normalized)
        normalized = normalized.lstrip("_")
        return any(fragment in normalized for fragment in self._KNOWN_NORETURN_NAME_FRAGMENTS)

    def _analyze_implicit_return_value(
        self,
        return_op,
        address: str,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        path_conditions: List[Condition],
        return_index: int,
        all_path_conditions: Optional[List[List[Condition]]] = None,
        path_entries=None,
        active_functions: Optional[Set[str]] = None,
        current_function=None,
    ) -> Optional[List[ReturnInfo]]:
        """RETURN オペランドが欠落している場合に、返り値レジスタ由来の値を復元する。"""
        path_recovered = self._recover_implicit_return_from_block_paths(
            return_op,
            address,
            tracer,
            condition_tracker,
            return_index,
            path_entries,
            active_functions=active_functions,
            current_function=current_function,
        )
        if path_recovered is not None:
            return path_recovered

        source_varnode = self._find_implicit_return_source_varnode(
            return_op,
            tracer,
            condition_tracker,
            current_function,
        )
        if source_varnode is None:
            if self.debug:
                self._debug_print(
                    "Implicit return storage recovery did not find a matching source varnode"
                )
        else:
            self._debug_print(
                "RETURN has no explicit value; retrying via implicit return storage source"
            )
            return self._analyze_return_value(
                source_varnode,
                address,
                tracer,
                condition_tracker,
                path_conditions,
                return_index,
                all_path_conditions=all_path_conditions,
                active_functions=active_functions,
                current_function=current_function,
            )

        terminal_call = self._find_terminal_call_before_return(
            return_op,
            condition_tracker,
        )
        if terminal_call is None:
            if self.debug:
                self._debug_print(
                    "Implicit return call-wrapper recovery did not find a safe terminal CALL/CALLIND"
                )
            return None

        return self._recover_implicit_return_from_terminal_call(
            terminal_call,
            address,
            tracer,
            condition_tracker,
            path_conditions,
            return_index,
            all_path_conditions=all_path_conditions,
            active_functions=active_functions,
            current_function=current_function,
        )

    def _recover_implicit_return_from_block_paths(
        self,
        return_op,
        address: str,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        return_index: int,
        path_entries,
        active_functions: Optional[Set[str]] = None,
        current_function=None,
    ) -> Optional[List[ReturnInfo]]:
        """RETURN block 以前の path 上にある返り値レジスタ更新から暗黙 return を復元する。"""
        normalized_entries = self._coerce_block_path_entries(path_entries)
        if not normalized_entries:
            return None

        recovered_results: List[ReturnInfo] = []
        unresolved_paths: List[int] = []

        for path_idx, (block_path, conditions) in enumerate(normalized_entries):
            source_varnode = self._find_implicit_return_source_varnode(
                return_op,
                tracer,
                condition_tracker,
                current_function,
                block_path=block_path,
                path_conditions=conditions,
            )
            if source_varnode is None:
                unresolved_paths.append(path_idx)
                continue

            recovered_results.extend(
                self._analyze_return_value(
                    source_varnode,
                    address,
                    tracer,
                    condition_tracker,
                    list(conditions),
                    return_index * 1000 + path_idx,
                    all_path_conditions=[list(conditions)],
                    active_functions=active_functions,
                    current_function=current_function,
                )
            )

        if recovered_results and not unresolved_paths:
            if self.debug:
                self._debug_print(
                    "Implicit return path recovery succeeded for all RETURN path variants"
                )
            return self._merge_equivalent_return_infos(recovered_results)

        if self.debug and unresolved_paths:
            self._debug_print(
                "Implicit return path recovery could not resolve source varnode on "
                f"path(s) {unresolved_paths}"
            )
        return None

    def _find_implicit_return_source_varnode(
        self,
        return_op,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        current_function=None,
        block_path=None,
        path_conditions: Optional[List[Condition]] = None,
    ):
        """同一 basic block 内で返り値レジスタへ最後に書いた varnode を探す。"""
        search_blocks = None
        if block_path:
            search_blocks = list(block_path)
        else:
            return_parent = getattr(return_op, "getParent", lambda: None)()
            return_block = condition_tracker.get_block_by_hash(return_parent)
            if return_block is None:
                return None
            search_blocks = [return_block]

        target_storages = self._get_implicit_return_target_storages(current_function, tracer)
        if not target_storages:
            return None

        candidate = None
        for block_info in search_blocks:
            for pcode_op in getattr(block_info, "pcode_ops", []) or []:
                if pcode_op is return_op:
                    break
                output = getattr(pcode_op, "getOutput", lambda: None)()
                if output is None:
                    continue
                output_storage = tracer._get_storage_info_from_varnode(output)
                if output_storage is None:
                    continue
                if not any(
                    self._storages_overlap_for_return_recovery(output_storage, target_storage)
                    for target_storage in target_storages
                ):
                    continue
                candidate = output

        candidate = self._select_path_specific_return_source(
            candidate,
            block_path,
            condition_tracker=condition_tracker,
            path_conditions=path_conditions,
        )

        if candidate is not None and self.debug:
            self._debug_print(
                f"Implicit return source matched to block-local output {candidate}"
            )
        return candidate

    def _select_path_specific_return_source(
        self,
        candidate,
        block_path,
        condition_tracker: Optional[ConditionTracker] = None,
        path_conditions: Optional[List[Condition]] = None,
    ):
        """PHI 出力をそのまま返す代わりに、実際の predecessor に対応する入力へ絞る。"""
        if candidate is None or not block_path or len(block_path) < 2:
            return candidate

        normalized_path = [getattr(entry, "block", entry) for entry in block_path]
        selected = candidate
        max_refinements = max(1, len(normalized_path))

        for _ in range(max_refinements):
            def_op = getattr(selected, "getDef", lambda: None)()
            if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                break

            phi_parent = getattr(def_op, "getParent", lambda: None)()
            phi_index = self._find_block_index_on_path(normalized_path, phi_parent)
            if phi_index is None or phi_index <= 0:
                break

            predecessor = normalized_path[phi_index - 1]
            refined = self._select_multiequal_input_for_return_path(
                multiequal_op=def_op,
                predecessor=predecessor,
                condition_tracker=condition_tracker,
                path_conditions=path_conditions,
            )
            if refined is None or refined is selected:
                break

            if self.debug:
                self._debug_print(
                    "Refined implicit return PHI source to predecessor-specific input "
                    f"{refined}"
                )
            selected = refined

        return selected

    def _find_block_index_on_path(self, block_path, target_block) -> Optional[int]:
        if target_block is None:
            return None

        for index in range(len(block_path) - 1, -1, -1):
            if self._blocks_match(block_path[index], target_block):
                return index
        return None

    def _select_multiequal_input_for_return_path(
        self,
        multiequal_op,
        predecessor,
        condition_tracker: Optional[ConditionTracker] = None,
        path_conditions: Optional[List[Condition]] = None,
    ):
        phi_parent = getattr(multiequal_op, "getParent", lambda: None)()
        get_in_size = getattr(phi_parent, "getInSize", None)
        get_in = getattr(phi_parent, "getIn", None)
        if not callable(get_in_size) or not callable(get_in):
            return None

        current_condition_keys = self._build_condition_signature_set(path_conditions or [])
        best_input = None
        best_score: Optional[Tuple[int, int, int]] = None

        try:
            for index in range(int(get_in_size())):
                incoming = get_in(index)
                score = self._score_multiequal_incoming_for_return_path(
                    incoming,
                    predecessor,
                    condition_tracker,
                    current_condition_keys,
                )
                candidate_input = multiequal_op.getInput(index)
                if candidate_input is None:
                    continue
                if best_score is None or score > best_score:
                    best_score = score
                    best_input = candidate_input
        except Exception:
            return None

        return best_input

    def _score_multiequal_incoming_for_return_path(
        self,
        incoming_block,
        predecessor,
        condition_tracker: Optional[ConditionTracker],
        current_condition_keys: Set[str],
    ) -> Tuple[int, int, int]:
        predecessor_match = 1 if self._blocks_match(incoming_block, predecessor) else 0
        if condition_tracker is None or not current_condition_keys:
            return (predecessor_match, 0, 0)

        block_info = condition_tracker.get_block_by_hash(incoming_block)
        if block_info is None:
            return (predecessor_match, 0, 0)

        incoming_conditions = condition_tracker.get_path_conditions_to_block(block_info)
        incoming_keys = self._build_condition_signature_set(incoming_conditions)
        if not incoming_keys:
            return (predecessor_match, 0, 0)

        matched = len(incoming_keys & current_condition_keys)
        specificity = len(incoming_keys)
        return (matched, predecessor_match, specificity)

    def _build_condition_signature_set(self, conditions: List[Condition]) -> Set[str]:
        from .condition.simplifier import ConditionSimplifier

        signatures: Set[str] = set()
        for condition in conditions:
            try:
                signatures.add(ConditionSimplifier.get_simplified_condition_string(condition))
            except Exception:
                try:
                    signatures.add(condition.to_string())
                except Exception:
                    continue
        return signatures

    def _blocks_match(self, lhs, rhs) -> bool:
        if lhs is rhs:
            return True
        try:
            if lhs == rhs:
                return True
        except Exception:
            pass

        lhs_start = self._get_block_start_address(lhs)
        rhs_start = self._get_block_start_address(rhs)
        if lhs_start is not None and rhs_start is not None:
            return lhs_start == rhs_start

        return False

    def _get_block_start_address(self, block) -> Optional[str]:
        get_start = getattr(block, "getStart", None)
        if not callable(get_start):
            return None
        try:
            start = get_start()
        except Exception:
            return None
        if start is None:
            return None
        return str(start)

    def _find_terminal_call_before_return(
        self,
        return_op,
        condition_tracker: ConditionTracker,
    ):
        """同一 basic block 内で wrapper return とみなせる末尾 CALL/CALLIND を探す。"""
        return_parent = getattr(return_op, "getParent", lambda: None)()
        return_block = condition_tracker.get_block_by_hash(return_parent)
        if return_block is None:
            return None

        ops_before_return = []
        for pcode_op in return_block.pcode_ops:
            if pcode_op is return_op:
                break
            ops_before_return.append(pcode_op)

        candidate = None
        candidate_index = -1
        for index in range(len(ops_before_return) - 1, -1, -1):
            pcode_op = ops_before_return[index]
            if pcode_op.getMnemonic() in {"CALL", "CALLIND"}:
                candidate = pcode_op
                candidate_index = index
                break

        if candidate is None:
            return None

        for later_op in ops_before_return[candidate_index + 1:]:
            mnemonic = later_op.getMnemonic()
            output = getattr(later_op, "getOutput", lambda: None)()
            if mnemonic in {"CALL", "CALLIND", "STORE", "BRANCH", "CBRANCH", "BRANCHIND"}:
                return None
            if output is not None:
                return None

        if self.debug:
            self._debug_print(
                f"Implicit return wrapper recovery selected terminal {candidate.getMnemonic()} before RETURN"
            )
        return candidate

    def _recover_implicit_return_from_terminal_call(
        self,
        call_op,
        address: str,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        path_conditions: List[Condition],
        return_index: int,
        all_path_conditions: Optional[List[List[Condition]]] = None,
        active_functions: Optional[Set[str]] = None,
        current_function=None,
    ) -> Optional[List[ReturnInfo]]:
        """`call foo(...); return;` 形式の wrapper を callee summary から復元する。"""
        from ..transform import ExpressionExpander

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
            record_deferred_call=self._make_deferred_call_recorder(
                current_function.getName() if current_function is not None else "<unknown>"
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
        )
        return results or None

    def _storages_overlap_for_return_recovery(self, left, right) -> bool:
        if left is None or right is None:
            return False
        try:
            if getattr(left, "is_register", False) and getattr(right, "is_register", False):
                return (
                    left.shares_base_register_with(right)
                    and left.bit_range_overlaps_with(right)
                )
        except Exception:
            return False

        return (
            getattr(left, "space_name", None) == getattr(right, "space_name", None)
            and getattr(left, "offset", None) == getattr(right, "offset", None)
            and getattr(left, "size", None) == getattr(right, "size", None)
        )
    
    def _analyze_return_value(
        self,
        return_varnode,
        address: str,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        path_conditions: List[Condition],
        return_index: int,
        all_path_conditions: Optional[List[List[Condition]]] = None,
        active_functions: Optional[Set[str]] = None,
        current_function=None,
    ) -> List[ReturnInfo]:
        """Return値を解析"""
        from ..transform import ExpressionExpander
        
        tracer.clear_cache()
        
        # MULTIEQUALが含まれるかチェック
        has_multiequal = self._contains_multiequal(return_varnode)
        
        if has_multiequal:
            self._debug_print("Return value contains MULTIEQUAL - using PHI-based expansion")
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
                record_deferred_call=self._make_deferred_call_recorder(
                    current_function.getName() if current_function is not None else "<unknown>"
                ),
            )
            path_condition_sets = all_path_conditions or []
            if not path_condition_sets:
                path_condition_sets = [path_conditions] if path_conditions else [[]]

            expanded_values = []
            for path_idx, conds in enumerate(path_condition_sets):
                if self.debug and len(path_condition_sets) > 1:
                    cond_strs = [
                        ConditionSimplifier.get_simplified_condition_string(c)
                        for c in conds
                    ]
                    self._debug_print(
                        f"Expanding PHI return with path[{path_idx}]: {cond_strs}"
                    )
                expanded_values.extend(
                    expander.expand_from_varnode(return_varnode, conds)
                )
        else:
            self._debug_print("Return value has no MULTIEQUAL - using path conditions")
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
                record_deferred_call=self._make_deferred_call_recorder(
                    current_function.getName() if current_function is not None else "<unknown>"
                ),
            )
            path_condition_sets = all_path_conditions or []
            if not path_condition_sets:
                path_condition_sets = [path_conditions] if path_conditions else [[]]

            expanded_values = []
            for path_idx, conds in enumerate(path_condition_sets):
                if self.debug and len(path_condition_sets) > 1:
                    cond_strs = [
                        ConditionSimplifier.get_simplified_condition_string(c)
                        for c in conds
                    ]
                    self._debug_print(
                        f"Expanding non-PHI return with path[{path_idx}]: {cond_strs}"
                    )
                expanded_values.extend(
                    expander.expand_from_varnode(return_varnode, conds)
                )
        
        self._debug_print(f"Expanded to {len(expanded_values)} candidate(s)")

        results = self._build_return_infos_from_expansions(
            address,
            expanded_values,
            return_index,
        )
        
        if not results:
            self._debug_print("WARNING: No valid expansions, falling back to simple trace")
            value = tracer.trace_varnode(return_varnode, use_cache=False)
            simplified_conds = ConditionSimplifier.simplify_conditions(path_conditions)
            resolved_value = self._concretize_readonly_loads(value, simplified_conds, self._current_parameters)
            return [ReturnInfo(
                address=address,
                value=resolved_value,
                conditions=simplified_conds,
                branch_index=return_index
            )]
        
        return results

    def _build_return_infos_from_expansions(
        self,
        address: str,
        expanded_values,
        return_index: int,
    ) -> List[ReturnInfo]:
        results = []
        for i, ev in enumerate(expanded_values):
            if not ev.is_valid():
                self._debug_print(f"Skipping contradictory expansion {i}")
                continue

            simplified_conds = ConditionSimplifier.simplify_conditions(ev.conditions)
            normalized_value = self._normalize_expanded_return_value(
                ev.value,
                simplified_conds,
            )
            resolved_value = self._concretize_readonly_loads(
                normalized_value,
                simplified_conds,
                self._current_parameters,
            )

            if self.debug:
                cond_strs = [
                    ConditionSimplifier.get_simplified_condition_string(c)
                    for c in simplified_conds
                ]
                self._debug_print(
                    f"Expansion {i}: value={self._debug_expr_summary(resolved_value)}"
                )
                self._debug_print(f"  conditions={cond_strs}")

            results.append(
                ReturnInfo(
                    address=address,
                    value=resolved_value,
                    conditions=simplified_conds,
                    branch_index=return_index * 100 + i,
                )
            )
        pruned = self._prune_less_precise_return_infos(results)
        return self._merge_equivalent_return_infos(pruned)

    def _prune_less_precise_return_infos(
        self,
        return_infos: List[ReturnInfo],
    ) -> List[ReturnInfo]:
        if len(return_infos) < 2:
            return return_infos

        grouped: Dict[Tuple[str, str], List[ReturnInfo]] = {}
        for info in return_infos:
            key = (
                info.address,
                self._pruning_conditions_signature(info.conditions),
            )
            grouped.setdefault(key, []).append(info)

        pruned: List[ReturnInfo] = []
        for group in grouped.values():
            precise_group = [
                info
                for info in group
                if not self._expression_contains_unresolved_value(info.value)
            ]
            unresolved_group = [
                info
                for info in group
                if self._expression_contains_unresolved_value(info.value)
            ]
            if not precise_group or not unresolved_group:
                pruned.extend(group)
                continue

            canonical_precise = precise_group[0]
            precise_values_are_unanimous = all(
                _expressions_equivalent(canonical_precise.value, info.value)
                for info in precise_group[1:]
            )
            if not precise_values_are_unanimous:
                if self.debug:
                    self._debug_print(
                        "Preserved unresolved return cases because precise cases "
                        "under the same condition region disagree"
                    )
                pruned.extend(group)
                continue

            dropped = len(unresolved_group)
            if dropped > 0 and self.debug:
                self._debug_print(
                    "Dropped less precise unresolved return cases under an "
                    "already-resolved condition region"
                )
            pruned.extend(precise_group)

        return pruned

    def _analysis_has_ambiguous_condition_region_returns(
        self,
        analysis: Optional[FunctionReturnAnalysis],
    ) -> bool:
        if analysis is None or len(analysis.returns or []) < 2:
            return False

        grouped: Dict[Tuple[str, str], List[ReturnInfo]] = {}
        for info in analysis.returns or []:
            key = (
                info.address,
                self._pruning_conditions_signature(info.conditions),
            )
            grouped.setdefault(key, []).append(info)

        for group in grouped.values():
            precise_group = [
                info
                for info in group
                if not self._expression_contains_unresolved_value(info.value)
            ]
            if len(precise_group) < 2:
                continue
            first = precise_group[0]
            if any(
                not _expressions_equivalent(first.value, candidate.value)
                for candidate in precise_group[1:]
            ):
                return True
        return False

    def _pruning_conditions_signature(
        self,
        conditions: List[Condition],
    ) -> str:
        parts = [
            ConditionSimplifier.get_simplified_condition_string(condition)
            for condition in (conditions or [])
        ]
        parts.sort()
        return ";;".join(parts)

    def _merge_equivalent_return_infos(
        self,
        return_infos: List[ReturnInfo],
    ) -> List[ReturnInfo]:
        if len(return_infos) < 2:
            return return_infos

        merged = list(return_infos)
        changed = True
        while changed:
            changed = False
            for i in range(len(merged)):
                for j in range(i + 1, len(merged)):
                    combined = self._merge_return_info_pair(
                        merged[i],
                        merged[j],
                        merged,
                        i,
                        j,
                    )
                    if combined is None:
                        continue
                    merged[i] = combined
                    del merged[j]
                    changed = True
                    break
                if changed:
                    break
        return merged

    def _merge_return_info_pair(
        self,
        left: ReturnInfo,
        right: ReturnInfo,
        all_infos: Optional[List[ReturnInfo]] = None,
        left_index: Optional[int] = None,
        right_index: Optional[int] = None,
    ) -> Optional[ReturnInfo]:
        if left.address != right.address:
            return None
        if not _expressions_equivalent(left.value, right.value):
            return None

        shared_conditions, left_residual, right_residual = self._partition_return_conditions(
            left.conditions,
            right.conditions,
        )

        if not left_residual and not right_residual:
            return self._make_merged_return_info(left, right, shared_conditions, "deduplicated identical return case")

        if len(left_residual) == 1 and len(right_residual) == 1:
            if ConditionSimplifier.are_contradictory_conditions(left_residual[0], right_residual[0]):
                if (
                    expression_contains_synthetic_location_reads(left.value)
                    or expression_contains_synthetic_location_reads(right.value)
                ):
                    if self.debug:
                        self._debug_print(
                            "skipping complementary return-case collapse due to "
                            "symbolic post-state reads in value"
                        )
                    return None
                if not self._can_safely_collapse_complementary_return_pair(
                    left,
                    right,
                    shared_conditions,
                    all_infos or [],
                    left_index,
                    right_index,
                ):
                    return None
                return self._make_merged_return_info(
                    left,
                    right,
                    shared_conditions,
                    "collapsed complementary same-valued return cases",
                )

        return None

    def _can_safely_collapse_complementary_return_pair(
        self,
        left: ReturnInfo,
        right: ReturnInfo,
        merged_conditions: List[Condition],
        all_infos: List[ReturnInfo],
        left_index: Optional[int],
        right_index: Optional[int],
    ) -> bool:
        if not all_infos:
            return True

        merged_scope = ConditionSimplifier.simplify_conditions(list(merged_conditions))
        for index, other in enumerate(all_infos):
            if index == left_index or index == right_index:
                continue
            if other.address != left.address:
                continue
            if _expressions_equivalent(other.value, left.value):
                continue

            overlap_conditions = ConditionSimplifier.simplify_conditions(
                list(merged_scope) + list(other.conditions)
            )
            if ConditionSimplifier.is_contradiction(overlap_conditions):
                continue

            if self.debug:
                cond_dump = [
                    ConditionSimplifier.get_simplified_condition_string(cond)
                    for cond in overlap_conditions
                ]
                self._debug_print(
                    "skipping complementary return-case collapse due to overlapping "
                    f"different-valued case: value={self._debug_expr_summary(other.value)} "
                    f"conditions={cond_dump}"
                )
            return False

        return True

    def _partition_return_conditions(
        self,
        left_conditions: List[Condition],
        right_conditions: List[Condition],
    ) -> Tuple[List[Condition], List[Condition], List[Condition]]:
        shared: List[Condition] = []
        right_used: Set[int] = set()
        left_residual: List[Condition] = []

        for left_cond in left_conditions:
            match_index = None
            for index, right_cond in enumerate(right_conditions):
                if index in right_used:
                    continue
                if ConditionSimplifier.are_equivalent_conditions(left_cond, right_cond):
                    match_index = index
                    break
            if match_index is None:
                left_residual.append(left_cond)
                continue
            right_used.add(match_index)
            shared.append(left_cond)

        right_residual = [
            cond for index, cond in enumerate(right_conditions) if index not in right_used
        ]
        return (
            ConditionSimplifier.simplify_conditions(shared),
            ConditionSimplifier.simplify_conditions(left_residual),
            ConditionSimplifier.simplify_conditions(right_residual),
        )

    def _make_merged_return_info(
        self,
        primary: ReturnInfo,
        secondary: ReturnInfo,
        merged_conditions: List[Condition],
        reason: str,
    ) -> ReturnInfo:
        normalized_conditions = ConditionSimplifier.simplify_conditions(list(merged_conditions))
        if self.debug:
            cond_dump = [
                ConditionSimplifier.get_simplified_condition_string(cond)
                for cond in normalized_conditions
            ]
            self._debug_print(
                f"{reason}: value={self._debug_expr_summary(primary.value)} conditions={cond_dump}"
            )
        return ReturnInfo(
            address=primary.address,
            value=primary.value,
            conditions=normalized_conditions,
            branch_index=self._min_branch_index(primary.branch_index, secondary.branch_index),
        )

    def _min_branch_index(
        self,
        left: Optional[int],
        right: Optional[int],
    ) -> Optional[int]:
        if left is None:
            return right
        if right is None:
            return left
        return min(left, right)

    def _normalize_expanded_return_value(
        self,
        value: Expression,
        conditions: List[Condition],
    ) -> Expression:
        normalized_value = value
        started_with_phi = self._expression_contains_phi(value)
        effect_summary = self._current_effect_summary
        has_effects = effect_summary is not None and bool(effect_summary.effects)

        if started_with_phi:
            reduced_value = _reduce_expression_under_conditions(value, conditions)
            if reduced_value is not None:
                normalized_value = reduced_value
            if self.debug and normalized_value is not value:
                self._debug_print(
                    "Reduced PHI-bearing expanded return under active conditions: "
                    f"{self._debug_expr_summary(value)} -> {self._debug_expr_summary(normalized_value)}"
                )

        if has_effects:
            assert effect_summary is not None
            canonicalized = self._normalize_return_value_with_effect_summary(
                normalized_value,
                conditions,
                effect_summary,
            )
            if canonicalized is not None:
                if self.debug and canonicalized is not normalized_value:
                    self._debug_print(
                        "Normalized expanded return with definite post-state replay: "
                        f"{self._debug_expr_summary(normalized_value)} -> "
                        f"{self._debug_expr_summary(canonicalized)}"
                    )
                normalized_value = canonicalized

        return normalized_value

    def _normalize_return_value_with_effect_summary(
        self,
        value: Expression,
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> Optional[Expression]:
        canonicalized = normalize_post_state_expression(
            value,
            conditions,
            effect_summary.effects,
            self._current_parameters,
            prefer_canonical_post_state=True,
            symbolic_post_state=True,
        )
        if self._should_replay_canonicalized_return(canonicalized, value):
            replayed = normalize_post_state_expression(
                canonicalized,
                conditions,
                effect_summary.effects,
                self._current_parameters,
                prefer_canonical_post_state=False,
            )
            if replayed is not None:
                canonicalized = replayed

        if self._symbolic_post_state_roundtrip_rejected(canonicalized, value, conditions, effect_summary):
            if self.debug:
                self._debug_print(
                    "Rejected symbolic post-state canonicalization due to non-equivalent round trip: "
                    f"{self._debug_expr_summary(value)} -> "
                    f"{self._debug_expr_summary(canonicalized)}"
                )
            fallback_replayed = normalize_post_state_expression(
                value,
                conditions,
                effect_summary.effects,
                self._current_parameters,
                prefer_canonical_post_state=False,
                preserve_composite_location_wrappers=True,
            )
            return fallback_replayed if fallback_replayed is not None else value

        return canonicalized

    def _should_replay_canonicalized_return(
        self,
        canonicalized: Optional[Expression],
        original: Expression,
    ) -> bool:
        return (
            canonicalized is not None
            and not _expressions_equivalent(canonicalized, original)
            and self._count_memory_reads(canonicalized) > self._count_memory_reads(original)
        )

    def _symbolic_post_state_roundtrip_rejected(
        self,
        canonicalized: Optional[Expression],
        original: Expression,
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> bool:
        if canonicalized is None or _expressions_equivalent(canonicalized, original):
            return False
        if not expression_contains_synthetic_location_reads(canonicalized):
            return False
        lowered_roundtrip = lower_post_state_expression_for_smt(
            canonicalized,
            conditions,
            effect_summary.effects,
            self._current_parameters,
        )
        return lowered_roundtrip is None or not _expressions_equivalent_under_conditions(
            lowered_roundtrip,
            original,
            conditions,
            self._current_parameters,
        )

    def _expression_contains_unresolved_value(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return True

        expr_type = getattr(expr, "expr_type", None)
        if expr_type is None:
            return True

        if expr_type in {ExpressionType.UNKNOWN, ExpressionType.CALL}:
            return True

        if expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                cond_expr = getattr(cond, "expression", None) if cond is not None else None
                if cond_expr is not None and self._expression_contains_unresolved_value(cond_expr):
                    return True
                if self._expression_contains_unresolved_value(value):
                    return True
            return False

        for operand in getattr(expr, "operands", []) or []:
            if self._expression_contains_unresolved_value(operand):
                return True

        return False

    def _count_memory_reads(self, expr: Optional[Expression]) -> int:
        if expr is None:
            return 0
        count = 1 if expr.expr_type == ExpressionType.MEMORY else 0
        if expr.expr_type == ExpressionType.PHI and expr.value:
            return count + sum(self._count_memory_reads(value) for _cond, value in expr.value)
        for operand in getattr(expr, "operands", []) or []:
            count += self._count_memory_reads(operand)
        return count

    def _contains_multiequal(self, varnode, depth: int = 0) -> bool:
        """Return値のチェーン内にMULTIEQUALが含まれるかチェック"""
        if depth > 15:
            return False
        
        if varnode is None:
            return False
        
        def_op = varnode.getDef()
        if def_op is None:
            return False
        
        mnemonic = def_op.getMnemonic()
        
        if mnemonic == "MULTIEQUAL":
            return True
        
        for i in range(def_op.getNumInputs()):
            input_vn = def_op.getInput(i)
            if self._contains_multiequal(input_vn, depth + 1):
                return True
        
        return False
    
    def analyze_function_by_name(self, function_name: str, timeout: int = 60) -> Optional[FunctionReturnAnalysis]:
        self._last_function_lookup_error = None
        function = self._find_function_by_name(function_name)
        if function is None:
            self._last_function_lookup_error = f"Function '{function_name}' not found"
            self._debug_print(self._last_function_lookup_error)
            return None
        return self.analyze_function(function, timeout)

    def get_last_function_lookup_error(self) -> Optional[str]:
        return self._last_function_lookup_error

    def _concretize_readonly_loads(
        self,
        value: Expression,
        conditions: List[Condition],
        parameters: List[Dict],
    ) -> Expression:
        """Resolve simple read-only indexed loads into finite PHI chains when possible."""
        try:
            return concretize_readonly_loads(
                value,
                conditions,
                parameters,
                self._read_memory_value,
                image_base=self.program.getImageBase().getOffset(),
                debug=self.debug,
            )
        except Exception as exc:
            self._debug_print(f"Readonly load concretization failed: {exc}")
            return value

    def _read_memory_value(self, address_value: int, size_bytes: int) -> Optional[int]:
        """Read an unsigned integer from program memory."""
        if address_value < 0 or size_bytes <= 0:
            return None

        try:
            memory = self.program.getMemory()
            default_space = self.program.getAddressFactory().getDefaultAddressSpace()
            addr = default_space.getAddress(address_value)
            if addr is None:
                return None

            raw_bytes = []
            for offset in range(size_bytes):
                byte_val = memory.getByte(addr.add(offset))
                raw_bytes.append(int(byte_val) & 0xFF)

            is_big_endian = self.program.getLanguage().isBigEndian()
            ordered = raw_bytes if is_big_endian else list(reversed(raw_bytes))

            result = 0
            for byte_val in ordered:
                result = (result << 8) | byte_val
            return result
        except Exception:
            return None
    
    def _find_function_by_name(self, function_name: str):
        function_manager = self.program.getFunctionManager()
        for func in function_manager.getFunctions(True):
            if func.getName() == function_name:
                return func
        return None
