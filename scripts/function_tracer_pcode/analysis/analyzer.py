# -*- coding: utf-8 -*-
"""Return解析メインモジュール（符号性検出統合版）"""

import re
from contextlib import contextmanager
from typing import Iterable, List, Dict, Optional, Any, Set, Tuple, cast

from ..model.expression import Expression, ExpressionType, Condition
from ..model.storage import StorageInfo
from ..model.analysis import DeferredCallInfo, ReturnInfo, FunctionReturnAnalysis, SignednessResult
from ..model.signature import (
    get_declared_type_signedness,
    is_void_data_type,
)
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
    _enumerate_constant_expression_branches,
    _expressions_equivalent,
    _expressions_equivalent_under_conditions,
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
    
    def _debug_print(self, msg: str, indent: int = 0):
        if self.debug:
            prefix = "  " * indent
            print(f"{prefix}[ReturnAnalyzer] {msg}")

    def _debug_expr_summary(self, expr: Optional[Expression], max_depth: int = 4) -> str:
        return summarize_expression(expr, max_depth=max_depth)

    def _coerce_optional_int(self, value: object) -> Optional[int]:
        if value is None or isinstance(value, bool):
            return None
        if isinstance(value, int):
            return value
        try:
            return int(cast(Any, value))
        except Exception:
            return None

    def _describe_pcode_site(
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
        }

    def _return_site_key(self, ret_info: ReturnInfo) -> str:
        return ret_info.site_key()

    def _make_return_info(
        self,
        *,
        address: str,
        value: Expression,
        conditions: List[Condition],
        branch_index: Optional[int] = None,
        site_metadata: Optional[Dict[str, Optional[object]]] = None,
    ) -> ReturnInfo:
        site_metadata = site_metadata or {}
        return ReturnInfo(
            address=address,
            value=value,
            conditions=list(conditions or []),
            branch_index=branch_index,
            pcode_identity=cast(Optional[str], site_metadata.get("pcode_identity")),
            pcode_order=self._coerce_optional_int(site_metadata.get("pcode_order")),
            pcode_time=self._coerce_optional_int(site_metadata.get("pcode_time")),
        )

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
            if ret_info.pcode_identity is not None:
                self._debug_print(f"    pcode_identity: {ret_info.pcode_identity}", 1)
            if ret_info.pcode_time is not None or ret_info.pcode_order is not None:
                self._debug_print(
                    f"    seq(time={ret_info.pcode_time}, order={ret_info.pcode_order})",
                    1,
                )
            
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
            return_type_obj, return_type = self._get_return_type_info(high_function)
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
                return_type_obj=return_type_obj,
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
            self._make_return_info(
                address=only_return.address,
                value=only_return.value,
                conditions=[],
                branch_index=only_return.branch_index,
                site_metadata={
                    "pcode_identity": only_return.pcode_identity,
                    "pcode_order": only_return.pcode_order,
                    "pcode_time": only_return.pcode_time,
                },
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
        """wrapper らしい unknown return を P-code/CFG ベースでのみ復元する。"""
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
        if self.debug:
            self._debug_print(
                "Call-wrapper recovery declined: no safe P-code/CFG reconstruction was available"
            )
        return None

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

            site_metadata = self._describe_pcode_site(return_op, analysis.entry_point)
            address = cast(str, site_metadata.get("address") or analysis.entry_point)
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

    def _analysis_needs_wrapper_recovery(
        self,
        analysis: Optional[FunctionReturnAnalysis],
    ) -> bool:
        if analysis is None or not analysis.returns:
            return False
        return analysis.has_unknown_return() or analysis.has_unresolved_return_value()

    def _should_attempt_switch_recovery(
        self,
        analysis: Optional[FunctionReturnAnalysis],
    ) -> bool:
        if analysis is None or not analysis.returns:
            return False
        if analysis.recovered_from_decompiler:
            return False
        if analysis.has_unknown_return():
            return True
        if analysis.has_overlapping_unconditional_returns():
            return True
        if self._analysis_has_ambiguous_condition_region_returns(analysis):
            return True
        if analysis.has_unresolved_return_value():
            return True
        return any(
            reason in {"callind_out_of_scope", "indirect_control_flow_unresolved"}
            for reason in getattr(analysis, "unknown_event_reasons", [])
        )

    def _recover_switch_like_returns_from_pcode(
        self,
        analysis: FunctionReturnAnalysis,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        return_ops: Optional[List[Any]] = None,
        current_function=None,
        active_functions: Optional[Set[str]] = None,
    ) -> Optional[List[ReturnInfo]]:
        from ..transform.expander import ExpandedValue

        if not self._should_attempt_switch_recovery(analysis):
            return None

        block_by_index = getattr(condition_tracker, "block_by_index", None) or {}
        switch_blocks = [
            block_info
            for block_info in block_by_index.values()
            if self._find_branchind_op_on_block(block_info) is not None
        ]
        if not switch_blocks:
            return None

        for switch_block in sorted(switch_blocks, key=lambda info: info.index):
            branchind_op = self._find_branchind_op_on_block(switch_block)
            if branchind_op is None:
                continue

            impacted_site_keys = self._collect_switch_impacted_return_sites(
                switch_block,
                return_ops or [],
                condition_tracker,
                analysis.entry_point,
            )
            if impacted_site_keys is None or not impacted_site_keys:
                continue

            affected_returns = [
                ret for ret in (analysis.returns or []) if self._return_site_key(ret) in impacted_site_keys
            ]
            unaffected_returns = [
                ret for ret in (analysis.returns or []) if self._return_site_key(ret) not in impacted_site_keys
            ]
            if not affected_returns:
                continue
            if not self._switch_recovery_targets_problematic_region(analysis, affected_returns):
                continue

            candidate_entries = self._enumerate_switch_branch_targets(
                switch_block,
                branchind_op,
                tracer,
                condition_tracker,
            )
            if not candidate_entries or len(candidate_entries) < 2:
                continue

            expanded_values: List[ExpandedValue] = []
            candidate_failed = False
            for address_value, branch_conditions in candidate_entries:
                resolved = self._resolve_local_code_target_expansions(
                    address_value,
                    active_functions or set(),
                    current_function=current_function,
                )
                if not resolved:
                    if self.debug:
                        cond_dump = [
                            ConditionSimplifier.get_simplified_condition_string(cond)
                            for cond in branch_conditions
                        ]
                        self._debug_print(
                            "Switch recovery aborted: local target expansion failed for "
                            f"0x{address_value:x} under {cond_dump}"
                        )
                    candidate_failed = True
                    break

                for ev in resolved:
                    merged_conditions = ConditionSimplifier.simplify_conditions(
                        list(branch_conditions) + list(getattr(ev, "conditions", []) or [])
                    )
                    if ConditionSimplifier.is_contradiction(merged_conditions):
                        continue
                    expanded_values.append(
                        ExpandedValue(
                            value=self._clone_expression(ev.value),
                            conditions=merged_conditions,
                        )
                    )

            if candidate_failed or not expanded_values:
                continue

            site_metadata = self._describe_pcode_site(
                branchind_op,
                analysis.entry_point,
                identity_prefix="branchind",
            )
            recovered = self._build_return_infos_from_expansions(
                cast(str, site_metadata.get("address") or analysis.entry_point),
                expanded_values,
                0,
                site_metadata=site_metadata,
            )
            recovered = self._merge_equivalent_return_infos(
                self._prune_less_precise_return_infos(recovered)
            )
            if not recovered:
                continue
            if not self._switch_recovery_improves_returns(analysis, affected_returns, recovered):
                continue
            if self._switch_recovery_conflicts_with_unaffected_returns(unaffected_returns, recovered):
                continue
            combined = self._merge_equivalent_return_infos(
                self._prune_less_precise_return_infos(list(unaffected_returns) + recovered)
            )
            if not combined:
                continue
            if self.debug:
                self._debug_print(
                    "Recovered switch-like return cases from BRANCHIND/CFG structure "
                    f"(affected_sites={sorted(impacted_site_keys)}, recovered={len(recovered)})"
                )
            return combined

        return None

    def _find_branchind_op_on_block(self, block_info) -> Optional[Any]:
        if block_info is None:
            return None
        for pcode_op in reversed(list(getattr(block_info, "pcode_ops", []) or [])):
            try:
                if pcode_op.getMnemonic() == "BRANCHIND":
                    return pcode_op
            except Exception:
                continue
        return None

    def _enumerate_switch_branch_targets(
        self,
        switch_block,
        branchind_op,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
    ) -> List[Tuple[int, List[Condition]]]:
        if branchind_op is None or branchind_op.getNumInputs() < 1:
            return []

        base_paths = condition_tracker.get_all_valid_block_paths_to_block(switch_block)
        if not base_paths:
            base_paths = [([switch_block], [])]

        resolved_targets: List[Tuple[int, List[Condition]]] = []
        seen = set()
        for _blocks, base_conditions in base_paths:
            try:
                target_varnode = branchind_op.getInput(0)
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
                        f"Switch recovery skipped on block {switch_block.index}: BRANCHIND target was not finitely enumerable"
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

    def _collect_switch_impacted_return_sites(
        self,
        switch_block,
        return_ops: List[Any],
        condition_tracker: ConditionTracker,
        fallback_address: str,
    ) -> Optional[Set[str]]:
        impacted: Set[str] = set()
        switch_index = getattr(switch_block, "index", None)

        for return_index, return_op in enumerate(return_ops or []):
            raw_entries = condition_tracker.get_all_valid_block_paths_to_return(return_op)
            path_entries = self._coerce_block_path_entries(raw_entries)
            if not path_entries:
                continue

            path_hits = [
                any(getattr(block_info, "index", None) == switch_index for block_info in (block_path or []))
                for block_path, _conditions in path_entries
            ]
            if not any(path_hits):
                continue
            if not all(path_hits):
                if self.debug:
                    self._debug_print(
                        "Switch recovery skipped: candidate BRANCHIND only influences a subset of "
                        f"paths to RETURN #{return_index}"
                    )
                return None

            site_metadata = self._describe_pcode_site(return_op, fallback_address)
            impacted.add(cast(str, site_metadata.get("pcode_identity") or site_metadata.get("address")))

        return impacted

    def _switch_recovery_targets_problematic_region(
        self,
        analysis: FunctionReturnAnalysis,
        affected_returns: List[ReturnInfo],
    ) -> bool:
        if not affected_returns:
            return False

        affected_analysis = FunctionReturnAnalysis(
            function_name=analysis.function_name,
            entry_point=analysis.entry_point,
            parameters=list(analysis.parameters or []),
            returns=list(affected_returns),
            return_type=analysis.return_type,
            return_type_obj=analysis.return_type_obj,
            unknown_event_count=analysis.unknown_event_count,
            unknown_event_reasons=list(analysis.unknown_event_reasons),
        )
        if affected_analysis.has_unknown_return():
            return True
        if affected_analysis.has_unresolved_return_value():
            return True
        if affected_analysis.has_overlapping_unconditional_returns():
            return True
        return self._analysis_has_ambiguous_condition_region_returns(affected_analysis)

    def _switch_recovery_improves_returns(
        self,
        analysis: FunctionReturnAnalysis,
        affected_returns: List[ReturnInfo],
        recovered: List[ReturnInfo],
    ) -> bool:
        if not recovered:
            return False
        if any(self._expression_contains_unresolved_value(ret.value) for ret in recovered):
            return False

        original_unresolved = sum(
            1 for ret in affected_returns if self._expression_contains_unresolved_value(ret.value)
        )
        recovered_unresolved = sum(
            1 for ret in recovered if self._expression_contains_unresolved_value(ret.value)
        )
        if recovered_unresolved < original_unresolved:
            return True

        affected_analysis = FunctionReturnAnalysis(
            function_name=analysis.function_name,
            entry_point=analysis.entry_point,
            parameters=list(analysis.parameters or []),
            returns=list(affected_returns),
            return_type=analysis.return_type,
            return_type_obj=analysis.return_type_obj,
            unknown_event_count=analysis.unknown_event_count,
            unknown_event_reasons=list(analysis.unknown_event_reasons),
        )
        if affected_analysis.has_overlapping_unconditional_returns():
            return True
        if self._analysis_has_ambiguous_condition_region_returns(affected_analysis):
            return True
        return False

    def _switch_recovery_conflicts_with_unaffected_returns(
        self,
        unaffected_returns: List[ReturnInfo],
        recovered: List[ReturnInfo],
    ) -> bool:
        for existing in unaffected_returns:
            for candidate in recovered:
                overlap_conditions = ConditionSimplifier.simplify_conditions(
                    list(existing.conditions) + list(candidate.conditions)
                )
                if ConditionSimplifier.is_contradiction(overlap_conditions):
                    continue
                if _expressions_equivalent(existing.value, candidate.value):
                    continue
                if self.debug:
                    cond_dump = [
                        ConditionSimplifier.get_simplified_condition_string(cond)
                        for cond in overlap_conditions
                    ]
                    self._debug_print(
                        "Switch recovery rejected due to overlap with unaffected return case: "
                        f"existing={self._debug_expr_summary(existing.value)} "
                        f"candidate={self._debug_expr_summary(candidate.value)} "
                        f"conditions={cond_dump}"
                    )
                return True
        return False

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
            self._debug_print(f"Call expansion skipped for '{function_name}': analysis unavailable")
            return None
        if not self._is_call_return_summary_allowed(analysis, args):
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

    def _decompile_function(self, function, timeout: int = 60):
        try:
            decompiler = self._get_decompiler()
            results = decompiler.decompileFunction(function, timeout, None)
            if not results.decompileCompleted():
                return None
            return results
        except Exception:
            return None

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
    
    def _get_return_type_info(self, high_function):
        """戻り値の型オブジェクトと表示名を取得"""
        try:
            func_proto = high_function.getFunctionPrototype()
            if func_proto:
                ret_type = func_proto.getReturnType()
                if ret_type:
                    return ret_type, self._get_return_type(high_function) or str(ret_type)
        except Exception as e:
            self._debug_print(f"Failed to get return type: {e}")
        return None, None

    def _get_return_type(self, high_function) -> Optional[str]:
        """後方互換: 戻り値の表示名だけを返す。"""
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
        return get_declared_type_signedness(data_type, fallback_signed=True)

    def _is_void_type(self, data_type) -> bool:
        """データ型が void かどうかを判定"""
        return is_void_data_type(data_type)
    
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
        site_metadata = self._describe_pcode_site(return_op, "unknown")
        address = cast(str, site_metadata.get("address") or "unknown")
        
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
                site_metadata=site_metadata,
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
                site_metadata=site_metadata,
            )
            if implicit_results is not None:
                return implicit_results
            # void return
            simplified_conds = ConditionSimplifier.simplify_conditions(path_conditions)
            return [self._make_return_info(
                address=address,
                value=Expression.unknown("void"),
                conditions=simplified_conds,
                branch_index=return_index,
                site_metadata=site_metadata,
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
        site_metadata: Optional[Dict[str, Optional[object]]] = None,
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
            site_metadata=site_metadata,
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
                site_metadata=site_metadata,
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
            site_metadata=site_metadata,
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
        site_metadata: Optional[Dict[str, Optional[object]]] = None,
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
                    site_metadata=site_metadata,
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
        current_condition_keys: Set[object],
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

    def _build_condition_signature_set(self, conditions: List[Condition]) -> Set[object]:
        from .condition.simplifier import ConditionSimplifier

        signatures: Set[object] = set()
        for condition in conditions:
            try:
                signatures.add(ConditionNormalizer.normalize_for_contradiction(condition))
            except Exception:
                try:
                    signatures.add(condition.structural_key())
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
        site_metadata: Optional[Dict[str, Optional[object]]] = None,
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
            site_metadata=site_metadata,
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
        site_metadata: Optional[Dict[str, Optional[object]]] = None,
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
            site_metadata=site_metadata,
        )
        
        if not results:
            self._debug_print("WARNING: No valid expansions, falling back to simple trace")
            value = tracer.trace_varnode(return_varnode, use_cache=False)
            simplified_conds = ConditionSimplifier.simplify_conditions(path_conditions)
            resolved_value = self._concretize_readonly_loads(value, simplified_conds, self._current_parameters)
            return [self._make_return_info(
                address=address,
                value=resolved_value,
                conditions=simplified_conds,
                branch_index=return_index,
                site_metadata=site_metadata,
            )]
        
        return results

    def _build_return_infos_from_expansions(
        self,
        address: str,
        expanded_values,
        return_index: int,
        site_metadata: Optional[Dict[str, Optional[object]]] = None,
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
                self._make_return_info(
                    address=address,
                    value=resolved_value,
                    conditions=simplified_conds,
                    branch_index=return_index * 100 + i,
                    site_metadata=site_metadata,
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
                self._return_site_key(info),
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
                self._return_site_key(info),
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
    ):
        parts = [
            ConditionNormalizer.normalize_for_contradiction(condition)
            for condition in (conditions or [])
        ]
        parts.sort()
        return tuple(parts)

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
        if self._return_site_key(left) != self._return_site_key(right):
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
            if self._return_site_key(other) != self._return_site_key(left):
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
        return self._make_return_info(
            address=primary.address,
            value=primary.value,
            conditions=normalized_conditions,
            branch_index=self._min_branch_index(primary.branch_index, secondary.branch_index),
            site_metadata={
                "pcode_identity": primary.pcode_identity,
                "pcode_order": primary.pcode_order,
                "pcode_time": primary.pcode_time,
            },
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
