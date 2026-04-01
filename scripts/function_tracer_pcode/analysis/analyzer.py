# -*- coding: utf-8 -*-
"""Return解析メインモジュール（符号性検出統合版）"""

import re
from typing import List, Dict, Optional, Any, Set

from ..model.expression import Expression, ExpressionType, Condition
from ..model.analysis import ReturnInfo, FunctionReturnAnalysis, SignednessResult
from . import PcodeTracer
from .condition import ConditionTracker, ConditionSimplifier
from .signedness import SignednessDetector
from .effect_summary import (
    _reduce_expression_under_conditions,
    canonicalize_post_state_subexpressions,
    summarize_store_effects,
    substitute_condition,
    substitute_expression,
)
from .memory_resolver import concretize_readonly_loads


class ReturnAnalyzer:
    """関数のReturn値を解析"""
    
    def __init__(self, program, debug: bool = False):
        self.program = program
        self.debug = debug
        self._decompiler = None
        self._current_parameters: List[Dict] = []
        self._current_effect_summary = None
        self._effect_summary_cache: Dict[str, Any] = {}
        self._effect_summary_parameter_cache: Dict[str, List[Dict]] = {}
        self._call_analysis_cache: Dict[str, Optional[FunctionReturnAnalysis]] = {}
    
    def _debug_print(self, msg: str, indent: int = 0):
        if self.debug:
            prefix = "  " * indent
            print(f"{prefix}[ReturnAnalyzer] {msg}")
    
    def _get_decompiler(self):
        if self._decompiler is None:
            from ghidra.app.decompiler import DecompInterface # type: ignore[import]
            self._decompiler = DecompInterface()
            self._decompiler.openProgram(self.program)
        return self._decompiler
    
    def dispose(self):
        if self._decompiler is not None:
            self._decompiler.dispose()
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
                value_str = ret_info.value.to_string()
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
        
        # Step 2: condition_tracker作成（まだビルドしない）
        condition_tracker = ConditionTracker(tracer)
        
        # Step 3: phi_handler作成 → tracerに注入
        from .phi_resolver import PhiHandler
        phi_handler = PhiHandler(tracer, condition_tracker)
        tracer.phi_handler = phi_handler
        
        # Step 4: ブロック情報構築（phi_handler準備後）
        condition_tracker.build()
        
        parameters = self._collect_parameters(high_function)
        self._current_parameters = parameters
        self._debug_print(f"Parameters: {[p['name'] for p in parameters]}")
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
                active_functions=active_functions,
            )
            return_infos.extend(infos)
        
        result = FunctionReturnAnalysis(
            function_name=function.getName(),
            entry_point=str(function.getEntryPoint()),
            parameters=parameters,
            returns=return_infos,
            return_type=return_type,
            signedness_result=signedness_result
        )

        result.returns = self._finalize_returns_with_effect_summary(
            result.returns,
            effect_summary,
            parameters,
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

    def _finalize_returns_with_effect_summary(
        self,
        returns: List[ReturnInfo],
        effect_summary,
        parameters: List[Dict],
    ) -> List[ReturnInfo]:
        """
        Return values are already normalized in _analyze_return_op().

        Re-applying effect-summary rewriting here can convert canonical post-state
        expressions back into observed pre-state values, which is unsound for
        swap-style memory effects. Keep the finalized returns as-is.
        """
        return returns

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
            callee = self._find_function_by_name(function_name)
            if callee is None:
                return []
            callee_key = str(callee.getEntryPoint())
            cached_parameters = self._effect_summary_parameter_cache.get(callee_key)
            if cached_parameters is not None:
                return cached_parameters

            decompiler = self._get_decompiler()
            results = decompiler.decompileFunction(callee, 60, None)
            if not results.decompileCompleted():
                return []
            callee_high = results.getHighFunction()
            if callee_high is None:
                return []
            callee_parameters = self._collect_parameters(callee_high)
            self._effect_summary_parameter_cache[callee_key] = list(callee_parameters)
            return callee_parameters

        summary = summarize_store_effects(
            condition_tracker.block_by_index.values(),
            tracer,
            condition_tracker,
            parameters,
            direct_call_summary=summarize_call,
            resolve_callee_parameters=resolve_callee_parameters,
            debug=self.debug,
        )
        self._effect_summary_cache[cache_key] = summary
        return summary

    def _make_call_resolver(self, active_functions: Set[str]):
        def resolve_call(function_name: str, args):
            return self._resolve_call_expansions(function_name, args, active_functions)

        return resolve_call

    def _resolve_call_expansions(
        self,
        function_name: str,
        args: List[Expression],
        active_functions: Set[str],
    ):
        from ..transform.expander import ExpandedValue

        if function_name in active_functions:
            self._debug_print(f"Skipping recursive call expansion for '{function_name}'")
            return None

        analysis = self._get_or_analyze_call_target(function_name, active_functions)
        if analysis is None or not self._is_call_return_summary_allowed(analysis, args):
            return None

        param_names = [param.get("name") for param in analysis.parameters if param.get("name")]
        if len(args) < len(param_names):
            self._debug_print(
                f"Call expansion skipped for '{function_name}': "
                f"expected {len(param_names)} args, got {len(args)}"
            )
            return None

        replacements = dict(zip(param_names, args))
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

    def _get_or_analyze_call_target(
        self,
        function_name: str,
        active_functions: Set[str],
    ) -> Optional[FunctionReturnAnalysis]:
        callee = self._find_function_by_name(function_name)
        if callee is None:
            return None

        cache_key = str(callee.getEntryPoint())
        if cache_key in self._call_analysis_cache:
            return self._call_analysis_cache[cache_key]

        analysis = self.analyze_function(
            callee,
            timeout=60,
            active_functions=active_functions | {function_name},
        )
        self._call_analysis_cache[cache_key] = analysis
        return analysis

    def _is_call_return_summary_allowed(
        self,
        analysis: FunctionReturnAnalysis,
        args: List[Expression],
    ) -> bool:
        if analysis is None or not analysis.returns:
            return False

        param_names = {param.get("name") for param in analysis.parameters if param.get("name")}
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
            varnodes = storage.getVarnodes()
            if not varnodes or len(varnodes) == 0:
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
        active_functions: Set[str],
    ) -> List[ReturnInfo]:
        """単一のRETURNを解析"""
        seq = return_op.getSeqnum()
        address = str(seq.getTarget()) if seq else "unknown"
        
        num_inputs = return_op.getNumInputs()
        self._debug_print(f"RETURN at {address}, inputs: {num_inputs}")
        
        # RETURNへのパス条件を取得
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
            )
        else:
            # void return
            simplified_conds = ConditionSimplifier.simplify_conditions(path_conditions)
            return [ReturnInfo(
                address=address,
                value=Expression.unknown("void"),
                conditions=simplified_conds,
                branch_index=return_index
            )]
    
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
                call_resolver=self._make_call_resolver(active_functions or set()),
                effect_summary=self._current_effect_summary,
                parameters=self._current_parameters,
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
                call_resolver=self._make_call_resolver(active_functions or set()),
                effect_summary=self._current_effect_summary,
                parameters=self._current_parameters,
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
                cond_strs = [ConditionSimplifier.get_simplified_condition_string(c) for c in simplified_conds]
                self._debug_print(f"Expansion {i}: value={resolved_value.to_string()}")
                self._debug_print(f"  conditions={cond_strs}")
            
            results.append(ReturnInfo(
                address=address,
                value=resolved_value,
                conditions=simplified_conds,
                branch_index=return_index * 100 + i
            ))
        
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

    def _normalize_expanded_return_value(
        self,
        value: Expression,
        conditions: List[Condition],
    ) -> Expression:
        normalized_value = value
        started_with_phi = self._expression_contains_phi(value)

        if started_with_phi:
            reduced_value = _reduce_expression_under_conditions(value, conditions)
            if reduced_value is not None:
                normalized_value = reduced_value
            if self.debug and normalized_value is not value:
                self._debug_print(
                    "Reduced PHI-bearing expanded return under active conditions: "
                    f"{value.to_string()} -> {normalized_value.to_string()}"
                )

        if (
            not started_with_phi
            and self._current_effect_summary is not None
            and self._current_effect_summary.effects
        ):
            normalized_value = canonicalize_post_state_subexpressions(
                normalized_value,
                conditions,
                self._current_effect_summary.effects,
                self._current_parameters,
            )

        return normalized_value

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
        function = self._find_function_by_name(function_name)
        if function is None:
            self._debug_print(f"Function '{function_name}' not found")
            return None
        return self.analyze_function(function, timeout)

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
        functions = function_manager.getFunctions(True)
        
        for func in functions:
            if func.getName() == function_name:
                return func

        match = re.fullmatch(r"(?:thunk_)?FUN_([0-9a-fA-F]+)", function_name or "")
        if not match:
            return None

        try:
            addr_value = int(match.group(1), 16)
            default_space = self.program.getAddressFactory().getDefaultAddressSpace()
            addr = default_space.getAddress(addr_value)
        except Exception:
            return None

        func = function_manager.getFunctionAt(addr)
        if func is None:
            func = function_manager.getFunctionContaining(addr)
        return func
