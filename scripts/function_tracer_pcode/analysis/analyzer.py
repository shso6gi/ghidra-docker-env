# -*- coding: utf-8 -*-
"""Return解析メインモジュール（符号性検出統合版）"""

from typing import List, Dict, Optional, Any

from ..model.expression import Expression, ExpressionType, Condition
from ..model.analysis import ReturnInfo, FunctionReturnAnalysis, SignednessResult
from . import PcodeTracer
from .condition import ConditionTracker, ConditionSimplifier
from .signedness import SignednessDetector


class ReturnAnalyzer:
    """関数のReturn値を解析"""
    
    def __init__(self, program, debug: bool = False):
        self.program = program
        self.debug = debug
        self._decompiler = None
    
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
    
    def analyze_function(self, function, timeout: int = 60) -> Optional[FunctionReturnAnalysis]:
         # デバッグフラグを ConditionSimplifier に伝播
        from .condition import ConditionSimplifier
        ConditionSimplifier.DEBUG = self.debug
        
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
        self._debug_print(f"Parameters: {[p['name'] for p in parameters]}")
        
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
            infos = self._analyze_return_op(return_op, tracer, condition_tracker, i)
            return_infos.extend(infos)
        
        result = FunctionReturnAnalysis(
            function_name=function.getName(),
            entry_point=str(function.getEntryPoint()),
            parameters=parameters,
            returns=return_infos,
            return_type=return_type,
            signedness_result=signedness_result
        )
        
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
        return_index: int
    ) -> List[ReturnInfo]:
        """単一のRETURNを解析"""
        seq = return_op.getSeqnum()
        address = str(seq.getTarget()) if seq else "unknown"
        
        num_inputs = return_op.getNumInputs()
        self._debug_print(f"RETURN at {address}, inputs: {num_inputs}")
        
        # RETURNへのパス条件を取得
        path_conditions = condition_tracker.get_path_conditions_to_return(return_op)
        
        if self.debug and path_conditions:
            cond_strs = [ConditionSimplifier.get_simplified_condition_string(c) for c in path_conditions]
            self._debug_print(f"Path conditions to RETURN: {cond_strs}")
        
        if num_inputs >= 2:
            return_varnode = return_op.getInput(1)
            return self._analyze_return_value(
                return_varnode, address, tracer, condition_tracker, path_conditions, return_index
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
        return_index: int
    ) -> List[ReturnInfo]:
        """Return値を解析"""
        from ..transform import ExpressionExpander
        
        tracer.clear_cache()
        
        # MULTIEQUALが含まれるかチェック
        has_multiequal = self._contains_multiequal(return_varnode)
        
        if has_multiequal:
            self._debug_print("Return value contains MULTIEQUAL - using PHI-based expansion")
            expander = ExpressionExpander(tracer, condition_tracker, debug=self.debug)
            # PHI内部で複数パスを考慮
            expanded_values = expander.expand_from_varnode(return_varnode, [])
        else:
            self._debug_print("Return value has no MULTIEQUAL - using path conditions")
            expander = ExpressionExpander(tracer, condition_tracker, debug=self.debug)
            expanded_values = expander.expand_from_varnode(return_varnode, path_conditions)
        
        self._debug_print(f"Expanded to {len(expanded_values)} candidate(s)")
        
        results = []
        for i, ev in enumerate(expanded_values):
            if not ev.is_valid():
                self._debug_print(f"Skipping contradictory expansion {i}")
                continue
            
            simplified_conds = ConditionSimplifier.simplify_conditions(ev.conditions)
            
            if self.debug:
                cond_strs = [ConditionSimplifier.get_simplified_condition_string(c) for c in simplified_conds]
                self._debug_print(f"Expansion {i}: value={ev.value.to_string()}")
                self._debug_print(f"  conditions={cond_strs}")
            
            results.append(ReturnInfo(
                address=address,
                value=ev.value,
                conditions=simplified_conds,
                branch_index=return_index * 100 + i
            ))
        
        if not results:
            self._debug_print("WARNING: No valid expansions, falling back to simple trace")
            value = tracer.trace_varnode(return_varnode, use_cache=False)
            simplified_conds = ConditionSimplifier.simplify_conditions(path_conditions)
            return [ReturnInfo(
                address=address,
                value=value,
                conditions=simplified_conds,
                branch_index=return_index
            )]
        
        return results

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
    
    def _find_function_by_name(self, function_name: str):
        function_manager = self.program.getFunctionManager()
        functions = function_manager.getFunctions(True)
        
        for func in functions:
            if func.getName() == function_name:
                return func
        return None