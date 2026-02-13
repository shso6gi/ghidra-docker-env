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
    
    def analyze_function(self, function, timeout: int = 60) -> Optional[FunctionReturnAnalysis]:
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
        
        tracer = PcodeTracer(self.program, high_function, debug=self.debug)
        condition_tracker = ConditionTracker(tracer)
        
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
        
        return FunctionReturnAnalysis(
            function_name=function.getName(),
            entry_point=str(function.getEntryPoint()),
            parameters=parameters,
            returns=return_infos,
            return_type=return_type,
            signedness_result=signedness_result
        )
    
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
            self._debug_print("Return value contains MULTIEQUAL - conditions from PHI")
            expander = ExpressionExpander(tracer, condition_tracker, debug=self.debug)
            expanded_values = expander.expand_from_varnode(return_varnode, [])
        else:
            self._debug_print("Return value has no MULTIEQUAL - using path conditions")
            expander = ExpressionExpander(tracer, condition_tracker, debug=self.debug)
            expanded_values = expander.expand_from_varnode(return_varnode, path_conditions)
        
        self._debug_print(f"Expanded to {len(expanded_values)} values")
        
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
            self._debug_print("No valid expansions, falling back to simple trace")
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