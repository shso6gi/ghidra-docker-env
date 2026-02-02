# -*- coding: utf-8 -*-
"""Return解析メインモジュール"""

from typing import List, Dict, Optional, Any
from .expression import Expression, ExpressionType, Condition
from .pcode_tracer import PcodeTracer
from .condition_tracker import ConditionTracker
from .condition_simplifier import ConditionSimplifier


class ReturnInfo:
    """Return情報"""
    
    def __init__(
        self,
        address: str,
        value: Expression,
        conditions: Optional[List[Condition]] = None,
        branch_index: Optional[int] = None
    ):
        self.address = address
        self.value = value
        self.conditions = conditions or []
        self.branch_index = branch_index
    
    def to_dict(self) -> Dict:
        return {
            "address": self.address,
            "value": self.value.to_dict(),
            "value_string": self.value.to_string(),
            "value_smt": self.value.to_smt(),
            "conditions": [c.to_string() for c in self.conditions],
            "conditions_smt": [c.to_smt() for c in self.conditions],
            "branch_index": self.branch_index,
        }


class FunctionReturnAnalysis:
    """関数のReturn解析結果"""
    
    def __init__(
        self,
        function_name: str,
        entry_point: str,
        parameters: List[Dict],
        returns: List[ReturnInfo],
        return_type: Optional[str] = None
    ):
        self.function_name = function_name
        self.entry_point = entry_point
        self.parameters = parameters
        self.returns = returns
        self.return_type = return_type
    
    def get_signature_string(self) -> str:
        """関数シグネチャを文字列で取得（例: int func(int a, long b)）"""
        ret_type = self.return_type or "unknown"
        
        if not self.parameters:
            params_str = "void"
        else:
            param_strs = []
            for p in self.parameters:
                dtype = p.get("data_type", "unknown")
                name = p.get("name", "")
                if name:
                    param_strs.append(f"{dtype} {name}")
                else:
                    param_strs.append(dtype)
            params_str = ", ".join(param_strs)
        
        return f"{ret_type} {self.function_name}({params_str})"
    
    def to_dict(self) -> Dict:
        return {
            "function_name": self.function_name,
            "entry_point": self.entry_point,
            "return_type": self.return_type,
            "parameters": self.parameters,
            "returns": [r.to_dict() for r in self.returns],
            "signature": self.get_signature_string(),
        }


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
            return_type=return_type
        )
    
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
        params = []
        local_map = high_function.getLocalSymbolMap()
        
        if local_map:
            for sym in local_map.getSymbols():
                if sym.isParameter():
                    param_info = {
                        "name": sym.getName(),
                        "data_type": str(sym.getDataType()) if sym.getDataType() else None,
                        "size": sym.getSize(),
                    }
                    try:
                        param_info["index"] = sym.getCategoryIndex()
                    except:
                        param_info["index"] = -1
                    params.append(param_info)
        
        params.sort(key=lambda x: x.get("index", -1))
        return params
    
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
        from .expression_expander import ExpressionExpander
        
        tracer.clear_cache()
        
        # MULTIEQUALが含まれるかチェック
        has_multiequal = self._contains_multiequal(return_varnode)
        
        if has_multiequal:
            self._debug_print("Return value contains MULTIEQUAL - conditions from PHI")
            # MULTIEQUALがある場合、パス条件は不要（MULTIEQUALが条件を提供）
            expander = ExpressionExpander(tracer, condition_tracker, debug=self.debug)
            expanded_values = expander.expand_from_varnode(return_varnode, [])
        else:
            self._debug_print("Return value has no MULTIEQUAL - using path conditions")
            # MULTIEQUALがない場合、パス条件を使用
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
        
        # 入力を再帰的にチェック
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