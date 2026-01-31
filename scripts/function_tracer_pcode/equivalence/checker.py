# -*- coding: utf-8 -*-
"""等価性判定メインロジック（型修正リトライ対応版）"""

from typing import Optional, Dict, Any, List
from dataclasses import dataclass, field
import time

from ..return_analyzer import FunctionReturnAnalysis
from ..smt.parallel_runner import ParallelSolverRunner, ParallelResult
from ..smt.solver_interface import SolverStatus
from .formula_builder import FormulaBuilder
from .counterexample import CounterexampleFormatter, FormattedCounterexample
from .type_fixer import TypeFixer, TypeFixerConfig, TypeFixResult


@dataclass
class EquivalenceResult:
    """等価性判定の結果"""
    is_equivalent: Optional[bool]
    function1_name: str
    function2_name: str
    binary1_name: str
    binary2_name: str
    solver_results: ParallelResult
    counterexample: Optional[FormattedCounterexample] = None
    smt_formula: Optional[str] = None
    total_time: float = 0.0
    error_message: Optional[str] = None
    upper_bits_mode: str = "free"
    type_fix_result: Optional[TypeFixResult] = None
    retry_count: int = 0
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "is_equivalent": self.is_equivalent,
            "function1_name": self.function1_name,
            "function2_name": self.function2_name,
            "binary1_name": self.binary1_name,
            "binary2_name": self.binary2_name,
            "solver_results": self.solver_results.to_dict() if self.solver_results else None,
            "counterexample": self.counterexample.to_string("json") if self.counterexample else None,
            "total_time": self.total_time,
            "error_message": self.error_message,
            "upper_bits_mode": self.upper_bits_mode,
            "type_fix_result": self.type_fix_result.to_dict() if self.type_fix_result else None,
            "retry_count": self.retry_count,
        }
    
    def to_string(self, verbose: bool = False) -> str:
        lines = []
        lines.append("=" * 70)
        lines.append("EQUIVALENCE CHECK RESULT")
        lines.append("=" * 70)
        lines.append(f"Binary 1: {self.binary1_name}")
        lines.append(f"Function 1: {self.function1_name}")
        lines.append(f"Binary 2: {self.binary2_name}")
        lines.append(f"Function 2: {self.function2_name}")
        lines.append(f"Upper bits mode: {self.upper_bits_mode}")
        
        if self.type_fix_result and self.type_fix_result.any_fix_applied():
            lines.append(f"Type fix applied: {self.type_fix_result}")
        if self.retry_count > 0:
            lines.append(f"Retry count: {self.retry_count}")
        
        lines.append("-" * 70)
        
        if self.error_message:
            lines.append(f"ERROR: {self.error_message}")
        elif self.is_equivalent is None:
            lines.append("Result: UNKNOWN (could not determine equivalence)")
        elif self.is_equivalent:
            lines.append("Result: EQUIVALENT ✓")
        else:
            lines.append("Result: NOT EQUIVALENT ✗")
            if self.counterexample:
                lines.append("")
                lines.append(self.counterexample.to_string())
            else:
                lines.append("")
                lines.append("(No counterexample available)")
        
        lines.append("-" * 70)
        lines.append(f"Total time: {self.total_time:.3f} seconds")
        
        if verbose and self.solver_results:
            lines.append("")
            lines.append("Solver Results:")
            for sr in self.solver_results.results:
                status_str = sr.status.name
                lines.append(f"  {sr.solver_name}: {status_str} ({sr.elapsed_time:.3f}s)")
                if sr.error_message:
                    lines.append(f"    Error: {sr.error_message}")
                if sr.model:
                    lines.append(f"    Model: {sr.model}")
        
        lines.append("=" * 70)
        return "\n".join(lines)


class EquivalenceChecker:
    """等価性判定を行うクラス"""
    
    def __init__(
        self,
        timeout: int = 180,
        debug: bool = False,
        upper_bits_zero: bool = False,
        type_fixer_config: Optional[TypeFixerConfig] = None
    ):
        self.timeout = timeout
        self.debug = debug
        self.upper_bits_zero = upper_bits_zero
        self.type_fixer_config = type_fixer_config or TypeFixerConfig()
        self.formula_builder = FormulaBuilder(debug=debug, upper_bits_zero=upper_bits_zero)
        self.solver_runner = ParallelSolverRunner(timeout=timeout, debug=debug)
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[EquivalenceChecker] {msg}")
    
    def _get_params_via_decompile(
        self,
        program,
        function_name: str,
        timeout: int
    ) -> List[Dict[str, Any]]:
        """
        デコンパイルして引数情報を取得
        
        Returns:
            [{"name": str, "data_type": str, "size": int, "index": int}, ...]
        """
        from ..return_analyzer import ReturnAnalyzer
        
        self._debug_print(f"Getting params via decompile for '{function_name}'")
        
        analyzer = ReturnAnalyzer(program, debug=self.debug)
        try:
            analysis = analyzer.analyze_function_by_name(function_name, timeout)
            if analysis and analysis.parameters:
                self._debug_print(f"Found {len(analysis.parameters)} parameters")
                return analysis.parameters
            self._debug_print("No parameters found")
            return []
        finally:
            analyzer.dispose()
    
    def check(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        binary1_name: str = "binary1",
        binary2_name: str = "binary2",
        save_formula: bool = False,
        type_fix_result: Optional[TypeFixResult] = None,
        retry_count: int = 0
    ) -> EquivalenceResult:
        """2つの関数の等価性を判定"""
        start_time = time.time()
        upper_bits_mode = "zero" if self.upper_bits_zero else "free"
        
        try:
            smt_formula, return_var1, return_var2 = self.formula_builder.build_equivalence_formula(
                analysis1, analysis2
            )
            
            if self.debug:
                print("\n" + "=" * 60)
                print("Generated SMT formula:")
                print("=" * 60)
                print(smt_formula)
                print("=" * 60 + "\n")
            
            available_solvers = self.solver_runner.get_available_solvers()
            if not available_solvers:
                return EquivalenceResult(
                    is_equivalent=None,
                    function1_name=analysis1.function_name,
                    function2_name=analysis2.function_name,
                    binary1_name=binary1_name,
                    binary2_name=binary2_name,
                    solver_results=ParallelResult(results=[]),
                    total_time=time.time() - start_time,
                    error_message="No SMT solvers available",
                    upper_bits_mode=upper_bits_mode,
                    type_fix_result=type_fix_result,
                    retry_count=retry_count
                )
            
            if self.debug:
                print(f"Available solvers: {available_solvers}")
                self._debug_print("Using sequential execution for debugging...")
                parallel_result = self.solver_runner.run_sequential(smt_formula)
            else:
                parallel_result = self.solver_runner.run_parallel(smt_formula)
            
            total_time = time.time() - start_time
            
            counterexample = None
            if parallel_result.is_equivalent is False:
                raw_model = parallel_result.get_counterexample()
                self._debug_print(f"Raw counterexample model: {raw_model}")
                
                if raw_model:
                    param_names = []
                    for p in analysis1.parameters:
                        param_names.append(f"{p.get('name', 'param')}_1")
                    for p in analysis2.parameters:
                        param_names.append(f"{p.get('name', 'param')}_2")
                    
                    counterexample = CounterexampleFormatter.format(
                        raw_model,
                        param_names,
                        return_var1,
                        return_var2
                    )
            
            return EquivalenceResult(
                is_equivalent=parallel_result.is_equivalent,
                function1_name=analysis1.function_name,
                function2_name=analysis2.function_name,
                binary1_name=binary1_name,
                binary2_name=binary2_name,
                solver_results=parallel_result,
                counterexample=counterexample,
                smt_formula=smt_formula if save_formula else None,
                total_time=total_time,
                upper_bits_mode=upper_bits_mode,
                type_fix_result=type_fix_result,
                retry_count=retry_count
            )
        
        except Exception as e:
            self._debug_print(f"Exception in check: {e}")
            if self.debug:
                import traceback
                print(traceback.format_exc())
            
            return EquivalenceResult(
                is_equivalent=None,
                function1_name=analysis1.function_name,
                function2_name=analysis2.function_name,
                binary1_name=binary1_name,
                binary2_name=binary2_name,
                solver_results=ParallelResult(results=[]),
                total_time=time.time() - start_time,
                error_message=str(e),
                upper_bits_mode=upper_bits_mode,
                type_fix_result=type_fix_result,
                retry_count=retry_count
            )
    
    def check_from_binaries(
        self,
        program1,
        program2,
        function_name1: str,
        function_name2: str,
        decompile_timeout: int = 60,
        save_formula: bool = False,
        retry_with_type_fix: bool = False
    ) -> EquivalenceResult:
        """2つのバイナリから関数を解析して等価性を判定"""
        start_time = time.time()
        binary1_name = program1.getName() if hasattr(program1, 'getName') else "binary1"
        binary2_name = program2.getName() if hasattr(program2, 'getName') else "binary2"
        
        type_fix_result = TypeFixResult()
        retry_count = 0
        
        if retry_with_type_fix:
            self._debug_print("=== Pre-analysis: Getting parameter info via decompile ===")
            
            # 最初にデコンパイルして引数情報を取得
            params1 = self._get_params_via_decompile(program1, function_name1, decompile_timeout)
            params2 = self._get_params_via_decompile(program2, function_name2, decompile_timeout)
            
            self._debug_print(f"Binary 1 params: {params1}")
            self._debug_print(f"Binary 2 params: {params2}")
            
            # 型修正が必要かチェック
            type_fixer1 = TypeFixer(program1, self.type_fixer_config, debug=self.debug)
            type_fixer2 = TypeFixer(program2, self.type_fixer_config, debug=self.debug)
            
            ret_needs_fix1, param_needs_fix1 = type_fixer1.check_needs_fix_with_params(
                function_name1, params1
            )
            ret_needs_fix2, param_needs_fix2 = type_fixer2.check_needs_fix_with_params(
                function_name2, params2
            )
            
            self._debug_print(f"Binary 1 needs fix: return={ret_needs_fix1}, params={param_needs_fix1}")
            self._debug_print(f"Binary 2 needs fix: return={ret_needs_fix2}, params={param_needs_fix2}")
            
            # 型修正を実行（引数情報を使用）
            if ret_needs_fix1 or param_needs_fix1 or ret_needs_fix2 or param_needs_fix2:
                self._debug_print("=== Fixing function signatures ===")
                type_fix_result.retry_phase = "signature_fix"
                
                if ret_needs_fix1 or param_needs_fix1:
                    ret_fixed1, param_fixed1 = type_fixer1.fix_function_signature_by_name(
                        function_name1,
                        params1,
                        fix_return_type=ret_needs_fix1,
                        fix_param_types=param_needs_fix1
                    )
                    type_fix_result.return_type_fixed_binary1 = ret_fixed1
                    type_fix_result.param_types_fixed_binary1 = param_fixed1
                
                if ret_needs_fix2 or param_needs_fix2:
                    ret_fixed2, param_fixed2 = type_fixer2.fix_function_signature_by_name(
                        function_name2,
                        params2,
                        fix_return_type=ret_needs_fix2,
                        fix_param_types=param_needs_fix2
                    )
                    type_fix_result.return_type_fixed_binary2 = ret_fixed2
                    type_fix_result.param_types_fixed_binary2 = param_fixed2
                
                retry_count += 1
        
        # 等価性判定を実行
        result = self._analyze_and_check(
            program1, program2,
            function_name1, function_name2,
            decompile_timeout, save_formula,
            binary1_name, binary2_name,
            type_fix_result=type_fix_result,
            retry_count=retry_count
        )
        
        result.total_time = time.time() - start_time
        return result
    
    def _analyze_and_check(
        self,
        program1,
        program2,
        function_name1: str,
        function_name2: str,
        decompile_timeout: int,
        save_formula: bool,
        binary1_name: str,
        binary2_name: str,
        type_fix_result: Optional[TypeFixResult] = None,
        retry_count: int = 0
    ) -> EquivalenceResult:
        """関数を解析して等価性をチェック（内部メソッド）"""
        from ..return_analyzer import ReturnAnalyzer
        
        start_time = time.time()
        upper_bits_mode = "zero" if self.upper_bits_zero else "free"
        
        # 関数1を解析
        analyzer1 = ReturnAnalyzer(program1, debug=self.debug)
        try:
            analysis1 = analyzer1.analyze_function_by_name(function_name1, decompile_timeout)
            if analysis1 is None:
                return EquivalenceResult(
                    is_equivalent=None,
                    function1_name=function_name1,
                    function2_name=function_name2,
                    binary1_name=binary1_name,
                    binary2_name=binary2_name,
                    solver_results=ParallelResult(results=[]),
                    total_time=time.time() - start_time,
                    error_message=f"Function '{function_name1}' not found in {binary1_name}",
                    upper_bits_mode=upper_bits_mode,
                    type_fix_result=type_fix_result,
                    retry_count=retry_count
                )
        finally:
            analyzer1.dispose()
        
        # 関数2を解析
        analyzer2 = ReturnAnalyzer(program2, debug=self.debug)
        try:
            analysis2 = analyzer2.analyze_function_by_name(function_name2, decompile_timeout)
            if analysis2 is None:
                return EquivalenceResult(
                    is_equivalent=None,
                    function1_name=function_name1,
                    function2_name=function_name2,
                    binary1_name=binary1_name,
                    binary2_name=binary2_name,
                    solver_results=ParallelResult(results=[]),
                    total_time=time.time() - start_time,
                    error_message=f"Function '{function_name2}' not found in {binary2_name}",
                    upper_bits_mode=upper_bits_mode,
                    type_fix_result=type_fix_result,
                    retry_count=retry_count
                )
        finally:
            analyzer2.dispose()
        
        return self.check(
            analysis1, analysis2,
            binary1_name, binary2_name,
            save_formula,
            type_fix_result=type_fix_result,
            retry_count=retry_count
        )