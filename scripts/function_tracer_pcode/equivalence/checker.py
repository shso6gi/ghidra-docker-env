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
    
    def is_timeout(self) -> bool:
        """タイムアウトで結果が不明かどうかを判定"""
        if self.is_equivalent is not None:
            return False
        if not self.solver_results or not self.solver_results.results:
            return False
        # いずれかのソルバーがタイムアウトしたかチェック
        for sr in self.solver_results.results:
            if sr.status == SolverStatus.TIMEOUT:
                return True
        return False
    
    def is_unknown(self) -> bool:
        """結果が不明（タイムアウト含む）かどうかを判定"""
        return self.is_equivalent is None and self.error_message is None
    
    def has_critical_error(self) -> bool:
        """致命的なエラー（リトライ不可能）があるかどうかを判定"""
        if self.error_message is None:
            return False
        # 関数が見つからないなどのエラーはリトライしても解決しない
        critical_keywords = ["not found", "not available", "No SMT solvers"]
        return any(kw in self.error_message for kw in critical_keywords)
    
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
            "is_timeout": self.is_timeout(),
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
            if self.is_timeout():
                lines.append("Result: TIMEOUT (could not determine equivalence within time limit)")
            else:
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
    
    def _should_retry(self, result: EquivalenceResult) -> bool:
        """
        リトライすべきかどうかを判定
        
        リトライする条件:
        - 非等価 (is_equivalent == False)
        - タイムアウトまたは不明 (is_equivalent == None かつ致命的エラーなし)
        
        リトライしない条件:
        - 等価 (is_equivalent == True)
        - 致命的エラー（関数が見つからないなど）
        """
        # 等価の場合はリトライ不要
        if result.is_equivalent is True:
            return False
        
        # 致命的エラーの場合はリトライしても解決しない
        if result.has_critical_error():
            return False
        
        # 非等価、タイムアウト、不明の場合はリトライ
        return True
    
    def _get_retry_reason(self, result: EquivalenceResult) -> str:
        """リトライの理由を取得（デバッグ用）"""
        if result.is_equivalent is False:
            return "NOT EQUIVALENT"
        elif result.is_timeout():
            return "TIMEOUT"
        elif result.is_equivalent is None:
            return "UNKNOWN"
        else:
            return "EQUIVALENT (no retry needed)"
    
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
        """
        2つのバイナリから関数を解析して等価性を判定
        
        型修正リトライが有効な場合のフロー:
        1. Phase 0: 型修正なしで等価性判定
        2. Phase 1: 非等価またはタイムアウトの場合、戻り値の型を修正してリトライ
        3. Phase 2: それでも非等価またはタイムアウトの場合、引数の型も修正してリトライ
        4. 最終結果: それでも非等価の場合は反例を表示、タイムアウトの場合はその旨を表示
        """
        start_time = time.time()
        binary1_name = program1.getName() if hasattr(program1, 'getName') else "binary1"
        binary2_name = program2.getName() if hasattr(program2, 'getName') else "binary2"
        
        type_fix_result = TypeFixResult()
        
        # ============================================
        # Phase 0: 型修正なしで等価性判定
        # ============================================
        self._debug_print("=" * 60)
        self._debug_print("Phase 0: Initial check without type fix")
        self._debug_print("=" * 60)
        type_fix_result.retry_phase = "initial"
        
        result = self._analyze_and_check(
            program1, program2,
            function_name1, function_name2,
            decompile_timeout, save_formula,
            binary1_name, binary2_name,
            type_fix_result=type_fix_result,
            retry_count=0
        )
        
        # 等価の場合は終了
        if result.is_equivalent is True:
            self._debug_print("Phase 0: EQUIVALENT - No retry needed")
            result.total_time = time.time() - start_time
            return result
        
        # リトライ判定
        should_retry = self._should_retry(result)
        retry_reason = self._get_retry_reason(result)
        self._debug_print(f"Phase 0 result: {retry_reason}")
        
        # 致命的エラーまたはリトライ無効の場合は終了
        if not should_retry:
            self._debug_print("Phase 0: Critical error - cannot retry")
            result.total_time = time.time() - start_time
            return result
        
        if not retry_with_type_fix:
            self._debug_print("Phase 0: Retry disabled - returning result")
            result.total_time = time.time() - start_time
            return result
        
        self._debug_print(f"Phase 0: {retry_reason} - preparing for type fix retry")
        
        # 型修正に必要な情報を事前に収集
        self._debug_print("Collecting parameter information for type fix...")
        params1 = self._get_params_via_decompile(program1, function_name1, decompile_timeout)
        params2 = self._get_params_via_decompile(program2, function_name2, decompile_timeout)
        
        type_fixer1 = TypeFixer(program1, self.type_fixer_config, debug=self.debug)
        type_fixer2 = TypeFixer(program2, self.type_fixer_config, debug=self.debug)
        
        ret_needs_fix1, param_needs_fix1 = type_fixer1.check_needs_fix_with_params(
            function_name1, params1
        )
        ret_needs_fix2, param_needs_fix2 = type_fixer2.check_needs_fix_with_params(
            function_name2, params2
        )
        
        self._debug_print(f"Binary 1 '{function_name1}' - return needs fix: {ret_needs_fix1}, params need fix: {param_needs_fix1}")
        self._debug_print(f"Binary 2 '{function_name2}' - return needs fix: {ret_needs_fix2}, params need fix: {param_needs_fix2}")
        
        # 型修正が不要な場合はPhase 0の結果を返す
        if not (ret_needs_fix1 or ret_needs_fix2 or param_needs_fix1 or param_needs_fix2):
            self._debug_print("No type fix needed for either binary - returning Phase 0 result")
            result.total_time = time.time() - start_time
            return result
        
        # ============================================
        # Phase 1: 戻り値の型を修正してリトライ
        # ============================================
        if ret_needs_fix1 or ret_needs_fix2:
            self._debug_print("=" * 60)
            self._debug_print("Phase 1: Fixing return types only")
            self._debug_print("=" * 60)
            type_fix_result.retry_phase = "return_type_fix"
            
            if ret_needs_fix1:
                ret_fixed1, _ = type_fixer1.fix_function_signature_by_name(
                    function_name1,
                    params1,
                    fix_return_type=True,
                    fix_param_types=False
                )
                type_fix_result.return_type_fixed_binary1 = ret_fixed1
                self._debug_print(f"Binary 1 return type fixed: {ret_fixed1}")
            
            if ret_needs_fix2:
                ret_fixed2, _ = type_fixer2.fix_function_signature_by_name(
                    function_name2,
                    params2,
                    fix_return_type=True,
                    fix_param_types=False
                )
                type_fix_result.return_type_fixed_binary2 = ret_fixed2
                self._debug_print(f"Binary 2 return type fixed: {ret_fixed2}")
            
            # 再解析と等価性判定
            result = self._analyze_and_check(
                program1, program2,
                function_name1, function_name2,
                decompile_timeout, save_formula,
                binary1_name, binary2_name,
                type_fix_result=type_fix_result,
                retry_count=1
            )
            
            # 等価の場合は終了
            if result.is_equivalent is True:
                self._debug_print("Phase 1: EQUIVALENT after return type fix")
                result.total_time = time.time() - start_time
                return result
            
            # リトライ判定
            should_retry = self._should_retry(result)
            retry_reason = self._get_retry_reason(result)
            self._debug_print(f"Phase 1 result: {retry_reason}")
            
            if not should_retry:
                self._debug_print("Phase 1: Critical error - cannot continue to Phase 2")
                result.total_time = time.time() - start_time
                return result
            
            self._debug_print(f"Phase 1: {retry_reason} - will try Phase 2")
        else:
            self._debug_print("Phase 1: Skipped - no return type fix needed")
        
        # ============================================
        # Phase 2: 引数の型も修正してリトライ
        # ============================================
        if param_needs_fix1 or param_needs_fix2:
            self._debug_print("=" * 60)
            self._debug_print("Phase 2: Fixing parameter types")
            self._debug_print("=" * 60)
            type_fix_result.retry_phase = "param_type_fix"
            
            # 戻り値修正後の状態で再度パラメータ情報を取得
            params1_updated = self._get_params_via_decompile(program1, function_name1, decompile_timeout)
            params2_updated = self._get_params_via_decompile(program2, function_name2, decompile_timeout)
            
            if param_needs_fix1:
                _, param_fixed1 = type_fixer1.fix_function_signature_by_name(
                    function_name1,
                    params1_updated,
                    fix_return_type=False,
                    fix_param_types=True
                )
                type_fix_result.param_types_fixed_binary1 = param_fixed1
                self._debug_print(f"Binary 1 param types fixed: {param_fixed1}")
            
            if param_needs_fix2:
                _, param_fixed2 = type_fixer2.fix_function_signature_by_name(
                    function_name2,
                    params2_updated,
                    fix_return_type=False,
                    fix_param_types=True
                )
                type_fix_result.param_types_fixed_binary2 = param_fixed2
                self._debug_print(f"Binary 2 param types fixed: {param_fixed2}")
            
            # 再解析と等価性判定
            result = self._analyze_and_check(
                program1, program2,
                function_name1, function_name2,
                decompile_timeout, save_formula,
                binary1_name, binary2_name,
                type_fix_result=type_fix_result,
                retry_count=2
            )
            
            # 結果のログ出力
            if result.is_equivalent is True:
                self._debug_print("Phase 2: EQUIVALENT after parameter type fix")
            elif result.is_equivalent is False:
                self._debug_print("Phase 2: NOT EQUIVALENT - returning final result with counterexample")
            elif result.is_timeout():
                self._debug_print("Phase 2: TIMEOUT - returning final result")
            else:
                self._debug_print("Phase 2: UNKNOWN - returning final result")
        else:
            self._debug_print("Phase 2: Skipped - no parameter type fix needed")
        
        # ============================================
        # 最終結果
        # ============================================
        self._debug_print("=" * 60)
        self._debug_print("Final Result")
        self._debug_print("=" * 60)
        
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
        self._debug_print(f"Analyzing function '{function_name1}' in {binary1_name}...")
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
        self._debug_print(f"Analyzing function '{function_name2}' in {binary2_name}...")
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
        
        self._debug_print("Running equivalence check...")
        return self.check(
            analysis1, analysis2,
            binary1_name, binary2_name,
            save_formula,
            type_fix_result=type_fix_result,
            retry_count=retry_count
        )