# -*- coding: utf-8 -*-
"""等価性判定メインロジック（デバッグ強化版）"""

from typing import Optional, Dict, Any, List
from dataclasses import dataclass, field
import time

from ..return_analyzer import FunctionReturnAnalysis
from ..smt.parallel_runner import ParallelSolverRunner, ParallelResult
from ..smt.solver_interface import SolverStatus
from .formula_builder import FormulaBuilder
from .counterexample import CounterexampleFormatter, FormattedCounterexample


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
    upper_bits_mode: str = "free"  # "free" or "zero"
    
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
        }
    
    def to_string(self, verbose: bool = False) -> str:
        """結果を文字列で返す"""
        lines = []
        lines.append("=" * 70)
        lines.append("EQUIVALENCE CHECK RESULT")
        lines.append("=" * 70)
        lines.append(f"Binary 1: {self.binary1_name}")
        lines.append(f"Function 1: {self.function1_name}")
        lines.append(f"Binary 2: {self.binary2_name}")
        lines.append(f"Function 2: {self.function2_name}")
        lines.append(f"Upper bits mode: {self.upper_bits_mode}")
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
        upper_bits_zero: bool = False
    ):
        """
        Args:
            timeout: SMTソルバーのタイムアウト（秒）
            debug: デバッグモード
            upper_bits_zero: ビット幅が異なる場合に上位ビットを0に制約するか
                             False（デフォルト）: 上位ビットは自由（ランダム）
                             True: 上位ビットは0に制約
        """
        self.timeout = timeout
        self.debug = debug
        self.upper_bits_zero = upper_bits_zero
        self.formula_builder = FormulaBuilder(debug=debug, upper_bits_zero=upper_bits_zero)
        self.solver_runner = ParallelSolverRunner(timeout=timeout, debug=debug)
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[EquivalenceChecker] {msg}")
    
    def check(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        binary1_name: str = "binary1",
        binary2_name: str = "binary2",
        save_formula: bool = False
    ) -> EquivalenceResult:
        """
        2つの関数の等価性を判定
        """
        start_time = time.time()
        upper_bits_mode = "zero" if self.upper_bits_zero else "free"
        
        try:
            # SMT式を構築
            smt_formula, return_var1, return_var2 = self.formula_builder.build_equivalence_formula(
                analysis1, analysis2
            )
            
            if self.debug:
                print("\n" + "=" * 60)
                print("Generated SMT formula:")
                print("=" * 60)
                print(smt_formula)
                print("=" * 60 + "\n")
            
            # 利用可能なソルバーを確認
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
                    upper_bits_mode=upper_bits_mode
                )
            
            if self.debug:
                print(f"Available solvers: {available_solvers}")
                print("Starting parallel solver execution...")
            
            # 並列実行
            parallel_result = self.solver_runner.run_parallel(smt_formula)

            # デバック用
            if self.debug:
                print("Using sequential execution for debugging...", flush=True)
            parallel_result = self.solver_runner.run_sequential(smt_formula)
            
            total_time = time.time() - start_time
            
            # 反例のフォーマット
            counterexample = None
            if parallel_result.is_equivalent is False:
                raw_model = parallel_result.get_counterexample()
                self._debug_print(f"Raw counterexample model: {raw_model}")
                
                if raw_model:
                    # パラメータ名を収集（サフィックス付き）
                    param_names = []
                    for p in analysis1.parameters:
                        param_names.append(f"{p.get('name', 'param')}_1")
                    for p in analysis2.parameters:
                        param_names.append(f"{p.get('name', 'param')}_2")
                    
                    self._debug_print(f"Parameter names for formatting: {param_names}")
                    
                    counterexample = CounterexampleFormatter.format(
                        raw_model,
                        param_names,
                        return_var1,
                        return_var2
                    )
                else:
                    self._debug_print("No model available from solvers")
            
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
                upper_bits_mode=upper_bits_mode
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
                upper_bits_mode=upper_bits_mode
            )
    
    def check_from_binaries(
        self,
        program1,
        program2,
        function_name1: str,
        function_name2: str,
        decompile_timeout: int = 60,
        save_formula: bool = False
    ) -> EquivalenceResult:
        """
        2つのバイナリから関数を解析して等価性を判定
        
        Args:
            program1: Ghidra Program オブジェクト1
            program2: Ghidra Program オブジェクト2
            function_name1: 関数名1
            function_name2: 関数名2
            decompile_timeout: デコンパイルのタイムアウト
            save_formula: SMT式を結果に含めるか
        """
        from ..return_analyzer import ReturnAnalyzer
        
        start_time = time.time()
        binary1_name = program1.getName() if hasattr(program1, 'getName') else "binary1"
        binary2_name = program2.getName() if hasattr(program2, 'getName') else "binary2"
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
                    upper_bits_mode=upper_bits_mode
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
                    upper_bits_mode=upper_bits_mode
                )
        finally:
            analyzer2.dispose()
        
        # 等価性チェック
        return self.check(
            analysis1, analysis2,
            binary1_name, binary2_name,
            save_formula
        )