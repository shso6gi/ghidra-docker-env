# -*- coding: utf-8 -*-
"""等価性判定メインロジック（リライト機能統合版）"""

from typing import Optional, Dict, Any, List, Tuple
from dataclasses import dataclass, field
import time

from ..return_analyzer import FunctionReturnAnalysis
from ..smt.parallel_runner import ParallelSolverRunner, ParallelResult
from ..smt.solver_interface import SolverStatus
from .formula_builder import FormulaBuilder
from .counterexample import CounterexampleFormatter, FormattedCounterexample
from .type_fixer import TypeFixer, TypeFixerConfig, TypeFixResult
from .expression_rewriter import ExpressionRewriter, RewriteResult, rewrite_analysis_returns


@dataclass
class FunctionSignature:
    """関数シグネチャ情報"""
    return_type: Optional[str] = None
    parameters: Optional[List[Dict[str, Any]]] = None
    
    def format_return_type(self) -> str:
        """戻り値の型をフォーマット"""
        return self.return_type if self.return_type else "unknown"
    
    def format_parameters(self) -> str:
        """引数リストをフォーマット（例: (int a, long b)）"""
        if not self.parameters:
            return "(void)"
        
        param_strs = []
        for p in self.parameters:
            dtype = p.get("data_type", "unknown")
            name = p.get("name", "")
            if name:
                param_strs.append(f"{dtype} {name}")
            else:
                param_strs.append(dtype)
        
        return f"({', '.join(param_strs)})"
    
    def format_full(self, func_name: str) -> str:
        """完全なシグネチャをフォーマット（例: int func(int a, long b)）"""
        return f"{self.format_return_type()} {func_name}{self.format_parameters()}"
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "return_type": self.return_type,
            "parameters": self.parameters
        }
    
    @classmethod
    def from_analysis(cls, analysis: FunctionReturnAnalysis) -> 'FunctionSignature':
        """FunctionReturnAnalysisからシグネチャを抽出"""
        return cls(
            return_type=analysis.return_type,
            parameters=analysis.parameters.copy() if analysis.parameters else None
        )


@dataclass
class RewriteInfo:
    """リライト情報"""
    applied: bool = False
    function1_rewrites: List[RewriteResult] = field(default_factory=list)
    function2_rewrites: List[RewriteResult] = field(default_factory=list)
    
    def get_summary(self) -> str:
        """リライトの概要を取得"""
        if not self.applied:
            return "No rewrite applied"
        
        lines = ["Rewrite applied:"]
        
        if any(r.was_rewritten for r in self.function1_rewrites):
            lines.append("  Function 1:")
            for i, r in enumerate(self.function1_rewrites):
                if r.was_rewritten:
                    for rule, before, after in r.history:
                        lines.append(f"    Return {i}: [{rule}] {before} -> {after}")
        
        if any(r.was_rewritten for r in self.function2_rewrites):
            lines.append("  Function 2:")
            for i, r in enumerate(self.function2_rewrites):
                if r.was_rewritten:
                    for rule, before, after in r.history:
                        lines.append(f"    Return {i}: [{rule}] {before} -> {after}")
        
        return "\n".join(lines)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "applied": self.applied,
            "function1_rewrites": [
                {"was_rewritten": r.was_rewritten, "history": r.history}
                for r in self.function1_rewrites
            ],
            "function2_rewrites": [
                {"was_rewritten": r.was_rewritten, "history": r.history}
                for r in self.function2_rewrites
            ],
        }


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
    type_fix_result: Optional[TypeFixResult] = None
    retry_count: int = 0
    function1_signature: Optional[FunctionSignature] = None
    function2_signature: Optional[FunctionSignature] = None
    auto_zero_constrained: List[str] = field(default_factory=list)
    rewrite_info: Optional[RewriteInfo] = None
    
    def is_timeout(self) -> bool:
        """タイムアウトで結果が不明かどうかを判定"""
        if self.is_equivalent is not None:
            return False
        if not self.solver_results or not self.solver_results.results:
            return False
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
        critical_keywords = ["not found", "not available", "No SMT solvers"]
        return any(kw in self.error_message for kw in critical_keywords)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "is_equivalent": self.is_equivalent,
            "function1_name": self.function1_name,
            "function2_name": self.function2_name,
            "binary1_name": self.binary1_name,
            "binary2_name": self.binary2_name,
            "function1_signature": self.function1_signature.to_dict() if self.function1_signature else None,
            "function2_signature": self.function2_signature.to_dict() if self.function2_signature else None,
            "solver_results": self.solver_results.to_dict() if self.solver_results else None,
            "counterexample": self.counterexample.to_string("json") if self.counterexample else None,
            "total_time": self.total_time,
            "error_message": self.error_message,
            "type_fix_result": self.type_fix_result.to_dict() if self.type_fix_result else None,
            "retry_count": self.retry_count,
            "is_timeout": self.is_timeout(),
            "auto_zero_constrained": self.auto_zero_constrained,
            "rewrite_info": self.rewrite_info.to_dict() if self.rewrite_info else None,
        }
    
    def to_string(self, verbose: bool = False) -> str:
        lines = []
        lines.append("=" * 70)
        lines.append("EQUIVALENCE CHECK RESULT")
        lines.append("=" * 70)
        
        # Binary 1 の情報
        lines.append(f"Binary 1: {self.binary1_name}")
        lines.append(f"Function 1: {self.function1_name}")
        if self.function1_signature:
            lines.append(f"  Original signature: {self.function1_signature.format_full(self.function1_name)}")
        
        lines.append("")
        
        # Binary 2 の情報
        lines.append(f"Binary 2: {self.binary2_name}")
        lines.append(f"Function 2: {self.function2_name}")
        if self.function2_signature:
            lines.append(f"  Original signature: {self.function2_signature.format_full(self.function2_name)}")
        
        lines.append("")
        
        # 自動0制約された変数を表示
        if self.auto_zero_constrained:
            vars_str = ", ".join(self.auto_zero_constrained)
            lines.append(f"Auto-simplified: {vars_str} (upper-bits variables constrained to 0)")
        
        if self.type_fix_result and self.type_fix_result.any_fix_applied():
            lines.append(f"Type fix applied: {self.type_fix_result}")
        if self.retry_count > 0:
            lines.append(f"Retry count: {self.retry_count}")
        
        # リライト情報
        if self.rewrite_info and self.rewrite_info.applied:
            lines.append("")
            lines.append(self.rewrite_info.get_summary())
        
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
        timeout: int = 10,
        debug: bool = False,
        type_fixer_config: Optional[TypeFixerConfig] = None,
        enable_rewrite: bool = True,
        rewrite_direction: str = "to_modulo"
    ):
        """
        Args:
            timeout: SMTソルバーのタイムアウト（秒）
            debug: デバッグ出力を有効にする
            type_fixer_config: 型修正の設定
            enable_rewrite: 式のリライトを有効にする
            rewrite_direction: リライト方向 ("to_modulo" or "to_expansion")
        """
        self.timeout = timeout
        self.debug = debug
        self.type_fixer_config = type_fixer_config or TypeFixerConfig()
        self.enable_rewrite = enable_rewrite
        self.rewrite_direction = rewrite_direction
        self.formula_builder = FormulaBuilder(debug=debug)
        self.solver_runner = ParallelSolverRunner(timeout=timeout, debug=debug)
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[EquivalenceChecker] {msg}")
    
    def _apply_rewrite(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis
    ) -> Tuple[FunctionReturnAnalysis, FunctionReturnAnalysis, RewriteInfo]:
        """
        両方の解析結果にリライトを適用
        
        Returns:
            (rewritten_analysis1, rewritten_analysis2, rewrite_info)
        """
        rewrite_info = RewriteInfo()
        
        if not self.enable_rewrite:
            self._debug_print("Rewrite is disabled")
            return analysis1, analysis2, rewrite_info
        
        self._debug_print(f"Applying rewrite with direction: {self.rewrite_direction}")
        
        rewriter = ExpressionRewriter(
            debug=self.debug,
            direction=self.rewrite_direction
        )
        
        # Function 1 のリライト
        rewritten1, results1 = rewrite_analysis_returns(analysis1, rewriter)
        rewrite_info.function1_rewrites = results1
        
        if any(r.was_rewritten for r in results1):
            self._debug_print(f"Function 1 was rewritten")
            rewrite_info.applied = True
            analysis1 = rewritten1
        
        # Function 2 のリライト
        rewritten2, results2 = rewrite_analysis_returns(analysis2, rewriter)
        rewrite_info.function2_rewrites = results2
        
        if any(r.was_rewritten for r in results2):
            self._debug_print(f"Function 2 was rewritten")
            rewrite_info.applied = True
            analysis2 = rewritten2
        
        return analysis1, analysis2, rewrite_info
    
    def _get_params_via_decompile(
        self,
        program,
        function_name: str,
        timeout: int
    ) -> List[Dict[str, Any]]:
        """デコンパイルして引数情報を取得"""
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
        """リトライすべきかどうかを判定"""
        if result.is_equivalent is True:
            return False
        if result.has_critical_error():
            return False
        return True
    
    def _get_retry_reason(self, result: EquivalenceResult) -> str:
        """リトライの理由を取得"""
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
        retry_count: int = 0,
        original_signature1: Optional[FunctionSignature] = None,
        original_signature2: Optional[FunctionSignature] = None
    ) -> EquivalenceResult:
        """2つの関数の等価性を判定"""
        start_time = time.time()
        
        # シグネチャが渡されなかった場合は現在の解析結果から取得
        if original_signature1 is None:
            original_signature1 = FunctionSignature.from_analysis(analysis1)
        if original_signature2 is None:
            original_signature2 = FunctionSignature.from_analysis(analysis2)
        
        try:
            # 拡張版のメソッドを使用して詳細情報を取得
            formula_result = self.formula_builder.build_equivalence_formula_extended(
                analysis1, analysis2
            )
            auto_zero_constrained = formula_result.auto_zero_constrained
            # リライトを適用
            analysis1, analysis2, rewrite_info = self._apply_rewrite(analysis1, analysis2)
            
            smt_formula, return_var1, return_var2 = self.formula_builder.build_equivalence_formula(
                analysis1, analysis2
            )
            
            if self.debug:
                print("\n" + "=" * 60)
                print("Generated SMT formula:")
                print("=" * 60)
                print(smt_formula)
                print("=" * 60 + "\n")

                if auto_zero_constrained:
                    print(f"[EquivalenceChecker] Auto-constrained to 0: {auto_zero_constrained}")
            
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
                    type_fix_result=type_fix_result,
                    retry_count=retry_count,
                    function1_signature=original_signature1,
                    function2_signature=original_signature2,
                    auto_zero_constrained=auto_zero_constrained,
                    rewrite_info=rewrite_info
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
                type_fix_result=type_fix_result,
                retry_count=retry_count,
                function1_signature=original_signature1,
                function2_signature=original_signature2,
                auto_zero_constrained=auto_zero_constrained,
                rewrite_info=rewrite_info
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
                type_fix_result=type_fix_result,
                retry_count=retry_count,
                function1_signature=original_signature1,
                function2_signature=original_signature2,
                auto_zero_constrained=[]
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
        
        # オリジナルのシグネチャを保存（型修正前）
        original_signature1: Optional[FunctionSignature] = None
        original_signature2: Optional[FunctionSignature] = None
        
        # ============================================
        # Phase 0: 型修正なしで等価性判定
        # ============================================
        self._debug_print("=" * 60)
        self._debug_print("Phase 0: Initial check without type fix")
        self._debug_print("=" * 60)
        type_fix_result.retry_phase = "initial"
        
        # 初回解析を実行し、解析結果も保持
        analysis1, analysis2, result = self._analyze_and_check_with_analysis(
            program1, program2,
            function_name1, function_name2,
            decompile_timeout, save_formula,
            binary1_name, binary2_name,
            type_fix_result=type_fix_result,
            retry_count=0
        )
        
        # オリジナルのシグネチャを保存
        original_signature1 = result.function1_signature
        original_signature2 = result.function2_signature
        
        # 等価の場合は終了
        if result.is_equivalent is True:
            self._debug_print("Phase 0: EQUIVALENT - No retry needed")
            result.total_time = time.time() - start_time
            return result
        
        # リトライ判定
        should_retry = self._should_retry(result)
        retry_reason = self._get_retry_reason(result)
        self._debug_print(f"Phase 0 result: {retry_reason}")
        
        if not should_retry or not retry_with_type_fix:
            result.total_time = time.time() - start_time
            return result
        
        self._debug_print(f"Phase 0: {retry_reason} - preparing for type fix retry")
        
        # ============================================
        # デコンパイル結果から取得した型情報を使用して判定
        # ============================================
        type_fixer1 = TypeFixer(program1, self.type_fixer_config, debug=self.debug)
        type_fixer2 = TypeFixer(program2, self.type_fixer_config, debug=self.debug)
        
        # デコンパイル結果から戻り値の型を取得して判定
        ret_needs_fix1 = self._should_fix_return_type_from_analysis(analysis1)
        ret_needs_fix2 = self._should_fix_return_type_from_analysis(analysis2)
        
        # パラメータ情報も解析結果から取得
        params1 = analysis1.parameters if analysis1 else []
        params2 = analysis2.parameters if analysis2 else []
        
        param_needs_fix1 = self._should_fix_params_from_analysis(analysis1)
        param_needs_fix2 = self._should_fix_params_from_analysis(analysis2)
        
        self._debug_print(f"Binary 1 '{function_name1}' - return needs fix: {ret_needs_fix1} (type: {analysis1.return_type if analysis1 else 'N/A'}), params need fix: {param_needs_fix1}")
        self._debug_print(f"Binary 2 '{function_name2}' - return needs fix: {ret_needs_fix2} (type: {analysis2.return_type if analysis2 else 'N/A'}), params need fix: {param_needs_fix2}")
        
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
            
            # 再解析と等価性判定（オリジナルシグネチャを引き継ぐ）
            result = self._analyze_and_check(
                program1, program2,
                function_name1, function_name2,
                decompile_timeout, save_formula,
                binary1_name, binary2_name,
                type_fix_result=type_fix_result,
                retry_count=1,
                original_signature1=original_signature1,
                original_signature2=original_signature2
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
            
            # 再解析と等価性判定（オリジナルシグネチャを引き継ぐ）
            result = self._analyze_and_check(
                program1, program2,
                function_name1, function_name2,
                decompile_timeout, save_formula,
                binary1_name, binary2_name,
                type_fix_result=type_fix_result,
                retry_count=2,
                original_signature1=original_signature1,
                original_signature2=original_signature2
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
    def _should_fix_return_type_from_analysis(
        self,
        analysis: Optional['FunctionReturnAnalysis']
    ) -> bool:
        """デコンパイル結果の戻り値の型が修正対象かチェック"""
        if analysis is None or analysis.return_type is None:
            return False
        
        type_str = analysis.return_type.lower().strip()
        
        for pattern in self.type_fixer_config.target_patterns:
            if pattern in type_str:
                self._debug_print(f"Return type '{analysis.return_type}' matches pattern '{pattern}' (from decompile)")
                return True
        
        return False


    def _should_fix_params_from_analysis(
        self,
        analysis: Optional['FunctionReturnAnalysis']
    ) -> bool:
        """デコンパイル結果のパラメータ型が修正対象かチェック"""
        if analysis is None or not analysis.parameters:
            return False
        
        for param in analysis.parameters:
            # data_type_obj があればそれを優先
            raw_dt = param.get("data_type_obj")
            if raw_dt is not None and hasattr(raw_dt, 'getName'):
                type_str = str(raw_dt).lower().strip()
            else:
                type_str = param.get("data_type", "").lower().strip()
            
            for pattern in self.type_fixer_config.target_patterns:
                if pattern in type_str:
                    self._debug_print(f"Param type '{type_str}' matches pattern '{pattern}' (from decompile)")
                    return True
        
        return False


    def _analyze_and_check_with_analysis(
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
        retry_count: int = 0,
        original_signature1: Optional[FunctionSignature] = None,
        original_signature2: Optional[FunctionSignature] = None
    ) -> tuple:
        """
        関数を解析して等価性をチェック（解析結果も返す版）
        
        Returns:
            (analysis1, analysis2, EquivalenceResult)
        """
        from ..return_analyzer import ReturnAnalyzer
        
        start_time = time.time()
        
        # 関数1を解析
        self._debug_print(f"Analyzing function '{function_name1}' in {binary1_name}...")
        analyzer1 = ReturnAnalyzer(program1, debug=self.debug)
        try:
            analysis1 = analyzer1.analyze_function_by_name(function_name1, decompile_timeout)
            if analysis1 is None:
                return None, None, EquivalenceResult(
                    is_equivalent=None,
                    function1_name=function_name1,
                    function2_name=function_name2,
                    binary1_name=binary1_name,
                    binary2_name=binary2_name,
                    solver_results=ParallelResult(results=[]),
                    total_time=time.time() - start_time,
                    error_message=f"Function '{function_name1}' not found in {binary1_name}",
                    type_fix_result=type_fix_result,
                    retry_count=retry_count,
                    function1_signature=original_signature1,
                    function2_signature=original_signature2
                )
        finally:
            analyzer1.dispose()
        
        # 関数2を解析
        self._debug_print(f"Analyzing function '{function_name2}' in {binary2_name}...")
        analyzer2 = ReturnAnalyzer(program2, debug=self.debug)
        try:
            analysis2 = analyzer2.analyze_function_by_name(function_name2, decompile_timeout)
            if analysis2 is None:
                return analysis1, None, EquivalenceResult(
                    is_equivalent=None,
                    function1_name=function_name1,
                    function2_name=function_name2,
                    binary1_name=binary1_name,
                    binary2_name=binary2_name,
                    solver_results=ParallelResult(results=[]),
                    total_time=time.time() - start_time,
                    error_message=f"Function '{function_name2}' not found in {binary2_name}",
                    type_fix_result=type_fix_result,
                    retry_count=retry_count,
                    function1_signature=original_signature1,
                    function2_signature=original_signature2
                )
        finally:
            analyzer2.dispose()
        
        # シグネチャをキャプチャ
        if original_signature1 is None:
            original_signature1 = FunctionSignature.from_analysis(analysis1)
        if original_signature2 is None:
            original_signature2 = FunctionSignature.from_analysis(analysis2)
        
        self._debug_print("Running equivalence check...")
        result = self.check(
            analysis1, analysis2,
            binary1_name, binary2_name,
            save_formula,
            type_fix_result=type_fix_result,
            retry_count=retry_count,
            original_signature1=original_signature1,
            original_signature2=original_signature2
        )
        
        return analysis1, analysis2, result

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
        retry_count: int = 0,
        capture_signature: bool = False,
        original_signature1: Optional[FunctionSignature] = None,
        original_signature2: Optional[FunctionSignature] = None
    ) -> EquivalenceResult:
        """関数を解析して等価性をチェック（内部メソッド）"""
        from ..return_analyzer import ReturnAnalyzer
        
        start_time = time.time()
        
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
                    type_fix_result=type_fix_result,
                    retry_count=retry_count,
                    function1_signature=original_signature1,
                    function2_signature=original_signature2
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
                    type_fix_result=type_fix_result,
                    retry_count=retry_count,
                    function1_signature=original_signature1,
                    function2_signature=original_signature2
                )
        finally:
            analyzer2.dispose()
        
        # シグネチャをキャプチャする場合（初回解析時）
        if capture_signature:
            original_signature1 = FunctionSignature.from_analysis(analysis1)
            original_signature2 = FunctionSignature.from_analysis(analysis2)
        
        self._debug_print("Running equivalence check...")
        return self.check(
            analysis1, analysis2,
            binary1_name, binary2_name,
            save_formula,
            type_fix_result=type_fix_result,
            retry_count=retry_count,
            original_signature1=original_signature1,
            original_signature2=original_signature2
        )