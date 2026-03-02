# -*- coding: utf-8 -*-
"""等価性判定メインロジック（リファクタリング版）"""

from typing import Optional, Dict, Any, List, Tuple
import time

from ..model import FunctionReturnAnalysis, FunctionSignature
from ..smt import ParallelSolverRunner, ParallelResult
from .formula import FormulaBuilder
from .counterexample import CounterexampleFormatter
from .type_fixer import TypeFixer, TypeFixerConfig, TypeFixResult
from .result import EquivalenceResult, RewriteInfo
from .phase_handler import PhaseHandler, PhaseContext
from ..transform.rewrite import ExpressionRewriter, rewrite_analysis_returns


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
        self.phase_handler = PhaseHandler(self.type_fixer_config, debug=debug)
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[EquivalenceChecker] {msg}")
    
    def _apply_rewrite(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis
    ) -> Tuple[FunctionReturnAnalysis, FunctionReturnAnalysis, RewriteInfo]:
        """両方の解析結果にリライトを適用"""
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
            self._debug_print("Function 1 was rewritten")
            rewrite_info.applied = True
            analysis1 = rewritten1
        
        # Function 2 のリライト
        rewritten2, results2 = rewrite_analysis_returns(analysis2, rewriter)
        rewrite_info.function2_rewrites = results2
        
        if any(r.was_rewritten for r in results2):
            self._debug_print("Function 2 was rewritten")
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
        from ..analysis import ReturnAnalyzer
        
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
        2. Phase 1: 符号性推定に基づく型修正
        3. Phase 2: パターンマッチに基づく型修正
        4. Phase 3: 引数の型も修正
        5. Phase 4: MIPS64 ABI Retry (偽反例検出→制約付き再solve)
        """
        start_time = time.time()
        binary1_name = program1.getName() if hasattr(program1, 'getName') else "binary1"
        binary2_name = program2.getName() if hasattr(program2, 'getName') else "binary2"
        
        type_fix_result = TypeFixResult()
        
        # コンテキスト作成
        ctx = PhaseContext(
            program1=program1,
            program2=program2,
            function_name1=function_name1,
            function_name2=function_name2,
            binary1_name=binary1_name,
            binary2_name=binary2_name,
            decompile_timeout=decompile_timeout,
            save_formula=save_formula,
            type_fix_result=type_fix_result,
            original_signature1=None,
            original_signature2=None
        )
        
        # ============================================
        # Phase 0: 型修正なしで等価性判定
        # ============================================
        self._debug_print("=" * 60)
        self._debug_print("Phase 0: Initial check without type fix")
        self._debug_print("=" * 60)
        type_fix_result.retry_phase = "initial"
        
        analysis1, analysis2, result = self._analyze_and_check_with_analysis(
            ctx, retry_count=0
        )
        ctx.analysis1 = analysis1
        ctx.analysis2 = analysis2
        ctx.original_signature1 = result.function1_signature
        ctx.original_signature2 = result.function2_signature
        
        if result.is_equivalent is True:
            self._debug_print("Phase 0: EQUIVALENT - No retry needed")
            result.total_time = time.time() - start_time
            return result
        
        should_retry = self.phase_handler.should_retry(result)
        retry_reason = self.phase_handler.get_retry_reason(result)
        self._debug_print(f"Phase 0 result: {retry_reason}")
        
        if not should_retry or not retry_with_type_fix:
            result.total_time = time.time() - start_time
            return result
        
        # TypeFixerを準備
        type_fixer1 = TypeFixer(program1, self.type_fixer_config, debug=self.debug)
        type_fixer2 = TypeFixer(program2, self.type_fixer_config, debug=self.debug)
        
        # ============================================
        # Phase 1: 符号性に基づく型修正
        # ============================================
        if self.phase_handler.run_phase1_signedness_fix(ctx, type_fixer1, type_fixer2):
            type_fix_result.retry_phase = "signedness_fix"
            result = self._run_check_after_phase(ctx, retry_count=1)
            
            if result.is_equivalent is True:
                self._debug_print("Phase 1: EQUIVALENT after signedness fix")
                result.total_time = time.time() - start_time
                return result
            
            if not self.phase_handler.should_retry(result):
                result.total_time = time.time() - start_time
                return result
        
        # ============================================
        # Phase 2: パターンマッチに基づく戻り値の型修正
        # ============================================
        if self.phase_handler.run_phase2_return_type_fix(ctx, type_fixer1, type_fixer2):
            type_fix_result.retry_phase = "return_type_fix"
            result = self._run_check_after_phase(ctx, retry_count=2)
            
            if result.is_equivalent is True:
                self._debug_print("Phase 2: EQUIVALENT after return type fix")
                result.total_time = time.time() - start_time
                return result
            
            if not self.phase_handler.should_retry(result):
                result.total_time = time.time() - start_time
                return result
        
        # ============================================
        # Phase 3: 引数の型修正
        # ============================================
        if self.phase_handler.run_phase3_param_type_fix(
            ctx, type_fixer1, type_fixer2, self._get_params_via_decompile
        ):
            type_fix_result.retry_phase = "param_type_fix"
            result = self._run_check_after_phase(ctx, retry_count=3)
            
            if result.is_equivalent is True:
                self._debug_print("Phase 3: EQUIVALENT after parameter type fix")
                result.total_time = time.time() - start_time
                return result
            
            if not self.phase_handler.should_retry(result):
                result.total_time = time.time() - start_time
                return result
        
        # ============================================
        # Phase 4-A: MIPS64 ABI param fix (conservative)
        # ============================================
        if self.phase_handler.run_phase4_mips64_fix(
            ctx, type_fixer1, type_fixer2, self._get_params_via_decompile
        ):
            type_fix_result.retry_phase = "mips64_abi_fix"
            result = self._run_check_after_phase(ctx, retry_count=4)
            
            if result.is_equivalent is True:
                self._debug_print("Phase 4-A: EQUIVALENT after MIPS64 ABI fix")
                result.total_time = time.time() - start_time
                return result
            
            if not self.phase_handler.should_retry(result):
                result.total_time = time.time() - start_time
                return result
        
        # ============================================
        # Phase 4-B: MIPS64 ABI Retry (spurious counterexample detection)
        # ============================================
        if result.is_equivalent is False:
            abi_constraints = self.phase_handler.run_phase4_mips64_retry(result, ctx)
            
            if abi_constraints:
                self._debug_print("Phase 4-B: Spurious counterexample detected, retrying with ABI constraints")
                type_fix_result.retry_phase = "mips64_abi_retry"
                
                # ABI整合制約を追加してSMT再生成
                result = self._retry_with_abi_constraints(
                    ctx, abi_constraints, retry_count=4
                )
                
                if result.is_equivalent is True:
                    self._debug_print("Phase 4-B: EQUIVALENT after MIPS64 ABI retry")
                elif result.is_equivalent is False:
                    self._debug_print("Phase 4-B: Still NOT EQUIVALENT after MIPS64 ABI retry (genuine counterexample)")
            else:
                self._debug_print("Phase 4-B: No spurious counterexample detected (genuine NOT EQUIVALENT)")
        
        # ============================================
        # 最終結果
        # ============================================
        self._debug_print("=" * 60)
        self._debug_print("Final Result")
        self._debug_print("=" * 60)
        
        result.total_time = time.time() - start_time
        return result
    
    def _retry_with_abi_constraints(
        self,
        ctx: PhaseContext,
        abi_constraints: Dict[str, Tuple[str, int]],
        retry_count: int
    ) -> EquivalenceResult:
        """ABI整合制約を追加してリトライ"""
        start_time = time.time()
        
        if ctx.analysis1 is None or ctx.analysis2 is None:
            return self._create_error_result(
                ctx.analysis1 or FunctionReturnAnalysis(ctx.function_name1, "", [], []),
                ctx.analysis2 or FunctionReturnAnalysis(ctx.function_name2, "", [], []),
                ctx.binary1_name,
                ctx.binary2_name,
                "Analysis not available for ABI retry",
                start_time,
                ctx.type_fix_result,
                retry_count,
                ctx.original_signature1,
                ctx.original_signature2
            )
        
        try:
            # リライトを適用
            analysis1, analysis2, rewrite_info = self._apply_rewrite(
                ctx.analysis1, ctx.analysis2
            )
            
            # 通常のSMT式を構築
            smt_formula, return_var1, return_var2 = (
                self.formula_builder.build_equivalence_formula(analysis1, analysis2)
            )
            
            # ABI整合制約を手動で追加
            constraint_lines = []
            for param_name, (signedness, narrow_bits) in abi_constraints.items():
                if signedness == "signed":
                    # 符号拡張: ((_ sign_extend X) ((_ extract N 0) param))
                    extend_bits = 64 - narrow_bits
                    constraint_lines.append(
                        f"(assert (= {param_name} "
                        f"((_ sign_extend {extend_bits}) "
                        f"((_ extract {narrow_bits - 1} 0) {param_name}))))"
                    )
                else:
                    # ゼロ拡張: ((_ zero_extend X) ((_ extract N 0) param))
                    extend_bits = 64 - narrow_bits
                    constraint_lines.append(
                        f"(assert (= {param_name} "
                        f"((_ zero_extend {extend_bits}) "
                        f"((_ extract {narrow_bits - 1} 0) {param_name}))))"
                    )
            
            # SMT式に制約を挿入 (check-sat の前に)
            if constraint_lines:
                parts = smt_formula.rsplit("(check-sat)", 1)
                if len(parts) == 2:
                    constraints_str = "\n".join(constraint_lines)
                    smt_formula = parts[0] + "\n" + constraints_str + "\n(check-sat)" + parts[1]
                else:
                    # check-satが見つからない場合は末尾に追加
                    constraints_str = "\n".join(constraint_lines)
                    smt_formula = smt_formula + "\n" + constraints_str
            
            if self.debug:
                print("\n" + "=" * 60)
                print("Generated SMT formula with ABI constraints:")
                print("=" * 60)
                print(smt_formula)
                print("=" * 60 + "\n")
            
            # 再solve
            if self.debug:
                parallel_result = self.solver_runner.run_sequential(smt_formula)
            else:
                parallel_result = self.solver_runner.run_parallel(smt_formula)
            
            total_time = time.time() - start_time
            
            # 反例取得
            counterexample = None
            if parallel_result.is_equivalent is False:
                raw_model = parallel_result.get_counterexample()
                if raw_model:
                    counterexample = self._format_counterexample(
                        raw_model, analysis1, analysis2, return_var1, return_var2
                    )
            
            return EquivalenceResult(
                is_equivalent=parallel_result.is_equivalent,
                function1_name=ctx.function_name1,
                function2_name=ctx.function_name2,
                binary1_name=ctx.binary1_name,
                binary2_name=ctx.binary2_name,
                solver_results=parallel_result,
                counterexample=counterexample,
                smt_formula=smt_formula if ctx.save_formula else None,
                total_time=total_time,
                type_fix_result=ctx.type_fix_result,
                retry_count=retry_count,
                function1_signature=ctx.original_signature1,
                function2_signature=ctx.original_signature2,
                constrained_fragments=list(abi_constraints.keys()),
                rewrite_info=rewrite_info,
                mips64_abi_constraints=abi_constraints
            )
        
        except Exception as e:
            self._debug_print(f"Exception in ABI retry: {e}")
            if self.debug:
                import traceback
                print(traceback.format_exc())
            
            return self._create_error_result(
                ctx.analysis1, ctx.analysis2,
                ctx.binary1_name, ctx.binary2_name,
                str(e), start_time,
                ctx.type_fix_result, retry_count,
                ctx.original_signature1, ctx.original_signature2
            )
    
    def _run_check_after_phase(
        self,
        ctx: PhaseContext,
        retry_count: int
    ) -> EquivalenceResult:
        """Phase実行後の再チェック"""
        return self._analyze_and_check(ctx, retry_count=retry_count)
    
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
        
        if original_signature1 is None:
            original_signature1 = FunctionSignature.from_analysis(analysis1)
        if original_signature2 is None:
            original_signature2 = FunctionSignature.from_analysis(analysis2)
        
        try:
            formula_result = self.formula_builder.build_equivalence_formula_extended(
                analysis1, analysis2
            )
            constrained_fragments = formula_result.param_fragment_constrained
            
            # リライトを適用
            analysis1, analysis2, rewrite_info = self._apply_rewrite(analysis1, analysis2)
            
            smt_formula, return_var1, return_var2 = (
                self.formula_builder.build_equivalence_formula(analysis1, analysis2)
            )
            
            if self.debug:
                print("\n" + "=" * 60)
                print("Generated SMT formula:")
                print("=" * 60)
                print(smt_formula)
                print("=" * 60 + "\n")
            
            available_solvers = self.solver_runner.get_available_solvers()
            if not available_solvers:
                return self._create_error_result(
                    analysis1, analysis2, binary1_name, binary2_name,
                    "No SMT solvers available", start_time,
                    type_fix_result, retry_count,
                    original_signature1, original_signature2
                )
            
            if self.debug:
                print(f"Available solvers: {available_solvers}")
                parallel_result = self.solver_runner.run_sequential(smt_formula)
            else:
                parallel_result = self.solver_runner.run_parallel(smt_formula)
            
            total_time = time.time() - start_time
            
            counterexample = None
            if parallel_result.is_equivalent is False:
                raw_model = parallel_result.get_counterexample()
                if raw_model:
                    counterexample = self._format_counterexample(
                        raw_model, analysis1, analysis2, return_var1, return_var2
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
                constrained_fragments=constrained_fragments,
                rewrite_info=rewrite_info
            )
        
        except Exception as e:
            self._debug_print(f"Exception in check: {e}")
            if self.debug:
                import traceback
                print(traceback.format_exc())
            
            return self._create_error_result(
                analysis1, analysis2, binary1_name, binary2_name,
                str(e), start_time,
                type_fix_result, retry_count,
                original_signature1, original_signature2
            )
    
    def _format_counterexample(
        self,
        raw_model: Dict,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        return_var1: str,
        return_var2: str
    ):
        """反例をフォーマット"""
        param_names = []
        for p in analysis1.parameters:
            param_names.append(f"{p.get('name', 'param')}_1")
        for p in analysis2.parameters:
            param_names.append(f"{p.get('name', 'param')}_2")
        
        return CounterexampleFormatter.format(
            raw_model, param_names, return_var1, return_var2
        )
    
    def _create_error_result(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        binary1_name: str,
        binary2_name: str,
        error_message: str,
        start_time: float,
        type_fix_result: Optional[TypeFixResult],
        retry_count: int,
        original_signature1: Optional[FunctionSignature],
        original_signature2: Optional[FunctionSignature]
    ) -> EquivalenceResult:
        """エラー結果を作成"""
        return EquivalenceResult(
            is_equivalent=None,
            function1_name=analysis1.function_name,
            function2_name=analysis2.function_name,
            binary1_name=binary1_name,
            binary2_name=binary2_name,
            solver_results=ParallelResult(results=[]),
            total_time=time.time() - start_time,
            error_message=error_message,
            type_fix_result=type_fix_result,
            retry_count=retry_count,
            function1_signature=original_signature1,
            function2_signature=original_signature2,
            constrained_fragments=[]
        )
    
    def _analyze_and_check_with_analysis(
        self,
        ctx: PhaseContext,
        retry_count: int = 0
    ) -> Tuple[Optional[FunctionReturnAnalysis], Optional[FunctionReturnAnalysis], EquivalenceResult]:
        """関数を解析して等価性をチェック（解析結果も返す版）"""
        from ..analysis import ReturnAnalyzer
        
        start_time = time.time()
        
        # 関数1を解析
        self._debug_print(f"Analyzing function '{ctx.function_name1}' in {ctx.binary1_name}...")
        analyzer1 = ReturnAnalyzer(ctx.program1, debug=self.debug)
        try:
            analysis1 = analyzer1.analyze_function_by_name(
                ctx.function_name1, ctx.decompile_timeout
            )
            if analysis1 is None:
                return None, None, EquivalenceResult(
                    is_equivalent=None,
                    function1_name=ctx.function_name1,
                    function2_name=ctx.function_name2,
                    binary1_name=ctx.binary1_name,
                    binary2_name=ctx.binary2_name,
                    solver_results=ParallelResult(results=[]),
                    total_time=time.time() - start_time,
                    error_message=f"Function '{ctx.function_name1}' not found in {ctx.binary1_name}",
                    type_fix_result=ctx.type_fix_result,
                    retry_count=retry_count,
                    function1_signature=ctx.original_signature1,
                    function2_signature=ctx.original_signature2
                )
        finally:
            analyzer1.dispose()
        
        # 関数2を解析
        self._debug_print(f"Analyzing function '{ctx.function_name2}' in {ctx.binary2_name}...")
        analyzer2 = ReturnAnalyzer(ctx.program2, debug=self.debug)
        try:
            analysis2 = analyzer2.analyze_function_by_name(
                ctx.function_name2, ctx.decompile_timeout
            )
            if analysis2 is None:
                return analysis1, None, EquivalenceResult(
                    is_equivalent=None,
                    function1_name=ctx.function_name1,
                    function2_name=ctx.function_name2,
                    binary1_name=ctx.binary1_name,
                    binary2_name=ctx.binary2_name,
                    solver_results=ParallelResult(results=[]),
                    total_time=time.time() - start_time,
                    error_message=f"Function '{ctx.function_name2}' not found in {ctx.binary2_name}",
                    type_fix_result=ctx.type_fix_result,
                    retry_count=retry_count,
                    function1_signature=ctx.original_signature1,
                    function2_signature=ctx.original_signature2
                )
        finally:
            analyzer2.dispose()
        
        # シグネチャをキャプチャ
        if ctx.original_signature1 is None:
            ctx.original_signature1 = FunctionSignature.from_analysis(analysis1)
        if ctx.original_signature2 is None:
            ctx.original_signature2 = FunctionSignature.from_analysis(analysis2)
        
        self._debug_print("Running equivalence check...")
        result = self.check(
            analysis1, analysis2,
            ctx.binary1_name, ctx.binary2_name,
            ctx.save_formula,
            type_fix_result=ctx.type_fix_result,
            retry_count=retry_count,
            original_signature1=ctx.original_signature1,
            original_signature2=ctx.original_signature2
        )
        
        return analysis1, analysis2, result
    
    def _analyze_and_check(
        self,
        ctx: PhaseContext,
        retry_count: int = 0
    ) -> EquivalenceResult:
        """関数を解析して等価性をチェック（内部メソッド）"""
        _, _, result = self._analyze_and_check_with_analysis(ctx, retry_count=retry_count)
        return result