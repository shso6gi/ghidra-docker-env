# -*- coding: utf-8 -*-
"""等価性判定メインロジック（Phase 1 符号性対応版）"""

from typing import Optional, Dict, Any, List, Tuple
import time

from ..model import FunctionReturnAnalysis, FunctionSignature
from ..model.analysis import SignednessResult
from ..smt import ParallelSolverRunner, ParallelResult, SolverStatus
from .formula import FormulaBuilder
from .counterexample import CounterexampleFormatter, FormattedCounterexample
from .type_fixer import TypeFixer, TypeFixerConfig, TypeFixResult
from ..transform import ExpressionRewriter, rewrite_analysis_returns
from .result import EquivalenceResult, RewriteInfo


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
        from ..core import ReturnAnalyzer
        
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
            constrained_fragments = formula_result.param_fragment_constrained
            
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

                if constrained_fragments:
                    print(f"[EquivalenceChecker] Parameter fragments constrained via extension: {constrained_fragments}")
            
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
                    constrained_fragments=constrained_fragments,
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
                constrained_fragments=constrained_fragments,
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
                constrained_fragments=[]
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
        2. Phase 1: 符号性推定に基づく型修正（ulong → long 等）
        3. Phase 2: パターンマッチに基づく型修正（undefined → int 等）
        4. Phase 3: 引数の型も修正
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
        # TypeFixerを準備
        # ============================================
        type_fixer1 = TypeFixer(program1, self.type_fixer_config, debug=self.debug)
        type_fixer2 = TypeFixer(program2, self.type_fixer_config, debug=self.debug)
        
        # ============================================
        # Phase 1: 符号性に基づく型修正
        # ============================================
        signedness_fix_applied = False

        if analysis1 and analysis1.signedness_result:
            type_fix_result.inferred_signedness_binary1 = analysis1.signedness_result.signedness
            
            if analysis1.should_fix_return_to_signed():
                self._debug_print("=" * 60)
                self._debug_print("Phase 1: Signedness-based type fix for Binary 1")
                self._debug_print("=" * 60)
                
                original_type = analysis1.return_type
                signed_type = self.type_fixer_config.get_signed_type_for(original_type or "")
                
                if signed_type:
                    # ★ 重要: fix_function_signature_by_name を使用（undefinedと同じ方法）
                    # override_return_type_name で戻り値の型を指定
                    params1 = analysis1.parameters if analysis1 else []
                    ret_fixed, _ = type_fixer1.fix_function_signature_by_name(
                        function_name1,
                        params1,
                        fix_return_type=False,  # パターンマッチは使わない
                        fix_param_types=False,
                        override_return_type_name=signed_type  # 符号性修正用
                    )
                    if ret_fixed:
                        type_fix_result.signedness_fixed_binary1 = True
                        type_fix_result.original_type_binary1 = original_type
                        type_fix_result.fixed_type_binary1 = signed_type
                        signedness_fix_applied = True
                        self._debug_print(f"Binary 1: {original_type} -> {signed_type} (signedness fix)")

        if analysis2 and analysis2.signedness_result:
            type_fix_result.inferred_signedness_binary2 = analysis2.signedness_result.signedness
            
            if analysis2.should_fix_return_to_signed():
                self._debug_print("=" * 60)
                self._debug_print("Phase 1: Signedness-based type fix for Binary 2")
                self._debug_print("=" * 60)
                
                original_type = analysis2.return_type
                signed_type = self.type_fixer_config.get_signed_type_for(original_type or "")
                
                if signed_type:
                    params2 = analysis2.parameters if analysis2 else []
                    ret_fixed, _ = type_fixer2.fix_function_signature_by_name(
                        function_name2,
                        params2,
                        fix_return_type=False,
                        fix_param_types=False,
                        override_return_type_name=signed_type
                    )
                    if ret_fixed:
                        type_fix_result.signedness_fixed_binary2 = True
                        type_fix_result.original_type_binary2 = original_type
                        type_fix_result.fixed_type_binary2 = signed_type
                        signedness_fix_applied = True
                        self._debug_print(f"Binary 2: {original_type} -> {signed_type} (signedness fix)")
        
        # 符号性修正が適用された場合、再チェック
        if signedness_fix_applied:
            type_fix_result.retry_phase = "signedness_fix"
            
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
            
            if result.is_equivalent is True:
                self._debug_print("Phase 1: EQUIVALENT after signedness fix")
                result.total_time = time.time() - start_time
                return result
            
            should_retry = self._should_retry(result)
            retry_reason = self._get_retry_reason(result)
            self._debug_print(f"Phase 1 result: {retry_reason}")
            
            if not should_retry:
                result.total_time = time.time() - start_time
                return result
        
        # ============================================
        # Phase 2: パターンマッチに基づく戻り値の型修正
        # ============================================
        # デコンパイル結果から取得した型情報を使用して判定
        ret_needs_fix1 = self._should_fix_return_type_from_analysis(analysis1)
        ret_needs_fix2 = self._should_fix_return_type_from_analysis(analysis2)
        
        # パラメータ情報も解析結果から取得
        params1 = analysis1.parameters if analysis1 else []
        params2 = analysis2.parameters if analysis2 else []
        
        param_needs_fix1 = self._should_fix_params_from_analysis(analysis1)
        param_needs_fix2 = self._should_fix_params_from_analysis(analysis2)
        
        self._debug_print(f"Binary 1 - return needs pattern fix: {ret_needs_fix1}, params need fix: {param_needs_fix1}")
        self._debug_print(f"Binary 2 - return needs pattern fix: {ret_needs_fix2}, params need fix: {param_needs_fix2}")
        
        if ret_needs_fix1 or ret_needs_fix2:
            self._debug_print("=" * 60)
            self._debug_print("Phase 2: Pattern-based return type fix")
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
                retry_count=2,
                original_signature1=original_signature1,
                original_signature2=original_signature2
            )
            
            if result.is_equivalent is True:
                self._debug_print("Phase 2: EQUIVALENT after return type fix")
                result.total_time = time.time() - start_time
                return result
            
            should_retry = self._should_retry(result)
            retry_reason = self._get_retry_reason(result)
            self._debug_print(f"Phase 2 result: {retry_reason}")
            
            if not should_retry:
                result.total_time = time.time() - start_time
                return result
        
        # ============================================
        # Phase 3: 引数の型も修正
        # ============================================
        if param_needs_fix1 or param_needs_fix2:
            self._debug_print("=" * 60)
            self._debug_print("Phase 3: Parameter type fix")
            self._debug_print("=" * 60)
            type_fix_result.retry_phase = "param_type_fix"
            
            # 修正後の状態で再度パラメータ情報を取得
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
            
            # 最終チェック
            result = self._analyze_and_check(
                program1, program2,
                function_name1, function_name2,
                decompile_timeout, save_formula,
                binary1_name, binary2_name,
                type_fix_result=type_fix_result,
                retry_count=3,
                original_signature1=original_signature1,
                original_signature2=original_signature2
            )
            
            if result.is_equivalent is True:
                self._debug_print("Phase 3: EQUIVALENT after parameter type fix")
            elif result.is_equivalent is False:
                self._debug_print("Phase 3: NOT EQUIVALENT - final result")
            elif result.is_timeout():
                self._debug_print("Phase 3: TIMEOUT - final result")
            else:
                self._debug_print("Phase 3: UNKNOWN - final result")
        
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
        """
        デコンパイル結果の戻り値の型が修正対象かチェック（パターンマッチ）
        
        注意: 符号性に基づく修正は別途Phase 1で行う
        """
        if analysis is None or analysis.return_type is None:
            return False
        
        # 既に符号性修正が適用されている場合はスキップ
        # (signedness_resultがsignedで、型がunsignedの場合はPhase 1で処理済み)
        if analysis.should_fix_return_to_signed():
            return False
        
        type_str = analysis.return_type.lower().strip()
        
        for pattern in self.type_fixer_config.target_patterns:
            if pattern in type_str:
                self._debug_print(f"Return type '{analysis.return_type}' matches pattern '{pattern}'")
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
            raw_dt = param.get("data_type_obj")
            if raw_dt is not None and hasattr(raw_dt, 'getName'):
                type_str = str(raw_dt).lower().strip()
            else:
                type_str = param.get("data_type", "").lower().strip()
            
            for pattern in self.type_fixer_config.target_patterns:
                if pattern in type_str:
                    self._debug_print(f"Param type '{type_str}' matches pattern '{pattern}'")
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
    ) -> Tuple[Optional[FunctionReturnAnalysis], Optional[FunctionReturnAnalysis], EquivalenceResult]:
        """
        関数を解析して等価性をチェック（解析結果も返す版）
        
        Returns:
            (analysis1, analysis2, EquivalenceResult)
        """
        from ..core import ReturnAnalyzer
        
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
        original_signature1: Optional[FunctionSignature] = None,
        original_signature2: Optional[FunctionSignature] = None
    ) -> EquivalenceResult:
        """関数を解析して等価性をチェック（内部メソッド）"""
        _, _, result = self._analyze_and_check_with_analysis(
            program1, program2,
            function_name1, function_name2,
            decompile_timeout, save_formula,
            binary1_name, binary2_name,
            type_fix_result=type_fix_result,
            retry_count=retry_count,
            original_signature1=original_signature1,
            original_signature2=original_signature2
        )
        return result