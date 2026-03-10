# -*- coding: utf-8 -*-
"""等価性判定メインロジック（Stage/Phase ループ骨格版）"""

from typing import Optional, Dict, Any, List, Tuple
from enum import Enum
from dataclasses import dataclass
import time

from ..model import FunctionReturnAnalysis, FunctionSignature
from ..smt import ParallelSolverRunner, ParallelResult, SolverResult, SolverStatus
from .formula import FormulaBuilder
from .counterexample import CounterexampleFormatter
from .typing.fixer import TypeFixer, TypeFixerConfig, TypeFixResult
from .result import EquivalenceResult, RewriteInfo
from .phases.handler import (
    PhaseHandler, PhaseContext, PhaseID, PhaseSpec, PhaseResult, DEFAULT_PHASE_PLAN
)
from ..transform.rewrite import ExpressionRewriter, rewrite_analysis_returns
from .strategies import create_strategy
from .strategies.pairwise import PairwiseStrategy
from .strategies.monolithic import MonolithicStrategy


# ============================================================================
# Stage 定義（新フロー骨格）
# ============================================================================

class StageID(Enum):
    """Stage識別子"""
    S_PAIRWISE = "S_PAIRWISE"
    S_MONOLITHIC_FALLBACK = "S_MONOLITHIC_FALLBACK"


@dataclass
class StageSpec:
    """Stage仕様"""
    stage_id: StageID
    description: str
    strategy: str  # "pairwise" or "monolithic"


# デフォルトの Stage plan
DEFAULT_STAGE_PLAN: List[StageSpec] = [
    StageSpec(StageID.S_PAIRWISE, "Pairwise strategy", strategy="pairwise"),
    StageSpec(StageID.S_MONOLITHIC_FALLBACK, "Monolithic fallback (UNKNOWN only)", strategy="monolithic"),
]


class EquivalenceChecker:
    """等価性判定を行うクラス"""
    
    def __init__(
        self,
        timeout: int = 10,
        debug: bool = False,
        type_fixer_config: Optional[TypeFixerConfig] = None,
        enable_rewrite: bool = True,
        rewrite_direction: str = "to_modulo",
        strategy: str = "pairwise",
        pairwise_timeout: int = 5,
        pairwise_timeout_hard: int = 30,
        pairwise_save_unknown: bool = False
    ):
        """
        Args:
            timeout: SMTソルバーのタイムアウト（秒）
            debug: デバッグ出力を有効にする
            type_fixer_config: 型修正の設定
            enable_rewrite: 式のリライトを有効にする
            rewrite_direction: リライト方向 ("to_modulo" or "to_expansion")
            strategy: 判定戦略 ("pairwise" or "monolithic")
        """
        self.timeout = timeout
        self.debug = debug
        self.type_fixer_config = type_fixer_config or TypeFixerConfig()
        self.enable_rewrite = enable_rewrite
        self.rewrite_direction = rewrite_direction
        self.strategy_name = strategy
        self.formula_builder = FormulaBuilder(debug=debug)
        self.solver_runner = ParallelSolverRunner(timeout=timeout, debug=debug)
        self.phase_handler = PhaseHandler(self.type_fixer_config, debug=debug)
        
        # 各 strategy の準備
        self.pairwise_strategy = PairwiseStrategy(
            self.formula_builder, self.solver_runner, debug=debug
        )
        self.pairwise_strategy.per_query_timeout = pairwise_timeout
        self.pairwise_strategy.per_query_timeout_hard = pairwise_timeout_hard
        self.pairwise_strategy.save_unknown_queries = pairwise_save_unknown
        
        self.monolithic_strategy = MonolithicStrategy(
            self.formula_builder, self.solver_runner, debug=debug
        )
        
        # ★ [P2修正] strategy 引数に応じて stage_plan を切り替える
        if strategy == "pairwise":
            # pairwise -> monolithic fallback の 2-stage plan
            self.stage_plan = [
                StageSpec(StageID.S_PAIRWISE, "Pairwise strategy", strategy="pairwise"),
                StageSpec(StageID.S_MONOLITHIC_FALLBACK, "Monolithic fallback (UNKNOWN only)", strategy="monolithic"),
            ]
            self.check_strategy = self.pairwise_strategy
        elif strategy == "monolithic":
            # monolithic のみの 1-stage plan（後方互換性）
            self.stage_plan = [
                StageSpec(StageID.S_MONOLITHIC_FALLBACK, "Monolithic strategy", strategy="monolithic"),
            ]
            self.check_strategy = self.monolithic_strategy
        else:
            raise ValueError(f"Unknown strategy: {strategy}")

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
    
    def _try_phase4b_if_applicable(
        self,
        result: EquivalenceResult,
        ctx: PhaseContext,
        retry_count: int,
        retry_with_type_fix: bool
    ) -> Optional[EquivalenceResult]:
        """SAT時にPhase 4-Bを試行すべきかチェックし、必要なら実行
        
        Args:
            result: 現在の判定結果
            ctx: Phaseコンテキスト
            retry_count: リトライカウント（Phase 4-B実行時に使用）
            retry_with_type_fix: 型修正リトライが有効か
        
        Returns:
            - Phase 4-B実行した場合: 新しいEquivalenceResult
            - Phase 4-B不要な場合: None
        """
        if not retry_with_type_fix:
            return None
        
        if result.is_equivalent is not False:  # SAT でない
            return None
        
        abi_constraints = self.phase_handler.run_phase4_mips64_retry(result, ctx)
        
        if not abi_constraints:
            return None
        
        self._debug_print("Phase 4-B: Spurious counterexample detected, retrying with ABI constraints")
        ctx.type_fix_result.retry_phase = "mips64_abi_retry"
        
        return self._retry_with_abi_constraints(ctx, abi_constraints, retry_count=retry_count)
    
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
        
        新フロー（Stage/Phase ループ骨格 + Selective Reanalysis）:
        1. Phase plan を定義（デフォルト: P0_BASE -> P1_SIGNEDNESS -> P2_PATTERN_INT）
        2. 各 Phase ごとに：
           a. Phase を実行（型修正など、P0 は何もしない）
           b. ★ 変更された側だけ再解析（未変更側は ctx.analysis1/2 を再利用）
           c. Stage plan を実行（等価性判定）
           d. 結果に応じた遷移判定
        3. Phase plan 完了後、Phase 4-A（MIPS64 conservative fix）を追加試行
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
        
        # TypeFixer を準備（Phase 1 以降で使用）
        type_fixer1 = None
        type_fixer2 = None
        if retry_with_type_fix:
            type_fixer1 = TypeFixer(program1, self.type_fixer_config, debug=self.debug)
            type_fixer2 = TypeFixer(program2, self.type_fixer_config, debug=self.debug)
        
        # Phase Plan の定義
        phase_plan = DEFAULT_PHASE_PLAN.copy()
        
        # Phase Loop
        result = None
        retry_count = 0
        first_phase = True
        
        for phase_idx, phase_spec in enumerate(phase_plan):
            phase_id = phase_spec.phase_id
            
            self._debug_print("=" * 60)
            self._debug_print(f"Phase {phase_id.value}: {phase_spec.description}")
            self._debug_print("=" * 60)
            
            # Phase 実行（型修正など）
            if first_phase:
                # P0: 初回は解析から実行
                first_phase = False
                type_fix_result.retry_phase = "initial"
                
                analysis1, analysis2, result = self._analyze_and_check_with_analysis(
                    ctx, retry_count=retry_count
                )
                ctx.analysis1 = analysis1
                ctx.analysis2 = analysis2
                ctx.original_signature1 = result.function1_signature
                ctx.original_signature2 = result.function2_signature
            
            else:
                # P1, P2, ... は型修正を試行
                if not retry_with_type_fix:
                    self._debug_print(f"Stopping: retry_with_type_fix=False")
                    break
                
                if type_fixer1 is None or type_fixer2 is None:
                    self._debug_print(f"Stopping: type_fixer not available")
                    break
                
                # Phase 実行
                phase_result = self.phase_handler.execute_phase(
                    phase_spec, ctx, type_fixer1, type_fixer2, self._get_params_via_decompile
                )
                
                if not phase_result.applied:
                    self._debug_print(f"Phase {phase_id.value}: No changes applied, skipping recheck")
                    continue  # 次 Phase へ
                
                # ★ NEW: 変更された側だけ再解析
                retry_count += 1
                type_fix_result.retry_phase = phase_result.retry_name
                
                analysis1, analysis2, result = self._selective_reanalysis_and_check(
                    ctx, phase_result, retry_count=retry_count
                )
                
                # 再解析結果を ctx に戻す
                ctx.analysis1 = analysis1
                ctx.analysis2 = analysis2
            
            # 結果に応じた遷移判定
            
            # UNSAT → 即終了
            if result.is_equivalent is True:
                self._debug_print(f"Phase {phase_id.value}: EQUIVALENT - stopping")
                result.total_time = time.time() - start_time
                return result
            
            # critical error → 即終了
            if result.has_critical_error():
                self._debug_print(f"Phase {phase_id.value}: Critical error - {result.error_message}")
                result.total_time = time.time() - start_time
                return result
            
            # SAT → Phase 4-B（MIPS64 偽反例対策）のみ試行
            if result.is_equivalent is False:
                self._debug_print(f"Phase {phase_id.value}: SAT - checking for Phase 4-B eligibility")
                
                if retry_with_type_fix:
                    phase4b_result = self._try_phase4b_if_applicable(
                        result, ctx, retry_count=retry_count + 1, retry_with_type_fix=True
                    )
                    
                    if phase4b_result is not None:
                        result = phase4b_result
                        if result.is_equivalent is True:
                            self._debug_print(
                                f"Phase 4-B: EQUIVALENT after MIPS64 ABI retry (from {phase_id.value})"
                            )
                            result.total_time = time.time() - start_time
                            return result
                else:
                    self._debug_print(f"Phase 4-B: Skipped (retry_with_type_fix=False)")
                
                # SAT で終了
                self._debug_print(f"Phase {phase_id.value}: NOT EQUIVALENT - stopping")
                result.total_time = time.time() - start_time
                return result
            
            # UNKNOWN/TIMEOUT → 次 Phase へ進むか判定
            should_retry = self.phase_handler.should_retry(result)
            retry_reason = self.phase_handler.get_retry_reason(result)
            self._debug_print(f"Phase {phase_id.value} result: {retry_reason}")
            
            if not should_retry:
                result.total_time = time.time() - start_time
                return result
            
            self._debug_print(f"Proceeding to next phase ({retry_reason})")
        
        # Phase Plan 完了後、Phase 4-A を追加試行
        if retry_with_type_fix and type_fixer1 and type_fixer2 and result is not None:
            phase4a_spec = PhaseSpec(PhaseID.P4A_MIPS64_ABI, "MIPS64 ABI param fix (conservative)")
            
            self._debug_print("=" * 60)
            self._debug_print(f"Phase {PhaseID.P4A_MIPS64_ABI.value}: {phase4a_spec.description}")
            self._debug_print("=" * 60)
            
            phase_result = self.phase_handler.execute_phase(
                phase4a_spec, ctx, type_fixer1, type_fixer2, self._get_params_via_decompile
            )
            
            if phase_result.applied:
                retry_count += 1
                type_fix_result.retry_phase = phase_result.retry_name
                
                # ★ NEW: selective reanalysis
                analysis1, analysis2, result = self._selective_reanalysis_and_check(
                    ctx, phase_result, retry_count=retry_count
                )
                ctx.analysis1 = analysis1
                ctx.analysis2 = analysis2
                
                if result.is_equivalent is True:
                    self._debug_print(f"Phase {PhaseID.P4A_MIPS64_ABI.value}: EQUIVALENT")
                    result.total_time = time.time() - start_time
                    return result
                
                # SAT 時に Phase 4-B を試行
                if result.is_equivalent is False and retry_with_type_fix:
                    phase4b_result = self._try_phase4b_if_applicable(
                        result, ctx, retry_count=retry_count + 1, retry_with_type_fix=True
                    )
                    if phase4b_result is not None:
                        result = phase4b_result
                        if result.is_equivalent is True:
                            self._debug_print(
                                f"Phase 4-B: EQUIVALENT after MIPS64 ABI retry (from Phase 4-A)"
                            )
                            result.total_time = time.time() - start_time
                            return result
        
        # 最終結果
        self._debug_print("=" * 60)
        self._debug_print("Final Result (end of phase plan)")
        self._debug_print("=" * 60)
        
        if result is None:
            raise RuntimeError(
                "No phase was executed: phase_plan is empty or no result was produced"
            )
        
        result.total_time = time.time() - start_time
        
        return result
    
    # ★ NEW: Selective Reanalysis Helper
    def _selective_reanalysis_and_check(
        self,
        ctx: PhaseContext,
        phase_result: PhaseResult,
        retry_count: int
    ) -> Tuple[Optional[FunctionReturnAnalysis], Optional[FunctionReturnAnalysis], EquivalenceResult]:
        """変更された側だけ再解析して等価性をチェック
        
        Args:
            ctx: Phaseコンテキスト（既存の ctx.analysis1/2 を含む）
            phase_result: Phase実行結果（changed_binary1/2 情報を含む）
            retry_count: リトライカウント
        
        Returns:
            (analysis1, analysis2, result)
        """
        from ..analysis import ReturnAnalyzer
        
        start_time = time.time()
        
        # 再解析対象を決定
        need_reanalyze1 = phase_result.changed_binary1
        need_reanalyze2 = phase_result.changed_binary2
        
        self._debug_print(
            f"Selective reanalysis: binary1={need_reanalyze1}, binary2={need_reanalyze2}"
        )
        
        # binary1 の再解析または再利用
        if need_reanalyze1:
            self._debug_print(f"Re-analyzing binary1: {ctx.function_name1}")
            analyzer1 = ReturnAnalyzer(ctx.program1, debug=self.debug)
            try:
                analysis1 = analyzer1.analyze_function_by_name(
                    ctx.function_name1, ctx.decompile_timeout
                )
                if analysis1 is None:
                    # エラー処理
                    return self._create_reanalysis_error(
                        ctx, f"Function '{ctx.function_name1}' not found after type fix",
                        retry_count
                    )
            finally:
                analyzer1.dispose()
        else:
            self._debug_print(f"Reusing cached analysis for binary1")
            analysis1 = ctx.analysis1
            # ★ ctx.analysis1 が None の場合はエラー
            if analysis1 is None:
                return self._create_reanalysis_error(
                    ctx, f"Cached analysis for binary1 is not available",
                    retry_count
                )
        
        # binary2 の再解析または再利用
        if need_reanalyze2:
            self._debug_print(f"Re-analyzing binary2: {ctx.function_name2}")
            analyzer2 = ReturnAnalyzer(ctx.program2, debug=self.debug)
            try:
                analysis2 = analyzer2.analyze_function_by_name(
                    ctx.function_name2, ctx.decompile_timeout
                )
                if analysis2 is None:
                    return self._create_reanalysis_error(
                        ctx, f"Function '{ctx.function_name2}' not found after type fix",
                        retry_count
                    )
            finally:
                analyzer2.dispose()
        else:
            self._debug_print(f"Reusing cached analysis for binary2")
            analysis2 = ctx.analysis2
            # ★ ctx.analysis2 が None の場合はエラー
            if analysis2 is None:
                return self._create_reanalysis_error(
                    ctx, f"Cached analysis for binary2 is not available",
                    retry_count
                )
        
        # Stage plan を実行（ここで analysis1, analysis2 は確実に non-None）
        result = self._run_stage_plan(
            analysis1, analysis2,
            ctx.binary1_name, ctx.binary2_name,
            ctx.save_formula,
            type_fix_result=ctx.type_fix_result,
            retry_count=retry_count,
            original_signature1=ctx.original_signature1,
            original_signature2=ctx.original_signature2
        )
        
        return analysis1, analysis2, result

    def _create_reanalysis_error(
        self,
        ctx: PhaseContext,
        error_message: str,
        retry_count: int
    ) -> Tuple[Optional[FunctionReturnAnalysis], Optional[FunctionReturnAnalysis], EquivalenceResult]:
        """再解析エラー用の結果を作成"""
        start_time = time.time()
        
        result = EquivalenceResult(
            is_equivalent=None,
            function1_name=ctx.function_name1,
            function2_name=ctx.function_name2,
            binary1_name=ctx.binary1_name,
            binary2_name=ctx.binary2_name,
            solver_results=ParallelResult(results=[]),
            total_time=time.time() - start_time,
            error_message=error_message,
            type_fix_result=ctx.type_fix_result,
            retry_count=retry_count,
            function1_signature=ctx.original_signature1,
            function2_signature=ctx.original_signature2,
            constrained_fragments=[]
        )
        
        return ctx.analysis1, ctx.analysis2, result
    
    # ★ [P3修正] _retry_with_abi_constraints の完全実装を復元
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
                constrained_fragments=[],
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
    
    # ★ [P2追加] Stage loop を実行
    def _run_stage_plan(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        binary1_name: str,
        binary2_name: str,
        save_formula: bool,
        type_fix_result: Optional[TypeFixResult],
        retry_count: int,
        original_signature1: Optional[FunctionSignature],
        original_signature2: Optional[FunctionSignature]
    ) -> EquivalenceResult:
        """
        Stage plan を実行
        
        デフォルトの Stage plan:
        1. S_PAIRWISE: pairwise strategy で判定
        2. S_MONOLITHIC_FALLBACK: UNKNOWN 時のみ monolithic fallback
        
        Returns:
            最終的な EquivalenceResult
        """
        result = None
        stage_path = []  # ★ [P2追加] 実際に通った stage を記録
        
        for stage_spec in self.stage_plan:
            stage_id = stage_spec.stage_id
            stage_path.append(stage_id.value)  # ★ 記録
            
            self._debug_print("-" * 60)
            self._debug_print(f"Stage {stage_id.value}: {stage_spec.description}")
            self._debug_print("-" * 60)
            
            # Stage を実行
            if stage_spec.strategy == "pairwise":
                strategy = self.pairwise_strategy
            elif stage_spec.strategy == "monolithic":
                strategy = self.monolithic_strategy
            else:
                raise ValueError(f"Unknown strategy: {stage_spec.strategy}")
            
            # Strategy を実行
            result = self.check(
                analysis1, analysis2,
                binary1_name, binary2_name,
                save_formula,
                type_fix_result=type_fix_result,
                retry_count=retry_count,
                original_signature1=original_signature1,
                original_signature2=original_signature2,
                force_strategy=strategy
            )
            
            # ★ [P2追加] stage_path を記録
            result.stage_path = stage_path.copy()
            
            # 結果判定
            if result.is_equivalent is True:
                # UNSAT → 即終了
                self._debug_print(f"Stage {stage_id.value}: EQUIVALENT - stopping stage plan")
                return result
            
            elif result.is_equivalent is False:
                # SAT → 即終了
                self._debug_print(f"Stage {stage_id.value}: NOT EQUIVALENT - stopping stage plan")
                return result
            
            else:
                # UNKNOWN/TIMEOUT
                if stage_id == StageID.S_PAIRWISE:
                    # pairwise が UNKNOWN → monolithic fallback へ
                    self._debug_print(f"Stage {stage_id.value}: UNKNOWN - proceeding to fallback")
                    continue
                else:
                    # fallback も UNKNOWN → 終了
                    self._debug_print(f"Stage {stage_id.value}: UNKNOWN - end of stage plan")
                    return result
        
        # Stage plan 完了
        if result is None:
            raise RuntimeError(
                "No stage was executed: stage_plan is empty or no result was produced"
            )
        
        return result
    
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
        original_signature2: Optional[FunctionSignature] = None,
        force_strategy = None  # ★ [P2追加] Stage から strategy を指定可能に
    ) -> EquivalenceResult:
        """2つの関数の等価性を判定"""
        start_time = time.time()
        
        if original_signature1 is None:
            original_signature1 = FunctionSignature.from_analysis(analysis1)
        if original_signature2 is None:
            original_signature2 = FunctionSignature.from_analysis(analysis2)
        
        try:
            # リライトを適用
            analysis1, analysis2, rewrite_info = self._apply_rewrite(analysis1, analysis2)
            
            # ★ [P2修正] strategy を選択
            strategy = force_strategy if force_strategy is not None else self.check_strategy
            
            # 戦略を使用してチェック
            self._debug_print(f"Using strategy: {strategy.__class__.__name__}")
            strategy_result = strategy.check(analysis1, analysis2, save_formula)
            
            if self.debug and strategy_result.smt_formula:
                print("\n" + "=" * 60)
                print("Generated SMT formula:")
                print("=" * 60)
                print(strategy_result.smt_formula)
                print("=" * 60 + "\n")
            
            total_time = time.time() - start_time
            
            # 反例をフォーマット
            counterexample = None
            if strategy_result.is_equivalent is False and strategy_result.counterexample_raw:
                counterexample = self._format_counterexample(
                    strategy_result.counterexample_raw,
                    analysis1, analysis2,
                    strategy_result.return_var1 or "return_1",
                    strategy_result.return_var2 or "return_2"
                )
            
            return EquivalenceResult(
                is_equivalent=strategy_result.is_equivalent,
                function1_name=analysis1.function_name,
                function2_name=analysis2.function_name,
                binary1_name=binary1_name,
                binary2_name=binary2_name,
                solver_results=strategy_result.solver_results,
                counterexample=counterexample,
                smt_formula=strategy_result.smt_formula if save_formula else None,
                total_time=total_time,
                type_fix_result=type_fix_result,
                retry_count=retry_count,
                function1_signature=original_signature1,
                function2_signature=original_signature2,
                constrained_fragments=strategy_result.constrained_fragments,
                rewrite_info=rewrite_info,
                pairwise_stats={
                    'total_pairs': strategy_result.total_pairs,
                    'unsat_pairs': strategy_result.unsat_pairs,
                    'sat_pairs': strategy_result.sat_pairs,
                    'unknown_pairs': strategy_result.unknown_pairs,
                    'error_pairs': strategy_result.error_pairs,
                } if strategy_result.total_pairs > 0 else None,
                sat_pair_info=strategy_result.sat_pair_info
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
        
        # ★ [P1修正] self.check() ではなく _run_stage_plan() を呼ぶ
        self._debug_print("Running stage plan...")
        result = self._run_stage_plan(
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