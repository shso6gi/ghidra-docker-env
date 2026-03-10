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
from .debug_trace import (  # ★ 新規追加
    DebugTrace, Attempt, TransitionReason, PairwiseDecisiveInfo, NormalizationRuleApplication
)


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
        
        # ★ strategy 引数に応じて stage_plan を切り替える
        if strategy == "pairwise":
            self.stage_plan = [
                StageSpec(StageID.S_PAIRWISE, "Pairwise strategy", strategy="pairwise"),
                StageSpec(StageID.S_MONOLITHIC_FALLBACK, "Monolithic fallback (UNKNOWN only)", strategy="monolithic"),
            ]
            self.check_strategy = self.pairwise_strategy
        elif strategy == "monolithic":
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
        
        新フロー（Stage/Phase ループ骨格 + Selective Reanalysis + Debug Trace）:
        1. DebugTrace を初期化
        2. Phase plan を定義（デフォルト: P0_BASE -> P1_SIGNEDNESS -> P2_PATTERN_INT）
        3. 各 Phase ごとに：
           a. Phase を実行（型修正など、P0 は何もしない）
           b. 変更された側だけ再解析（未変更側は ctx.analysis1/2 を再利用）
           c. Stage plan を実行（等価性判定）
           d. **Attempt を記録**
           e. 結果に応じた遷移判定
        4. Phase Plan 完了後、Phase 4-A（MIPS64 conservative fix）を追加試行
        5. 最終的な EquivalenceResult に debug_trace を設定
        """
        start_time = time.time()
        binary1_name = program1.getName() if hasattr(program1, 'getName') else "binary1"
        binary2_name = program2.getName() if hasattr(program2, 'getName') else "binary2"
        
        type_fix_result = TypeFixResult()
        
        # ★ DebugTrace を初期化
        debug_trace = DebugTrace()
        
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
        attempt_id = 0
        
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
                    
                    # ★ Attempt 記録（スキップ）
                    self._record_attempt(
                        debug_trace, attempt_id, retry_count, phase_id.value,
                        [], self.strategy_name, None, TransitionReason.NO_CHANGES.value,
                        type_fix_result, None, None, None, None, None, None, None, 0.0  # ★ mips64_abi_constraints: None を追加
                    )
                    attempt_id += 1
                    
                    continue  # 次 Phase へ
                
                # 変更された側だけ再解析
                retry_count += 1
                type_fix_result.retry_phase = phase_result.retry_name
                
                analysis1, analysis2, result = self._selective_reanalysis_and_check(
                    ctx, phase_result, retry_count=retry_count
                )
                
                # 再解析結果を ctx に戻す
                ctx.analysis1 = analysis1
                ctx.analysis2 = analysis2
            
            # ★ 結果記録前に Phase 4-B 試行可能性をチェック
            will_try_phase4b = False
            if result.is_equivalent is False and retry_with_type_fix:
                # run_phase4_mips64_retry を先にチェック（実際の retry はしない）
                abi_constraints_check = self.phase_handler.run_phase4_mips64_retry(result, ctx)
                will_try_phase4b = abi_constraints_check is not None
            
            # ★ Attempt を記録
            transition_reason = self._get_transition_reason(
                result, retry_with_type_fix, phase_id.value, will_try_phase4b
            )
            self._record_attempt_from_result(
                debug_trace, attempt_id, retry_count, phase_id.value,
                result, transition_reason, type_fix_result
            )
            attempt_id += 1
            
            # 結果に応じた遷移判定
            
            # UNSAT → 即終了
            if result.is_equivalent is True:
                self._debug_print(f"Phase {phase_id.value}: EQUIVALENT - stopping")
                result.total_time = time.time() - start_time
                result.debug_trace = debug_trace
                debug_trace.final_result = True
                debug_trace.total_time = result.total_time
                return result
            
            # critical error → 即終了
            if result.has_critical_error():
                self._debug_print(f"Phase {phase_id.value}: Critical error - {result.error_message}")
                result.total_time = time.time() - start_time
                result.debug_trace = debug_trace
                debug_trace.final_result = None
                debug_trace.total_time = result.total_time
                debug_trace.error_message = result.error_message
                return result
            
            # SAT → Phase 4-B（MIPS64 偽反例対策）のみ試行
            if result.is_equivalent is False:
                self._debug_print(f"Phase {phase_id.value}: SAT - checking for Phase 4-B eligibility")
                
                if retry_with_type_fix and will_try_phase4b:
                    # Phase 4-B 実行（既にチェック済みなので再度 run_phase4_mips64_retry を呼ぶ）
                    abi_constraints = self.phase_handler.run_phase4_mips64_retry(result, ctx)
                    
                    if abi_constraints:
                        phase4b_result = self._retry_with_abi_constraints(
                            ctx, abi_constraints, retry_count=retry_count + 1
                        )
                        
                        if phase4b_result is not None:
                            result = phase4b_result
                            
                            # ★ Phase 4-B の Attempt を記録
                            p4b_transition = self._get_transition_reason(result, retry_with_type_fix)
                            self._record_attempt_from_result(
                                debug_trace, attempt_id, retry_count + 1, "P4B_MIPS64_SPURIOUS",
                                result, p4b_transition, type_fix_result
                            )
                            attempt_id += 1
                            
                            if result.is_equivalent is True:
                                self._debug_print(
                                    f"Phase 4-B: EQUIVALENT after MIPS64 ABI retry (from {phase_id.value})"
                                )
                                result.total_time = time.time() - start_time
                                result.debug_trace = debug_trace
                                debug_trace.final_result = True
                                debug_trace.total_time = result.total_time
                                return result
                else:
                    self._debug_print(f"Phase 4-B: Skipped")
                
                # SAT で終了
                self._debug_print(f"Phase {phase_id.value}: NOT EQUIVALENT - stopping")
                result.total_time = time.time() - start_time
                result.debug_trace = debug_trace
                debug_trace.final_result = False
                debug_trace.total_time = result.total_time
                return result
            
            # UNKNOWN/TIMEOUT → 次 Phase へ進むか判定
            should_retry = self.phase_handler.should_retry(result)
            retry_reason = self.phase_handler.get_retry_reason(result)
            self._debug_print(f"Phase {phase_id.value} result: {retry_reason}")
            
            if not should_retry:
                result.total_time = time.time() - start_time
                result.debug_trace = debug_trace
                debug_trace.final_result = None
                debug_trace.total_time = result.total_time
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
                
                # 変更された側だけ再解析
                analysis1, analysis2, result = self._selective_reanalysis_and_check(
                    ctx, phase_result, retry_count=retry_count
                )
                ctx.analysis1 = analysis1
                ctx.analysis2 = analysis2
                
                # ★ 修正前: will_try_phase4b を計算せずに transition_reason を取得
                # transition_reason = self._get_transition_reason(result, retry_with_type_fix)
                
                # ★ 修正: Phase 4-B を試行するかチェック
                will_try_phase4b = False
                if result.is_equivalent is False:
                    # Phase 4-B の条件を事前チェック
                    abi_constraints_check = self.phase_handler.run_phase4_mips64_retry(result, ctx)
                    will_try_phase4b = abi_constraints_check is not None
                
                # ★ Attempt を記録（will_try_phase4b を渡す）
                transition_reason = self._get_transition_reason(
                    result, retry_with_type_fix, PhaseID.P4A_MIPS64_ABI.value, will_try_phase4b
                )
                self._record_attempt_from_result(
                    debug_trace, attempt_id, retry_count, PhaseID.P4A_MIPS64_ABI.value,
                    result, transition_reason, type_fix_result
                )
                attempt_id += 1
                
                if result.is_equivalent is True:
                    self._debug_print(f"Phase {PhaseID.P4A_MIPS64_ABI.value}: EQUIVALENT")
                    result.total_time = time.time() - start_time
                    result.debug_trace = debug_trace
                    debug_trace.final_result = True
                    debug_trace.total_time = result.total_time
                    return result
                
                # SAT 時に Phase 4-B を試行
                if result.is_equivalent is False and retry_with_type_fix:
                    # ★ 修正: 既にチェック済みなので、条件分岐を追加
                    if will_try_phase4b:
                        # 再度 run_phase4_mips64_retry を呼ぶ（実際の ABI constraints を取得）
                        abi_constraints = self.phase_handler.run_phase4_mips64_retry(result, ctx)
                        
                        if abi_constraints:
                            phase4b_result = self._retry_with_abi_constraints(
                                ctx, abi_constraints, retry_count=retry_count + 1
                            )
                            if phase4b_result is not None:
                                result = phase4b_result
                                
                                # ★ Phase 4-B の Attempt を記録
                                p4b_transition = self._get_transition_reason(result, retry_with_type_fix)
                                self._record_attempt_from_result(
                                    debug_trace, attempt_id, retry_count + 1, "P4B_MIPS64_SPURIOUS",
                                    result, p4b_transition, type_fix_result
                                )
                                attempt_id += 1
                                
                                if result.is_equivalent is True:
                                    self._debug_print(
                                        f"Phase 4-B: EQUIVALENT after MIPS64 ABI retry (from Phase 4-A)"
                                    )
                                    result.total_time = time.time() - start_time
                                    result.debug_trace = debug_trace
                                    debug_trace.final_result = True
                                    debug_trace.total_time = result.total_time
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
        result.debug_trace = debug_trace
        debug_trace.final_result = result.is_equivalent
        debug_trace.total_time = result.total_time
        
        return result
    
    # ★ 新規: 遷移理由を判定
    def _get_transition_reason(
        self,
        result: EquivalenceResult,
        retry_with_type_fix: bool,
        phase_id: Optional[str] = None,
        will_try_phase4b: bool = False
    ) -> str:
        """結果から遷移理由を取得（Phase レベルの遷移理由）
        
        Note:
            stage fallback は stage_path で既に表現されているため、
            ここでは Phase レベルの遷移理由のみを記録する。
        """
        if result.is_equivalent is True:
            return TransitionReason.UNSAT.value
        elif result.is_equivalent is False:
            # SAT時にPhase 4-Bが適用可能かチェック
            if will_try_phase4b:
                return TransitionReason.SAT_PHASE4B.value
            return TransitionReason.SAT.value
        elif result.has_critical_error():
            return TransitionReason.CRITICAL_ERROR.value
        elif result.is_timeout():
            return TransitionReason.TIMEOUT.value
        else:
            # UNKNOWN
            # ★ stage_path チェックを削除（stage fallback は stage_path で表現）
            return TransitionReason.UNKNOWN.value
    
    # ★ 新規: Attempt を記録（汎用版）
    def _record_attempt(
        self,
        debug_trace: DebugTrace,
        attempt_id: int,
        retry_count: int,
        phase: str,
        stage_path: List[str],
        strategy: str,
        result: Optional[bool],
        transition_reason: str,
        type_fix_result: Optional[TypeFixResult],
        rewrite_info: Optional[RewriteInfo],
        solver_results: Optional[ParallelResult],
        final_smt: Optional[str],
        counterexample: Optional[Dict],
        pairwise_decisive: Optional[PairwiseDecisiveInfo],
        normalization_rules: Optional[List],
        mips64_abi_constraints: Optional[Dict],
        elapsed_time: float
    ):
        """Attemptを記録"""
        attempt = Attempt(
            attempt_id=attempt_id,
            retry_count=retry_count,
            phase=phase,
            stage_path=stage_path.copy() if stage_path else [],
            strategy=strategy,
            result=result,
            transition_reason=transition_reason,
            type_fix_result=type_fix_result.to_dict() if type_fix_result else None,
            rewrite_info=rewrite_info.to_dict() if rewrite_info else None,
            solver_results=solver_results.to_dict() if solver_results else None,
            final_smt_excerpt=final_smt[:500] if final_smt else None,
            final_smt=final_smt,  # ★ 完全なSMTを保存
            counterexample=counterexample,
            pairwise_decisive=pairwise_decisive,
            normalization_rules=normalization_rules or [],
            mips64_abi_constraints=mips64_abi_constraints,
            elapsed_time=elapsed_time
        )
        
        debug_trace.add_attempt(attempt)
    
    # ★ 新規: EquivalenceResult から Attempt を記録
    def _record_attempt_from_result(
        self,
        debug_trace: DebugTrace,
        attempt_id: int,
        retry_count: int,
        phase: str,
        result: EquivalenceResult,
        transition_reason: str,
        type_fix_result: TypeFixResult
    ):
        """EquivalenceResult から Attempt を記録"""
        # Pairwise decisive 情報を構築
        pairwise_decisive = None
        if result.pairwise_stats and result.pairwise_stats['total_pairs'] > 0:
            decisive_result_str = "UNKNOWN"
            if result.is_equivalent is True:
                decisive_result_str = "UNSAT"
            elif result.is_equivalent is False:
                decisive_result_str = "SAT"
            
            pairwise_decisive = PairwiseDecisiveInfo(
                decisive_result=decisive_result_str,
                total_pairs=result.pairwise_stats['total_pairs'],
                unsat_pairs=result.pairwise_stats['unsat_pairs'],
                sat_pairs=result.pairwise_stats['sat_pairs'],
                unknown_pairs=result.pairwise_stats['unknown_pairs']
            )
            
            # SAT時のdecisive pair情報
            if result.sat_pair_info:
                info = result.sat_pair_info
                pairwise_decisive.decisive_pair = (info['i'], info['j'])
                pairwise_decisive.pair_stage = info.get('pair_stage', 'unknown')
                pairwise_decisive.case1_summary = info.get('case1_summary')
                pairwise_decisive.case2_summary = info.get('case2_summary')
                pairwise_decisive.value1_expr = info.get('value1', '')[:200]
                pairwise_decisive.value2_expr = info.get('value2', '')[:200]
                
                # ★ 修正: 完全なクエリと抜粋の両方を保存
                final_query_full = info.get('final_query')
                if final_query_full:
                    pairwise_decisive.final_query = final_query_full
                    pairwise_decisive.final_query_excerpt = final_query_full[:200]
                elif result.smt_formula:
                    # fallback: smt_formula から設定
                    pairwise_decisive.final_query = result.smt_formula
                    pairwise_decisive.final_query_excerpt = result.smt_formula[:200]
        
        # 正規化ルールを抽出
        normalization_rules = []
        if hasattr(result, 'normalization_rules') and result.normalization_rules:
            from .debug_trace import NormalizationRuleApplication
            for rule in result.normalization_rules:
                if isinstance(rule, NormalizationRuleApplication):
                    normalization_rules.append(rule)
                else:
                    normalization_rules.append(rule)
        
        # Counterexample を辞書に変換
        counterexample_dict = None
        if result.counterexample:
            counterexample_dict = result.counterexample.to_dict()
        
        # MIPS64 ABI constraints を辞書に変換
        mips64_abi_dict = None
        if result.mips64_abi_constraints:
            mips64_abi_dict = {
                k: {"signedness": v[0], "narrow_bits": v[1]}
                for k, v in result.mips64_abi_constraints.items()
            }
        
        self._record_attempt(
            debug_trace,
            attempt_id,
            retry_count,
            phase,
            result.stage_path,
            self.strategy_name,
            result.is_equivalent,
            transition_reason,
            type_fix_result,
            result.rewrite_info,
            result.solver_results,
            result.smt_formula,
            counterexample_dict,
            pairwise_decisive,
            normalization_rules,
            mips64_abi_dict,
            result.total_time
        )
    
    def _selective_reanalysis_and_check(
        self,
        ctx: PhaseContext,
        phase_result: PhaseResult,
        retry_count: int
    ) -> Tuple[Optional[FunctionReturnAnalysis], Optional[FunctionReturnAnalysis], EquivalenceResult]:
        """変更された側だけ再解析して等価性をチェック"""
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
                    return self._create_reanalysis_error(
                        ctx, f"Function '{ctx.function_name1}' not found after type fix",
                        retry_count
                    )
            finally:
                analyzer1.dispose()
        else:
            self._debug_print(f"Reusing cached analysis for binary1")
            analysis1 = ctx.analysis1
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
            if analysis2 is None:
                return self._create_reanalysis_error(
                    ctx, f"Cached analysis for binary2 is not available",
                    retry_count
                )
        
        # Stage plan を実行
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
            
            # ABI制約セクションを FormulaBuilder に完全委譲
            abi_assertion_section = self.formula_builder.build_abi_assertion_section(
                abi_constraints, "_1", "_2"
            )
            
            # SMT式を構築（ABI制約を extra_assertions として渡す）
            result = self.formula_builder.build_equivalence_formula_extended(
                analysis1, analysis2,
                extra_assertions=abi_assertion_section if abi_assertion_section else None
            )
            
            smt_formula = result.formula
            return_var1 = result.return_var1
            return_var2 = result.return_var2
            
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
            
            # ★ 修正: save_formula に関わらず smt_formula を保持（debug trace 用）
            # user-facing 出力は EquivalenceResult.to_string() / to_dict() で制御される
            return EquivalenceResult(
                is_equivalent=parallel_result.is_equivalent,
                function1_name=ctx.function_name1,
                function2_name=ctx.function_name2,
                binary1_name=ctx.binary1_name,
                binary2_name=ctx.binary2_name,
                solver_results=parallel_result,
                counterexample=counterexample,
                smt_formula=smt_formula,  # ★ 条件削除: 常に保存
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
        """Stage plan を実行"""
        result = None
        stage_path = []
        
        for stage_spec in self.stage_plan:
            stage_id = stage_spec.stage_id
            stage_path.append(stage_id.value)
            
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
            
            # stage_path を記録
            result.stage_path = stage_path.copy()
            
            # 結果判定
            if result.is_equivalent is True:
                self._debug_print(f"Stage {stage_id.value}: EQUIVALENT - stopping stage plan")
                return result
            
            elif result.is_equivalent is False:
                self._debug_print(f"Stage {stage_id.value}: NOT EQUIVALENT - stopping stage plan")
                return result
            
            else:
                # UNKNOWN/TIMEOUT
                if stage_id == StageID.S_PAIRWISE:
                    self._debug_print(f"Stage {stage_id.value}: UNKNOWN - proceeding to fallback")
                    continue
                else:
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
        force_strategy = None
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
            
            # strategy を選択
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
                # ★ 修正: save_formula に関わらず smt_formula を保持（debug trace 用）
                # ただし to_string() での出力は save_formula で制御
                smt_formula=strategy_result.smt_formula,  # ← 条件を削除
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
                sat_pair_info=strategy_result.sat_pair_info,
                normalization_rules=strategy_result.normalization_rules
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
        
        # Stage plan を実行
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