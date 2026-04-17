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
from .result_factory import create_error_result, create_reanalysis_error
from .phases.handler import PhaseHandler, PhaseContext, PhaseResult
from .reanalysis import analyze_and_check_with_analysis, selective_reanalysis_and_check
from ..transform.rewrite import ExpressionRewriter, rewrite_analysis_returns
from .strategies.pairwise import PairwiseStrategy
from .strategies.loop_template import LoopTemplatePairwiseStrategy
from .strategies.monolithic import MonolithicStrategy
from .normalize import NormalizationSettings
from .debug_trace import DebugTrace, PairwiseDecisiveInfo
from .attempts import get_transition_reason, record_attempt, record_attempt_from_result
from .recursive_abstraction import abstract_recursive_calls  # type: ignore[import-not-found]
from .workflow import run_check_from_binaries


# ============================================================================
# Stage 定義（新フロー骨格）
# ============================================================================

class StageID(Enum):
    """Stage識別子"""
    S_PAIRWISE = "S_PAIRWISE"
    S_LOOP_TEMPLATE_ABSTRACTION = "S_LOOP_TEMPLATE_ABSTRACTION"
    S_ABSTRACT_RECURSIVE_SUMMARY = "S_ABSTRACT_RECURSIVE_SUMMARY"
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
    StageSpec(StageID.S_ABSTRACT_RECURSIVE_SUMMARY, "Recursive abstraction fallback (UNKNOWN only)", strategy="abstract_pairwise"),
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
        pairwise_save_unknown: bool = False,
        normalization_mode: str = "safe",
        enable_fact_normalization: bool = False,
        enable_template_abstraction: bool = False,
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
        self.normalization_mode = normalization_mode
        self.enable_fact_normalization = enable_fact_normalization
        self.enable_template_abstraction = enable_template_abstraction
        self.normalization_settings = self._build_normalization_settings(
            normalization_mode,
            enable_fact_normalization,
        )
        self.formula_builder = FormulaBuilder(debug=debug)
        self.solver_runner = ParallelSolverRunner(timeout=timeout, debug=debug)
        self.phase_handler = PhaseHandler(self.type_fixer_config, debug=debug)
        
        # 各 strategy の準備
        self.pairwise_strategy = PairwiseStrategy(
            self.formula_builder,
            self.solver_runner,
            debug=debug,
            normalization_settings=self.normalization_settings,
        )
        self.pairwise_strategy.per_query_timeout = pairwise_timeout
        self.pairwise_strategy.per_query_timeout_hard = pairwise_timeout_hard
        self.pairwise_strategy.save_unknown_queries = pairwise_save_unknown
        
        self.monolithic_strategy = MonolithicStrategy(
            self.formula_builder,
            self.solver_runner,
            debug=debug,
            normalization_settings=self.normalization_settings,
        )
        self.loop_template_strategy = LoopTemplatePairwiseStrategy(
            self.formula_builder,
            self.solver_runner,
            debug=debug,
            normalization_settings=self.normalization_settings,
        )
        self.loop_template_strategy.per_query_timeout = pairwise_timeout
        self.loop_template_strategy.per_query_timeout_hard = pairwise_timeout_hard
        self.loop_template_strategy.save_unknown_queries = pairwise_save_unknown
        
        # ★ strategy 引数に応じて stage_plan を切り替える
        if strategy == "pairwise":
            self.stage_plan = [
                StageSpec(StageID.S_PAIRWISE, "Pairwise strategy", strategy="pairwise"),
                StageSpec(StageID.S_ABSTRACT_RECURSIVE_SUMMARY, "Recursive abstraction fallback (UNKNOWN only)", strategy="abstract_pairwise"),
                StageSpec(StageID.S_MONOLITHIC_FALLBACK, "Monolithic fallback (UNKNOWN only)", strategy="monolithic"),
            ]
            if self.enable_template_abstraction:
                self.stage_plan.insert(
                    1,
                    StageSpec(
                        StageID.S_LOOP_TEMPLATE_ABSTRACTION,
                        "Exact loop-template abstraction fallback (UNKNOWN only)",
                        strategy="loop_template_pairwise",
                    ),
                )
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

    def _build_normalization_settings(
        self,
        normalization_mode: str,
        enable_fact_normalization: bool,
    ) -> NormalizationSettings:
        if normalization_mode == "off":
            return NormalizationSettings.off()
        if normalization_mode == "safe":
            return NormalizationSettings.safe()
        if normalization_mode == "full":
            return NormalizationSettings.full(
                enable_fact_simplifications=enable_fact_normalization
            )
        raise ValueError(f"Unknown normalization mode: {normalization_mode}")

    def _create_type_fixer(self, program):
        """TypeFixer の生成を 1 箇所に集約する。"""
        return TypeFixer(program, self.type_fixer_config, debug=self.debug)
    
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
        
        return self._retry_with_iterative_abi_constraints(
            ctx, abi_constraints, retry_count=retry_count
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
        return run_check_from_binaries(
            self,
            program1,
            program2,
            function_name1,
            function_name2,
            decompile_timeout=decompile_timeout,
            save_formula=save_formula,
            retry_with_type_fix=retry_with_type_fix,
        )
    
    # ★ 新規: 遷移理由を判定
    def _get_transition_reason(
        self,
        result: EquivalenceResult,
        retry_with_type_fix: bool,
        phase_id: Optional[str] = None,
        will_try_phase4b: bool = False
    ) -> str:
        """結果から遷移理由を取得する互換ラッパー"""
        return get_transition_reason(
            result, retry_with_type_fix, phase_id=phase_id, will_try_phase4b=will_try_phase4b
        )
    
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
        original_function1_signature: Optional[Dict],
        original_function2_signature: Optional[Dict],
        effective_function1_signature: Optional[Dict],
        effective_function2_signature: Optional[Dict],
        function1_signature_hypotheses: Optional[List[Dict]],
        function2_signature_hypotheses: Optional[List[Dict]],
        solver_results: Optional[ParallelResult],
        final_smt: Optional[str],
        counterexample: Optional[Dict],
        pairwise_decisive: Optional[PairwiseDecisiveInfo],
        normalization_rules: Optional[List],
        mips64_abi_constraints: Optional[Dict],
        elapsed_time: float
    ):
        """Attempt を記録する互換ラッパー"""
        record_attempt(
            debug_trace=debug_trace,
            attempt_id=attempt_id,
            retry_count=retry_count,
            phase=phase,
            stage_path=stage_path,
            strategy=strategy,
            result=result,
            transition_reason=transition_reason,
            type_fix_result=type_fix_result,
            rewrite_info=rewrite_info,
            original_function1_signature=original_function1_signature,
            original_function2_signature=original_function2_signature,
            effective_function1_signature=effective_function1_signature,
            effective_function2_signature=effective_function2_signature,
            function1_signature_hypotheses=function1_signature_hypotheses,
            function2_signature_hypotheses=function2_signature_hypotheses,
            solver_results=solver_results,
            final_smt=final_smt,
            counterexample=counterexample,
            pairwise_decisive=pairwise_decisive,
            normalization_rules=normalization_rules,
            mips64_abi_constraints=mips64_abi_constraints,
            elapsed_time=elapsed_time,
        )
    
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
        """EquivalenceResult から Attempt を記録する互換ラッパー"""
        record_attempt_from_result(
            debug_trace=debug_trace,
            attempt_id=attempt_id,
            retry_count=retry_count,
            phase=phase,
            result=result,
            transition_reason=transition_reason,
            type_fix_result=type_fix_result,
            strategy_name=self.strategy_name,
        )
    
    def _selective_reanalysis_and_check(
        self,
        ctx: PhaseContext,
        phase_result: PhaseResult,
        retry_count: int
    ) -> Tuple[Optional[FunctionReturnAnalysis], Optional[FunctionReturnAnalysis], EquivalenceResult]:
        """再解析 helper への互換ラッパー"""
        return selective_reanalysis_and_check(
            self, ctx, phase_result, retry_count
        )

    def _create_reanalysis_error(
        self,
        ctx: PhaseContext,
        error_message: str,
        retry_count: int
    ) -> Tuple[Optional[FunctionReturnAnalysis], Optional[FunctionReturnAnalysis], EquivalenceResult]:
        """再解析エラー結果作成の互換ラッパー"""
        return create_reanalysis_error(ctx, error_message, retry_count)
    
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
                effective_function1_signature=FunctionSignature.from_analysis(analysis1),
                effective_function2_signature=FunctionSignature.from_analysis(analysis2),
                function1_signature_hypotheses=list(analysis1.signature_hypotheses),
                function2_signature_hypotheses=list(analysis2.signature_hypotheses),
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

    def _merge_abi_constraints(
        self,
        accumulated: Dict[str, Tuple[str, int]],
        discovered: Dict[str, Tuple[str, int]],
    ) -> Tuple[Dict[str, Tuple[str, int]], Dict[str, Tuple[str, int]], List[str]]:
        """ABI 制約を累積し、新規追加分と競合を返す。"""
        merged = dict(accumulated)
        added: Dict[str, Tuple[str, int]] = {}
        conflicts: List[str] = []

        for param_name, constraint in discovered.items():
            existing = merged.get(param_name)
            if existing is None:
                merged[param_name] = constraint
                added[param_name] = constraint
                continue

            if existing != constraint:
                conflicts.append(param_name)

        return merged, added, conflicts

    def _retry_with_iterative_abi_constraints(
        self,
        ctx: PhaseContext,
        abi_constraints: Dict[str, Tuple[str, int]],
        retry_count: int,
    ) -> EquivalenceResult:
        """ABI 制約を累積しながら Phase 4-B を反復する。"""
        if not abi_constraints:
            return self._retry_with_abi_constraints(ctx, abi_constraints, retry_count)

        param_budget = 0
        if ctx.analysis1 is not None:
            param_budget += len(ctx.analysis1.parameters)
        if ctx.analysis2 is not None:
            param_budget += len(ctx.analysis2.parameters)
        max_iterations = max(1, param_budget or len(abi_constraints))

        accumulated = dict(abi_constraints)
        current_retry_count = retry_count
        latest_result: Optional[EquivalenceResult] = None

        for iteration in range(max_iterations):
            self._debug_print(
                f"Phase 4-B iterative retry {iteration + 1}/{max_iterations} "
                f"with constraints: {accumulated}"
            )
            latest_result = self._retry_with_abi_constraints(
                ctx, accumulated, current_retry_count
            )

            if latest_result.is_equivalent is not False:
                return latest_result

            discovered = self.phase_handler.run_phase4_mips64_retry(latest_result, ctx)
            if not discovered:
                self._debug_print(
                    "Phase 4-B iterative retry: no additional ABI constraints found"
                )
                return latest_result

            merged, added, conflicts = self._merge_abi_constraints(
                accumulated, discovered
            )
            if conflicts:
                self._debug_print(
                    "Phase 4-B iterative retry: conflicting ABI constraints "
                    f"detected for {conflicts}; stopping"
                )
                return latest_result

            if not added:
                self._debug_print(
                    "Phase 4-B iterative retry: discovered constraints were already "
                    "applied; stopping"
                )
                return latest_result

            accumulated = merged
            current_retry_count += 1

        self._debug_print(
            "Phase 4-B iterative retry: reached iteration limit; returning latest result"
        )
        if latest_result is None:
            return self._retry_with_abi_constraints(ctx, abi_constraints, retry_count)
        return latest_result

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
        last_result = None
        stage_path = []
        
        for stage_spec in self.stage_plan:
            stage_id = stage_spec.stage_id
            if (
                stage_id == StageID.S_LOOP_TEMPLATE_ABSTRACTION
                and not self._should_try_loop_template_stage(last_result)
            ):
                self._debug_print(
                    "Stage S_LOOP_TEMPLATE_ABSTRACTION: skipped because prior result was not a timeout-driven UNKNOWN"
                )
                continue
            stage_path.append(stage_id.value)
            
            self._debug_print("-" * 60)
            self._debug_print(f"Stage {stage_id.value}: {stage_spec.description}")
            self._debug_print("-" * 60)
            
            # Stage を実行
            if stage_spec.strategy == "pairwise":
                strategy = self.pairwise_strategy
            elif stage_spec.strategy == "loop_template_pairwise":
                strategy = self.loop_template_strategy
            elif stage_spec.strategy == "abstract_pairwise":
                strategy = None
            elif stage_spec.strategy == "monolithic":
                strategy = self.monolithic_strategy
            else:
                raise ValueError(f"Unknown strategy: {stage_spec.strategy}")
            
            # Strategy を実行
            if stage_spec.strategy == "abstract_pairwise":
                result = self._run_recursive_abstraction_stage(
                    analysis1,
                    analysis2,
                    binary1_name,
                    binary2_name,
                    save_formula,
                    type_fix_result,
                    retry_count,
                    original_signature1,
                    original_signature2,
                )
                if result is None:
                    self._debug_print(
                        f"Stage {stage_id.value}: no abstraction candidate - proceeding to next fallback"
                    )
                    stage_path.pop()
                    if self._should_skip_monolithic_fallback(analysis1, analysis2):
                        self._debug_print(
                            "Stage S_MONOLITHIC_FALLBACK: skipped due to incomplete control-flow summary"
                        )
                        if last_result is None:
                            raise RuntimeError(
                                "Recursive abstraction produced no candidate and no prior stage result exists"
                            )
                        return last_result
                    continue
            else:
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
            last_result = result
            
            # 結果判定
            if result.is_equivalent is True:
                self._debug_print(f"Stage {stage_id.value}: EQUIVALENT - stopping stage plan")
                return result
            
            elif result.is_equivalent is False:
                self._debug_print(f"Stage {stage_id.value}: NOT EQUIVALENT - stopping stage plan")
                return result
            
            else:
                # UNKNOWN/TIMEOUT
                if stage_id in {StageID.S_PAIRWISE, StageID.S_LOOP_TEMPLATE_ABSTRACTION}:
                    self._debug_print(f"Stage {stage_id.value}: UNKNOWN - proceeding to fallback")
                    continue
                elif stage_id == StageID.S_ABSTRACT_RECURSIVE_SUMMARY:
                    if self._should_skip_monolithic_fallback(analysis1, analysis2):
                        self._debug_print(
                            "Stage S_MONOLITHIC_FALLBACK: skipped due to incomplete control-flow summary"
                        )
                        return result
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

    def _should_skip_monolithic_fallback(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> bool:
        """monolithic 化で誤判定しやすい不完全要約を検出する。"""
        return (
            analysis1.should_skip_monolithic_fallback()
            or analysis2.should_skip_monolithic_fallback()
        )

    def _should_try_loop_template_stage(
        self,
        last_result: Optional[EquivalenceResult],
    ) -> bool:
        """Layer 2 は solver timeout に起因する UNKNOWN にだけ適用する。"""
        if last_result is None:
            return False
        if last_result.is_equivalent is not None or last_result.error_message is not None:
            return False
        if last_result.is_timeout():
            return True

        pairwise_stats = last_result.pairwise_debug_stats or {}
        timeout_fallback_attempts = int(pairwise_stats.get("timeout_fallback_attempts", 0) or 0)
        if timeout_fallback_attempts > 0:
            self._debug_print(
                "Stage S_LOOP_TEMPLATE_ABSTRACTION: enabling due to pairwise query timeouts "
                f"(timeout_fallback_attempts={timeout_fallback_attempts})"
            )
            return True

        return False

    def _run_recursive_abstraction_stage(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        binary1_name: str,
        binary2_name: str,
        save_formula: bool,
        type_fix_result: Optional[TypeFixResult],
        retry_count: int,
        original_signature1: Optional[FunctionSignature],
        original_signature2: Optional[FunctionSignature],
    ) -> Optional[EquivalenceResult]:
        abstraction = abstract_recursive_calls(
            analysis1,
            analysis2,
            debug=self.debug,
        )
        if not abstraction.applied:
            self._debug_print("Recursive abstraction fallback: no compatible deferred-call matches")
            return None

        self._debug_print(
            "Recursive abstraction fallback: matched "
            f"{len(abstraction.matches)} deferred recursive call(s)"
        )
        return self.check(
            abstraction.analysis1,
            abstraction.analysis2,
            binary1_name,
            binary2_name,
            save_formula,
            type_fix_result=type_fix_result,
            retry_count=retry_count,
            original_signature1=original_signature1,
            original_signature2=original_signature2,
            force_strategy=self.pairwise_strategy,
        )
    
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
                effective_function1_signature=FunctionSignature.from_analysis(analysis1),
                effective_function2_signature=FunctionSignature.from_analysis(analysis2),
                function1_signature_hypotheses=list(analysis1.signature_hypotheses),
                function2_signature_hypotheses=list(analysis2.signature_hypotheses),
                constrained_fragments=strategy_result.constrained_fragments,
                rewrite_info=rewrite_info,
                pairwise_stats={
                    'total_pairs': strategy_result.total_pairs,
                    'unsat_pairs': strategy_result.unsat_pairs,
                    'sat_pairs': strategy_result.sat_pairs,
                    'unknown_pairs': strategy_result.unknown_pairs,
                    'error_pairs': strategy_result.error_pairs,
                } if strategy_result.total_pairs > 0 else None,
                pairwise_debug_stats=strategy_result.pairwise_debug_stats,
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
        """エラー結果作成の互換ラッパー"""
        return create_error_result(
            analysis1=analysis1,
            analysis2=analysis2,
            binary1_name=binary1_name,
            binary2_name=binary2_name,
            error_message=error_message,
            start_time=start_time,
            type_fix_result=type_fix_result,
            retry_count=retry_count,
            original_signature1=original_signature1,
            original_signature2=original_signature2,
        )
    
    def _analyze_and_check_with_analysis(
        self,
        ctx: PhaseContext,
        retry_count: int = 0
    ) -> Tuple[Optional[FunctionReturnAnalysis], Optional[FunctionReturnAnalysis], EquivalenceResult]:
        """初回解析 helper への互換ラッパー"""
        return analyze_and_check_with_analysis(self, ctx, retry_count=retry_count)
