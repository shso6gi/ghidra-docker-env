# -*- coding: utf-8 -*-
"""等価性判定メインロジック（Stage/Phase ループ骨格版）"""

from typing import Optional, Dict, Any, List, Mapping, Tuple
from enum import Enum
from dataclasses import dataclass
import time

from ..model import FunctionReturnAnalysis, FunctionSignature
from ..smt import ParallelSolverRunner, ParallelResult, SolverResult
from .formula import FormulaBuilder
from .formula.returns import ReturnWidthMismatchError
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
from .unknown_reason import make_unknown_reason
from .call_effect_obligations import (
    EquivalenceObservationContract,
    build_call_effect_shadow_manifest,
    build_structural_coverage_certificate,
)


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
        pairwise_unknown_dir: Optional[str] = None,
        normalization_mode: str = "safe",
        enable_fact_normalization: bool = False,
        enable_template_abstraction: bool = False,
        enable_completed_recovery_proofs: bool = True,
        assume_fp_non_nan: bool = False,
        observes_errno: bool = False,
        observes_fenv: bool = False,
        observation_contract: Optional[EquivalenceObservationContract] = None,
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
        self.enable_completed_recovery_proofs = enable_completed_recovery_proofs
        self.assume_fp_non_nan = assume_fp_non_nan
        self.observes_errno = observes_errno
        self.observes_fenv = observes_fenv
        self.observation_contract = observation_contract or EquivalenceObservationContract(
            observe_errno=observes_errno,
            observe_fenv=observes_fenv,
        )
        self.normalization_settings = self._build_normalization_settings(
            normalization_mode,
            enable_fact_normalization,
        )
        self.formula_builder = FormulaBuilder(
            debug=debug,
            assume_fp_non_nan=assume_fp_non_nan,
        )
        self.solver_runner = ParallelSolverRunner(timeout=timeout, debug=debug)
        self.phase_handler = PhaseHandler(self.type_fixer_config, debug=debug)
        
        # 各 strategy の準備
        self.pairwise_strategy = PairwiseStrategy(
            self.formula_builder,
            self.solver_runner,
            debug=debug,
            normalization_settings=self.normalization_settings,
            enable_completed_recovery_proofs=enable_completed_recovery_proofs,
        )
        self.pairwise_strategy.per_query_timeout = pairwise_timeout
        self.pairwise_strategy.per_query_timeout_hard = pairwise_timeout_hard
        self.pairwise_strategy.save_unknown_queries = pairwise_save_unknown
        if pairwise_unknown_dir is not None:
            self.pairwise_strategy.unknown_query_dir = pairwise_unknown_dir
        
        self.monolithic_strategy = MonolithicStrategy(
            self.formula_builder,
            self.solver_runner,
            debug=debug,
            normalization_settings=self.normalization_settings,
            enable_completed_recovery_proofs=enable_completed_recovery_proofs,
        )
        self.loop_template_strategy = LoopTemplatePairwiseStrategy(
            self.formula_builder,
            self.solver_runner,
            debug=debug,
            normalization_settings=self.normalization_settings,
            enable_completed_recovery_proofs=enable_completed_recovery_proofs,
        )
        self.loop_template_strategy.per_query_timeout = pairwise_timeout
        self.loop_template_strategy.per_query_timeout_hard = pairwise_timeout_hard
        self.loop_template_strategy.save_unknown_queries = pairwise_save_unknown
        if pairwise_unknown_dir is not None:
            self.loop_template_strategy.unknown_query_dir = pairwise_unknown_dir
        
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

        self._debug_print(
            "Object-centric solver-only policy: skipping rewrite stage "
            f"(requested direction: {self.rewrite_direction})"
        )
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
        
        analyzer = ReturnAnalyzer(
            program,
            debug=self.debug,
            enable_completed_recovery_proofs=self.enable_completed_recovery_proofs,
        )
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
        retry_with_type_fix: bool = False,
        binary1_id: Optional[str] = None,
        binary2_id: Optional[str] = None,
        declared_return_type1: Optional[str] = None,
        declared_return_type2: Optional[str] = None,
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
            binary1_id=binary1_id,
            binary2_id=binary2_id,
            declared_return_type1=declared_return_type1,
            declared_return_type2=declared_return_type2,
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
        
        rewrite_info = None
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
                mips64_abi_constraints=abi_constraints,
                unknown_reasons=(
                    [
                        make_unknown_reason(
                            "solver_unknown_timeout",
                            stage="ABI_RETRY",
                            evidence_refs=(
                                str(parallel_result.results[0].status.name)
                                if parallel_result.results
                                else "no_solver_result",
                            ),
                            evidence_kind="query_hash",
                            object_target_key=self.monolithic_strategy._solver_timeout_object_target_key(
                                analysis1=analysis1,
                                analysis2=analysis2,
                                stage="ABI_RETRY",
                                query=smt_formula,
                                timeout_seconds=getattr(self.solver_runner, "timeout", None),
                                parallel_result=parallel_result,
                            ),
                            detail="ABI retry solver query timed out",
                        )
                    ]
                    if parallel_result.is_equivalent is None
                    else []
                ),
            )

        except ReturnWidthMismatchError as e:
            reason_id = getattr(e, "reason_id", "return_width_bridge_missing")
            self._debug_print(f"ABI retry blocked: {reason_id}: {e}")
            blocked_analysis1 = locals().get("analysis1", ctx.analysis1)
            blocked_analysis2 = locals().get("analysis2", ctx.analysis2)
            return EquivalenceResult(
                is_equivalent=None,
                function1_name=ctx.function_name1,
                function2_name=ctx.function_name2,
                binary1_name=ctx.binary1_name,
                binary2_name=ctx.binary2_name,
                solver_results=ParallelResult(results=[]),
                counterexample=None,
                smt_formula=None,
                total_time=time.time() - start_time,
                type_fix_result=ctx.type_fix_result,
                retry_count=retry_count,
                function1_signature=ctx.original_signature1,
                function2_signature=ctx.original_signature2,
                effective_function1_signature=FunctionSignature.from_analysis(blocked_analysis1),
                effective_function2_signature=FunctionSignature.from_analysis(blocked_analysis2),
                function1_signature_hypotheses=list(blocked_analysis1.signature_hypotheses),
                function2_signature_hypotheses=list(blocked_analysis2.signature_hypotheses),
                constrained_fragments=[],
                rewrite_info=rewrite_info,
                mips64_abi_constraints=abi_constraints,
                pairwise_debug_stats={reason_id: 1},
                unknown_reasons=[
                    make_unknown_reason(
                        reason_id,
                        stage="ABI_RETRY",
                        evidence_refs=(str(e),),
                        detail=str(e),
                    )
                ],
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
            self._merge_completed_recovery_proofs_from_result(
                analysis1,
                analysis2,
                result,
            )
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
            assume_fp_non_nan=self.assume_fp_non_nan,
            observes_errno=self.observes_errno,
            observes_fenv=self.observes_fenv,
            debug=self.debug,
        )
        if not abstraction.applied:
            self._debug_print("Recursive abstraction fallback: no compatible deferred-call matches")
            return None

        self._debug_print(
            "Deferred call abstraction fallback: matched "
            f"{len(abstraction.matches)} deferred call(s)"
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
            call_effect_shadow_manifest = self._call_effect_shadow_manifest(
                analysis1,
                analysis2,
                binary1_name,
                binary2_name,
            )
            self._apply_phase2_relational_call_discharge(
                strategy_result,
                analysis1,
                analysis2,
                call_effect_shadow_manifest,
            )
            strategy_result.unknown_reasons = self._specialize_call_effect_unknown_reasons(
                list(getattr(strategy_result, "unknown_reasons", ()) or ()),
                call_effect_shadow_manifest,
            )
            
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
                unknown_reasons=strategy_result.unknown_reasons,
                sat_pair_info=strategy_result.sat_pair_info,
                normalization_rules=strategy_result.normalization_rules,
                completed_recovery_proof_evidence=self._completed_recovery_proof_payload(
                    analysis1,
                    analysis2,
                    binary1_name,
                    binary2_name,
                ),
                call_effect_shadow_manifest=call_effect_shadow_manifest,
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

    def _call_effect_shadow_manifest(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        binary1_name: str,
        binary2_name: str,
    ) -> Dict[str, Any]:
        """Build decision-neutral evidence; shadow failures must not change a result."""

        try:
            manifest = build_call_effect_shadow_manifest(
                analysis1,
                analysis2,
                binary1_name=binary1_name,
                binary2_name=binary2_name,
                observation_contract=self.observation_contract,
            )
            return self._attach_structural_coverage_certificate(manifest)
        except Exception as exc:
            self._debug_print(f"Call/effect shadow manifest unavailable: {exc}")
            return {
                "schema_version": 1,
                "mode": "shadow_no_decision_effect",
                "observation_contract": self.observation_contract.to_dict(),
                "shadow_status": "inconclusive",
                "failure_cause": "shadow_manifest_construction_failed",
                "error_type": type(exc).__name__,
            }

    @staticmethod
    def _attach_structural_coverage_certificate(
        manifest: Dict[str, Any],
    ) -> Dict[str, Any]:
        """Attach an exact deterministic certificate, not a semantic SMT proof."""

        certificate = build_structural_coverage_certificate(manifest)
        manifest["structural_coverage_certificate"] = certificate.to_dict()
        summary = manifest.get("summary")
        if isinstance(summary, dict):
            summary["structural_certificate_status"] = certificate.status
            summary["solver_proof_record_count"] = 0
            summary["solver_proven_stage_count"] = 0
            summary["decision_eligible_obligation_count"] = 0
        return manifest

    def _apply_phase2_relational_call_discharge(
        self,
        strategy_result,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        manifest: Dict[str, Any],
    ) -> None:
        """Decision-neutral until stage-specific semantic producers exist."""

        manifest["phase2_discharge_gate"] = {
            "status": "disabled",
            "decision_effect": "diagnostic_only",
            "failure_cause": "stage_specific_semantic_producers_not_implemented",
        }

    @staticmethod
    def _specialize_call_effect_unknown_reasons(
        reasons: List[Any],
        manifest: Mapping[str, Any],
    ) -> List[Any]:
        """Move broad call unsafety to the first concrete relational proof stage."""

        backlog = manifest.get("proof_stage_backlog")
        mappings = manifest.get("legacy_blocker_mapping")
        if not isinstance(backlog, list) or not isinstance(mappings, list):
            return reasons
        stage_by_obligation = {
            str(item.get("obligation_id")): str(item.get("primary_proof_stage"))
            for item in backlog
            if isinstance(item, Mapping)
            and item.get("obligation_id")
            and item.get("primary_proof_stage")
        }
        blocker_stages: Dict[str, Tuple[str, ...]] = {}
        for item in mappings:
            if not isinstance(item, Mapping):
                continue
            blocker = str(item.get("legacy_blocker") or "")
            stages = tuple(
                sorted(
                    {
                        stage_by_obligation[str(obligation_id)]
                        for obligation_id in item.get("obligation_ids", ()) or ()
                        if str(obligation_id) in stage_by_obligation
                    }
                )
            )
            if blocker and stages:
                blocker_stages[blocker] = stages

        specialized: List[Any] = []
        for reason in reasons:
            if str(getattr(reason, "reason_id", "")) != "equivalence_blocking_unsafety":
                specialized.append(reason)
                continue
            stages = {
                stage
                for ref in getattr(reason, "evidence_refs", ()) or ()
                for stage in blocker_stages.get(str(ref), ())
            }
            if not stages:
                specialized.append(reason)
                continue
            proof_stage = (
                next(iter(stages))
                if len(stages) == 1
                else "multiple_relational_call_effect_stages_missing"
            )
            specialized.append(
                make_unknown_reason(
                    reason.reason_id,
                    count_kind=reason.count_kind,
                    reason_class=reason.reason_class,
                    decision_effect=reason.decision_effect,
                    reason_scope=reason.reason_scope,
                    aggregation_unit=reason.aggregation_unit,
                    stage=reason.stage,
                    pair_or_case=reason.pair_or_case,
                    evidence_refs=reason.evidence_refs,
                    recovery_proof_kind=reason.recovery_proof_kind,
                    recovery_proof_obligations=(
                        {
                            "proof_kind": reason.recovery_proof_kind,
                            "proof_stage": proof_stage,
                            "required_evidence": (
                                "relational_call_effect_obligation",
                                "solver_proof_record",
                            ),
                            "description": "Complete the obligation-specific relational call/effect proof stage.",
                        },
                    ),
                    proof_stage=proof_stage,
                    evidence_kind=reason.evidence_kind,
                    object_target_key=reason.object_target_key,
                    object_evidence=reason.object_evidence,
                    proof_obligation_id=None,
                    recovery_action="relational_call_effect_stage_proof_required",
                    action_status=reason.action_status,
                    target_regression=reason.target_regression,
                    detail=(
                        f"Relational call/effect proof is incomplete at {proof_stage}."
                    ),
                )
            )
        return specialized

    def _completed_recovery_proof_payload(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        binary1_name: str,
        binary2_name: str,
    ) -> List[Dict[str, Any]]:
        if not self.enable_completed_recovery_proofs:
            return []
        records: List[Dict[str, Any]] = []
        for side, binary_name, analysis in (
            ("function1", binary1_name, analysis1),
            ("function2", binary2_name, analysis2),
        ):
            for evidence in getattr(analysis, "completed_recovery_proof_evidence", ()) or ():
                if not isinstance(evidence, Mapping):
                    continue
                records.append(
                    {
                        "side": side,
                        "function_name": analysis.function_name,
                        "binary_name": binary_name,
                        "binary_id": getattr(analysis, "binary_id", None),
                        "evidence": dict(evidence),
                    }
                )
        return records

    def _merge_completed_recovery_proofs_from_result(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        result: EquivalenceResult,
    ) -> None:
        if not self.enable_completed_recovery_proofs:
            return
        payload = getattr(result, "completed_recovery_proof_evidence", None) or ()
        if not payload:
            return
        by_side = {
            "function1": analysis1,
            "function2": analysis2,
        }
        for item in payload:
            if not isinstance(item, Mapping):
                continue
            side = str(item.get("side") or "")
            analysis = by_side.get(side)
            if analysis is None:
                continue
            evidence = item.get("evidence")
            if not isinstance(evidence, Mapping):
                continue
            records = [
                dict(record)
                for record in getattr(analysis, "completed_recovery_proof_evidence", ()) or ()
                if isinstance(record, Mapping)
            ]
            proof_id = evidence.get("proof_obligation_id")
            existing_ids = {record.get("proof_obligation_id") for record in records}
            if proof_id is not None and proof_id in existing_ids:
                continue
            records.append(dict(evidence))
            analysis.completed_recovery_proof_evidence = tuple(records)
    
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
