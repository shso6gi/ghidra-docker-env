# -*- coding: utf-8 -*-
"""等価性判定メインロジック（Stage/Phase ループ骨格版）"""

from typing import Optional, Dict, Any, List, Mapping, Tuple
from enum import Enum
from dataclasses import dataclass, replace
import time
from uuid import uuid4

from ..model import FunctionReturnAnalysis, FunctionSignature
from ..model.render_smt import (
    UnknownSmtExtensionWidthError,
    UnsupportedSmtOperatorError,
)
from ..smt import ParallelSolverRunner, ParallelResult
from .formula import FormulaBuilder
from .formula.returns import ReturnWidthMismatchError
from .counterexample import CounterexampleFormatter
from .typing.fixer import TypeFixer, TypeFixerConfig, TypeFixResult
from .result import EquivalenceResult, RewriteInfo
from .result_factory import create_error_result
from .phases.handler import PhaseHandler, PhaseContext, PhaseResult
from .reanalysis import analyze_and_check_with_analysis, selective_reanalysis_and_check
from .strategies.pairwise import PairwiseStrategy
from .strategies.loop_template import LoopTemplatePairwiseStrategy
from .strategies.monolithic import MonolithicStrategy
from .normalize import NormalizationSettings
from .debug_trace import DebugTrace, PairwiseDecisiveInfo
from .attempts import get_transition_reason, record_attempt, record_attempt_from_result
from .obligations.snapshot import SnapshotFingerprintCodec
from .recursive_abstraction import abstract_recursive_calls  # type: ignore[import-not-found]
from .v2.production_boundary import run_check_from_binaries_with_v2_pilot as run_check_from_binaries
from .unknown_reason import (
    build_unknown_recovery_actions,
    make_internal_v2_reason_diagnostic,
    make_unknown_reason,
)
from .cause_identity import (
    ProofRequirementContract,
    ProofRequirementId,
    UnaryCauseKey,
    RelationalCauseKey,
    canonical_cause_tuple,
)
from .call_effect_obligations import (
    EquivalenceObservationContract,
    apply_solver_proof_artifacts_to_manifest,
    build_call_effect_shadow_manifest,
    build_structural_coverage_certificate,
)
from .call_effect_producer import (
    produce_pure_direct_call_proofs,
    produce_v2_pure_direct_call_proofs,
)
from .v2.call_effect import CALL_EFFECT_PRODUCTION_STAGE_REGISTRY
from .v2.call_effect_sites import CALL_EFFECT_PROOF_BATCH_SITE
from .v2.production_signals import (
    CallEffectProofBatchProductionSignal,
    build_active_call_effect_execution_context,
    emit_call_effect_signal,
    record_production_pilot_shadow_error,
)
from .call_effect_preflight import (
    CallProofDecisionMode,
    PreparedDispatchFrame,
    StrategySourceAnalysisPair,
    close_prepared_dispatch_frame,
    diagnostic_projection,
    finalize_pairwise_comparison_receipt,
    prepare_solver_surface,
    push_prepared_dispatch_frame,
    validate_call_resolution_projection,
    verify_monolithic_terminal_receipt,
    verify_monolithic_proof_receipt,
)
from .recurrence_promotion import (
    PairPromotionState,
    PairRecurrencePromotionAuthority,
    promote_recurrence_pair,
)
from ..model.recurrence_contracts import RecurrenceDigestCodec


# Re-exports kept for callers that import these names from this module.
from ..smt import SolverResult  # noqa: F401


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
        monolithic_timeout: Optional[int] = None,
        monolithic_query_mode: str = "split",
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
        call_proof_decision_mode: str = "preflight_projection",
        canonical_decision_cutover: bool = True,
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
        self.call_proof_decision_mode = CallProofDecisionMode(call_proof_decision_mode)
        if type(canonical_decision_cutover) is not bool:
            raise TypeError("canonical decision cutover flag must be exact bool")
        self.canonical_decision_cutover = canonical_decision_cutover
        if canonical_decision_cutover:
            from .v2.phase8_cutover import build_default_cutover_connector

            self.v2_dual_write_pilot_connector = build_default_cutover_connector()
        self._call_proof_generation = 0
        self.normalization_settings = self._build_normalization_settings(
            normalization_mode,
            enable_fact_normalization,
        )
        self.formula_builder = FormulaBuilder(
            debug=debug,
            assume_fp_non_nan=assume_fp_non_nan,
        )
        self.solver_runner = ParallelSolverRunner(timeout=timeout, debug=debug)
        self._last_internal_call_effect_artifacts = ()
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
        self.monolithic_strategy.total_timeout = max(
            1, int(timeout if monolithic_timeout is None else monolithic_timeout)
        )
        if monolithic_query_mode not in {"split", "legacy"}:
            raise ValueError("invalid_monolithic_query_mode")
        self.monolithic_strategy.query_mode = monolithic_query_mode
        self.monolithic_strategy.per_query_timeout = min(
            self.monolithic_strategy.per_query_timeout,
            self.monolithic_strategy.total_timeout,
        )
        self.monolithic_strategy.per_query_timeout_hard = max(
            self.monolithic_strategy.per_query_timeout,
            self.monolithic_strategy.per_query_timeout_hard,
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
        # Both strategies encode the same guard/value obligations.  Sharing the
        # process-local attempt cache lets the loop-template fallback reuse the
        # base branch's identical queries while its template-specific queries
        # retain distinct logical digests.
        self.loop_template_strategy._exact_query_attempt_cache = (
            self.pairwise_strategy._exact_query_attempt_cache
        )
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
        binary1_content_identity: Optional[Tuple[Any, ...]] = None,
        binary2_content_identity: Optional[Tuple[Any, ...]] = None,
    ) -> EquivalenceResult:
        """2つのバイナリから関数を解析して等価性を判定"""
        previous_context = getattr(self, "_active_binary_content_identities", None)
        self._active_binary_content_identities = (
            binary1_content_identity,
            binary2_content_identity,
        )
        try:
            result = run_check_from_binaries(
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
            result.binary1_content_identity = binary1_content_identity
            result.binary2_content_identity = binary2_content_identity
            return result
        finally:
            self._active_binary_content_identities = previous_context
    
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
            pairwise_debug_stats=None,
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
            counterexample_raw = None
            if parallel_result.is_equivalent is False:
                counterexample_raw = parallel_result.get_counterexample()
                if counterexample_raw:
                    counterexample = self._format_counterexample(
                        counterexample_raw,
                        analysis1,
                        analysis2,
                        return_var1,
                        return_var2,
                    )
            
            # ★ 修正: save_formula に関わらず smt_formula を保持（debug trace 用）
            # user-facing 出力は EquivalenceResult.to_string() / to_dict() で制御される
            equivalence_result = EquivalenceResult(
                is_equivalent=parallel_result.is_equivalent,
                function1_name=ctx.function_name1,
                function2_name=ctx.function_name2,
                binary1_name=ctx.binary1_name,
                binary2_name=ctx.binary2_name,
                solver_results=parallel_result,
                counterexample=counterexample,
                counterexample_raw=counterexample_raw,
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
                # Solver TIMEOUT/UNKNOWN is execution authority, not a
                # semantic UNKNOWN reason.  The v2 finalizer joins its receipt
                # to independently live requirements.
                unknown_reasons=[],
            )
            return equivalence_result

        except (UnknownSmtExtensionWidthError, UnsupportedSmtOperatorError) as e:
            diagnostic_kind = (
                "unknown_smt_extension_width"
                if isinstance(e, UnknownSmtExtensionWidthError)
                else "unsupported_smt_operator"
            )
            self._debug_print(
                f"ABI retry blocked by unsupported SMT expression semantics: {e}"
            )
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
                counterexample_raw=None,
                smt_formula=None,
                total_time=time.time() - start_time,
                type_fix_result=ctx.type_fix_result,
                retry_count=retry_count,
                function1_signature=ctx.original_signature1,
                function2_signature=ctx.original_signature2,
                effective_function1_signature=FunctionSignature.from_analysis(
                    blocked_analysis1
                ),
                effective_function2_signature=FunctionSignature.from_analysis(
                    blocked_analysis2
                ),
                function1_signature_hypotheses=list(
                    blocked_analysis1.signature_hypotheses
                ),
                function2_signature_hypotheses=list(
                    blocked_analysis2.signature_hypotheses
                ),
                constrained_fragments=[],
                rewrite_info=rewrite_info,
                mips64_abi_constraints=abi_constraints,
                pairwise_debug_stats={
                    diagnostic_kind: 1,
                },
                unknown_reasons=[
                    make_internal_v2_reason_diagnostic(
                        "expression_semantics_unsupported",
                        stage="ABI_RETRY",
                        evidence_refs=(diagnostic_kind,),
                        object_target_key=(
                            diagnostic_kind,
                            e.operator,
                            e.operand_bits,
                            getattr(e, "result_bits", 0),
                            tuple(blocked_analysis1.outcome_function_identity()),
                            tuple(blocked_analysis2.outcome_function_identity()),
                        ),
                        detail=str(e),
                    )
                ],
            )

        except ReturnWidthMismatchError as e:
            reason_id = getattr(e, "reason_id", "return_width_bridge_missing")
            self._debug_print(f"ABI retry blocked: {reason_id}: {e}")
            blocked_analysis1 = locals().get("analysis1", ctx.analysis1)
            blocked_analysis2 = locals().get("analysis2", ctx.analysis2)
            equivalence_result = EquivalenceResult(
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
            return equivalence_result
        
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
        """Run the typed obligation branch plan (default production path)."""
        from .obligations.stage_runner import run_obligation_branch_plan

        return run_obligation_branch_plan(
            self,
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
        self._last_recursive_derived_view_identity = None
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
        runtime = getattr(self, "_obligation_runtime_session", None)
        if runtime is None:
            from .obligations.runtime import ObligationRuntimeSession

            runtime = ObligationRuntimeSession.create(analysis1, analysis2)
            self._obligation_runtime_session = runtime
        recursive_view = runtime.create_recursive_view(
            abstraction.analysis1,
            abstraction.analysis2,
            abstraction.matches,
        )
        self._last_recursive_derived_view = recursive_view
        self._last_recursive_derived_view_identity = recursive_view.view_id
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

            replan_plan = getattr(self, "_active_pair_replan_plan", None)
            if replan_plan is None:
                self._call_proof_generation += 1
                generation = int(
                    getattr(self, "_active_comparison_generation", None)
                    or self._call_proof_generation
                )
                comparison_session_id = str(
                    getattr(self, "_active_comparison_session_id", None)
                    or uuid4().hex
                )
                branch_id = str(
                    getattr(self, "_active_call_proof_branch_id", None)
                    or strategy.__class__.__name__
                )
            else:
                generation = int(replan_plan.frame_generation)
                comparison_session_id = str(
                    replan_plan.comparison_session_id
                )
                branch_id = str(replan_plan.branch_id)
            decision_mode = self.call_proof_decision_mode
            dispatch_frame = None
            locally_issued_branch_authority = None
            cleanup_complete = True
            preflight_gate_delta_diagnostic = None

            if decision_mode == CallProofDecisionMode.PREFLIGHT_PROJECTION:
                source_pair = StrategySourceAnalysisPair.create(analysis1, analysis2)
                prepared_pair = prepare_solver_surface(
                    source_pair,
                    observation_contract_digest=self.observation_contract.contract_id,
                    comparison_session_id=comparison_session_id,
                    branch_id=branch_id,
                    generation=generation,
                    decision_mode=decision_mode,
                )
                call_effect_shadow_manifest = self._call_effect_shadow_manifest(
                    prepared_pair.analysis1,
                    prepared_pair.analysis2,
                    binary1_name,
                    binary2_name,
                )
                projection = validate_call_resolution_projection(
                    call_effect_shadow_manifest,
                    prepared_pair,
                    generation=generation,
                    trusted_proof_artifacts=self._last_internal_call_effect_artifacts,
                )
                if not self.enable_completed_recovery_proofs and projection.required:
                    projection = replace(
                        projection,
                        status="inconclusive",
                        root_blockers=("completed_recovery_proofs_disabled",),
                        covered_blockers=(),
                    )
                branch_authority = getattr(
                    self, "_active_production_branch_authority_lease", None
                )
                if (
                    isinstance(strategy, MonolithicStrategy)
                    and branch_authority is None
                ):
                    # Direct checker calls are a compatibility execution domain;
                    # production stage execution supplies the parent lease.
                    from .monolithic_authority import issue_production_branch_authority
                    locally_issued_branch_authority = issue_production_branch_authority(
                        comparison_session_id,
                        branch_id,
                        generation,
                        "direct_checker_compatibility_view",
                    )
                    branch_authority = locally_issued_branch_authority
                try:
                    dispatch_frame = PreparedDispatchFrame(
                        comparison_session_id=comparison_session_id,
                        branch_id=branch_id,
                        generation=generation,
                        source=source_pair,
                        prepared=prepared_pair,
                        projection=projection,
                        preflight_manifest=call_effect_shadow_manifest,
                        trusted_proof_artifacts=tuple(
                            self._last_internal_call_effect_artifacts
                        ),
                        decision_mode=decision_mode,
                        production_branch_authority_lease=branch_authority,
                    )
                except Exception:
                    if locally_issued_branch_authority is not None:
                        from .monolithic_authority import revoke_production_branch_authority
                        revoke_production_branch_authority(
                            locally_issued_branch_authority
                        )
                        locally_issued_branch_authority = None
                    raise
                obligation_runtime = getattr(
                    self, "_obligation_runtime_session", None
                )
                if (
                    obligation_runtime is not None
                    and replan_plan is None
                    and obligation_runtime.pair_ledger_manager.pending_successor
                    is not None
                ):
                    # A successor intent is branch-local authority.  Recursive
                    # abstraction or another strategy must not consume it.
                    from .obligations.runtime import ObligationRuntimeSession

                    obligation_runtime = ObligationRuntimeSession.create(
                        analysis1, analysis2
                    )
                if obligation_runtime is None:
                    from .obligations.runtime import ObligationRuntimeSession

                    obligation_runtime = ObligationRuntimeSession.create(
                        analysis1, analysis2
                    )
                    self._obligation_runtime_session = obligation_runtime
                try:
                    strategy._obligation_runtime_session = obligation_runtime
                except (AttributeError, TypeError):
                    pass
                dispatch_frame.obligation_runtime = obligation_runtime
                if replan_plan is not None:
                    current_plan = (
                        obligation_runtime.pair_ledger_manager.pending_successor
                    )
                    if current_plan is not replan_plan:
                        raise RuntimeError("pair_replan_successor_plan_missing")
                    dispatch_frame.replan_successor_plan = replan_plan

                self._debug_print(f"Using strategy: {strategy.__class__.__name__}")
                if isinstance(strategy, (PairwiseStrategy, MonolithicStrategy)):
                    token = None
                    try:
                        token = push_prepared_dispatch_frame(dispatch_frame)
                        strategy_result = strategy.check(analysis1, analysis2, save_formula)
                        if (
                            isinstance(strategy, PairwiseStrategy)
                            and dispatch_frame.pair_disposition_ledger is not None
                            and dispatch_frame.receipt is None
                        ):
                            strategy_result.comparison_execution_receipt = (
                                finalize_pairwise_comparison_receipt(dispatch_frame)
                            )
                    finally:
                        if token is None:
                            dispatch_frame.close()
                            dispatch_frame.cleanup_complete = True
                            cleanup_complete = True
                        else:
                            cleanup_complete = close_prepared_dispatch_frame(
                                dispatch_frame,
                                token,
                            )
                        if locally_issued_branch_authority is not None:
                            from .monolithic_authority import revoke_production_branch_authority
                            revoke_production_branch_authority(
                                locally_issued_branch_authority
                            )
                else:
                    # Non-built-in compatibility branches cannot consume a
                    # projection.  Their EQ is vetoed below whenever call proof
                    # preflight is required.
                    try:
                        strategy_result = strategy.check(analysis1, analysis2, save_formula)
                    finally:
                        dispatch_frame.close()
                        dispatch_frame.cleanup_complete = True
                ordinary_outcome = strategy_result.is_equivalent
                stage_runner_owns_finalization = str(branch_id).startswith("S_")
                if (
                    isinstance(strategy, PairwiseStrategy)
                    and dispatch_frame.pair_disposition_ledger is not None
                    and not stage_runner_owns_finalization
                ):
                    strategy_result.comparison_execution_receipt = (
                        finalize_pairwise_comparison_receipt(dispatch_frame)
                    )
                elif isinstance(strategy, MonolithicStrategy) and not stage_runner_owns_finalization:
                    from .call_effect_preflight import (
                        finalize_monolithic_comparison_receipt,
                    )
                    strategy_result.comparison_execution_receipt = (
                        finalize_monolithic_comparison_receipt(dispatch_frame)
                    )
                if not stage_runner_owns_finalization:
                    self._apply_preflight_final_gate(
                        strategy_result,
                        dispatch_frame,
                        cleanup_complete=cleanup_complete,
                    )
                call_effect_shadow_manifest = diagnostic_projection(
                    call_effect_shadow_manifest,
                    dispatch_frame,
                )
                preflight_gate_delta_diagnostic = {
                    "status": "diagnostic_not_legacy_canary",
                    "ordinary_comparison_outcome": (
                        "EQ" if ordinary_outcome is True
                        else "NOT_EQ" if ordinary_outcome is False
                        else "UNKNOWN"
                    ),
                    "preflight_terminal_outcome": (
                        "EQ" if strategy_result.is_equivalent is True
                        else "NOT_EQ" if strategy_result.is_equivalent is False
                        else "UNKNOWN"
                    ),
                    "gate_effect": (
                        "agree"
                        if ordinary_outcome is strategy_result.is_equivalent
                        else "preflight_veto"
                    ),
                    "decision_mode": "preflight_projection",
                    "comparison_branch": branch_id,
                }
                call_effect_shadow_manifest["preflight_gate_delta_diagnostic"] = (
                    preflight_gate_delta_diagnostic
                )
            else:
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
            comparison_identity = self._call_effect_comparison_identity(
                analysis1,
                analysis2,
                call_effect_shadow_manifest,
            )
            strategy_result.unknown_reasons = self._attach_recurrence_proposal_blockers(
                strategy_result,
                analysis1,
                analysis2,
                branch_id=branch_id,
            )
            strategy_result.unknown_reasons = self._specialize_call_effect_unknown_reasons(
                list(getattr(strategy_result, "unknown_reasons", ()) or ()),
                call_effect_shadow_manifest,
                comparison_identity=comparison_identity,
            )
            strategy_result.unknown_reasons = self._attach_root_blocker_identities(
                strategy_result.unknown_reasons,
                comparison_identity,
            )

            # Recurrence is a recovery proof for this already-inconclusive
            # branch, never an alternative surface evaluated before the
            # branch decision.  The pair-local authority names the exact
            # blockers observed above and is intentionally absent from the
            # function-local unary artifact.
            if getattr(self, "_active_recurrence_promotion_authority", None) is None:
                authority = self._recurrence_promotion_authority(
                    strategy_result,
                    comparison_session_id=comparison_session_id,
                    branch_id=branch_id,
                )
                if authority is not None:
                    (
                        promoted1,
                        promoted2,
                        recurrence_runtime,
                        recurrence_attempt,
                    ) = promote_recurrence_pair(analysis1, analysis2, authority)
                    self._last_recurrence_promotion_attempt = recurrence_attempt
                    if recurrence_attempt.state == PairPromotionState.ABORTED:
                        self._debug_print(
                            "Recurrence promotion declined: "
                            + str(recurrence_attempt.failure or "unknown")
                        )
                    elif recurrence_attempt.state == PairPromotionState.COMPOSED and (
                        recurrence_attempt.left is not None
                        and recurrence_attempt.left.proposal is not None
                        or recurrence_attempt.right is not None
                        and recurrence_attempt.right.proposal is not None
                    ):
                        for promoted_side in (
                            recurrence_attempt.left,
                            recurrence_attempt.right,
                        ):
                            if (
                                promoted_side is None
                                or promoted_side.proposal is None
                            ):
                                continue
                            try:
                                from .v2.loop_recurrence import (
                                    RecurrenceValidationCompletionSignal,
                                )
                                from .v2.production_signals import (
                                    emit_loop_recurrence_signal,
                                )

                                emit_loop_recurrence_signal(
                                    RecurrenceValidationCompletionSignal.from_side_promotion(
                                        promoted_side
                                    ),
                                    producer_site_manifest_id=(
                                        "checker-recurrence-validation-completed"
                                    ),
                                )
                            except Exception as exc:
                                from .v2.production_signals import (
                                    record_production_pilot_shadow_error,
                                )

                                record_production_pilot_shadow_error(exc)
                        self._obligation_runtime_session = recurrence_runtime
                        self._active_recurrence_promotion_authority = authority
                        try:
                            return self.check(
                                promoted1,
                                promoted2,
                                binary1_name,
                                binary2_name,
                                save_formula,
                                type_fix_result=type_fix_result,
                                retry_count=retry_count,
                                original_signature1=original_signature1,
                                original_signature2=original_signature2,
                                force_strategy=strategy,
                            )
                        finally:
                            del self._active_recurrence_promotion_authority
            function1_identity = self._deterministic_analysis_identity(strategy, analysis1)
            function2_identity = self._deterministic_analysis_identity(strategy, analysis2)
            
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

            completed_proofs = self._completed_recovery_proof_payload(
                analysis1,
                analysis2,
                binary1_name,
                binary2_name,
                extra_records=getattr(
                    strategy_result, "completed_recovery_proof_evidence", ()
                ),
            )
            completion_contexts = self._reason_completion_applicability_contexts(
                completed_proofs,
                analysis1,
                analysis2,
            )
            from .v2.comparison_closure import (
                query_execution_record_projection,
            )
            
            equivalence_result = EquivalenceResult(
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
                error_message=strategy_result.error_message,
                failure_status=strategy_result.error_kind,
                failure_message=strategy_result.error_message,
                sat_pair_info=strategy_result.sat_pair_info,
                normalization_rules=strategy_result.normalization_rules,
                completed_recovery_proof_evidence=completed_proofs,
                reason_completion_applicability_contexts=completion_contexts,
                call_effect_shadow_manifest=call_effect_shadow_manifest,
                recurrence_promotion_receipt=self._recurrence_promotion_result_receipt(
                    strategy_result
                ),
                call_proof_terminal_provenance=(
                    {
                        "comparison_session_id": comparison_session_id,
                        "terminal_branch_id": branch_id,
                        "decision_owner_mode": decision_mode.value,
                        "decision_owner_lease_id": (
                            dispatch_frame.decision_lease.decision_owner_id
                            if dispatch_frame is not None else None
                        ),
                        "terminal_outcome": (
                            "EQ" if strategy_result.is_equivalent is True
                            else "NOT_EQ" if strategy_result.is_equivalent is False
                            else "UNKNOWN"
                        ),
                        "projection_generation": generation,
                        "comparison_receipt_id": (
                            dispatch_frame.receipt.receipt_id
                            if dispatch_frame is not None and dispatch_frame.receipt is not None
                            else None
                        ),
                        "monolithic_terminal_receipt": (
                            {
                                "receipt_digest": dispatch_frame.monolithic_terminal_receipt.receipt_digest,
                                "comparison_receipt_id": dispatch_frame.monolithic_terminal_receipt.comparison_receipt_id,
                                "outcome_kind": dispatch_frame.monolithic_terminal_receipt.outcome_kind,
                                "parent_lease_digest": dispatch_frame.monolithic_terminal_receipt.parent_lease_digest,
                                "execution_lease_digest": dispatch_frame.monolithic_terminal_receipt.execution_lease_digest,
                                "frozen_surface_digest": dispatch_frame.monolithic_terminal_receipt.frozen_surface_digest,
                                "census_digest": dispatch_frame.monolithic_terminal_receipt.census_digest,
                                "region_receipt_digests": list(
                                    dispatch_frame.monolithic_terminal_receipt.region_receipt_digests
                                ),
                                "sat_region_id": dispatch_frame.monolithic_terminal_receipt.sat_region_id,
                                "model_digest": dispatch_frame.monolithic_terminal_receipt.model_digest,
                                "fixed_model_assertion_digest": dispatch_frame.monolithic_terminal_receipt.fixed_model_assertion_digest,
                                "legacy_replay_receipt_digest": dispatch_frame.monolithic_terminal_receipt.legacy_replay_receipt_digest,
                                "counterexample_safety_receipt_digest": dispatch_frame.monolithic_terminal_receipt.counterexample_safety_receipt_digest,
                                "proof_bundle_digest": dispatch_frame.monolithic_terminal_receipt.proof_bundle_digest,
                                "typed_global_replay_receipt_count": len(tuple(
                                    getattr(
                                        dispatch_frame.monolithic_terminal_receipt.counterexample_safety_receipt,
                                        "global_replay_receipts", (),
                                    ) or ()
                                )),
                                "gate_reference_digests": list(dispatch_frame.monolithic_terminal_receipt.gate_reference_digests),
                                "validated": dispatch_frame.monolithic_terminal_receipt.validates(),
                            }
                            if dispatch_frame is not None
                            and dispatch_frame.monolithic_terminal_receipt is not None
                            else None
                        ),
                        "query_execution_receipts": [
                            query_execution_record_projection(record)
                            for record in tuple(getattr(
                                getattr(dispatch_frame, "receipt", None),
                                "query_records",
                                (),
                            ) or ())
                        ],
                        "dispatch_cleanup_complete": (
                            dispatch_frame.cleanup_complete if dispatch_frame is not None else True
                        ),
                        "preflight_gate_delta_diagnostic": (
                            preflight_gate_delta_diagnostic
                        ),
                    }
                ),
                function1_identity=function1_identity,
                function2_identity=function2_identity,
            )
            # The obligation runner performs the final runtime-generation
            # validation after proof gates and evidence application.  Keep the
            # capability objects private; they are never serialized.
            equivalence_result._prepared_dispatch_frame = dispatch_frame
            equivalence_result._strategy_result = strategy_result
            if (
                dispatch_frame is not None
                and dispatch_frame.receipt is not None
                and dispatch_frame.monolithic_terminal_receipt is not None
                and dispatch_frame.monolithic_terminal_receipt.outcome_kind
                == "inconclusive_diagnostic"
                and tuple(dispatch_frame.receipt.query_records)
            ):
                from .v2.comparison_closure import (
                    InconclusiveComparisonAuthority,
                )
                equivalence_result._inconclusive_comparison_authority = (
                    InconclusiveComparisonAuthority.issue(dispatch_frame)
                )
            else:
                equivalence_result._inconclusive_comparison_authority = None
            return equivalence_result
        
        except (UnknownSmtExtensionWidthError, UnsupportedSmtOperatorError) as e:
            diagnostic_kind = (
                "unknown_smt_extension_width"
                if isinstance(e, UnknownSmtExtensionWidthError)
                else "unsupported_smt_operator"
            )
            self._debug_print(
                f"Check blocked by unsupported SMT expression semantics: {e}"
            )
            blocked_analysis1 = locals().get("analysis1", analysis1)
            blocked_analysis2 = locals().get("analysis2", analysis2)
            return EquivalenceResult(
                is_equivalent=None,
                function1_name=blocked_analysis1.function_name,
                function2_name=blocked_analysis2.function_name,
                binary1_name=binary1_name,
                binary2_name=binary2_name,
                solver_results=ParallelResult(results=[]),
                counterexample=None,
                smt_formula=None,
                total_time=time.time() - start_time,
                type_fix_result=type_fix_result,
                retry_count=retry_count,
                function1_signature=original_signature1,
                function2_signature=original_signature2,
                effective_function1_signature=FunctionSignature.from_analysis(
                    blocked_analysis1
                ),
                effective_function2_signature=FunctionSignature.from_analysis(
                    blocked_analysis2
                ),
                function1_signature_hypotheses=list(
                    blocked_analysis1.signature_hypotheses
                ),
                function2_signature_hypotheses=list(
                    blocked_analysis2.signature_hypotheses
                ),
                constrained_fragments=[],
                pairwise_debug_stats={
                    diagnostic_kind: 1,
                },
                unknown_reasons=[
                    make_internal_v2_reason_diagnostic(
                        "expression_semantics_unsupported",
                        stage="S_PAIRWISE",
                        evidence_refs=(diagnostic_kind,),
                        object_target_key=(
                            diagnostic_kind,
                            e.operator,
                            e.operand_bits,
                            getattr(e, "result_bits", 0),
                            tuple(blocked_analysis1.outcome_function_identity()),
                            tuple(blocked_analysis2.outcome_function_identity()),
                        ),
                        detail=str(e),
                    )
                ],
            )

        except Exception as e:
            self._debug_print(f"Exception in check: {e}")
            if self.debug:
                import traceback
                print(traceback.format_exc())

            from .v2.abi_width_readonly import ReturnAbiAuthorityInvalid
            if isinstance(e, ReturnAbiAuthorityInvalid):
                return create_error_result(
                    analysis1=analysis1,
                    analysis2=analysis2,
                    binary1_name=binary1_name,
                    binary2_name=binary2_name,
                    error_message=e.canonical_error_kind,
                    start_time=start_time,
                    type_fix_result=type_fix_result,
                    retry_count=retry_count,
                    original_signature1=original_signature1,
                    original_signature2=original_signature2,
                    failure_status=e.canonical_error_kind,
                    failure_message=str(e),
                )
            
            return self._create_error_result(
                analysis1, analysis2, binary1_name, binary2_name,
                str(e), start_time,
                type_fix_result, retry_count,
                original_signature1, original_signature2
            )

    def _recurrence_promotion_result_receipt(self, strategy_result: Any) -> Optional[Dict[str, Any]]:
        attempt = getattr(self, "_last_recurrence_promotion_attempt", None)
        active_authority = getattr(self, "_active_recurrence_promotion_authority", None)
        if (
            attempt is None
            or active_authority is None
            or attempt.authority is None
            or attempt.authority.digest != active_authority.digest
            or attempt.state != PairPromotionState.COMPOSED
        ):
            return None
        receipt = dict(attempt.to_dict())
        comparison_receipt = getattr(strategy_result, "comparison_execution_receipt", None)
        receipt.update({
            "final_decision_used_promoted_successor": True,
            "promoted_successor_final_outcome": (
                "EQ" if strategy_result.is_equivalent is True
                else "NOT_EQ" if strategy_result.is_equivalent is False
                else "UNKNOWN"
            ),
            "promoted_successor_comparison_receipt_id": getattr(
                comparison_receipt, "receipt_id", None
            ),
        })
        return receipt

    @staticmethod
    def _recurrence_promotion_authority(
        strategy_result: Any,
        *,
        comparison_session_id: str,
        branch_id: str,
    ) -> Optional[PairRecurrencePromotionAuthority]:
        if getattr(strategy_result, "is_equivalent", None) is not None:
            return None
        reasons = tuple(getattr(strategy_result, "unknown_reasons", ()) or ())
        if not reasons:
            return None
        sat_reason_ids = {
            "counterexample_analysis_safety_unproven",
            "counterexample_same_function_replay_unproven",
            "counterexample_partition_replay_ambiguous",
            "sat_counterexample_ambiguous",
        }
        if (
            int(getattr(strategy_result, "sat_pairs", 0) or 0) > 0
            or getattr(strategy_result, "counterexample_raw", None) is not None
            or any(
                str(getattr(reason, "reason_id", "") or "") in sat_reason_ids
                or str(getattr(reason, "recovery_proof_kind", "") or "")
                == "sat_unsafety_resolution"
                for reason in reasons
            )
        ):
            return None
        recurrence_proof_kinds = {
            "loop_summary_completion", "loop_recurrence_proof",
            "call_effect_summary_proof", "effect_summary_completion",
            "guard_partition_completion", "return_partition_overlap_proof",
            "precondition_completion",
        }
        targeted = []
        for reason in reasons:
            reason_id = getattr(reason, "reason_id", None)
            if not isinstance(reason_id, str) or not reason_id:
                continue
            proof_kind = str(getattr(reason, "recovery_proof_kind", "") or "")
            if proof_kind not in recurrence_proof_kinds:
                continue
            payload = {
                "reason_id": reason_id,
                "recovery_proof_kind": proof_kind,
                "proof_stage": str(getattr(reason, "proof_stage", "") or ""),
                "object_target_key": getattr(reason, "object_target_key", None),
                "proof_obligation_id": getattr(reason, "proof_obligation_id", None),
                "typed_cause_key": getattr(reason, "typed_cause_key", None),
                "proof_requirement_ids": tuple(
                    getattr(reason, "proof_requirement_ids", ()) or ()
                ),
            }
            try:
                blocker_digest = RecurrenceDigestCodec.digest(
                    "recurrence_targeted_branch_blocker_v1", payload
                )
            except TypeError:
                continue
            targeted.append((
                "recurrence_targeted_branch_blocker_v1",
                payload["reason_id"],
                proof_kind,
                payload["object_target_key"],
                blocker_digest,
            ))
        if not targeted:
            return None
        return PairRecurrencePromotionAuthority(
            str(comparison_session_id),
            str(branch_id),
            tuple(dict.fromkeys(targeted)),
        )

    @staticmethod
    def _attach_recurrence_proposal_blockers(
        strategy_result: Any,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        *,
        branch_id: str,
    ) -> List[Any]:
        reasons = list(getattr(strategy_result, "unknown_reasons", ()) or ())
        if (
            getattr(strategy_result, "is_equivalent", None) is not None
            or int(getattr(strategy_result, "sat_pairs", 0) or 0) > 0
            or getattr(strategy_result, "counterexample_raw", None) is not None
        ):
            return reasons
        known_targets = {
            tuple(getattr(reason, "object_target_key", ()) or ())
            for reason in reasons
        }
        for side, analysis in (("function1", analysis1), ("function2", analysis2)):
            for proposal in tuple(
                getattr(analysis, "quarantined_recurrence_proposals", ()) or ()
            ):
                try:
                    from .v2.loop_recurrence import LoopBlockerProductionSignal
                    from .v2.production_signals import emit_loop_recurrence_signal

                    emit_loop_recurrence_signal(
                        LoopBlockerProductionSignal.from_recurrence_proposal(
                            analysis, proposal
                        ),
                        producer_site_manifest_id=(
                            "checker-recurrence-proposal-blocker"
                        ),
                    )
                except Exception as exc:
                    from .v2.production_signals import (
                        record_production_pilot_shadow_error,
                    )

                    record_production_pilot_shadow_error(exc)
                target = (
                    "quarantined_recurrence_proposal_blocker_v1",
                    side,
                    analysis.outcome_function_identity(),
                    proposal.digest,
                )
                if target in known_targets:
                    continue
                reasons.append(make_internal_v2_reason_diagnostic(
                    "recurrence_proposal_validation_unproven",
                    stage=str(branch_id),
                    recovery_proof_kind="loop_recurrence_proof",
                    proof_stage="recurrence_validation_complete",
                    evidence_kind="quarantined_recurrence_proposal",
                    object_target_key=target,
                    evidence_refs=(proposal.digest,),
                    detail="proof-free recurrence proposal awaits branch-local validation",
                ))
                known_targets.add(target)
        return reasons

    def _apply_preflight_final_gate(
        self,
        strategy_result: Any,
        frame: PreparedDispatchFrame,
        *,
        cleanup_complete: bool,
    ) -> None:
        """Apply veto-only preflight checks without rewriting pair outcomes."""

        receipt = getattr(strategy_result, "comparison_execution_receipt", None)
        receipt_valid = bool(
            receipt is not None
            and frame.receipt is receipt
            and receipt.is_trusted_for(frame)
        )
        source_valid = frame.source.is_unchanged()
        prepared_valid = frame.prepared.is_valid_for(frame.source) and frame.prepared.is_unchanged()
        projection_valid = frame.projection.proven
        recomputed_projection = validate_call_resolution_projection(
            frame.preflight_manifest,
            frame.prepared,
            generation=frame.generation,
            trusted_proof_artifacts=frame.trusted_proof_artifacts,
        )
        mapping_valid = (
            recomputed_projection.projection_id == frame.projection.projection_id
            and recomputed_projection.use_census_digest == frame.projection.use_census_digest
            and recomputed_projection.coverage_mapping_digest
            == frame.projection.coverage_mapping_digest
        )
        total = int(getattr(strategy_result, "total_pairs", 0) or 0)
        pairwise_complete = (
            total > 0
            and int(getattr(strategy_result, "unsat_pairs", 0) or 0) == total
            and int(getattr(strategy_result, "sat_pairs", 0) or 0) == 0
            and int(getattr(strategy_result, "unknown_pairs", 0) or 0) == 0
            and int(getattr(strategy_result, "error_pairs", 0) or 0) == 0
        )
        receipt_queries = tuple(getattr(receipt, "query_records", ()) or ())
        receipt_counts = dict(getattr(receipt, "disposition_counts", ()) or ())
        receipt_matches_pair_dispositions = bool(
            receipt is not None
            and receipt_counts.get("total") == total
            and receipt_counts.get("unsat")
            == int(getattr(strategy_result, "unsat_pairs", 0) or 0)
            and receipt_counts.get("sat")
            == int(getattr(strategy_result, "sat_pairs", 0) or 0)
            and receipt_counts.get("unknown")
            == int(getattr(strategy_result, "unknown_pairs", 0) or 0)
            and receipt_counts.get("error")
            == int(getattr(strategy_result, "error_pairs", 0) or 0)
        )
        legacy_monolithic_complete = (
            len(receipt_queries) == 1
            and receipt_queries[0].query_label == "monolithic"
            and receipt_queries[0].disposition == "unsat"
            and all(
                receipt_counts.get(name) == count
                for name, count in {
                    "total": 1,
                    "unsat": 1,
                    "sat": 0,
                    "unknown": 0,
                    "error": 0,
                }.items()
            )
            and getattr(getattr(strategy_result, "solver_results", None), "is_equivalent", None)
            is True
        )
        terminal_receipt = frame.monolithic_terminal_receipt
        from .query_receipt_authority import (
            canonical_region_query_receipt_digests,
        )
        terminal_region_digests = (
            canonical_region_query_receipt_digests(receipt_queries)
        )
        terminal_receipt_valid = bool(
            terminal_receipt is not None
            and verify_monolithic_terminal_receipt(frame)
            and receipt is not None
            and terminal_receipt.comparison_receipt_id == receipt.receipt_id
            and terminal_receipt.region_receipt_digests == terminal_region_digests
        )
        split_region_complete = bool(
            terminal_receipt_valid
            and verify_monolithic_proof_receipt(frame)
            and frame.monolithic_proof_bundle.outcome_kind == "eq_closure"
            and terminal_receipt.outcome_kind == "eq_closure"
            and receipt_counts.get("total", 0) > 0
            and receipt_counts.get("unsat") == receipt_counts.get("total")
            and receipt_counts.get("sat") == 0
            and receipt_counts.get("unknown") == 0
            and receipt_counts.get("error") == 0
            and getattr(getattr(strategy_result, "solver_results", None), "is_equivalent", None)
            is True
        )
        monolithic_complete = (
            terminal_receipt_valid
            and terminal_receipt.outcome_kind == "eq_closure"
            and (legacy_monolithic_complete or split_region_complete)
        )
        decisive_not_eq_receipt = bool(
            getattr(strategy_result, "is_equivalent", None) is False
            and (
                (
                    getattr(receipt, "branch_payload_kind", None) == "pairwise_ledger"
                    and int(receipt_counts.get("sat", 0) or 0) > 0
                )
                or (
                    terminal_receipt_valid
                    and verify_monolithic_proof_receipt(frame)
                    and frame.monolithic_proof_bundle.outcome_kind
                    == "decisive_counterexample"
                    and terminal_receipt.outcome_kind == "decisive_counterexample"
                    and (
                        (
                            len(receipt_queries) == 1
                            and receipt_queries[0].query_label == "monolithic"
                            and receipt_queries[0].disposition == "sat"
                        )
                        or any(
                            record.proof_kind == "monolithic_global_counterexample_replay"
                            and record.disposition == "sat"
                            for record in receipt_queries
                        )
                    )
                )
            )
        )
        ordinary_complete = (
            pairwise_complete
            and receipt_matches_pair_dispositions
            and getattr(receipt, "branch_payload_kind", None) == "pairwise_ledger"
            and len(tuple(getattr(receipt, "closure_snapshot", ()) or ())) == total
        ) or monolithic_complete
        required_projection_binding_ids = tuple(sorted(
            binding.binding_id for binding in frame.projection.semantic_bindings
        ))
        consumed_projection_binding_ids = tuple(
            getattr(receipt, "consumed_projection_binding_ids", ()) or ()
        )
        excluded_projection_binding_ids = tuple(
            getattr(receipt, "excluded_projection_binding_ids", ()) or ()
        )
        receipt_required_projection_binding_ids = tuple(
            getattr(receipt, "required_projection_binding_ids", ()) or ()
        )
        projection_bindings_consumed = (
            not frame.projection.required
            or (
                bool(required_projection_binding_ids)
                and receipt_required_projection_binding_ids
                == required_projection_binding_ids
                and not (
                    set(consumed_projection_binding_ids)
                    & set(excluded_projection_binding_ids)
                )
                and tuple(sorted(
                    set(consumed_projection_binding_ids)
                    | set(excluded_projection_binding_ids)
                )) == required_projection_binding_ids
            )
        )
        projection_active_total = int(
            receipt_counts.get("projection_active_total", -1)
        )
        projection_receipt_partition_valid = bool(
            receipt is not None
            and projection_active_total
            == sum(1 for record in receipt_queries if record.projection_binding_ids)
            and int(receipt_counts.get("projection_inactive_total", -1))
            == sum(1 for record in receipt_queries if not record.projection_binding_ids)
        )
        no_active_pair_proven = bool(
            int(receipt_counts.get("projection_no_active_pair_proven", 0)) == 1
        )

        blockers = []
        expected_terminal_kind = (
            "eq_closure" if getattr(strategy_result, "is_equivalent", None) is True
            else "decisive_counterexample"
            if getattr(strategy_result, "is_equivalent", None) is False
            else "inconclusive_diagnostic"
        )
        if (
            terminal_receipt is not None
            and (
                not terminal_receipt_valid
                or terminal_receipt.outcome_kind != expected_terminal_kind
            )
        ):
            blockers.append("monolithic_terminal_outcome_mismatch")
        if not cleanup_complete or not frame.cleanup_complete:
            blockers.append("dispatch_cleanup_incomplete")
        if not source_valid:
            blockers.append("source_analysis_mutated")
        if not prepared_valid:
            blockers.append("prepared_surface_invalid")
        if frame.projection.required and not projection_valid:
            blockers.extend(frame.projection.root_blockers or ("call_effect_preflight_incomplete",))
        if not mapping_valid:
            blockers.append("deferred_call_use_coverage_mapping_invalid")
        split_stats = dict(
            getattr(strategy_result, "pairwise_debug_stats", None) or {}
        )
        split_receipt_required = int(
            split_stats.get("monolithic_split_planned_regions", 0) or 0
        ) > 0
        if (
            getattr(strategy_result, "is_equivalent", None) in {True, False}
            and not receipt_valid
            and (frame.projection.required or split_receipt_required)
        ):
            blockers.append("comparison_receipt_missing")
        if receipt_valid and not projection_receipt_partition_valid:
            blockers.append("call_projection_active_pair_receipt_invalid")
        if (
            receipt_valid
            and frame.projection.required
            and projection_valid
            and projection_active_total == 0
            and not no_active_pair_proven
        ):
            blockers.append("call_projection_no_active_pair_proof_missing")
        if (
            receipt_valid
            and getattr(strategy_result, "is_equivalent", None) is True
            and not projection_bindings_consumed
        ):
            blockers.append("call_projection_binding_consumption_incomplete")
        if receipt_valid and getattr(strategy_result, "is_equivalent", None) is True and not ordinary_complete:
            blockers.append("ordinary_comparison_proof_incomplete")
        if receipt_valid and getattr(strategy_result, "is_equivalent", None) is False and not decisive_not_eq_receipt:
            blockers.append("decisive_counterexample_receipt_incomplete")

        if blockers:
            if getattr(strategy_result, "is_equivalent", None) in {True, False}:
                strategy_result.is_equivalent = None
            existing = {
                str(ref)
                for reason in tuple(getattr(strategy_result, "unknown_reasons", ()) or ())
                for ref in tuple(getattr(reason, "evidence_refs", ()) or ())
            }
            for blocker in dict.fromkeys(str(item) for item in blockers):
                if blocker in existing:
                    continue
                strategy_result.unknown_reasons.append(
                    make_internal_v2_reason_diagnostic(
                        "pure_call_semantics_unproven",
                        stage="CALL_EFFECT_PREFLIGHT",
                        evidence_refs=(blocker,),
                        detail=f"Call/effect preflight veto: {blocker}",
                    )
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
            self._attach_structural_coverage_certificate(manifest)
            production = produce_pure_direct_call_proofs(
                manifest,
                analysis1,
                analysis2,
                solver_runner=self.solver_runner,
                timeout_seconds=self.timeout,
            )
            if not any(
                signal.effect_stage_required
                for signal in production.v2_blocker_signals
            ):
                try:
                    v2_context = build_active_call_effect_execution_context(
                        production.v2_blocker_signals,
                        CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
                    )
                    if v2_context is not None:
                        v2_production = produce_v2_pure_direct_call_proofs(
                            manifest,
                            analysis1,
                            analysis2,
                            execution_context=v2_context,
                            timeout_seconds=self.timeout,
                        )
                        apply_solver_proof_artifacts_to_manifest(
                            manifest,
                            v2_production.artifacts,
                        )
                        completed_obligation_ids = {
                            str(item.get("obligation_id") or "")
                            for item in manifest.get("proof_readiness", ()) or ()
                            if isinstance(item, Mapping)
                            and item.get("decision_eligible") is True
                        }
                        required_obligation_ids = {
                            signal.obligation_id
                            for signal in production.v2_blocker_signals
                        }
                        if (
                            v2_production.failure_causes
                            and required_obligation_ids
                            and required_obligation_ids.issubset(
                                completed_obligation_ids
                            )
                        ):
                            raise ValueError(
                                "V2 call/effect proof has unmaterialized post-stage blockers"
                            )
                        artifacts_by_obligation: Dict[str, List[Any]] = {}
                        for artifact in v2_production.artifacts:
                            artifacts_by_obligation.setdefault(
                                artifact.record.obligation_id, []
                            ).append(artifact)
                        for signal in production.v2_blocker_signals:
                            artifacts = tuple(
                                artifacts_by_obligation.get(signal.obligation_id, ())
                            )
                            if artifacts:
                                emit_call_effect_signal(
                                    CallEffectProofBatchProductionSignal(
                                        signal, artifacts
                                    ),
                                    producer_site_manifest_id=(
                                        CALL_EFFECT_PROOF_BATCH_SITE.site_id
                                    ),
                                )
                        manifest["v2_call_effect_shadow_producer"] = {
                            "mode": "pinned_execution_dual_write",
                            "artifact_count": len(v2_production.artifacts),
                            "failure_causes": list(v2_production.failure_causes),
                            "completed_obligation_ids": sorted(
                                completed_obligation_ids
                            ),
                        }
                except Exception as exc:
                    record_production_pilot_shadow_error(exc)
                    manifest["v2_call_effect_shadow_producer"] = {
                        "mode": "shadow_evidence_incomplete",
                        "error_kind": type(exc).__name__,
                    }
            self._last_internal_call_effect_artifacts = production.artifacts
            if production.artifacts:
                manifest["mode"] = "typed_relational_call_effect_proof"
            apply_solver_proof_artifacts_to_manifest(
                manifest,
                production.artifacts,
            )
            manifest["stage_specific_producer"] = {
                "producer_kind": "typed_pure_direct_call_v1",
                "artifact_count": len(production.artifacts),
                "failure_causes": list(production.failure_causes),
            }
            return manifest
        except Exception as exc:
            self._last_internal_call_effect_artifacts = ()
            self._debug_print(f"Call/effect shadow manifest unavailable: {exc}")
            return {
                "schema_version": 1,
                "mode": "shadow_no_decision_effect",
                "observation_contract": self.observation_contract.to_dict(),
                "shadow_status": "inconclusive",
                "failure_cause": "shadow_manifest_construction_failed",
                "error_type": type(exc).__name__,
                "error_detail": str(exc),
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
        """Promote only an all-UNSAT caller result with complete typed call proofs."""

        gate = {
            "status": "blocked",
            "decision_effect": "blocks_equivalence",
            "failure_cause": "call_effect_stage_proofs_incomplete",
        }
        manifest["phase2_discharge_gate"] = gate
        if not self.enable_completed_recovery_proofs:
            gate["status"] = "disabled"
            gate["decision_effect"] = "diagnostic_only"
            gate["failure_cause"] = "completed_recovery_proofs_disabled"
            return
        apply_solver_proof_artifacts_to_manifest(
            manifest,
            self._last_internal_call_effect_artifacts,
        )
        certificate = manifest.get("structural_coverage_certificate")
        rebuilt_certificate = build_structural_coverage_certificate(manifest)
        if not isinstance(certificate, Mapping) or (
            certificate.get("status") != "complete"
            or certificate.get("verification_status") != "verified"
            or certificate.get("certificate_id") != rebuilt_certificate.certificate_id
            or rebuilt_certificate.verification_failure() is not None
        ):
            gate["failure_cause"] = "structural_coverage_certificate_incomplete"
            return
        obligations = tuple(
            item
            for item in manifest.get("relational_obligations", ()) or ()
            if isinstance(item, Mapping)
        )
        readiness = tuple(
            item
            for item in manifest.get("proof_readiness", ()) or ()
            if isinstance(item, Mapping)
        )
        if not obligations or len(readiness) != len(obligations):
            gate["failure_cause"] = "call_effect_obligation_coverage_incomplete"
            return
        supported_relation_kinds = {
            "call_to_call",
            "call_to_region",
            "region_to_call",
        }
        if any(
            item.get("relation_kind") not in supported_relation_kinds
            for item in obligations
        ):
            gate["failure_cause"] = "unsupported_relational_call_effect_lane"
            return
        caller_memory_effect_counts = []
        for side, analysis in (("function1", analysis1), ("function2", analysis2)):
            effect_summary = getattr(analysis, "effect_summary", None)
            effect_count = len(tuple(getattr(effect_summary, "effects", ()) or ()))
            profile = getattr(
                effect_summary,
                "function_control_effect_profile",
                None,
            )
            explicit_store_count = int(getattr(profile, "store_count", 0) or 0)
            call_derived_store_count = sum(
                int(getattr(evidence, "memory_effect_count", 0) or 0)
                for evidence in tuple(
                    getattr(
                        effect_summary,
                        "call_site_effect_summary_evidence",
                        (),
                    )
                    or ()
                )
            )
            if effect_count or explicit_store_count or call_derived_store_count:
                caller_memory_effect_counts.append(
                    {
                        "side": side,
                        "effect_count": effect_count,
                        "explicit_store_count": explicit_store_count,
                        "call_derived_store_count": call_derived_store_count,
                    }
                )
        caller_memory_proven = bool(readiness) and all(
            "caller_memory_relation"
            in tuple(item.get("completed_stages", ()) or ())
            for item in readiness
        )
        if caller_memory_effect_counts and not caller_memory_proven:
            gate["failure_cause"] = "caller_memory_relation_not_proven"
            gate["caller_memory_effects"] = caller_memory_effect_counts
            return
        if not all(item.get("decision_eligible") is True for item in readiness):
            gate["failure_cause"] = "call_effect_stage_proofs_incomplete"
            return
        for analysis in (analysis1, analysis2):
            effect_summary = getattr(analysis, "effect_summary", None)
            incomplete_reasons = tuple(
                getattr(effect_summary, "incomplete_reasons", ()) or ()
            )
            if incomplete_reasons:
                gate["failure_cause"] = "non_call_effect_unsafety_present"
                gate["non_call_effect_unsafety"] = list(incomplete_reasons)
                return
            if bool(getattr(effect_summary, "has_unsupported_call", False)):
                gate["failure_cause"] = "unsupported_call_effect_present"
                return
            if "effect_summary_path_coverage_incomplete" in tuple(
                getattr(analysis, "analysis_notes", ()) or ()
            ):
                gate["failure_cause"] = "non_call_effect_unsafety_present"
                gate["non_call_effect_unsafety"] = [
                    "effect_summary_path_coverage_incomplete"
                ]
                return
        replacement_readiness = manifest.get("legacy_replacement_readiness")
        if not isinstance(replacement_readiness, Mapping) or (
            replacement_readiness.get("status") != "ready"
        ):
            gate["failure_cause"] = "legacy_blocker_replacement_not_ready"
            return
        raw_reasons = list(getattr(strategy_result, "unknown_reasons", ()) or ())
        from .v2.call_effect import CALL_EFFECT_REASON_SPECS

        if not raw_reasons or any(
            str(getattr(reason, "reason_id", "")) not in CALL_EFFECT_REASON_SPECS
            for reason in raw_reasons
        ):
            gate["failure_cause"] = "non_call_unknown_reason_present"
            return
        completed_obligation_ids = {
            str(item.get("obligation_id"))
            for item in readiness
            if item.get("decision_eligible") is True and item.get("obligation_id")
        }
        blocker_mappings = tuple(
            item
            for item in manifest.get("legacy_blocker_mapping", ()) or ()
            if isinstance(item, Mapping)
        )
        for reason in raw_reasons:
            evidence_refs = tuple(getattr(reason, "evidence_refs", ()) or ())
            if len(evidence_refs) != 1:
                gate["failure_cause"] = "call_blocker_obligation_mapping_incomplete"
                return
            matching = tuple(
                item
                for item in blocker_mappings
                if str(item.get("legacy_blocker") or "") == str(evidence_refs[0])
            )
            if len(matching) != 1:
                gate["failure_cause"] = "call_blocker_obligation_mapping_incomplete"
                return
            mapping = matching[0]
            obligation_ids = tuple(mapping.get("obligation_ids", ()) or ())
            if (
                mapping.get("mapping_basis") != "callsite_pcode_ref"
                or mapping.get("mapping_status") != "mapped"
                or len(obligation_ids) != 1
                or str(obligation_ids[0]) not in completed_obligation_ids
            ):
                gate["failure_cause"] = "call_blocker_not_exactly_mapped"
                gate["unmapped_blocker"] = str(evidence_refs[0])
                return
        total_pairs = int(getattr(strategy_result, "total_pairs", 0) or 0)
        if (
            total_pairs <= 0
            or int(getattr(strategy_result, "unsat_pairs", 0) or 0) != total_pairs
            or int(getattr(strategy_result, "sat_pairs", 0) or 0) != 0
            or int(getattr(strategy_result, "unknown_pairs", 0) or 0) != 0
            or int(getattr(strategy_result, "error_pairs", 0) or 0) != 0
            or getattr(strategy_result, "is_equivalent", None) is False
        ):
            gate["failure_cause"] = "caller_relational_return_proof_incomplete"
            return
        strategy_result.is_equivalent = True
        strategy_result.unknown_reasons = []
        coupling = manifest.get("coupling")
        if isinstance(coupling, dict):
            coupling["semantic_proof_status"] = "proven"
        summary = manifest.get("summary")
        if isinstance(summary, dict):
            summary["semantic_proof_status"] = "proven"
        gate.update(
            {
                "status": "proven",
                "decision_effect": "promotes_equivalence",
                "failure_cause": None,
                "proof_kind": "typed_pure_direct_call_relational_proof",
            }
        )

    @staticmethod
    def _specialize_call_effect_unknown_reasons(
        reasons: List[Any],
        manifest: Mapping[str, Any],
        comparison_identity: Optional[Mapping[str, Any]] = None,
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
        blocker_obligations: Dict[str, Tuple[str, ...]] = {}
        for item in mappings:
            if not isinstance(item, Mapping):
                continue
            if (
                item.get("mapping_basis") != "callsite_pcode_ref"
                or item.get("mapping_status") != "mapped"
            ):
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
                blocker_obligations[blocker] = tuple(
                    sorted(str(value) for value in (item.get("obligation_ids") or ()))
                )

        specialized: List[Any] = []
        for reason in reasons:
            from .v2.call_effect import CALL_EFFECT_REASON_SPECS

            if str(getattr(reason, "reason_id", "")) not in CALL_EFFECT_REASON_SPECS:
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
            matched_blockers = tuple(
                sorted(
                    str(ref)
                    for ref in getattr(reason, "evidence_refs", ()) or ()
                    if str(ref) in blocker_stages
                )
            )
            obligation_ids = tuple(
                sorted(
                    {
                        obligation_id
                        for blocker in matched_blockers
                        for obligation_id in blocker_obligations.get(blocker, ())
                    }
                )
            )
            coupling = manifest.get("coupling") if isinstance(manifest.get("coupling"), Mapping) else {}
            observation = manifest.get("observation_contract") if isinstance(manifest.get("observation_contract"), Mapping) else {}
            typed_cause = RelationalCauseKey(
                cause_kind="deferred_call_effect_relation",
                comparison_domain=(
                    "semantic_comparison_domain",
                    tuple((comparison_identity or {}).get("left_binary_content_identity") or ()),
                    tuple((comparison_identity or {}).get("right_binary_content_identity") or ()),
                    tuple((comparison_identity or {}).get("function_identity") or ()),
                    tuple((comparison_identity or {}).get("architecture_identity") or ()),
                    tuple((comparison_identity or {}).get("abi_identity") or ()),
                    tuple((comparison_identity or {}).get("signature_storage_contract") or ()),
                    tuple((comparison_identity or {}).get("calling_convention_fingerprint") or ()),
                    tuple((comparison_identity or {}).get("comparison_policy_fingerprint") or ()),
                    "call_effect_coupling",
                    str(coupling.get("coupling_id") or "missing_coupling_id"),
                    str(observation.get("contract_id") or "missing_observation_contract"),
                ),
                left_semantic_object=(
                    "legacy_blocker_target",
                    reason.object_target_key,
                ),
                right_semantic_object=(
                    "relational_obligation_ids",
                    obligation_ids,
                ),
                correspondence_contract=(
                    "mapping_basis",
                    "callsite_pcode_ref",
                    "proof_stages",
                    tuple(sorted(stages)),
                ),
            )
            proof_requirement = ProofRequirementId.create(
                reason.recovery_proof_kind,
                canonical_cause_tuple(typed_cause),
                ProofRequirementContract(
                    "prove relational deferred call return/effect equivalence",
                    relation_direction="ordered",
                    observation_surface=(
                        str(observation.get("contract_id") or "missing_observation_contract"),
                    ),
                    active_precondition=("mapped_obligations", obligation_ids),
                ),
            )
            comparison_identity_complete = bool(
                (comparison_identity or {}).get("left_binary_content_identity")
                and (comparison_identity or {}).get("right_binary_content_identity")
            )
            specialized.append(
                make_internal_v2_reason_diagnostic(
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
                    typed_cause_key=(
                        typed_cause.to_dict() if comparison_identity_complete else None
                    ),
                    proof_requirement_ids=(
                        (proof_requirement.to_dict(),)
                        if comparison_identity_complete
                        else ()
                    ),
                    recovery_action="relational_call_effect_stage_proof_required",
                    action_status=reason.action_status,
                    target_regression=reason.target_regression,
                    detail=(
                        f"Relational call/effect proof is incomplete at {proof_stage}."
                    ),
                )
            )
        return specialized

    @classmethod
    def _attach_root_blocker_identities(
        cls,
        reasons: List[Any],
        comparison_identity: Mapping[str, Any],
    ) -> List[Any]:
        """Attach typed root-cause/proof identities to all key-backed reasons."""

        if not (
            comparison_identity.get("left_binary_content_identity")
            and comparison_identity.get("right_binary_content_identity")
        ):
            return reasons
        enriched = []
        for reason in reasons:
            if getattr(reason, "typed_cause_key", None):
                enriched.append(reason)
                continue
            target = getattr(reason, "object_target_key", None)
            if not target:
                enriched.append(reason)
                continue
            cause = cls._typed_cause_for_reason(reason, target, comparison_identity)
            if cause is None:
                enriched.append(reason)
                continue
            requirements = []
            for action in build_unknown_recovery_actions((reason,)):
                proof_kind = str(getattr(action, "proof_kind", "none") or "none")
                if proof_kind == "none":
                    continue
                contract = ProofRequirementContract(
                    proposition=f"complete {proof_kind}",
                    relation_direction=(
                        "ordered"
                        if getattr(cause, "identity_scope", "") == "relational"
                        else "unary"
                    ),
                    observation_surface=tuple(
                        getattr(action, "required_evidence", ()) or ()
                    ),
                    active_precondition=(
                        "recovery_action",
                        str(getattr(action, "recovery_action", "") or "unspecified"),
                    ),
                )
                requirements.append(
                    ProofRequirementId.create(
                        proof_kind,
                        canonical_cause_tuple(cause),
                        contract,
                    ).to_dict()
                )
            enriched.append(
                replace(
                    reason,
                    typed_cause_key=cause.to_dict(),
                    proof_requirement_ids=tuple(requirements),
                )
            )
        return enriched

    @classmethod
    def _typed_cause_for_reason(
        cls,
        reason: Any,
        target: Tuple[Any, ...],
        comparison_identity: Mapping[str, Any],
    ) -> Any:
        raw_reason_id = getattr(reason, "reason_id", None)
        if not isinstance(raw_reason_id, str) or not raw_reason_id:
            return None
        reason_id = raw_reason_id
        side = cls._root_cause_side(target)
        relational_reasons = {
            "sat_counterexample_ambiguous",
            "return_width_bridge_missing",
        }
        unary_reasons = {
            "return_coverage_gap",
            "return_coverage_inconclusive",
            "phi_circular_replacement_unproven",
            "summary_return_candidate_invalid",
            "summary_return_overlap_unproven",
            "summary_effect_unmodeled",
            "summary_precondition_incomplete",
            "summary_partition_not_total",
        }
        if side is not None:
            local_content = (
                comparison_identity.get("left_binary_content_identity")
                if side == "function1"
                else comparison_identity.get("right_binary_content_identity")
            )
            function_identities = tuple(
                comparison_identity.get("function_identity") or ()
            )
            local_function = (
                function_identities[0]
                if side == "function1" and function_identities
                else function_identities[1]
                if side == "function2" and len(function_identities) > 1
                else ("missing_function_identity",)
            )
            return UnaryCauseKey(
                cause_kind=reason_id,
                binary_content_identity=tuple(local_content or ()),
                function_ir_identity=("function_identity", local_function),
                semantic_object_identity=(
                    "object_target",
                    cls._strip_root_cause_side(target),
                ),
            )
        if reason_id in relational_reasons or reason_id in unary_reasons or reason_id == (
            "unresolved_value_expression"
        ):
            function_identities = tuple(
                comparison_identity.get("function_identity") or ()
            )
            return RelationalCauseKey(
                cause_kind=reason_id,
                comparison_domain=cls._root_comparison_domain(comparison_identity),
                left_semantic_object=(
                    "left_function",
                    function_identities[0] if function_identities else (),
                    "target",
                    target,
                ),
                right_semantic_object=(
                    "right_function",
                    function_identities[1] if len(function_identities) > 1 else (),
                    "target",
                    target,
                ),
                correspondence_contract=("reason_scope", getattr(reason, "reason_scope", None)),
            )
        return None

    @staticmethod
    def _root_cause_side(value: Any) -> Optional[str]:
        if isinstance(value, tuple):
            for item in value[:4]:
                if isinstance(item, str) and item in {"function1", "function2"}:
                    return str(item)
        return None

    @classmethod
    def _strip_root_cause_side(cls, value: Any) -> Any:
        if isinstance(value, tuple):
            return tuple(
                "local_function"
                if isinstance(item, str) and item in {"function1", "function2"}
                else cls._strip_root_cause_side(item)
                for item in value
            )
        return value

    @staticmethod
    def _root_comparison_domain(identity: Mapping[str, Any]) -> Tuple[Any, ...]:
        return tuple(
            (name, tuple(identity.get(name) or ()))
            for name in (
                "left_binary_content_identity",
                "right_binary_content_identity",
                "function_identity",
                "architecture_identity",
                "abi_identity",
                "signature_storage_contract",
                "calling_convention_fingerprint",
                "comparison_policy_fingerprint",
            )
        )

    @staticmethod
    def _deterministic_analysis_identity(strategy: Any, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
        method = getattr(strategy, "_deterministic_function_identity", None)
        if callable(method):
            return tuple(method(analysis))
        function_ref = getattr(analysis, "function_ref", None)
        return (
            "function_identity",
            ("binary_id", getattr(analysis, "binary_id", None)),
            ("function_name", getattr(analysis, "function_name", None)),
            ("entry_offset", getattr(function_ref, "entry_offset", None)),
            ("entry_point", getattr(analysis, "entry_point", None)),
            ("signature", FunctionSignature.from_analysis(analysis).to_dict()),
            ("calling_convention", getattr(analysis, "calling_convention", None)),
        )

    def _call_effect_comparison_identity(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        manifest: Mapping[str, Any],
    ) -> Dict[str, Any]:
        left_content, right_content = getattr(
            self, "_active_binary_content_identities", (None, None)
        ) or (None, None)
        left_identity = self._deterministic_analysis_identity(
            self.pairwise_strategy, analysis1
        )
        right_identity = self._deterministic_analysis_identity(
            self.pairwise_strategy, analysis2
        )
        observation = manifest.get("observation_contract")
        observation = observation if isinstance(observation, Mapping) else {}
        return {
            "left_binary_content_identity": tuple(left_content or ()),
            "right_binary_content_identity": tuple(right_content or ()),
            "function_identity": (
                ("left_function_identity", left_identity),
                ("right_function_identity", right_identity),
            ),
            "architecture_identity": (
                ("left", self._analysis_architecture_identity(analysis1)),
                ("right", self._analysis_architecture_identity(analysis2)),
            ),
            "abi_identity": (
                ("left", self._analysis_abi_identity(analysis1)),
                ("right", self._analysis_abi_identity(analysis2)),
            ),
            "signature_storage_contract": (
                ("left_signature", FunctionSignature.from_analysis(analysis1).to_dict()),
                ("right_signature", FunctionSignature.from_analysis(analysis2).to_dict()),
            ),
            "calling_convention_fingerprint": (
                getattr(analysis1, "calling_convention", None)
                or getattr(analysis1, "calling_convention_name", None)
                or "unknown_calling_convention",
                getattr(analysis2, "calling_convention", None)
                or getattr(analysis2, "calling_convention_name", None)
                or "unknown_calling_convention",
            ),
            "comparison_policy_fingerprint": (
                "observation_contract",
                observation.get("contract_id"),
                "normalize_mode",
                getattr(self.normalization_settings, "mode", None),
            ),
        }

    @staticmethod
    def _analysis_architecture_identity(analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
        return (
            "architecture_identity",
            ("language_id", getattr(analysis, "language_id", None) or getattr(analysis, "program_language_id", None)),
            ("processor", getattr(analysis, "processor", None) or getattr(analysis, "processor_name", None)),
            ("endianness", getattr(analysis, "endianness", None) or getattr(analysis, "endian", None)),
            ("address_size", getattr(analysis, "address_size", None) or getattr(analysis, "pointer_size", None)),
        )

    @staticmethod
    def _analysis_abi_identity(analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
        return (
            "abi_identity",
            ("abi_name", getattr(analysis, "abi_name", None) or getattr(analysis, "abi", None)),
            ("compiler_spec_id", getattr(analysis, "compiler_spec_id", None)),
            ("compiler_artifact_identity", getattr(analysis, "compiler_artifact_identity", None)),
        )

    def _completed_recovery_proof_payload(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        binary1_name: str,
        binary2_name: str,
        *,
        extra_records=(),
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
        records.extend(
            dict(item) for item in tuple(extra_records or ())
            if isinstance(item, Mapping)
        )
        unique = {}
        for item in records:
            evidence = item.get("evidence") or {}
            identity = (
                item.get("side"),
                SnapshotFingerprintCodec.freeze(
                    evidence.get("proof_requirement_id")
                    or evidence.get("proof_obligation_id")
                    or evidence
                ),
            )
            unique.setdefault(identity, item)
        return list(unique.values())

    @staticmethod
    def _reason_completion_applicability_contexts(
        completed_proofs,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> List[Dict[str, Any]]:
        """Validate completion artifacts against the live analysis snapshots.

        This is the runtime trust boundary used by attempt recording.  Evidence
        fields are never reused as their own current applicability values.
        """

        from .obligations.runtime import (
            GLOBAL_VALIDATED_UNARY_ARTIFACT_CACHE,
            ObligationRuntimeSession,
        )

        by_side = {"function1": analysis1, "function2": analysis2}
        contexts: List[Dict[str, Any]] = []
        for wrapper in tuple(completed_proofs or ()):
            if not isinstance(wrapper, Mapping):
                continue
            analysis = by_side.get(str(wrapper.get("side") or ""))
            evidence = wrapper.get("evidence")
            if analysis is None or not isinstance(evidence, Mapping):
                continue
            artifact_id = evidence.get("proof_artifact_ref")
            requirement = evidence.get("proof_requirement_id")
            if artifact_id is None or not isinstance(requirement, Mapping):
                continue
            try:
                artifact_id = tuple(SnapshotFingerprintCodec.freeze(artifact_id))
                current_snapshot = ObligationRuntimeSession._snapshot(
                    analysis, "completion_applicability"
                ).semantic_fingerprint
            except (TypeError, ValueError):
                continue
            entry = GLOBAL_VALIDATED_UNARY_ARTIFACT_CACHE.find_applicable_artifact(
                artifact_id,
                function_snapshot_fingerprint=current_snapshot,
            )
            if entry is None:
                continue
            artifact_digest = SnapshotFingerprintCodec.digest((
                entry.artifact.artifact_id,
                entry.artifact.payload,
            ))
            contexts.append({
                "proof_requirement_id": dict(requirement),
                "proof_artifact_ref": entry.artifact.artifact_id,
                "current_snapshot_fingerprint": current_snapshot,
                "current_semantic_seed_or_premise_digest": entry.function_premise_digest,
                "current_evidence_or_artifact_digest": artifact_digest,
                "artifact_is_valid": True,
            })
        return contexts

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
