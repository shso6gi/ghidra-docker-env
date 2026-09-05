# -*- coding: utf-8 -*-
"""等価性判定メインロジック（Stage/Phase ループ骨格版）"""

from typing import Optional, Dict, Any, List, Mapping, Tuple
from enum import Enum
from dataclasses import dataclass
import time
import warnings

from scripts.function_tracer_pcode.core import FunctionReturnAnalysis, FunctionSignature
from scripts.function_tracer_pcode.core.render_smt import (
    UnknownSmtExtensionWidthError,
    UnsupportedSmtOperatorError,
)
from scripts.function_tracer_pcode.smt import ParallelSolverRunner, ParallelResult
from scripts.function_tracer_pcode.proof.formula import FormulaBuilder
from scripts.function_tracer_pcode.proof.formula.returns import ReturnWidthMismatchError
from scripts.function_tracer_pcode.checker.counterexample import CounterexampleFormatter
from scripts.function_tracer_pcode.semantics.typing.fixer import (
    TypeFixer,
    TypeFixerConfig,
    TypeFixResult,
)
from scripts.function_tracer_pcode.checker.result import EquivalenceResult, RewriteInfo
from scripts.function_tracer_pcode.checker.result_factory import create_error_result
from scripts.function_tracer_pcode.checker.phases.handler import (
    PhaseHandler,
    PhaseContext,
    PhaseResult,
)
from scripts.function_tracer_pcode.checker.reanalysis import (
    analyze_and_check_with_analysis,
    selective_reanalysis_and_check,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.proof.strategies.loop_template import (
    LoopTemplatePairwiseStrategy,
)
from scripts.function_tracer_pcode.proof.strategies.monolithic import MonolithicStrategy
from scripts.function_tracer_pcode.semantics.normalize import NormalizationSettings
from scripts.function_tracer_pcode.checker.debug_trace import DebugTrace, PairwiseDecisiveInfo
from scripts.function_tracer_pcode.checker.attempts import (
    get_transition_reason,
    record_attempt,
    record_attempt_from_result,
)
from scripts.function_tracer_pcode.proof.obligations.snapshot import SnapshotFingerprintCodec
from scripts.function_tracer_pcode.proof.recursive_abstraction import abstract_recursive_calls
from scripts.function_tracer_pcode.authority.lifecycle.production_boundary import (
    run_check_from_binaries_with_v2_pilot as run_check_from_binaries,
)
from scripts.function_tracer_pcode.checker.unknown_reason import (
    build_unknown_recovery_actions,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.checker.cause_identity import (
    ProofRequirementContract,
    ProofRequirementId,
    UnaryCauseKey,
    RelationalCauseKey,
    canonical_cause_tuple,
)
from scripts.function_tracer_pcode.proof.call_effect.obligations import (
    EquivalenceObservationContract,
    apply_solver_proof_artifacts_to_manifest,
    build_call_effect_shadow_manifest,
    build_structural_coverage_certificate,
)
from scripts.function_tracer_pcode.proof.call_effect.producer import (
    produce_pure_direct_call_proofs,
    produce_v2_pure_direct_call_proofs,
)
from scripts.function_tracer_pcode.authority.domains.call_effect import (
    CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
)
from scripts.function_tracer_pcode.authority.domains.call_effect_sites import (
    CALL_EFFECT_PROOF_BATCH_SITE,
)
from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
    CallEffectProofBatchProductionSignal,
    build_active_call_effect_execution_context,
    emit_call_effect_signal,
    record_production_pilot_shadow_error,
)
from scripts.function_tracer_pcode.proof.call_effect.preflight import (
    CallProofDecisionMode,
    verify_monolithic_terminal_receipt,
    verify_monolithic_proof_receipt,
)
from scripts.function_tracer_pcode.proof.recurrence_promotion import (
    PairRecurrencePromotionAuthority,
)
from scripts.function_tracer_pcode.core.recurrence_contracts import RecurrenceDigestCodec


# Re-exports kept for callers that import these names from this module.
from scripts.function_tracer_pcode.smt import SolverResult
from scripts.function_tracer_pcode.checker.abi_retry import AbiRetryMixin
from scripts.function_tracer_pcode.checker.branch_context import BranchCheckContext, build_branch_check_context
from scripts.function_tracer_pcode.checker.unknown_refinement import refine_unknown_reasons
from scripts.function_tracer_pcode.checker.recurrence_promotion import (
    complete_recurrence_promotion_signals,
    prepare_recurrence_promotion,
)
from scripts.function_tracer_pcode.checker.result_assembly import (
    assemble_equivalence_result,
    canonical_abi_error_result,
    unsupported_smt_result,
)
from scripts.function_tracer_pcode.checker.strategy_execution import (
    build_prepared_dispatch_frame,
    prepare_preflight_projection,
    prepare_strategy_runtime,
    run_legacy_strategy,
    run_strategy_branch,
)
from scripts.function_tracer_pcode.checker.preflight_gate import PreflightGateMixin
from scripts.function_tracer_pcode.checker.root_causes import RootCauseMixin
from scripts.function_tracer_pcode.checker.recovery_proofs import RecoveryProofMixin
from scripts.function_tracer_pcode.checker.recurrence_stage import RecurrenceStageMixin


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


class EquivalenceChecker(AbiRetryMixin, PreflightGateMixin, RootCauseMixin, RecoveryProofMixin, RecurrenceStageMixin):
    """等価性判定を行うクラス"""
    
    def __init__(
        self,
        timeout: int = 10,
        debug: bool = False,
        type_fixer_config: Optional[TypeFixerConfig] = None,
        enable_rewrite: Optional[bool] = None,
        rewrite_direction: Optional[str] = None,
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
            enable_rewrite: 非推奨・無効（互換のため受け付けるだけ）。
                リライト段階は object-centric solver-only 方針で解析結果を
                変更しておらず、設定は判定に影響しない。
            rewrite_direction: 非推奨・無効（同上）。
            strategy: 判定戦略 ("pairwise" or "monolithic")
        """
        self.timeout = timeout
        self.debug = debug
        self.type_fixer_config = type_fixer_config or TypeFixerConfig()
        if enable_rewrite is not None or rewrite_direction is not None:
            warnings.warn(
                "EquivalenceChecker(enable_rewrite=..., rewrite_direction=...) has no "
                "effect and is deprecated; the rewrite stage never modified the analysis",
                DeprecationWarning,
                stacklevel=2,
            )
        # 互換 surface（#54 で撤去予定）: 従来どおりの既定値を持つ属性として残す
        # が、内部コードはこの 2 属性を読まない。
        self.enable_rewrite = True if enable_rewrite is None else enable_rewrite
        self.rewrite_direction = "to_modulo" if rewrite_direction is None else rewrite_direction
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
            from scripts.function_tracer_pcode.authority.decision.production_cutover import (
                build_default_cutover_connector,
            )

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
    
    def _get_params_via_decompile(
        self,
        program,
        function_name: str,
        timeout: int
    ) -> List[Dict[str, Any]]:
        """デコンパイルして引数情報を取得"""
        from scripts.function_tracer_pcode.analysis import ReturnAnalyzer
        
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
        from scripts.function_tracer_pcode.proof.obligations.stage_runner import (
            run_obligation_branch_plan,
        )

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
        force_strategy = None,
        *,
        branch_context: Optional[BranchCheckContext] = None,
    ) -> EquivalenceResult:
        """2つの関数の等価性を判定

        ``branch_context``: Internal execution context (stage runner → checker の明示的な
        branch 文脈、Phase 6c #93); ordinary direct callers should normally omit it.
        与えられればそのまま使い、無ければ従来どおり facade の ``_active_*`` から組み立てる。
        """
        start_time = time.time()
        
        if original_signature1 is None:
            original_signature1 = FunctionSignature.from_analysis(analysis1)
        if original_signature2 is None:
            original_signature2 = FunctionSignature.from_analysis(analysis2)
        
        try:
            # リライト段階は廃止済み（解析結果を変更したことはない）。結果 JSON の
            # `rewrite_info` は互換のため従来どおりの定数を出す。
            rewrite_info = RewriteInfo()

            # strategy を選択
            strategy = force_strategy if force_strategy is not None else self.check_strategy

            if branch_context is not None:
                replan_plan = branch_context.replan_plan
            else:
                replan_plan = getattr(self, "_active_pair_replan_plan", None)
            if replan_plan is None:
                # 6b-1: generation の increment は facade write として check() に残す（replan でない場合のみ）。
                # 6c-1: 明示 ctx が渡されても increment の条件と副作用は同じ（ctx の generation は supplied value のまま）。
                self._call_proof_generation += 1
            # 6c-1: 明示 ctx があればそれを使う（dual-write 期間。legacy fallback は 6c-2 で閉じる）。
            ctx = branch_context if branch_context is not None else build_branch_check_context(
                strategy=strategy,
                replan_plan=replan_plan,
                call_proof_generation=self._call_proof_generation,
                active_comparison_generation=getattr(self, "_active_comparison_generation", None),
                active_comparison_session_id=getattr(self, "_active_comparison_session_id", None),
                active_call_proof_branch_id=getattr(self, "_active_call_proof_branch_id", None),
                decision_mode=self.call_proof_decision_mode,
                production_branch_authority_lease=getattr(
                    self, "_active_production_branch_authority_lease", None
                ),
            )
            generation = ctx.generation
            comparison_session_id = ctx.comparison_session_id
            branch_id = ctx.branch_id
            decision_mode = ctx.decision_mode
            dispatch_frame = None
            preflight_gate_delta_diagnostic = None

            if decision_mode == CallProofDecisionMode.PREFLIGHT_PROJECTION:
                projection_preparation = prepare_preflight_projection(
                    ctx,
                    analysis1,
                    analysis2,
                    binary1_name,
                    binary2_name,
                    observation_contract_id=self.observation_contract.contract_id,
                    trusted_proof_artifacts=lambda: self._last_internal_call_effect_artifacts,
                    enable_completed_recovery_proofs=self.enable_completed_recovery_proofs,
                    call_effect_shadow_manifest=self._call_effect_shadow_manifest,
                )
                branch_authority = ctx.production_branch_authority_lease
                locally_issued_branch_authority = None
                if (
                    isinstance(strategy, MonolithicStrategy)
                    and branch_authority is None
                ):
                    # Direct checker calls are a compatibility execution domain;
                    # production stage execution supplies the parent lease.
                    # 6b-2: issue_production_branch_authority は呼び出し元を
                    # EquivalenceChecker.check の code object に pin する authority TCB
                    # なので、発行は（projection の後・frame 構築の前という位置のまま）check() に残す。
                    from scripts.function_tracer_pcode.proof.monolithic_authority import (
                        issue_production_branch_authority,
                    )
                    locally_issued_branch_authority = issue_production_branch_authority(
                        comparison_session_id,
                        branch_id,
                        generation,
                        "direct_checker_compatibility_view",
                    )
                    branch_authority = locally_issued_branch_authority
                dispatch_frame = build_prepared_dispatch_frame(
                    ctx,
                    projection_preparation,
                    trusted_proof_artifacts=lambda: self._last_internal_call_effect_artifacts,
                    branch_authority=branch_authority,
                    locally_issued_branch_authority=locally_issued_branch_authority,
                )
                runtime_preparation = prepare_strategy_runtime(
                    getattr(self, "_obligation_runtime_session", None),
                    replan_plan,
                    analysis1,
                    analysis2,
                )
                if runtime_preparation.store_on_facade:
                    # 6b-2: facade write は check() に残す。strategy 実行より前、必要な場合のみ。
                    self._obligation_runtime_session = runtime_preparation.runtime
                outcome = run_strategy_branch(
                    ctx,
                    dispatch_frame,
                    runtime_preparation.runtime,
                    analysis1,
                    analysis2,
                    save_formula,
                    locally_issued_branch_authority=locally_issued_branch_authority,
                    call_effect_shadow_manifest=projection_preparation.call_effect_shadow_manifest,
                    debug_print=self._debug_print,
                    apply_preflight_final_gate=self._apply_preflight_final_gate,
                )
                strategy_result = outcome.strategy_result
                call_effect_shadow_manifest = outcome.call_effect_shadow_manifest
                preflight_gate_delta_diagnostic = outcome.preflight_gate_delta_diagnostic
            else:
                legacy_outcome = run_legacy_strategy(
                    strategy,
                    analysis1,
                    analysis2,
                    binary1_name,
                    binary2_name,
                    save_formula,
                    debug_print=self._debug_print,
                    call_effect_shadow_manifest=self._call_effect_shadow_manifest,
                    apply_phase2_relational_call_discharge=self._apply_phase2_relational_call_discharge,
                )
                strategy_result = legacy_outcome.strategy_result
                call_effect_shadow_manifest = legacy_outcome.call_effect_shadow_manifest
            # 6b-3: C 段（UNKNOWN reason refinement）。順序と各段の受け渡しは段関数内で固定。
            # mixin メソッドは call 時に self から解決する（instance patch seam 維持）。
            refine_unknown_reasons(
                strategy_result,
                analysis1,
                analysis2,
                call_effect_shadow_manifest,
                branch_id=branch_id,
                call_effect_comparison_identity=self._call_effect_comparison_identity,
                attach_recurrence_proposal_blockers=self._attach_recurrence_proposal_blockers,
                specialize_call_effect_unknown_reasons=self._specialize_call_effect_unknown_reasons,
                attach_root_blocker_identities=self._attach_root_blocker_identities,
            )

            # Recurrence is a recovery proof for this already-inconclusive
            # branch, never an alternative surface evaluated before the
            # branch decision.  The pair-local authority names the exact
            # blockers observed above and is intentionally absent from the
            # function-local unary artifact.
            if getattr(self, "_active_recurrence_promotion_authority", None) is None:
                # 6b-4: (1)(2) は段関数、(3) の facade write はその直後・(4) より前に check() が書く。
                promotion = prepare_recurrence_promotion(
                    strategy_result,
                    analysis1,
                    analysis2,
                    comparison_session_id=comparison_session_id,
                    branch_id=branch_id,
                    recurrence_promotion_authority=self._recurrence_promotion_authority,
                )
                if promotion is not None:
                    self._last_recurrence_promotion_attempt = promotion.attempt
                    if complete_recurrence_promotion_signals(
                        promotion.attempt,
                        debug_print=self._debug_print,
                    ):
                        self._obligation_runtime_session = promotion.recurrence_runtime
                        self._active_recurrence_promotion_authority = promotion.authority
                        try:
                            return self.check(
                                promotion.promoted1,
                                promotion.promoted2,
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
            # 6b-5: E・F 段（結果組み立て + 私的付帯 3 つ）は段関数。mixin は call 時に self から解決する。
            return assemble_equivalence_result(
                strategy_result,
                analysis1,
                analysis2,
                binary1_name,
                binary2_name,
                ctx=ctx,
                dispatch_frame=dispatch_frame,
                preflight_gate_delta_diagnostic=preflight_gate_delta_diagnostic,
                call_effect_shadow_manifest=call_effect_shadow_manifest,
                start_time=start_time,
                type_fix_result=type_fix_result,
                retry_count=retry_count,
                original_signature1=original_signature1,
                original_signature2=original_signature2,
                rewrite_info=rewrite_info,
                debug=self.debug,
                deterministic_analysis_identity=self._deterministic_analysis_identity,
                format_counterexample=self._format_counterexample,
                completed_recovery_proof_payload=self._completed_recovery_proof_payload,
                reason_completion_applicability_contexts=self._reason_completion_applicability_contexts,
                recurrence_promotion_result_receipt=self._recurrence_promotion_result_receipt,
            )
        
        except (UnknownSmtExtensionWidthError, UnsupportedSmtOperatorError) as e:
            self._debug_print(
                f"Check blocked by unsupported SMT expression semantics: {e}"
            )
            # 6b-5: handler 本体は段関数（catch scope・handler の種類と順序は check() に残す）。
            return unsupported_smt_result(
                e,
                analysis1=analysis1,
                analysis2=analysis2,
                binary1_name=binary1_name,
                binary2_name=binary2_name,
                start_time=start_time,
                type_fix_result=type_fix_result,
                retry_count=retry_count,
                original_signature1=original_signature1,
                original_signature2=original_signature2,
            )

        except Exception as e:
            self._debug_print(f"Exception in check: {e}")
            if self.debug:
                import traceback
                print(traceback.format_exc())

            from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
                ReturnAbiAuthorityInvalid,
            )
            if isinstance(e, ReturnAbiAuthorityInvalid):
                return canonical_abi_error_result(
                    e,
                    analysis1=analysis1,
                    analysis2=analysis2,
                    binary1_name=binary1_name,
                    binary2_name=binary2_name,
                    start_time=start_time,
                    type_fix_result=type_fix_result,
                    retry_count=retry_count,
                    original_signature1=original_signature1,
                    original_signature2=original_signature2,
                )
            
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
