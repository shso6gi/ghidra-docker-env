# -*- coding: utf-8 -*-
"""Monolithic戦略（全条件を一度に検証）"""

import time

from typing import Optional, Dict, Any

from ...model import FunctionReturnAnalysis
from ...smt import ParallelResult
from ..formula.symbol_replace import build_symbol_replacer
from ..formula.returns import ReturnWidthMismatchError
from ..normalize import NormalizationSettings
from ..param_semantics import infer_parameter_semantics
from ..semantic_width import align_return_value_extension_surfaces, normalize_analysis_semantic_width
from ..unknown_reason import UnknownReasonId, make_unknown_reason
from .base import CheckStrategy, StrategyResult
from .pairwise_query_builder import extract_return_cases
from .pairwise_query_executor import (
    count_counterexample_model_assertions,
    validate_counterexample_globally,
)


class MonolithicStrategy(CheckStrategy):
    """Monolithic戦略（全条件を一度に検証）"""

    def __init__(
        self,
        formula_builder,
        solver_runner,
        debug: bool = False,
        normalization_settings: Optional[NormalizationSettings] = None,
        enable_completed_recovery_proofs: bool = True,
    ):
        super().__init__(
            formula_builder,
            solver_runner,
            debug,
            enable_completed_recovery_proofs=enable_completed_recovery_proofs,
        )
        self.normalization_settings = normalization_settings or NormalizationSettings.safe()

    def _counterexample_is_decisive_across_case_split(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        counterexample_raw: Optional[Dict[str, Any]],
    ) -> bool:
        self._last_counterexample_replay_fixed_model_assertion_count = 0
        if not counterexample_raw:
            return True

        normalized1, normalized2 = self._build_validation_analyses(analysis1, analysis2)
        base_ctx = self.formula_builder.build_base_context(normalized1, normalized2)
        self._last_counterexample_replay_fixed_model_assertion_count = (
            count_counterexample_model_assertions(base_ctx, counterexample_raw)
        )
        render_analysis1 = normalize_analysis_semantic_width(
            normalized1,
            infer_parameter_semantics(normalized1),
            base_ctx.get("extra_vars1", []),
        )
        render_analysis2 = normalize_analysis_semantic_width(
            normalized2,
            infer_parameter_semantics(normalized2),
            base_ctx.get("extra_vars2", []),
        )

        cases1 = extract_return_cases(render_analysis1, self.normalization_settings)
        cases2 = extract_return_cases(render_analysis2, self.normalization_settings)
        if not cases1 or not cases2:
            self._debug_print(
                "Monolithic SAT counterexample rejected: no return cases available for validation"
            )
            return False

        replace1 = build_symbol_replacer(
            base_ctx["params1"],
            base_ctx.get("extra_vars1", []),
        )
        replace2 = build_symbol_replacer(
            base_ctx["params2"],
            base_ctx.get("extra_vars2", []),
        )
        return validate_counterexample_globally(
            self,
            base_ctx,
            cases1,
            cases2,
            replace1,
            replace2,
            counterexample_raw,
        )

    def _build_validation_analyses(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> tuple[FunctionReturnAnalysis, FunctionReturnAnalysis]:
        hints1 = infer_parameter_semantics(analysis1)
        hints2 = infer_parameter_semantics(analysis2)
        normalized1 = normalize_analysis_semantic_width(analysis1, hints1)
        normalized2 = normalize_analysis_semantic_width(analysis2, hints2)
        return align_return_value_extension_surfaces(
            normalized1,
            normalized2,
        )

    def _collect_monolithic_return_coverage_unsafety_reasons(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> list[str]:
        normalized1, normalized2 = self._build_validation_analyses(analysis1, analysis2)
        preliminary_cases1 = extract_return_cases(normalized1, self.normalization_settings)
        preliminary_cases2 = extract_return_cases(normalized2, self.normalization_settings)
        if self._return_cases_have_object_centric_total_coverage(
            preliminary_cases1
        ) and self._return_cases_have_object_centric_total_coverage(preliminary_cases2):
            return []

        base_ctx = self.formula_builder.build_base_context(normalized1, normalized2)
        render_analysis1 = normalize_analysis_semantic_width(
            normalized1,
            infer_parameter_semantics(normalized1),
            base_ctx.get("extra_vars1", []),
        )
        render_analysis2 = normalize_analysis_semantic_width(
            normalized2,
            infer_parameter_semantics(normalized2),
            base_ctx.get("extra_vars2", []),
        )
        render_analysis1, render_analysis2 = align_return_value_extension_surfaces(
            render_analysis1,
            render_analysis2,
        )
        cases1 = extract_return_cases(render_analysis1, self.normalization_settings)
        cases2 = extract_return_cases(render_analysis2, self.normalization_settings)
        replace1 = build_symbol_replacer(
            base_ctx["params1"],
            base_ctx.get("extra_vars1", []),
        )
        replace2 = build_symbol_replacer(
            base_ctx["params2"],
            base_ctx.get("extra_vars2", []),
        )
        reasons = self._collect_return_coverage_unsafety_reasons(
            base_ctx,
            cases1,
            cases2,
            replace1,
            replace2,
            analysis1,
            analysis2,
        )
        self._record_return_coverage_notes(analysis1, analysis2, reasons)
        return reasons

    def _record_return_coverage_notes(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        reasons: list[str],
    ) -> None:
        for label, analysis in (("function1", analysis1), ("function2", analysis2)):
            if f"{label}:return_coverage_gap" in reasons and "return_case_coverage_gap" not in analysis.analysis_notes:
                analysis.analysis_notes.append("return_case_coverage_gap")
            if (
                f"{label}:return_coverage_inconclusive" in reasons
                and "return_case_coverage_inconclusive" not in analysis.analysis_notes
            ):
                analysis.analysis_notes.append("return_case_coverage_inconclusive")
    
    def check(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        save_formula: bool = False
    ) -> StrategyResult:
        """等価性をチェック（monolithic方式）"""
        start_time = time.time()  # ★ これで使える
        
        try:
            # SMT式を構築
            result = self.formula_builder.build_equivalence_formula_extended(
                analysis1, analysis2
            )
            smt_formula = result.formula
            return_var1 = result.return_var1
            return_var2 = result.return_var2
            constrained_fragments = result.constrained_fragments
            
            if self.debug:
                print("\n" + "=" * 60)
                print("Generated SMT formula (monolithic):")
                print("=" * 60)
                print(smt_formula)
                print("=" * 60 + "\n")
            
            # ソルバーを実行
            if self.debug:
                parallel_result = self.solver_runner.run_sequential(smt_formula)
            else:
                parallel_result = self.solver_runner.run_parallel(smt_formula)
            
            # 反例を取得
            counterexample_raw = None
            if parallel_result.is_equivalent is False:
                counterexample_raw = parallel_result.get_counterexample()

            final_is_equivalent = parallel_result.is_equivalent
            unknown_reasons = []
            sat_unsafety_reasons = self._collect_decisive_sat_unsafety_reasons(
                analysis1,
                analysis2,
            )
            equivalence_blocking_reasons = self._collect_equivalence_blocking_unsafety_reasons(
                analysis1,
                analysis2,
            )
            coverage_unsafety_reasons = []
            if final_is_equivalent in {True, False}:
                coverage_unsafety_reasons = self._collect_monolithic_return_coverage_unsafety_reasons(
                    analysis1,
                    analysis2,
                )
            sat_unsafety_reasons.extend(coverage_unsafety_reasons)
            if final_is_equivalent is True and coverage_unsafety_reasons:
                coverage_unknown_reasons = self._unresolved_return_coverage_unknown_reasons(
                    coverage_unsafety_reasons,
                    analysis1,
                    analysis2,
                    stage="S_MONOLITHIC_FALLBACK",
                )
                if coverage_unknown_reasons:
                    unknown_reasons.extend(coverage_unknown_reasons)
                    self._debug_print(
                        "Monolithic UNSAT downgraded to UNKNOWN due to incomplete return coverage "
                        f"({', '.join(coverage_unsafety_reasons)})"
                    )
                    final_is_equivalent = None
            if final_is_equivalent is True and equivalence_blocking_reasons:
                unresolved_blocking_reasons = self._unresolved_equivalence_blocking_unknown_reasons(
                    equivalence_blocking_reasons,
                    analysis1,
                    analysis2,
                    stage="S_MONOLITHIC_FALLBACK",
                )
                if unresolved_blocking_reasons:
                    unknown_reasons.extend(unresolved_blocking_reasons)
                    self._debug_print(
                        "Monolithic UNSAT downgraded to UNKNOWN due to incomplete effect analysis "
                        f"({', '.join(equivalence_blocking_reasons)})"
                    )
                    final_is_equivalent = None
                else:
                    self._debug_print(
                        "Monolithic UNSAT accepted after completed call-effect summary proof "
                        f"({', '.join(equivalence_blocking_reasons)})"
                    )
            if final_is_equivalent is False and sat_unsafety_reasons:
                sat_unsafety_reason = self._make_sat_unsafety_unknown_reason(
                    sat_unsafety_reasons,
                    analysis1,
                    analysis2,
                    case1=None,
                    case2=None,
                    pair_id="monolithic",
                    stage="S_MONOLITHIC_FALLBACK",
                )
                if not self._sat_unsafety_resolution_proof_is_complete(
                    sat_unsafety_reason,
                    analysis1,
                    analysis2,
                    current_counterexample_raw=counterexample_raw,
                ):
                    unknown_reasons.append(sat_unsafety_reason)
                    self._debug_print(
                        "Monolithic SAT downgraded to UNKNOWN due to unsafe analysis summary "
                        f"({', '.join(sat_unsafety_reasons)})"
                    )
                    final_is_equivalent = None
                    counterexample_raw = None
            if final_is_equivalent is False and not self._counterexample_is_decisive_across_case_split(
                analysis1,
                analysis2,
                counterexample_raw,
            ):
                unknown_reasons.append(
                    self._make_sat_counterexample_ambiguous_unknown_reason(
                        ("monolithic_case_partition_replay",),
                        analysis1,
                        analysis2,
                        case1=None,
                        case2=None,
                        pair_id="monolithic",
                        stage="S_MONOLITHIC_FALLBACK",
                    )
                )
                self._debug_print(
                    "Monolithic SAT downgraded to UNKNOWN after global counterexample validation"
                )
                final_is_equivalent = None
                counterexample_raw = None
            same_function_replay_reasons = ()
            if final_is_equivalent is False:
                same_function_replay_reasons = self._same_function_counterexample_replay_reasons(
                    analysis1,
                    analysis2,
                )
            if final_is_equivalent is False and same_function_replay_reasons:
                sat_replay_reason = self._make_sat_unsafety_unknown_reason(
                    same_function_replay_reasons,
                    analysis1,
                    analysis2,
                    case1=None,
                    case2=None,
                    pair_id="monolithic",
                    stage="S_MONOLITHIC_FALLBACK",
                )
                if not self._sat_unsafety_resolution_proof_is_complete(
                    sat_replay_reason,
                    analysis1,
                    analysis2,
                    current_counterexample_raw=counterexample_raw,
                ):
                    unknown_reasons.append(sat_replay_reason)
                    self._debug_print(
                        "Monolithic SAT downgraded to UNKNOWN until same-function "
                        "counterexample replay is completed"
                    )
                    final_is_equivalent = None
                    counterexample_raw = None
            if final_is_equivalent is None and not unknown_reasons:
                timeout_budget = getattr(self.solver_runner, "timeout", None)
                timeout_target = self._solver_timeout_object_target_key(
                    analysis1=analysis1,
                    analysis2=analysis2,
                    stage="S_MONOLITHIC_FALLBACK",
                    query=smt_formula,
                    timeout_seconds=timeout_budget,
                    parallel_result=parallel_result,
                )
                unknown_reasons.append(
                    make_unknown_reason(
                        UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT,
                        stage="S_MONOLITHIC_FALLBACK",
                        evidence_refs=("monolithic_query_timeout",),
                        evidence_kind="query_hash",
                        object_target_key=timeout_target,
                        detail="monolithic solver query timed out",
                    )
                )
            
            return StrategyResult(
                is_equivalent=final_is_equivalent,
                solver_results=parallel_result,
                smt_formula=smt_formula,  # ★ 修正: save_formula の条件を削除（常に保存）
                counterexample_raw=counterexample_raw,
                return_var1=return_var1,
                return_var2=return_var2,
                constrained_fragments=constrained_fragments,
                unknown_reasons=unknown_reasons,
            )
        
        except ReturnWidthMismatchError as e:
            reason_id = getattr(e, "reason_id", "return_width_bridge_missing")
            self._debug_print(f"Monolithic check blocked: {reason_id}: {e}")
            return StrategyResult(
                is_equivalent=None,
                solver_results=ParallelResult(results=[]),
                smt_formula=None,
                counterexample_raw=None,
                return_var1=None,
                return_var2=None,
                constrained_fragments=[],
                pairwise_debug_stats={reason_id: 1},
                unknown_reasons=[
                    make_unknown_reason(
                        reason_id,
                        stage="S_MONOLITHIC_FALLBACK",
                        evidence_refs=(str(e),),
                        object_target_key=self._return_width_bridge_object_target_key(
                            analysis1=analysis1,
                            analysis2=analysis2,
                            mismatch=e,
                        ),
                        detail=str(e),
                    )
                ],
            )

        except Exception as e:
            self._debug_print(f"Exception in monolithic check: {e}")
            if self.debug:
                import traceback
                print(traceback.format_exc())
            
            return StrategyResult(
                is_equivalent=None,
                solver_results=ParallelResult(results=[]),
                smt_formula=None,
                counterexample_raw=None,
                return_var1=None,
                return_var2=None,
                constrained_fragments=[],
                unknown_reasons=[
                    make_unknown_reason(
                        UnknownReasonId.STRATEGY_EXCEPTION,
                        stage="S_MONOLITHIC_FALLBACK",
                        evidence_refs=(str(e),),
                        detail=str(e),
                    )
                ],
            )
