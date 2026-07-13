# -*- coding: utf-8 -*-
"""Monolithic戦略（全条件を一度に検証）"""

import hashlib
import time

from dataclasses import dataclass
from typing import Optional, Dict, Any, Mapping, Set

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


@dataclass(frozen=True)
class _MonolithicDecisionExecutionContext:
    decision_surface: str
    analysis_object_ids: tuple[int, int]
    prepared_surface_digest: Optional[str] = None

    @classmethod
    def create(
        cls,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        *,
        decision_surface: str,
        prepared_surface_digest: Optional[str] = None,
    ) -> "_MonolithicDecisionExecutionContext":
        if decision_surface not in {"prepared", "legacy_source"}:
            raise ValueError("invalid_monolithic_decision_surface")
        if decision_surface == "prepared" and not prepared_surface_digest:
            raise ValueError("prepared_monolithic_surface_digest_missing")
        if decision_surface == "legacy_source" and prepared_surface_digest is not None:
            raise ValueError("legacy_monolithic_surface_has_prepared_digest")
        return cls(
            decision_surface=decision_surface,
            analysis_object_ids=(id(analysis1), id(analysis2)),
            prepared_surface_digest=prepared_surface_digest,
        )

    def assert_bound_to(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> None:
        if self.analysis_object_ids != (id(analysis1), id(analysis2)):
            raise RuntimeError("monolithic_decision_context_analysis_mismatch")

    @property
    def uses_prepared_surface(self) -> bool:
        return self.decision_surface == "prepared"


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
        decision_context = _MonolithicDecisionExecutionContext.create(
            analysis1,
            analysis2,
            decision_surface="legacy_source",
        )
        return self._counterexample_is_decisive_for_surface(
            analysis1,
            analysis2,
            counterexample_raw,
            decision_context,
        )

    def _counterexample_is_decisive_for_surface(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        counterexample_raw: Optional[Dict[str, Any]],
        decision_context: _MonolithicDecisionExecutionContext,
    ) -> bool:
        decision_context.assert_bound_to(analysis1, analysis2)
        self._last_counterexample_replay_fixed_model_assertion_count = 0
        if not counterexample_raw:
            return True

        normalized1, normalized2 = self._build_validation_analyses_for_surface(
            analysis1,
            analysis2,
            decision_context,
        )
        base_ctx = self.formula_builder.build_base_context(normalized1, normalized2)
        bridge_narrow_bits = self._completed_return_width_bridge_narrow_bits_for_sizes(
            analysis1,
            analysis2,
            base_ctx.get("return_size1"),
            base_ctx.get("return_size2"),
        )
        if bridge_narrow_bits is not None:
            base_ctx["return_width_bridge_narrow_bits"] = bridge_narrow_bits
        self._last_counterexample_replay_fixed_model_assertion_count = (
            count_counterexample_model_assertions(base_ctx, counterexample_raw)
        )
        if decision_context.uses_prepared_surface:
            render_analysis1, render_analysis2 = normalized1, normalized2
        else:
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
            float_mode="fp",
        )
        replace2 = build_symbol_replacer(
            base_ctx["params2"],
            base_ctx.get("extra_vars2", []),
            float_mode="fp",
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

    def _dispatch_counterexample_decisiveness(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        counterexample_raw: Optional[Dict[str, Any]],
        decision_context: _MonolithicDecisionExecutionContext,
    ) -> bool:
        """Preserve the legacy override hook without ambient context reads."""

        validator = self._counterexample_is_decisive_across_case_split
        if getattr(validator, "__func__", None) is MonolithicStrategy._counterexample_is_decisive_across_case_split:
            return self._counterexample_is_decisive_for_surface(
                analysis1,
                analysis2,
                counterexample_raw,
                decision_context,
            )
        return validator(analysis1, analysis2, counterexample_raw)

    def _completed_return_width_bridge_narrow_bits_for_sizes(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        return_size1,
        return_size2,
    ) -> Optional[int]:
        try:
            mismatch = ReturnWidthMismatchError(
                "validation return width mismatch",
                return_size1=int(return_size1),
                return_size2=int(return_size2),
            )
        except (TypeError, ValueError):
            return None
        return self._completed_return_width_bridge_narrow_bits_for_monolithic(
            analysis1,
            analysis2,
            mismatch,
        )

    def _build_validation_analyses(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> tuple[FunctionReturnAnalysis, FunctionReturnAnalysis]:
        decision_context = _MonolithicDecisionExecutionContext.create(
            analysis1,
            analysis2,
            decision_surface="legacy_source",
        )
        return self._build_validation_analyses_for_surface(
            analysis1,
            analysis2,
            decision_context,
        )

    def _build_validation_analyses_for_surface(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        decision_context: _MonolithicDecisionExecutionContext,
    ) -> tuple[FunctionReturnAnalysis, FunctionReturnAnalysis]:
        decision_context.assert_bound_to(analysis1, analysis2)
        if decision_context.uses_prepared_surface:
            # The preflight certificate and comparison receipt are bound to
            # these exact children.  Decision-side validation must not derive
            # an unreceipted normalization/alignment surface.
            return analysis1, analysis2
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
        decision_context: _MonolithicDecisionExecutionContext,
    ) -> list[str]:
        decision_context.assert_bound_to(analysis1, analysis2)
        normalized1, normalized2 = self._build_validation_analyses_for_surface(
            analysis1,
            analysis2,
            decision_context,
        )
        preliminary_cases1 = extract_return_cases(normalized1, self.normalization_settings)
        preliminary_cases2 = extract_return_cases(normalized2, self.normalization_settings)
        if self._return_cases_have_object_centric_total_coverage(
            preliminary_cases1
        ) and self._return_cases_have_object_centric_total_coverage(preliminary_cases2):
            return []

        base_ctx = self.formula_builder.build_base_context(normalized1, normalized2)
        if decision_context.uses_prepared_surface:
            render_analysis1, render_analysis2 = normalized1, normalized2
            assert render_analysis1 is analysis1 and render_analysis2 is analysis2
        else:
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
            float_mode="fp",
        )
        replace2 = build_symbol_replacer(
            base_ctx["params2"],
            base_ctx.get("extra_vars2", []),
            float_mode="fp",
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
        from ..call_effect_preflight import (
            QueryExecutionRecord,
            consume_prepared_dispatch_frame,
            current_dispatch_depth,
            issue_builtin_comparison_receipt,
            lower_call_projection_for_case_pair,
            projection_binding_evidence_from_query,
        )

        source_analysis1 = analysis1
        source_analysis2 = analysis2
        dispatch_frame = None
        if current_dispatch_depth() > 0:
            dispatch_frame = consume_prepared_dispatch_frame(analysis1, analysis2)
            analysis1 = dispatch_frame.prepared.analysis1
            analysis2 = dispatch_frame.prepared.analysis2
        decision_context = _MonolithicDecisionExecutionContext.create(
            analysis1,
            analysis2,
            decision_surface=(
                "prepared" if dispatch_frame is not None else "legacy_source"
            ),
            prepared_surface_digest=(
                dispatch_frame.prepared.surface_digest
                if dispatch_frame is not None
                else None
            ),
        )
        call_projection_assertions = ()
        call_projection_binding_ids = ()
        if dispatch_frame is not None and dispatch_frame.projection.semantic_bindings:
            lowered_call_projection = lower_call_projection_for_case_pair(
                dispatch_frame,
                analysis1,
                analysis2,
                pair_id="monolithic",
            )
            if lowered_call_projection.status != "proven":
                return StrategyResult(
                    is_equivalent=None,
                    solver_results=ParallelResult(results=[]),
                    unknown_reasons=[
                        make_unknown_reason(
                            "equivalence_blocking_unsafety",
                            stage="CALL_EFFECT_PREFLIGHT",
                            evidence_refs=(
                                lowered_call_projection.failure_cause,
                                lowered_call_projection.evidence_digest,
                            ),
                            detail="Certified call projection could not be lowered into the monolithic query.",
                        )
                    ],
                )
            call_projection_assertions = lowered_call_projection.assertions
            call_projection_binding_ids = lowered_call_projection.binding_ids
        
        try:
            # SMT式を構築
            try:
                build_kwargs = {}
                if call_projection_assertions:
                    build_kwargs["extra_assertions"] = list(call_projection_assertions)
                result = self.formula_builder.build_equivalence_formula_extended(
                    analysis1,
                    analysis2,
                    **build_kwargs,
                )
            except ReturnWidthMismatchError as width_mismatch:
                bridge_narrow_bits = (
                    self._completed_return_width_bridge_narrow_bits_for_monolithic(
                        analysis1,
                        analysis2,
                        width_mismatch,
                    )
                )
                if bridge_narrow_bits is None:
                    raise
                self._debug_print(
                    "Monolithic return-width mismatch bridged by completed pairwise "
                    f"proofs at {bridge_narrow_bits} bits"
                )
                bridge_build_kwargs = dict(build_kwargs)
                bridge_build_kwargs["return_width_bridge_narrow_bits"] = bridge_narrow_bits
                result = self.formula_builder.build_equivalence_formula_extended(
                    analysis1,
                    analysis2,
                    **bridge_build_kwargs,
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
                source_analysis1,
                source_analysis2,
            )
            equivalence_blocking_reasons = self._collect_equivalence_blocking_unsafety_reasons(
                source_analysis1,
                source_analysis2,
            )
            if dispatch_frame is not None and dispatch_frame.projection.proven:
                covered_blockers = set(dispatch_frame.projection.covered_blockers)
                equivalence_blocking_reasons = [
                    reason
                    for reason in equivalence_blocking_reasons
                    if reason not in covered_blockers
                ]
            coverage_unsafety_reasons = []
            if final_is_equivalent in {True, False}:
                coverage_unsafety_reasons = self._collect_monolithic_return_coverage_unsafety_reasons(
                    analysis1,
                    analysis2,
                    decision_context,
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
            if final_is_equivalent is False and not self._dispatch_counterexample_decisiveness(
                analysis1,
                analysis2,
                counterexample_raw,
                decision_context,
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
            
            strategy_result = StrategyResult(
                is_equivalent=final_is_equivalent,
                solver_results=parallel_result,
                smt_formula=smt_formula,  # ★ 修正: save_formula の条件を削除（常に保存）
                counterexample_raw=counterexample_raw,
                return_var1=return_var1,
                return_var2=return_var2,
                constrained_fragments=constrained_fragments,
                unknown_reasons=unknown_reasons,
            )
            if dispatch_frame is not None:
                query_digest = hashlib.sha256(
                    smt_formula.encode("utf-8")
                ).hexdigest()
                disposition = (
                    "unsat" if parallel_result.is_equivalent is True
                    else "sat" if parallel_result.is_equivalent is False
                    else "unknown"
                )
                expected_binding_evidence = dict(
                    lowered_call_projection.binding_assertion_digests
                    if call_projection_binding_ids else ()
                )
                actual_call_projection_binding_ids = tuple(sorted(
                    binding_id
                    for binding_id, assertion_digest in (
                        projection_binding_evidence_from_query(smt_formula).items()
                    )
                    if expected_binding_evidence.get(binding_id) == assertion_digest
                ))
                strategy_result.comparison_execution_receipt = issue_builtin_comparison_receipt(
                    dispatch_frame,
                    query_records=(
                        QueryExecutionRecord(
                            query_label="monolithic",
                            premise_digest=query_digest,
                            formula_digest=query_digest,
                            disposition=disposition,
                            proof_kind="monolithic_solver_query",
                            projection_binding_ids=actual_call_projection_binding_ids,
                            formula_text=smt_formula,
                        ),
                    ),
                    consumed_projection_binding_ids=actual_call_projection_binding_ids,
                    disposition_counts={
                        "total": 1,
                        "unsat": 1 if parallel_result.is_equivalent is True else 0,
                        "sat": 1 if parallel_result.is_equivalent is False else 0,
                        "unknown": 1 if parallel_result.is_equivalent is None else 0,
                        "error": 0,
                    },
                )
            return strategy_result
        
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

        except ValueError as e:
            message = str(e)
            if "Unsupported intrinsic for SMT lowering" not in message:
                raise
            self._debug_print(f"Monolithic check blocked by unresolved intrinsic: {message}")
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
                        UnknownReasonId.UNRESOLVED_EXPRESSION,
                        stage="S_MONOLITHIC_FALLBACK",
                        evidence_refs=("unsupported_intrinsic_smt_lowering",),
                        detail=message,
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

    def _completed_return_width_bridge_narrow_bits_for_monolithic(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        mismatch: ReturnWidthMismatchError,
    ) -> Optional[int]:
        try:
            return_size1 = int(getattr(mismatch, "return_size1"))
            return_size2 = int(getattr(mismatch, "return_size2"))
        except (TypeError, ValueError):
            return None
        if return_size1 <= 0 or return_size2 <= 0 or return_size1 == return_size2:
            return None

        narrow_bits = min(return_size1, return_size2)
        if return_size1 > return_size2:
            wide_side_label = "left"
            wide_analysis = analysis1
        else:
            wide_side_label = "right"
            wide_analysis = analysis2
        expected_widths = (return_size1, return_size2)

        required_wide_members = self._monolithic_return_case_members_for_bridge(
            wide_analysis,
        )
        if not required_wide_members:
            return None

        completed_targets = self._completed_return_width_bridge_targets_by_slot(
            analysis1,
            analysis2,
        )
        covered_wide_members: Set[tuple] = set()
        for target, slot_evidence in completed_targets.items():
            if set(slot_evidence) != {"abi_relation", "high_bit_relation"}:
                continue
            if self._return_width_bridge_target_widths(target) != expected_widths:
                continue
            if self._return_width_bridge_target_narrow_width(target) != narrow_bits:
                continue
            wide_side = self._return_width_bridge_find_side(target, wide_side_label)
            if wide_side is None:
                continue
            if (
                self._return_width_bridge_find_tagged_entry(wide_side, "function_ref")
                != self._analysis_entry_key(wide_analysis)
            ):
                continue
            if (
                self._return_width_bridge_find_tagged_entry(wide_side, "return_storage")
                != self._return_storage_object_key(wide_analysis)
            ):
                continue
            member = self._return_width_bridge_find_tagged_entry(
                wide_side,
                "return_case_partition_member",
            )
            if member in required_wide_members:
                covered_wide_members.add(member)
            high_bit_evidence = slot_evidence.get("high_bit_relation")
            if (
                self._evidence_text(high_bit_evidence, "discharge_proof_kind")
                == "semantic_return_width_narrowing_proof"
            ):
                profile = self._evidence_get(
                    self._evidence_get(high_bit_evidence, "proof_content") or {},
                    "wide_surface_profile",
                )
                semantic_members = self._normalize_nested_tuple(
                    self._evidence_get(profile or {}, "required_wide_members")
                )
                if isinstance(semantic_members, tuple):
                    covered_wide_members.update(
                        member
                        for member in semantic_members
                        if member in required_wide_members
                    )

        if required_wide_members.issubset(covered_wide_members):
            return narrow_bits
        return None

    def _monolithic_return_case_members_for_bridge(
        self,
        analysis: FunctionReturnAnalysis,
    ) -> Set[tuple]:
        try:
            cases = extract_return_cases(analysis, self.normalization_settings)
        except Exception:
            return set()
        members: Set[tuple] = set()
        for case in cases:
            return_info = getattr(case, "return_info", None)
            member = self._return_case_partition_member_object_key(case, return_info)
            if member is not None:
                members.add(self._normalize_nested_tuple(member))
        return members

    def _completed_return_width_bridge_targets_by_slot(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> Dict[tuple, Dict[str, Mapping[str, object]]]:
        completed: Dict[tuple, Dict[str, Mapping[str, object]]] = {}
        for evidence in self._completed_recovery_proof_evidence(analysis1, analysis2):
            if self._return_width_bridge_slot_id_from_evidence(evidence) is None:
                continue
            if not self._return_width_bridge_slot_evidence_matches_current_analyses(
                evidence,
                analysis1,
                analysis2,
            ):
                continue
            target = self._normalize_nested_tuple(
                self._evidence_get(evidence, "object_target_key")
            )
            if not self._return_width_bridge_target_is_specific(target):
                continue
            slot_stage = self._evidence_text(evidence, "slot_stage") or self._evidence_text(
                evidence,
                "proof_stage",
            )
            if slot_stage not in {"abi_relation", "high_bit_relation"}:
                continue
            completed.setdefault(target, {})[slot_stage] = evidence
        return completed


from ..call_effect_preflight import _register_builtin_receipt_executor

_register_builtin_receipt_executor("monolithic", MonolithicStrategy.check)
