"""Phase 4 MIPS64 ABI-constrained solver retries."""

from __future__ import annotations

from typing import Optional, Dict, List, Tuple
import time
from scripts.function_tracer_pcode.core import FunctionReturnAnalysis, FunctionSignature
from scripts.function_tracer_pcode.core.render_smt import (
    SMT_SEMANTICS_REFUSALS,
)
from scripts.function_tracer_pcode.smt import ParallelResult
from scripts.function_tracer_pcode.proof.formula.returns import ReturnWidthMismatchError
from scripts.function_tracer_pcode.checker.result import EquivalenceResult
from scripts.function_tracer_pcode.checker.arch.input_extension import produce_final_input_correspondence
from scripts.function_tracer_pcode.checker.phases.handler import PhaseContext
from scripts.function_tracer_pcode.authority.lifecycle.production_boundary import (
    run_check_from_binaries_with_v2_pilot as run_check_from_binaries,
)
from scripts.function_tracer_pcode.checker.unknown_reason import (
    make_internal_v2_reason_diagnostic,
    make_unknown_reason,
)


class AbiRetryMixin:
    """Phase 4 MIPS64 ABI-constrained solver retries."""

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
            analysis1, analysis2 = ctx.analysis1, ctx.analysis2

            # ABI制約セクションを FormulaBuilder に完全委譲
            abi_assertion_section = self.formula_builder.build_abi_assertion_section(
                abi_constraints, "_1", "_2"
            )
            
            # SMT式を構築（ABI制約を extra_assertions として渡す）
            result = self.formula_builder.build_equivalence_formula_extended(
                analysis1, analysis2,
                extra_assertions=abi_assertion_section if abi_assertion_section else None,
                # phase の raw pair から作った最終 relation（builder は作らない）。
                input_correspondence=produce_final_input_correspondence(analysis1, analysis2),
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
                mips64_abi_constraints=abi_constraints,
                # Solver TIMEOUT/UNKNOWN is execution authority, not a
                # semantic UNKNOWN reason.  The v2 finalizer joins its receipt
                # to independently live requirements.
                unknown_reasons=[],
            )
            return equivalence_result

        except SMT_SEMANTICS_REFUSALS as e:
            diagnostic_kind = e.refusal_evidence_ref
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
                            *e.refusal_target_fields(),
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
