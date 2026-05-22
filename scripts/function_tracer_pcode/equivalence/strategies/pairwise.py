# -*- coding: utf-8 -*-
"""Pairwise戦略（分岐ペア分割方式・二段階チェック対応）"""

from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Sequence, Tuple
import time

from ...model import (
    COUNTED_LOOP_SUM_OPCODE,
    Condition,
    CountedLoopSummaryRef,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReadonlyReductionRef,
    ReadonlyReductionTermRef,
    StorageInfo,
    compare_loop_summaries,
)
from ...model.runtime_refs import _loop_summary_term_at_index
from ...analysis.effect_summary import canonicalize_location
from ...model.render_smt import (
    collect_intrinsic_smt_declarations,
    expression_contains_unsupported_smt_ops,
    expression_smt_bit_width,
)
from ...analysis.condition.simplifier import ConditionSimplifier
from ...analysis.condition.smt_oracle import ConditionSMTOracle
from ...smt import ParallelResult, SolverResult, SolverStatus
from ...smt.solvers.z3 import Z3Solver
from .base import CheckStrategy, StrategyResult
from .pairwise_models import QueryResult, ReturnCase
from .pairwise_normalization import try_normalization_equivalence
from .pairwise_solver_proven_rewrite import try_solver_proven_rewrite_equivalence
from .pairwise_query_builder import (
    build_condition_only_query,
    build_single_case_condition_query,
    build_normalized_inequality_query,
    build_pair_query,
    extract_return_cases,
    save_unknown_query,
)
from .pairwise_query_executor import (
    solve_query_internal,
    solve_query_twostage,
    validate_counterexample_across_cases,
)
from .expression_safety import ExpressionSafetyChecker
from ..formula.symbol_replace import build_symbol_replacer
from ..formula.types import ParameterInfo
from ..normalize import (
    SignFacts,
    normalize_expression,
    NormalizationContext,
    NormalizationSettings,
    extract_min_excluded_params,
    extract_upper_bound_facts,
    extract_sign_facts,
    normalize_udiv_with_guard,
    contains_udiv,
    are_structurally_equivalent,
    get_structural_summary,
)
from ..param_semantics import (
    infer_parameter_semantics,
    parameter_identity_key_from_descriptor,
    parameter_identity_key_from_expression,
)
from ..semantic_width import (
    align_return_value_extension_surfaces,
    normalize_analysis_semantic_width,
)
from ..debug_trace import NormalizationRuleApplication
from ..unknown_reason import (
    UnknownReasonId,
    make_unknown_reason,
)


@dataclass(frozen=True)
class _RuntimeShortcutDecision:
    equivalent: bool
    requires_guard_equivalence: bool
    reason: str = "unknown"


@dataclass(frozen=True)
class _ExactReadonlyReductionProof:
    """Object proof that an exact load-sum denotes one reduction count."""

    exact_terms: tuple[ReadonlyReductionTermRef, ...]
    constant_bias: int
    result_size: int
    count_value: int
    expected_terms: tuple[ReadonlyReductionTermRef, ...]
    evidence: str


@dataclass(frozen=True)
class _ReadonlyLoopSummaryProofAdapter:
    """Narrow proof adapter for exact-return checks against a loop summary."""

    pointer_base_ref: Any
    count_parameter_name: str
    count_parameter_index: Optional[int]
    count_parameter_storage_identity_key: Optional[Tuple[Any, ...]]
    limit_expr: Any
    result_size: int
    loop_summary: Any

    @property
    def start_index(self) -> int:
        return self._int_constant(getattr(self.loop_summary, "start_expr", None), default=0)

    @property
    def index_step(self) -> int:
        return max(1, self._int_constant(getattr(self.loop_summary, "step_expr", None), default=1))

    @property
    def seed_terms(self) -> Tuple[ReadonlyReductionTermRef, ...]:
        return tuple(getattr(self.loop_summary, "seed_terms", ()) or ())

    @property
    def seed_term_count(self) -> Optional[int]:
        value = getattr(self.loop_summary, "seed_term_count", None)
        try:
            return None if value is None else max(0, int(value))
        except (TypeError, ValueError):
            return None

    @staticmethod
    def _int_constant(value: Any, *, default: int) -> int:
        if isinstance(value, bool):
            return default
        if isinstance(value, int):
            return int(value)
        if getattr(getattr(value, "expr_type", None), "name", None) == "CONSTANT":
            try:
                return int(getattr(value, "value"))
            except (TypeError, ValueError):
                return default
        return default

    def full_terms_for_count_value(self, count_value: int) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        try:
            count = int(count_value)
        except (TypeError, ValueError):
            return None
        if count <= 0:
            return None
        start = self.start_index
        step = self.index_step
        if count < start:
            return None
        terms: List[ReadonlyReductionTermRef] = list(self.seed_terms)
        if any(not isinstance(term, ReadonlyReductionTermRef) for term in terms):
            return None
        if not terms and self.seed_term_count is not None:
            if self.seed_term_count != start:
                return None
            for index in range(start):
                term = _loop_summary_term_at_index(self.loop_summary, index)
                if not isinstance(term, ReadonlyReductionTermRef):
                    return None
                terms.append(term)
        for index in range(start, count, step):
            term = _loop_summary_term_at_index(self.loop_summary, index)
            if not isinstance(term, ReadonlyReductionTermRef):
                return None
            terms.append(term)
        return tuple(terms)


@dataclass(frozen=True)
class _PendingLoopSummaryPair:
    """Pair-local loop-summary proof deferred to the return-partition level."""

    i: int
    j: int
    left_case: ReturnCase
    right_case: ReturnCase
    reason: str


class PairwiseStrategy(CheckStrategy):
    """
    Pairwise戦略（分岐ペア分割方式・二段階チェック）

    各ペア(i,j)に対して：
    1. Stage 1: 条件のみチェック（C1_i ∧ C2_j）
    2. Stage 2: 値不等式を追加してチェック（C1_i ∧ C2_j ∧ V1_i≠V2_j）
    3. Stage 3: 正規化 fallback
    """

    def __init__(
        self,
        formula_builder,
        solver_runner,
        debug: bool = False,
        normalization_settings: Optional[NormalizationSettings] = None,
    ):
        super().__init__(formula_builder, solver_runner, debug)
        self.per_query_timeout = 5
        self.per_query_timeout_hard = 30
        self.save_unknown_queries = False
        self.unknown_query_dir = "/tmp"
        self.normalization_settings = normalization_settings or NormalizationSettings.safe()
        self.solver_proven_rewrite_settings = self.normalization_settings
        self.enable_solver_proven_rewrite_fallback = True
        self.enable_normalization_fallback = False
        self._active_safety_checker = None

    def check(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        save_formula: bool = False
    ) -> StrategyResult:
        start_time = time.time()

        solver_analysis1 = normalize_analysis_semantic_width(
            analysis1,
            infer_parameter_semantics(analysis1),
        )
        solver_analysis2 = normalize_analysis_semantic_width(
            analysis2,
            infer_parameter_semantics(analysis2),
        )
        solver_analysis1, solver_analysis2 = align_return_value_extension_surfaces(
            solver_analysis1,
            solver_analysis2,
        )

        base_ctx = self.formula_builder.build_base_context(
            solver_analysis1,
            solver_analysis2,
        )
        base_ctx["analysis1"] = solver_analysis1
        base_ctx["analysis2"] = solver_analysis2
        safety_checker = ExpressionSafetyChecker(
            solver_runner=self.solver_runner,
            debug_print=self._debug_print,
            per_query_timeout=self.per_query_timeout,
            base_ctx=base_ctx,
        )
        self._active_safety_checker = safety_checker
        sat_unsafety_reasons = self._collect_decisive_sat_unsafety_reasons(
            analysis1,
            analysis2,
        )
        equivalence_blocking_reasons = self._collect_equivalence_blocking_unsafety_reasons(
            analysis1,
            analysis2,
        )

        cases1 = self._extract_return_cases(solver_analysis1)
        cases2 = self._extract_return_cases(solver_analysis2)

        self._rewrite_cases_with_parameter_fragments(cases1, base_ctx.get("extra_vars1", []))
        self._rewrite_cases_with_parameter_fragments(cases2, base_ctx.get("extra_vars2", []))
        symbol_replace_fn1 = build_symbol_replacer(
            base_ctx["params1"],
            base_ctx.get("extra_vars1", []),
        )
        symbol_replace_fn2 = build_symbol_replacer(
            base_ctx["params2"],
            base_ctx.get("extra_vars2", []),
        )

        if self.debug:
            self._debug_symbol_mapping(base_ctx)

        original_case_count1 = len(cases1)
        original_case_count2 = len(cases2)
        cases1 = self._prune_unreachable_cases(
            cases1,
            base_ctx,
            symbol_replace_fn1,
            label="Case1",
        )
        cases2 = self._prune_unreachable_cases(
            cases2,
            base_ctx,
            symbol_replace_fn2,
            label="Case2",
        )
        coverage_unsafety_reasons = self._collect_return_coverage_unsafety_reasons(
            base_ctx,
            cases1,
            cases2,
            symbol_replace_fn1,
            symbol_replace_fn2,
            analysis1,
            analysis2,
        )
        sat_unsafety_reasons.extend(coverage_unsafety_reasons)
        if "function1:return_coverage_gap" in sat_unsafety_reasons:
            if "return_case_coverage_gap" not in analysis1.analysis_notes:
                analysis1.analysis_notes.append("return_case_coverage_gap")
        if "function2:return_coverage_gap" in sat_unsafety_reasons:
            if "return_case_coverage_gap" not in analysis2.analysis_notes:
                analysis2.analysis_notes.append("return_case_coverage_gap")
        if "function1:return_coverage_inconclusive" in sat_unsafety_reasons:
            if "return_case_coverage_inconclusive" not in analysis1.analysis_notes:
                analysis1.analysis_notes.append("return_case_coverage_inconclusive")
        if "function2:return_coverage_inconclusive" in sat_unsafety_reasons:
            if "return_case_coverage_inconclusive" not in analysis2.analysis_notes:
                analysis2.analysis_notes.append("return_case_coverage_inconclusive")
        total_pairs = len(cases1) * len(cases2)

        self._debug_print("=" * 60)
        self._debug_print("Pairwise strategy (two-stage check):")
        self._debug_print(
            f"  Function 1: {len(cases1)} return cases"
            + (
                f" (pruned {original_case_count1 - len(cases1)} unreachable)"
                if len(cases1) != original_case_count1
                else ""
            )
        )
        self._debug_print(
            f"  Function 2: {len(cases2)} return cases"
            + (
                f" (pruned {original_case_count2 - len(cases2)} unreachable)"
                if len(cases2) != original_case_count2
                else ""
            )
        )
        self._debug_print(f"  Total pairs to check: {total_pairs}")
        self._debug_print(f"  Per-query timeout (stage1): {self.per_query_timeout}s")
        self._debug_print(f"  Per-query timeout (stage2 hard): {self.per_query_timeout_hard}s")
        self._debug_print("=" * 60)

        if total_pairs == 0:
            self._debug_print("No return cases to check")
            return self._create_empty_result()

        unsat_count = 0
        sat_count = 0
        unknown_count = 0
        error_count = 0
        sat_pair_info = None
        counterexample_raw = None
        last_formula = None
        resolved_pairs: set[tuple[int, int]] = set()
        pending_loop_summary_pairs: List[_PendingLoopSummaryPair] = []
        all_normalization_rules = []
        normalization_stats = {
            "solver_proven_rewrite_attempts": 0,
            "solver_proven_rewrite_successes": 0,
            "solver_proven_rewrite_failures": 0,
            "timeout_fallback_attempts": 0,
            "changed_pairs": 0,
            "no_change_pairs": 0,
            "unsat_results": 0,
            "sat_results": 0,
            "unknown_results": 0,
            "return_width_bridge_missing": 0,
        }
        unknown_reasons = []
        self._active_normalization_stats = normalization_stats

        for i, case1 in enumerate(cases1):
            for j, case2 in enumerate(cases2):
                pair_id = f"({i},{j})"
                if self._cases_are_contradictory(case1, case2):
                    unsat_count += 1
                    resolved_pairs.add((i, j))
                    if self.debug and (unsat_count % 10 == 0 or unsat_count <= 5):
                        self._debug_print(
                            f"  Pair {pair_id}: CONTRADICTION PRECHECK -> UNSAT ({unsat_count}/{total_pairs})"
                        )
                    continue
                if self._cases_have_equivalent_runtime_reductions(case1, case2):
                    unsat_count += 1
                    resolved_pairs.add((i, j))
                    if self.debug and (unsat_count % 10 == 0 or unsat_count <= 5):
                        self._debug_print(
                            f"  Pair {pair_id}: object-centric runtime summary match -> UNSAT "
                            f"({unsat_count}/{total_pairs})"
                        )
                    continue
                loop_fallback_reason = self._case_pair_loop_summary_safe_fallback_reason(case1, case2)
                if loop_fallback_reason is not None:
                    if self._case_pair_conditions_unsat_under_shared_inputs(
                        base_ctx,
                        case1,
                        case2,
                        symbol_replace_fn1,
                        symbol_replace_fn2,
                        pair_id,
                        loop_fallback_reason,
                    ):
                        unsat_count += 1
                        resolved_pairs.add((i, j))
                        if self.debug and (unsat_count % 10 == 0 or unsat_count <= 5):
                            self._debug_print(
                                f"  Pair {pair_id}: loop fallback conditions unreachable -> UNSAT "
                                f"({unsat_count}/{total_pairs})"
                            )
                        continue
                    if self._case_pair_can_defer_loop_summary_proof(
                        case1,
                        case2,
                        loop_fallback_reason,
                    ):
                        pending_loop_summary_pairs.append(
                            _PendingLoopSummaryPair(i, j, case1, case2, loop_fallback_reason)
                        )
                        self._debug_print(
                            f"  Pair {pair_id}: loop summary proof deferred to aggregate partition "
                            f"({loop_fallback_reason})"
                        )
                        continue
                    unknown_count += 1
                    unknown_reasons.append(
                        make_unknown_reason(
                            self._unknown_reason_id_for_loop_fallback(loop_fallback_reason),
                            stage="S_PAIRWISE",
                            pair_or_case=pair_id,
                            evidence_refs=(loop_fallback_reason,),
                            detail=loop_fallback_reason,
                        )
                    )
                    self._debug_print(
                        f"  Pair {pair_id}: loop summary requires semantic proof "
                        f"({loop_fallback_reason}) -> UNKNOWN"
                    )
                    continue
                if self._case_contains_unresolved_expression(
                    case1,
                    case2.conditions,
                    own_render_fn=symbol_replace_fn1,
                    extra_render_fn=symbol_replace_fn2,
                    base_ctx=base_ctx,
                    query_label=f"{pair_id}:case1",
                ) or self._case_contains_unresolved_expression(
                    case2,
                    case1.conditions,
                    own_render_fn=symbol_replace_fn2,
                    extra_render_fn=symbol_replace_fn1,
                    base_ctx=base_ctx,
                    query_label=f"{pair_id}:case2",
                ):
                    unknown_count += 1
                    unknown_reasons.append(
                        make_unknown_reason(
                            UnknownReasonId.UNRESOLVED_EXPRESSION,
                            stage="S_PAIRWISE",
                            pair_or_case=pair_id,
                            evidence_refs=(f"{pair_id}:case1", f"{pair_id}:case2"),
                        )
                    )
                    self._debug_print(
                        f"  Pair {pair_id}: unresolved expression detected -> UNKNOWN"
                    )
                    continue

                result = self._solve_query_twostage(
                    base_ctx,
                    case1,
                    case2,
                    symbol_replace_fn1,
                    symbol_replace_fn2,
                    pair_id,
                )

                if result.last_query:
                    last_formula = result.last_query
                if result.normalization_rules:
                    all_normalization_rules.extend(result.normalization_rules)

                if result.is_equivalent is False:
                    if sat_unsafety_reasons:
                        unknown_count += 1
                        unknown_reasons.append(
                            make_unknown_reason(
                                UnknownReasonId.SAT_UNSAFETY,
                                stage="S_PAIRWISE",
                                pair_or_case=pair_id,
                                evidence_refs=tuple(sat_unsafety_reasons),
                                detail=", ".join(sat_unsafety_reasons),
                            )
                        )
                        self._debug_print(
                            "  Pair "
                            f"{pair_id}: SAT downgraded to UNKNOWN due to unsafe analysis "
                            f"summary ({', '.join(sat_unsafety_reasons)})"
                        )
                        continue

                    is_decisive = validate_counterexample_across_cases(
                        self,
                        base_ctx,
                        cases1,
                        cases2,
                        symbol_replace_fn1,
                        symbol_replace_fn2,
                        (i, j),
                        result.counterexample_raw,
                    )
                    if not is_decisive:
                        unknown_count += 1
                        unknown_reasons.append(
                            make_unknown_reason(
                                UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS,
                                stage="S_PAIRWISE",
                                pair_or_case=pair_id,
                                evidence_refs=(result.pair_stage or "unknown",),
                            )
                        )
                        self._debug_print(
                            f"  Pair {pair_id}: SAT counterexample was ambiguous -> downgraded to UNKNOWN"
                        )
                        continue

                    sat_count += 1
                    sat_pair_info = {
                        "i": i,
                        "j": j,
                        "case1_summary": case1.get_condition_summary(),
                        "case2_summary": case2.get_condition_summary(),
                        "value1": case1.get_value_smt(symbol_replace_fn1),
                        "value2": case2.get_value_smt(symbol_replace_fn2),
                        "pair_stage": result.pair_stage or "unknown",
                        "final_query": result.last_query,
                    }
                    counterexample_raw = result.counterexample_raw

                    self._debug_print(f"  Pair {pair_id}: SAT (NOT EQUIVALENT) - stopping")
                    self._debug_print(f"    Case1[{i}]: {sat_pair_info['case1_summary']}")
                    self._debug_print(f"    Case2[{j}]: {sat_pair_info['case2_summary']}")
                    self._debug_print(f"    Value1: {sat_pair_info['value1'][:60]}...")
                    self._debug_print(f"    Value2: {sat_pair_info['value2'][:60]}...")
                    break

                if result.is_equivalent is True:
                    unsat_count += 1
                    resolved_pairs.add((i, j))
                    if self.debug and (unsat_count % 10 == 0 or unsat_count <= 5):
                        self._debug_print(f"  Pair {pair_id}: UNSAT ({unsat_count}/{total_pairs})")
                    continue

                unknown_count += 1
                unknown_reasons.append(
                    make_unknown_reason(
                        result.blocking_reason or UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT,
                        stage="S_PAIRWISE",
                        pair_or_case=pair_id,
                        evidence_refs=(result.pair_stage or "unknown", result.blocking_detail),
                        object_target_key=getattr(result, "object_target_key", None),
                        proof_obligation_id=getattr(result, "proof_obligation_id", None),
                        detail=result.blocking_detail,
                    )
                )
                self._debug_print(f"  Pair {pair_id}: final result UNKNOWN/TIMEOUT")

            if sat_count > 0:
                break

        if sat_count == 0 and pending_loop_summary_pairs:
            resolved_pending = self._resolve_pending_loop_summary_pairs_with_partition_proof(
                pending_loop_summary_pairs,
                cases1,
                cases2,
                resolved_pairs,
            )
            for pending in pending_loop_summary_pairs:
                pair_id = f"({pending.i},{pending.j})"
                if (pending.i, pending.j) in resolved_pending:
                    unsat_count += 1
                    resolved_pairs.add((pending.i, pending.j))
                    self._debug_print(
                        f"  Pair {pair_id}: aggregate return-partition proof -> UNSAT"
                    )
                else:
                    unknown_count += 1
                    unknown_reasons.append(
                        make_unknown_reason(
                            self._unknown_reason_id_for_loop_fallback(pending.reason),
                            stage="S_PAIRWISE",
                            pair_or_case=pair_id,
                            evidence_refs=(pending.reason,),
                            detail=pending.reason,
                        )
                    )
                    self._debug_print(
                        f"  Pair {pair_id}: loop summary requires semantic proof "
                        f"({pending.reason}) -> UNKNOWN"
                    )

        elapsed_time = time.time() - start_time
        if sat_count > 0:
            final_is_equiv = False
            self._debug_print("=" * 60)
            self._debug_print("Result: NOT EQUIVALENT (found SAT pair)")
        elif unknown_count > 0:
            final_is_equiv = None
            self._debug_print("=" * 60)
            self._debug_print(f"Result: UNKNOWN (timeout/unknown in {unknown_count} pairs)")
        elif coverage_unsafety_reasons or equivalence_blocking_reasons:
            self._debug_print("=" * 60)
            coverage_unknown_reasons = self._unresolved_return_coverage_unknown_reasons(
                coverage_unsafety_reasons,
                analysis1,
                analysis2,
                stage="S_PAIRWISE",
            )
            unresolved_equivalence_blocking_reasons = self._unresolved_equivalence_blocking_unknown_reasons(
                equivalence_blocking_reasons,
                analysis1,
                analysis2,
                stage="S_PAIRWISE",
            )
            if coverage_unknown_reasons or unresolved_equivalence_blocking_reasons:
                final_is_equiv = None
                unknown_reasons.extend(coverage_unknown_reasons)
                unknown_reasons.extend(unresolved_equivalence_blocking_reasons)
                blocking_reasons = coverage_unsafety_reasons + equivalence_blocking_reasons
                self._debug_print(
                    "Result: UNKNOWN (equivalence proof is blocked by incomplete analysis: "
                    f"{', '.join(blocking_reasons)})"
                )
            else:
                final_is_equiv = True
                self._debug_print(
                    "Result: EQUIVALENT (all pairs UNSAT; recovery proof complete)"
                )
        elif unsat_count == total_pairs:
            final_is_equiv = True
            self._debug_print("=" * 60)
            self._debug_print("Result: EQUIVALENT (all pairs UNSAT)")
        else:
            final_is_equiv = None
            error_count = total_pairs - unsat_count - sat_count - unknown_count
            unknown_reasons.append(
                make_unknown_reason(
                    UnknownReasonId.UNEXPECTED_PAIRWISE_STATE,
                    stage="S_PAIRWISE",
                    evidence_refs=(f"errors={error_count}",),
                )
            )
            self._debug_print("=" * 60)
            self._debug_print(f"Result: UNKNOWN (unexpected state, errors={error_count})")

        self._debug_print(f"  Total pairs: {total_pairs}")
        self._debug_print(
            f"  UNSAT: {unsat_count}, SAT: {sat_count}, UNKNOWN: {unknown_count}, ERROR: {error_count}"
        )
        self._debug_print(f"  Total time: {elapsed_time:.3f}s")
        self._debug_print("=" * 60)

        aggregate_result = self._create_aggregate_result(
            final_is_equiv,
            elapsed_time,
            counterexample_raw,
        )

        try:
            return StrategyResult(
                is_equivalent=final_is_equiv,
                solver_results=aggregate_result,
                smt_formula=last_formula,
                counterexample_raw=counterexample_raw,
                return_var1="return_1",
                return_var2="return_2",
                constrained_fragments=base_ctx.get("constrained_fragments", []),
                total_pairs=total_pairs,
                unsat_pairs=unsat_count,
                sat_pairs=sat_count,
                unknown_pairs=unknown_count,
                error_pairs=error_count,
                sat_pair_info=sat_pair_info,
                normalization_rules=all_normalization_rules,
                pairwise_debug_stats=normalization_stats,
                unknown_reasons=unknown_reasons,
            )
        finally:
            self._active_safety_checker = None
            self._active_normalization_stats = None

    def _unknown_reason_id_for_loop_fallback(self, reason: Optional[str]):
        reason_text = str(reason or "")
        if reason_text.startswith("readonly_contract_"):
            return UnknownReasonId.READONLY_IDENTITY_MISSING
        if reason_text in {
            "semantic_key_missing",
            "semantic_key_unavailable",
            "semantic_key_none",
            "semantic_key_mismatch",
        }:
            return UnknownReasonId.READONLY_IDENTITY_MISSING
        if reason_text in {
            "loop_summary_guard_mismatch",
            "loop_summary_shape_mismatch",
            "loop_summary_unproven",
            "loop_summary_unknown",
            "loop_summary_operand_mismatch",
            "loop_summary_intrinsic_mismatch",
        }:
            return UnknownReasonId.METHOD_B_CLOSURE_BLOCKED
        return UnknownReasonId.LOOP_SUMMARY_PROOF_MISSING

    def _case_pair_conditions_unsat_under_shared_inputs(
        self,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        param_replace_fn1,
        param_replace_fn2,
        pair_id: str,
        loop_fallback_reason: Optional[str],
    ) -> bool:
        if loop_fallback_reason != "loop_summary_shape_mismatch":
            return False
        if not case1.conditions or not case2.conditions:
            return False
        query = self._build_condition_only_query(
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            pair_id,
        )
        result = Z3Solver(timeout=1, debug=False).check_equivalence_direct(query)
        return result.status == SolverStatus.UNSAT

    def _solve_query_twostage(
        self,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        param_replace_fn1,
        param_replace_fn2,
        pair_id: str
    ) -> QueryResult:
        return solve_query_twostage(
            self,
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            pair_id,
        )

    def _cases_have_equivalent_runtime_reductions(
        self,
        case1: ReturnCase,
        case2: ReturnCase,
    ) -> bool:
        if self._intrinsic_runtime_values_equivalent(
            case1.value_expr,
            case2.value_expr,
            left_case=case1,
            right_case=case2,
        ):
            return True
        return self._cases_have_equivalent_readonly_reduction_proof(case1, case2)

    def _cases_have_equivalent_readonly_reduction_proof(
        self,
        case1: ReturnCase,
        case2: ReturnCase,
    ) -> bool:
        return (
            self._exact_value_matches_readonly_reduction_proof(case1, case2)
            or self._exact_value_matches_readonly_reduction_proof(case2, case1)
        )

    def _exact_value_matches_readonly_reduction_proof(
        self,
        exact_case: ReturnCase,
        summary_case: ReturnCase,
    ) -> bool:
        return self._prove_exact_load_sum_matches_readonly_reduction(exact_case, summary_case) is not None

    def _prove_exact_load_sum_matches_readonly_reduction(
        self,
        exact_case: ReturnCase,
        summary_case: ReturnCase,
    ) -> Optional[_ExactReadonlyReductionProof]:
        summary_expr = summary_case.value_expr
        summary_ref = getattr(summary_expr, "runtime_ref", None)
        if not isinstance(summary_ref, ReadonlyReductionRef):
            return None
        accumulator_proof = getattr(summary_ref, "accumulator_proof", None)
        if accumulator_proof is None:
            return self._prove_exact_load_sum_matches_readonly_loop_summary(
                exact_case,
                summary_case,
                summary_ref,
            )
        if getattr(summary_ref, "loop_summary", None) is None:
            return None
        result_size = max(1, int(getattr(accumulator_proof, "result_size", 0) or 0))
        if max(1, int(getattr(summary_ref, "result_size", 0) or 0)) != result_size:
            return None
        if self._normalize_constant_bias(
            int(getattr(summary_ref, "constant_bias", 0) or 0),
            result_size,
        ) != self._normalize_constant_bias(
            int(getattr(accumulator_proof, "constant_bias", 0) or 0),
            result_size,
        ):
            return None
        extracted = self._extract_readonly_reduction_terms_and_bias_from_expression(
            exact_case.value_expr,
            exact_case.parameters,
            getattr(accumulator_proof, "pointer_base_ref", None),
            program_is_big_endian=getattr(exact_case, "program_is_big_endian", None),
        )
        if extracted is None:
            return None
        extracted_terms, extracted_bias = extracted
        exact_bits = int(expression_smt_bit_width(exact_case.value_expr) or 0)
        if exact_bits != result_size * 8:
            return None
        if self._normalize_constant_bias(extracted_bias, result_size) != self._normalize_constant_bias(
            int(getattr(accumulator_proof, "constant_bias", 0) or 0),
            result_size,
        ):
            return None
        extracted_key = tuple(term.stable_key() for term in extracted_terms)
        exact_witnesses = tuple(getattr(accumulator_proof, "exact_return_witnesses", ()) or ())
        for witness in exact_witnesses:
            if extracted_key != tuple(term.stable_key() for term in getattr(witness, "terms", ()) or ()):
                continue
            if self._cases_admit_reduction_count(
                exact_case,
                summary_case,
                accumulator_proof,
                int(getattr(witness, "exact_count", 0) or 0),
            ):
                count_value = int(getattr(witness, "exact_count", 0) or 0)
                return _ExactReadonlyReductionProof(
                    exact_terms=tuple(extracted_terms),
                    constant_bias=self._normalize_constant_bias(extracted_bias, result_size),
                    result_size=result_size,
                    count_value=count_value,
                    expected_terms=tuple(getattr(witness, "terms", ()) or ()),
                    evidence="exact_return_witness",
                )
        return self._exact_terms_match_reduction_proof_under_case_conditions(
            exact_case,
            summary_case,
            accumulator_proof,
            extracted_key,
            exact_terms=tuple(extracted_terms),
            constant_bias=self._normalize_constant_bias(extracted_bias, result_size),
            result_size=result_size,
        )

    def _prove_exact_load_sum_matches_readonly_loop_summary(
        self,
        exact_case: ReturnCase,
        summary_case: ReturnCase,
        summary_ref: ReadonlyReductionRef,
    ) -> Optional[_ExactReadonlyReductionProof]:
        loop_summary = getattr(summary_ref, "loop_summary", None)
        if loop_summary is None:
            return None
        requires_effect_proof = getattr(loop_summary, "requires_effect_proof", None)
        if callable(requires_effect_proof) and requires_effect_proof():
            return None
        requires_path_proof = getattr(loop_summary, "requires_path_proof", None)
        if callable(requires_path_proof) and requires_path_proof():
            return None
        result_size = max(1, int(getattr(summary_ref, "result_size", 0) or 0))
        term_descriptor = getattr(loop_summary, "term_descriptor", None)
        if term_descriptor is None:
            return None
        if max(1, int(getattr(term_descriptor, "result_size", 0) or result_size)) != result_size:
            return None
        if self._normalize_constant_bias(
            int(getattr(summary_ref, "constant_bias", 0) or 0),
            result_size,
        ) != self._normalize_constant_bias(
            int(getattr(loop_summary, "constant_bias", 0) or 0),
            result_size,
        ):
            return None
        extracted = self._extract_readonly_reduction_terms_and_bias_from_expression(
            exact_case.value_expr,
            exact_case.parameters,
            getattr(summary_ref, "pointer_base_ref", None),
            program_is_big_endian=getattr(exact_case, "program_is_big_endian", None),
        )
        if extracted is None:
            return None
        extracted_terms, extracted_bias = extracted
        exact_bits = int(expression_smt_bit_width(exact_case.value_expr) or 0)
        if exact_bits != result_size * 8:
            return None
        if self._normalize_constant_bias(extracted_bias, result_size) != self._normalize_constant_bias(
            int(getattr(loop_summary, "constant_bias", 0) or 0),
            result_size,
        ):
            return None
        adapter = _ReadonlyLoopSummaryProofAdapter(
            pointer_base_ref=getattr(summary_ref, "pointer_base_ref", None),
            count_parameter_name=str(getattr(summary_ref, "count_parameter_name", None) or "count"),
            count_parameter_index=getattr(summary_ref, "count_parameter_index", None),
            count_parameter_storage_identity_key=getattr(
                summary_ref,
                "count_parameter_storage_identity_key",
                None,
            ),
            limit_expr=getattr(loop_summary, "limit_expr", None),
            result_size=result_size,
            loop_summary=loop_summary,
        )
        extracted_key = tuple(term.stable_key() for term in extracted_terms)
        max_count = self._exact_reduction_count_search_bound(adapter, len(extracted_terms))
        for count_value in range(1, max_count + 1):
            expected_terms = adapter.full_terms_for_count_value(count_value)
            if expected_terms is None:
                continue
            if extracted_key != tuple(term.stable_key() for term in expected_terms):
                continue
            if self._cases_admit_reduction_count(
                exact_case,
                summary_case,
                adapter,
                count_value,
            ):
                return _ExactReadonlyReductionProof(
                    exact_terms=tuple(extracted_terms),
                    constant_bias=self._normalize_constant_bias(extracted_bias, result_size),
                    result_size=result_size,
                    count_value=int(count_value),
                    expected_terms=tuple(expected_terms),
                    evidence="loop_summary_materialized_terms",
                )
        return None

    def _exact_terms_match_reduction_proof_under_case_conditions(
        self,
        exact_case: ReturnCase,
        summary_case: ReturnCase,
        accumulator_proof,
        extracted_key: tuple,
        *,
        exact_terms: tuple[ReadonlyReductionTermRef, ...],
        constant_bias: int,
        result_size: int,
    ) -> Optional[_ExactReadonlyReductionProof]:
        max_count = self._exact_reduction_count_search_bound(accumulator_proof, len(exact_terms))
        for count_value in range(1, max_count + 1):
            expected_terms_fn = getattr(accumulator_proof, "full_terms_for_count_value", None)
            if not callable(expected_terms_fn):
                return None
            expected_terms = expected_terms_fn(count_value)
            if expected_terms is None:
                continue
            if extracted_key != tuple(term.stable_key() for term in expected_terms):
                continue
            if self._cases_admit_reduction_count(
                exact_case,
                summary_case,
                accumulator_proof,
                count_value,
            ):
                return _ExactReadonlyReductionProof(
                    exact_terms=tuple(exact_terms),
                    constant_bias=int(constant_bias),
                    result_size=int(result_size),
                    count_value=int(count_value),
                    expected_terms=tuple(expected_terms),
                    evidence="materialized_full_terms",
                )
        return None

    def _exact_reduction_count_search_bound(self, accumulator_proof, exact_term_count: int) -> int:
        witness_counts = [
            int(getattr(witness, "exact_count", 0) or 0)
            for witness in tuple(getattr(accumulator_proof, "loop_body_witnesses", ()) or ())
        ] + [
            int(getattr(witness, "exact_count", 0) or 0)
            for witness in tuple(getattr(accumulator_proof, "exact_return_witnesses", ()) or ())
        ]
        start_index = max(0, int(getattr(accumulator_proof, "start_index", 0) or 0))
        index_step = max(1, int(getattr(accumulator_proof, "index_step", 1) or 1))
        seed_count = max(
            len(tuple(getattr(accumulator_proof, "seed_terms", ()) or ())),
            max(0, int(getattr(accumulator_proof, "seed_term_count", 0) or 0)),
        )
        term_budget = max(1, int(exact_term_count or 0) + seed_count + 1)
        materialization_bound = start_index + term_budget * index_step + 1
        return max(1, materialization_bound, *witness_counts)

    def _intrinsic_runtime_values_equivalent(
        self,
        left: Expression,
        right: Expression,
        *,
        left_case: Optional[ReturnCase] = None,
        right_case: Optional[ReturnCase] = None,
    ) -> bool:
        if left is None or right is None:
            return False
        if left.expr_type != ExpressionType.INTRINSIC or right.expr_type != ExpressionType.INTRINSIC:
            return False
        left_ref = getattr(left, "runtime_ref", None)
        right_ref = getattr(right, "runtime_ref", None)
        comparison_result_size = self._case_pair_comparison_result_size(left_case, right_case)
        loop_contract_decision = self._runtime_loop_contract_shortcut_decision(
            left_ref,
            right_ref,
            result_size=comparison_result_size,
        )
        if loop_contract_decision.equivalent:
            if loop_contract_decision.requires_guard_equivalence and (
                left_case is None
                or right_case is None
                or not self._case_pair_has_runtime_guard_coverage_or_equivalence(left_case, right_case)
            ):
                return False
            return True
        if getattr(left, "opcode", None) != getattr(right, "opcode", None):
            return False
        if (getattr(left, "name", None) or "") != (getattr(right, "name", None) or ""):
            return False
        shortcut_decision = self._runtime_refs_shortcut_decision(
            left_ref,
            right_ref,
            result_size=comparison_result_size,
        )
        if not shortcut_decision.equivalent:
            if self._counted_loop_values_are_provably_equivalent(
                left,
                right,
                left_case=left_case,
                right_case=right_case,
            ):
                return True
            return False
        if shortcut_decision.requires_guard_equivalence and (
            left_case is None
            or right_case is None
            or not self._case_pair_has_runtime_guard_coverage_or_equivalence(left_case, right_case)
        ):
            return False
        if len(left.operands) != len(right.operands):
            return False
        return all(
            self._expressions_share_object_centric_structure(left_operand, right_operand)
            for left_operand, right_operand in zip(left.operands, right.operands)
        )

    def _runtime_refs_share_shortcut_semantics(self, left_ref, right_ref) -> tuple[bool, bool]:
        decision = self._runtime_refs_shortcut_decision(left_ref, right_ref)
        return decision.equivalent, decision.requires_guard_equivalence

    def _runtime_refs_shortcut_decision(
        self,
        left_ref,
        right_ref,
        *,
        result_size: Optional[int] = None,
    ) -> _RuntimeShortcutDecision:
        if left_ref is None or right_ref is None:
            return _RuntimeShortcutDecision(False, False, reason="missing_runtime_ref")

        left_loop_summary = getattr(left_ref, "loop_summary", None)
        right_loop_summary = getattr(right_ref, "loop_summary", None)
        if left_loop_summary is not None or right_loop_summary is not None:
            if isinstance(left_ref, ReadonlyReductionRef) and isinstance(right_ref, ReadonlyReductionRef):
                exact_readonly_decision = self._runtime_refs_exact_shortcut_decision(
                    left_ref,
                    right_ref,
                    requires_guard_equivalence=(
                        self._runtime_ref_has_guard_constraints(left_ref)
                        or self._runtime_ref_has_guard_constraints(right_ref)
                    ),
                )
                if exact_readonly_decision.equivalent:
                    return exact_readonly_decision
            readonly_decision = self._readonly_reduction_contract_shortcut_decision(
                left_ref,
                right_ref,
                requires_guard_equivalence=True,
                result_size=result_size,
            )
            if readonly_decision.equivalent:
                return readonly_decision
            if readonly_decision.reason in {
                "readonly_contract_type_mismatch",
                "readonly_contract_result_width_mismatch",
                "readonly_contract_mismatch",
            }:
                return readonly_decision
            loop_result = compare_loop_summaries(left_loop_summary, right_loop_summary)
            decisive = loop_result.is_equivalent()
            if decisive is not None:
                return _RuntimeShortcutDecision(
                    bool(decisive),
                    True,
                    reason=f"loop_summary_{loop_result.status}",
                )
            if loop_result.blocks_shortcut():
                return _RuntimeShortcutDecision(
                    False,
                    True,
                    reason=f"loop_summary_{loop_result.status}",
                )
            exact_decision = self._runtime_refs_exact_shortcut_decision(
                left_ref,
                right_ref,
                requires_guard_equivalence=True,
            )
            if exact_decision.equivalent:
                return exact_decision
            semantic_decision = self._runtime_refs_semantic_shortcut_decision(left_ref, right_ref)
            if semantic_decision.equivalent:
                return _RuntimeShortcutDecision(
                    True,
                    True,
                    reason=semantic_decision.reason,
                )
            return _RuntimeShortcutDecision(
                False,
                True,
                reason="loop_summary_unproven",
            )

        exact_decision = self._runtime_refs_exact_shortcut_decision(
            left_ref,
            right_ref,
            requires_guard_equivalence=self._runtime_refs_require_guard_equivalence(left_ref, right_ref),
        )
        if exact_decision.equivalent:
            return exact_decision

        semantic_decision = self._runtime_refs_semantic_shortcut_decision(left_ref, right_ref)
        if semantic_decision.equivalent:
            return semantic_decision
        return _RuntimeShortcutDecision(False, False, reason="no_shortcut")

    def _runtime_loop_contract_shortcut_decision(
        self,
        left_ref,
        right_ref,
        *,
        result_size: Optional[int] = None,
    ) -> _RuntimeShortcutDecision:
        left_loop_summary = getattr(left_ref, "loop_summary", None)
        right_loop_summary = getattr(right_ref, "loop_summary", None)
        if left_loop_summary is None and right_loop_summary is None:
            return _RuntimeShortcutDecision(False, False, reason="not_loop_contract")
        return self._runtime_refs_shortcut_decision(left_ref, right_ref, result_size=result_size)

    def _runtime_refs_require_guard_equivalence(self, left_ref, right_ref) -> bool:
        left_guard_fn = getattr(left_ref, "pairwise_requires_guard_equivalence", None)
        right_guard_fn = getattr(right_ref, "pairwise_requires_guard_equivalence", None)
        return bool(callable(left_guard_fn) and left_guard_fn()) or bool(
            callable(right_guard_fn) and right_guard_fn()
        )

    def _runtime_ref_has_guard_constraints(self, runtime_ref) -> bool:
        for owner in (
            runtime_ref,
            getattr(runtime_ref, "accumulator_proof", None),
            getattr(runtime_ref, "loop_summary", None),
        ):
            if tuple(getattr(owner, "guard_constraints", ()) or ()):
                return True
        return False

    def _case_pair_comparison_result_size(
        self,
        left_case: Optional[ReturnCase],
        right_case: Optional[ReturnCase],
    ) -> Optional[int]:
        left_bits = self._case_comparison_bit_width(left_case)
        right_bits = self._case_comparison_bit_width(right_case)
        if left_bits is None or right_bits is None:
            return None
        if left_bits <= 0 or right_bits <= 0 or left_bits % 8 != 0 or right_bits % 8 != 0:
            return None
        if left_bits == right_bits:
            return left_bits // 8
        return None

    def _case_comparison_bit_width(self, case: Optional[ReturnCase]) -> Optional[int]:
        if case is None:
            return None
        surface = getattr(case, "comparison_surface", None)
        bits = getattr(surface, "explicit_bit_width", None)
        try:
            if bits is not None and int(bits) > 0:
                return int(bits)
        except (TypeError, ValueError):
            return None
        return None

    def _runtime_refs_exact_shortcut_decision(
        self,
        left_ref,
        right_ref,
        *,
        requires_guard_equivalence: bool,
    ) -> _RuntimeShortcutDecision:
        left_exact_key_fn = getattr(left_ref, "pairwise_exact_key", None)
        right_exact_key_fn = getattr(right_ref, "pairwise_exact_key", None)
        if callable(left_exact_key_fn) and callable(right_exact_key_fn):
            try:
                left_exact_key = left_exact_key_fn()
                right_exact_key = right_exact_key_fn()
                if left_exact_key is not None and right_exact_key is not None and left_exact_key == right_exact_key:
                    return _RuntimeShortcutDecision(
                        True,
                        requires_guard_equivalence,
                        reason="exact_runtime_key",
                    )
            except (AttributeError, TypeError, ValueError):
                return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="exact_key_unavailable")
        return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="exact_key_mismatch")

    def _readonly_reduction_contract_shortcut_decision(
        self,
        left_ref,
        right_ref,
        *,
        requires_guard_equivalence: bool,
        result_size: Optional[int] = None,
    ) -> _RuntimeShortcutDecision:
        if not isinstance(left_ref, ReadonlyReductionRef) or not isinstance(right_ref, ReadonlyReductionRef):
            return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="readonly_contract_type_mismatch")
        if getattr(left_ref, "loop_summary", None) is None or getattr(right_ref, "loop_summary", None) is None:
            return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="readonly_contract_missing_loop")
        left_loop_summary = getattr(left_ref, "loop_summary", None)
        right_loop_summary = getattr(right_ref, "loop_summary", None)
        left_profile = getattr(left_loop_summary, "side_effect_profile", None)
        right_profile = getattr(right_loop_summary, "side_effect_profile", None)
        if left_profile is None or right_profile is None:
            return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="readonly_contract_missing_effect_profile")
        if bool(getattr(left_loop_summary, "requires_effect_proof", lambda: True)()) or bool(
            getattr(right_loop_summary, "requires_effect_proof", lambda: True)()
        ):
            return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="readonly_contract_effects_unproven")

        left_base_key = getattr(getattr(left_ref, "pointer_base_ref", None), "semantic_key", lambda: None)()
        right_base_key = getattr(getattr(right_ref, "pointer_base_ref", None), "semantic_key", lambda: None)()
        effective_result_size = self._readonly_contract_effective_result_size(
            left_ref,
            right_ref,
            result_size=result_size,
        )
        if effective_result_size is None:
            return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="readonly_contract_result_width_mismatch")
        if (
            getattr(left_ref, "reduction_kind", None) != getattr(right_ref, "reduction_kind", None)
            or left_base_key is None
            or right_base_key is None
            or left_base_key != right_base_key
            or not self._readonly_count_identities_compatible(left_ref, right_ref)
            or self._normalize_constant_bias(int(getattr(left_ref, "constant_bias", 0) or 0), effective_result_size)
            != self._normalize_constant_bias(int(getattr(right_ref, "constant_bias", 0) or 0), effective_result_size)
        ):
            return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="readonly_contract_mismatch")
        left_semantic_key = self._readonly_reduction_term_sequence_contract_key(
            left_ref,
            result_size=effective_result_size,
        )
        right_semantic_key = self._readonly_reduction_term_sequence_contract_key(
            right_ref,
            result_size=effective_result_size,
        )
        if left_semantic_key is None or right_semantic_key is None:
            return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="readonly_contract_missing_term_sequence")
        if not self._readonly_reduction_contract_keys_compatible(
            left_semantic_key,
            right_semantic_key,
            left_ref,
            right_ref,
        ):
            return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="readonly_contract_term_sequence_mismatch")
        return _RuntimeShortcutDecision(True, requires_guard_equivalence, reason="readonly_reduction_contract")

    def _readonly_contract_effective_result_size(
        self,
        left_ref: ReadonlyReductionRef,
        right_ref: ReadonlyReductionRef,
        *,
        result_size: Optional[int],
    ) -> Optional[int]:
        try:
            left_result_size = max(1, int(getattr(left_ref, "result_size", 0) or 0))
            right_result_size = max(1, int(getattr(right_ref, "result_size", 0) or 0))
        except (TypeError, ValueError):
            return None
        if result_size is None:
            return left_result_size if left_result_size == right_result_size else None
        try:
            target_result_size = max(1, int(result_size))
        except (TypeError, ValueError):
            return None
        if target_result_size > left_result_size or target_result_size > right_result_size:
            return None
        return target_result_size

    def _readonly_reduction_term_sequence_contract_key(
        self,
        readonly_ref: ReadonlyReductionRef,
        *,
        result_size: Optional[int] = None,
    ) -> Optional[tuple]:
        contract_key_fn = getattr(readonly_ref, "readonly_term_sequence_contract_key", None)
        if callable(contract_key_fn):
            try:
                contract_key = contract_key_fn(result_size=result_size)
            except (AttributeError, TypeError, ValueError):
                contract_key = None
            if contract_key is not None:
                return contract_key
        accumulator_proof = getattr(readonly_ref, "accumulator_proof", None)
        if accumulator_proof is not None:
            proof_key_fn = getattr(accumulator_proof, "readonly_term_sequence_contract_key", None)
            if callable(proof_key_fn):
                try:
                    proof_key = proof_key_fn(result_size=result_size)
                except (AttributeError, TypeError, ValueError):
                    proof_key = None
                if proof_key is not None:
                    return proof_key
        if result_size is not None:
            try:
                if max(1, int(result_size)) != max(1, int(getattr(readonly_ref, "result_size", 0) or 0)):
                    return None
            except (TypeError, ValueError):
                return None
        loop_summary = getattr(readonly_ref, "loop_summary", None)
        loop_key_fn = getattr(loop_summary, "pairwise_semantic_key", None)
        if callable(loop_key_fn):
            try:
                loop_key = loop_key_fn()
            except (AttributeError, TypeError, ValueError):
                loop_key = None
            if loop_key is not None:
                return loop_key
        semantic_key_fn = getattr(readonly_ref, "semantic_key", None)
        if callable(semantic_key_fn):
            try:
                return semantic_key_fn()
            except (AttributeError, TypeError, ValueError):
                return None
        return None

    def _readonly_reduction_contract_keys_compatible(
        self,
        left_key: tuple,
        right_key: tuple,
        left_ref: ReadonlyReductionRef,
        right_ref: ReadonlyReductionRef,
    ) -> bool:
        if left_key == right_key:
            return True
        if (
            not isinstance(left_key, tuple)
            or not isinstance(right_key, tuple)
            or len(left_key) != len(right_key)
            or len(left_key) < 5
            or left_key[0] != "readonly_reduction_term_sequence_contract"
            or right_key[0] != "readonly_reduction_term_sequence_contract"
        ):
            return False
        if left_key[:3] != right_key[:3] or left_key[4:] != right_key[4:]:
            return False
        if not self._readonly_count_identities_compatible(left_ref, right_ref):
            return False
        return tuple(left_key[3]) in self._readonly_count_identity_keys(left_ref) and tuple(
            right_key[3]
        ) in self._readonly_count_identity_keys(right_ref)

    def _readonly_count_identity_key(self, readonly_ref: ReadonlyReductionRef) -> Optional[tuple]:
        identity_fn = getattr(readonly_ref, "count_parameter_semantic_identity", None)
        if callable(identity_fn):
            try:
                identity = identity_fn()
            except (AttributeError, TypeError, ValueError):
                identity = None
            if identity is not None:
                return identity
        storage_key = getattr(readonly_ref, "count_parameter_storage_identity_key", None)
        if storage_key is not None:
            return ("parameter_storage", tuple(storage_key))
        try:
            index = getattr(readonly_ref, "count_parameter_index", None)
            if index is not None and int(index) >= 0:
                return ("parameter", int(index))
        except (TypeError, ValueError):
            pass
        return None

    def _readonly_count_identity_keys(self, readonly_ref: ReadonlyReductionRef) -> set[tuple]:
        identities: set[tuple] = set()
        identities_fn = getattr(readonly_ref, "count_parameter_semantic_identities", None)
        if callable(identities_fn):
            try:
                identities.update(tuple(identity) for identity in identities_fn() if identity is not None)
            except (AttributeError, TypeError, ValueError):
                pass
        identity = self._readonly_count_identity_key(readonly_ref)
        if identity is not None:
            identities.add(tuple(identity))
        storage_key = getattr(readonly_ref, "count_parameter_storage_identity_key", None)
        if storage_key is not None:
            identities.add(("parameter_storage", tuple(storage_key)))
        index = getattr(readonly_ref, "count_parameter_index", None)
        try:
            if index is not None and int(index) >= 0:
                identities.add(("parameter", int(index)))
        except (TypeError, ValueError):
            pass
        return identities

    def _readonly_count_storage_identity_key(self, readonly_ref: ReadonlyReductionRef) -> Optional[tuple]:
        storage_key = getattr(readonly_ref, "count_parameter_storage_identity_key", None)
        if storage_key is None:
            return None
        return ("parameter_storage", tuple(storage_key))

    def _readonly_count_index_identity_key(self, readonly_ref: ReadonlyReductionRef) -> Optional[tuple]:
        index = getattr(readonly_ref, "count_parameter_index", None)
        try:
            if index is not None and int(index) >= 0:
                return ("parameter", int(index))
        except (TypeError, ValueError):
            return None
        return None

    def _readonly_count_identities_compatible(
        self,
        left_ref: ReadonlyReductionRef,
        right_ref: ReadonlyReductionRef,
    ) -> bool:
        return self._count_identity_components_compatible(
            self._readonly_count_storage_identity_key(left_ref),
            self._readonly_count_index_identity_key(left_ref),
            self._readonly_count_storage_identity_key(right_ref),
            self._readonly_count_index_identity_key(right_ref),
        )

    def _count_identity_components_compatible(
        self,
        left_storage: Optional[tuple],
        left_index: Optional[tuple],
        right_storage: Optional[tuple],
        right_index: Optional[tuple],
    ) -> bool:
        if left_storage is not None and right_storage is not None:
            return left_storage == right_storage
        return left_index is not None and right_index is not None and left_index == right_index

    def _runtime_refs_semantic_shortcut_decision(self, left_ref, right_ref) -> _RuntimeShortcutDecision:
        left_semantic_key_fn = getattr(left_ref, "pairwise_semantic_key", None)
        right_semantic_key_fn = getattr(right_ref, "pairwise_semantic_key", None)
        if not callable(left_semantic_key_fn) or not callable(right_semantic_key_fn):
            return _RuntimeShortcutDecision(False, False, reason="semantic_key_missing")
        try:
            left_semantic_key = left_semantic_key_fn()
            right_semantic_key = right_semantic_key_fn()
        except (AttributeError, TypeError, ValueError):
            return _RuntimeShortcutDecision(False, False, reason="semantic_key_unavailable")
        if left_semantic_key is None or right_semantic_key is None:
            return _RuntimeShortcutDecision(False, False, reason="semantic_key_none")
        if left_semantic_key != right_semantic_key:
            return _RuntimeShortcutDecision(False, False, reason="semantic_key_mismatch")

        left_guard_fn = getattr(left_ref, "pairwise_requires_guard_equivalence", None)
        right_guard_fn = getattr(right_ref, "pairwise_requires_guard_equivalence", None)
        requires_guard_equivalence = bool(callable(left_guard_fn) and left_guard_fn()) or bool(
            callable(right_guard_fn) and right_guard_fn()
        )
        return _RuntimeShortcutDecision(
            True,
            requires_guard_equivalence,
            reason="semantic_runtime_key",
        )

    def _case_pair_loop_summary_safe_fallback_reason(
        self,
        case1: ReturnCase,
        case2: ReturnCase,
    ) -> Optional[str]:
        return self._loop_summary_safe_fallback_reason_for_values(
            case1.value_expr,
            case2.value_expr,
            left_case=case1,
            right_case=case2,
        )

    def _loop_summary_safe_fallback_reason_for_values(
        self,
        left: Optional[Expression],
        right: Optional[Expression],
        *,
        left_case: Optional[ReturnCase],
        right_case: Optional[ReturnCase],
    ) -> Optional[str]:
        if left is None or right is None:
            return None
        left_has_loop = self._expression_contains_loop_summary_runtime(left)
        right_has_loop = self._expression_contains_loop_summary_runtime(right)
        if not left_has_loop and not right_has_loop:
            return None
        if left_case is not None and right_case is not None and self._cases_have_equivalent_readonly_reduction_proof(
            left_case,
            right_case,
        ):
            return None
        if left.expr_type == ExpressionType.INTRINSIC and right.expr_type == ExpressionType.INTRINSIC:
            loop_contract_decision = self._runtime_loop_contract_shortcut_decision(
                getattr(left, "runtime_ref", None),
                getattr(right, "runtime_ref", None),
                result_size=self._case_pair_comparison_result_size(left_case, right_case),
            )
            if loop_contract_decision.equivalent:
                if loop_contract_decision.requires_guard_equivalence and (
                    left_case is None
                    or right_case is None
                    or not self._case_pair_has_runtime_guard_coverage_or_equivalence(left_case, right_case)
                ):
                    return "loop_summary_guard_mismatch"
                return None
            if left_has_loop and right_has_loop and loop_contract_decision.reason != "not_loop_contract":
                return loop_contract_decision.reason
        if left_has_loop != right_has_loop:
            return "loop_summary_shape_mismatch"
        if left.expr_type != right.expr_type:
            return "loop_summary_shape_mismatch"

        if left.expr_type == ExpressionType.INTRINSIC:
            left_ref = getattr(left, "runtime_ref", None)
            right_ref = getattr(right, "runtime_ref", None)
            if (
                getattr(left_ref, "loop_summary", None) is not None
                or getattr(right_ref, "loop_summary", None) is not None
            ):
                decision = self._runtime_refs_shortcut_decision(
                    left_ref,
                    right_ref,
                    result_size=self._case_pair_comparison_result_size(left_case, right_case),
                )
                if not decision.equivalent:
                    return decision.reason
                if decision.requires_guard_equivalence and (
                    left_case is None
                    or right_case is None
                    or not self._case_pair_has_runtime_guard_coverage_or_equivalence(left_case, right_case)
                ):
                    return "loop_summary_guard_mismatch"
            if getattr(left, "opcode", None) != getattr(right, "opcode", None):
                return "loop_summary_intrinsic_mismatch"
            if (getattr(left, "name", None) or "") != (getattr(right, "name", None) or ""):
                return "loop_summary_intrinsic_mismatch"
            left_operands = list(getattr(left, "operands", []) or [])
            right_operands = list(getattr(right, "operands", []) or [])
            if len(left_operands) != len(right_operands):
                return "loop_summary_operand_mismatch"
            for left_operand, right_operand in zip(left_operands, right_operands):
                reason = self._loop_summary_safe_fallback_reason_for_values(
                    left_operand,
                    right_operand,
                    left_case=left_case,
                    right_case=right_case,
                )
                if reason is not None:
                    return reason
            return None

        left_operands = list(getattr(left, "operands", []) or [])
        right_operands = list(getattr(right, "operands", []) or [])
        if len(left_operands) != len(right_operands):
            return "loop_summary_shape_mismatch"
        for left_operand, right_operand in zip(left_operands, right_operands):
            reason = self._loop_summary_safe_fallback_reason_for_values(
                left_operand,
                right_operand,
                left_case=left_case,
                right_case=right_case,
            )
            if reason is not None:
                return reason
        return None

    def _expression_contains_loop_summary_runtime(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        runtime_ref = getattr(expr, "runtime_ref", None)
        if getattr(runtime_ref, "loop_summary", None) is not None:
            return True
        if expr.expr_type == ExpressionType.PHI and getattr(expr, "value", None):
            for condition, value in expr.value:
                if condition is not None and self._expression_contains_loop_summary_runtime(condition.expression):
                    return True
                if self._expression_contains_loop_summary_runtime(value):
                    return True
            return False
        return any(
            self._expression_contains_loop_summary_runtime(operand)
            for operand in getattr(expr, "operands", []) or []
        )

    def _counted_loop_values_are_provably_equivalent(
        self,
        left: Expression,
        right: Expression,
        *,
        left_case: Optional[ReturnCase],
        right_case: Optional[ReturnCase],
    ) -> bool:
        if left_case is None or right_case is None:
            return False
        if getattr(left, "opcode", None) != COUNTED_LOOP_SUM_OPCODE:
            return False
        if getattr(right, "opcode", None) != COUNTED_LOOP_SUM_OPCODE:
            return False
        if len(getattr(left, "operands", None) or []) != 3 or len(getattr(right, "operands", None) or []) != 3:
            return False

        left_ref = getattr(left, "runtime_ref", None)
        right_ref = getattr(right, "runtime_ref", None)
        if not self._counted_loop_refs_allow_value_proof(left_ref, right_ref):
            return False
        if (
            getattr(left_ref, "loop_summary", None) is not None
            or getattr(right_ref, "loop_summary", None) is not None
        ) and not self._case_pair_has_runtime_guard_coverage_or_equivalence(left_case, right_case):
            return False
        if not self._counted_loop_refs_match_ignoring_signedness(left_ref, right_ref):
            return False
        if not all(
            self._expressions_share_object_centric_structure(left_operand, right_operand)
            for left_operand, right_operand in zip(left.operands, right.operands)
        ):
            return False
        if bool(getattr(left_ref, "signed_loop", False)) == bool(getattr(right_ref, "signed_loop", False)):
            return True
        conditions = self._combined_summary_conditions(left_case, right_case)
        parameters = self._collect_intrinsic_parameter_specs(
            left_case,
            right_case,
            left,
            right,
            *(condition.expression for condition in conditions or [] if condition is not None),
        )
        if parameters is None:
            return False
        if self._counted_loop_signedness_difference_is_guarded(
            left,
            right,
            conditions,
            parameters,
        ):
            return True
        return self._prove_intrinsic_equivalence_under_conditions(
            left,
            right,
            conditions,
            parameters,
        )

    def _counted_loop_refs_allow_value_proof(self, left_ref, right_ref) -> bool:
        if left_ref is None or right_ref is None:
            return False
        if not isinstance(left_ref, CountedLoopSummaryRef) or not isinstance(right_ref, CountedLoopSummaryRef):
            return False
        left_loop_summary = getattr(left_ref, "loop_summary", None)
        right_loop_summary = getattr(right_ref, "loop_summary", None)
        if left_loop_summary is None and right_loop_summary is None:
            return True
        for loop_summary in (left_loop_summary, right_loop_summary):
            requires_effect_proof = getattr(loop_summary, "requires_effect_proof", None)
            if callable(requires_effect_proof) and requires_effect_proof():
                return False
            requires_path_proof = getattr(loop_summary, "requires_path_proof", None)
            if callable(requires_path_proof) and requires_path_proof():
                return False
        loop_result = compare_loop_summaries(left_loop_summary, right_loop_summary)
        if loop_result.blocks_shortcut():
            return False
        return loop_result.is_equivalent() is True

    def _counted_loop_refs_match_ignoring_signedness(self, left_ref, right_ref) -> bool:
        if left_ref is None or right_ref is None:
            return False
        if not isinstance(left_ref, CountedLoopSummaryRef) or not isinstance(right_ref, CountedLoopSummaryRef):
            return False
        try:
            return (
                int(getattr(left_ref, "induction_step", 0) or 0)
                == int(getattr(right_ref, "induction_step", 0) or 0)
                and max(1, int(getattr(left_ref, "result_size", 0) or 0))
                == max(1, int(getattr(right_ref, "result_size", 0) or 0))
                and tuple(getattr(left_ref, "residue_cases", ()) or ())
                == tuple(getattr(right_ref, "residue_cases", ()) or ())
                and getattr(left_ref, "source", None) == getattr(right_ref, "source", None)
            )
        except Exception:
            return False

    def _counted_loop_signedness_difference_is_guarded(
        self,
        left: Expression,
        right: Expression,
        conditions: Sequence[Condition],
        parameters: Sequence[Dict[str, Any]],
    ) -> bool:
        left_ref = getattr(left, "runtime_ref", None)
        right_ref = getattr(right, "runtime_ref", None)
        if bool(getattr(left_ref, "signed_loop", False)) == bool(getattr(right_ref, "signed_loop", False)):
            return True
        operands = list(getattr(left, "operands", None) or [])
        if len(operands) != 3:
            return False
        # Signed and unsigned COUNTED_LOOP_SUM lowerings differ in how start/limit
        # are extended to the wide arithmetic domain. If both are non-negative
        # under the current pair guard, the two interpretations coincide.
        return all(
            self._expression_is_provably_nonnegative_under_conditions(expr, conditions, parameters)
            for expr in operands[1:3]
        )

    def _expression_is_provably_nonnegative_under_conditions(
        self,
        expr: Expression,
        conditions: Sequence[Condition],
        parameters: Sequence[Dict[str, Any]],
    ) -> bool:
        width_bits = max(1, int(getattr(expr, "size", 0) or 4) * 8)
        if width_bits <= 1:
            return True
        if getattr(expr, "expr_type", None) == ExpressionType.CONSTANT:
            try:
                raw = int(getattr(expr, "value", 0) or 0) % (1 << width_bits)
                return raw < (1 << (width_bits - 1))
            except Exception:
                return False
        query = self._build_nonnegative_query(expr, conditions, parameters, width_bits)
        if not query:
            return False
        result = Z3Solver(timeout=1, debug=False).check_equivalence_direct(query)
        return result.status == SolverStatus.UNSAT

    def _build_nonnegative_query(
        self,
        expr: Expression,
        conditions: Sequence[Condition],
        parameters: Sequence[Dict[str, Any]],
        width_bits: int,
    ) -> Optional[str]:
        declarations = ["(set-logic QF_BV)"]
        symbol_infos = self._build_auxiliary_parameter_infos(parameters)
        for symbol in symbol_infos:
            declarations.append(f"(declare-const {symbol.smt_name} (_ BitVec {symbol.bit_width}))")

        intrinsic_declarations: List[str] = []
        for item in [expr, *(condition.expression for condition in conditions or [] if condition is not None)]:
            for declaration in collect_intrinsic_smt_declarations(item):
                if declaration not in intrinsic_declarations:
                    intrinsic_declarations.append(declaration)
        declarations.extend(intrinsic_declarations)

        assertions = []
        for condition in conditions or []:
            if condition is None:
                continue
            rendered_condition = self._render_auxiliary_smt(condition, parameters)
            if rendered_condition is None:
                return None
            assertions.append(f"(assert {rendered_condition})")
        expr_smt = self._render_auxiliary_smt(expr, parameters)
        if expr_smt is None:
            return None
        assertions.append(f"(assert (= ((_ extract {width_bits - 1} {width_bits - 1}) {expr_smt}) #b1))")
        return "\n".join(declarations + assertions + ["(check-sat)"])

    def _combined_summary_conditions(
        self,
        left_case: ReturnCase,
        right_case: ReturnCase,
    ) -> List[Condition]:
        left_conditions = left_case.summary_conditions if left_case.summary_conditions is not None else left_case.conditions
        right_conditions = right_case.summary_conditions if right_case.summary_conditions is not None else right_case.conditions
        return ConditionSimplifier.simplify_conditions_object_centric(
            list(left_conditions or []) + list(right_conditions or [])
        )

    def _collect_intrinsic_parameter_specs(
        self,
        left_case: ReturnCase,
        right_case: ReturnCase,
        *exprs: Expression,
    ) -> Optional[List[Dict[str, Any]]]:
        specs: Dict[Tuple[object, ...], Dict[str, Any]] = {}
        unresolved_symbol = False

        def add_spec(identity: Optional[Tuple[object, ...]], candidate: Dict[str, Any]) -> None:
            if identity is None:
                return
            size = max(1, int(candidate.get("size", 0) or 4))
            existing = specs.get(identity)
            if existing is None:
                specs[identity] = {
                    **candidate,
                    "identity": identity,
                    "size": size,
                }
                return
            if int(existing.get("size", 0) or 0) < size:
                existing.update(candidate)
                existing["identity"] = identity
                existing["size"] = size

        for case in (left_case, right_case):
            for parameter in list(getattr(case, "parameters", None) or []):
                candidate = dict(parameter)
                candidate["name"] = str(parameter.get("name") or "")
                add_spec(parameter_identity_key_from_descriptor(candidate), candidate)

        def visit(expr: Optional[Expression]) -> None:
            nonlocal unresolved_symbol
            if expr is None:
                return
            if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER:
                identity = parameter_identity_key_from_expression(expr)
                if identity is None:
                    unresolved_symbol = True
                    return
                candidate = {
                    "name": str(getattr(expr, "name", None) or ""),
                    "index": int(getattr(expr, "value", -1) or -1),
                    "size": max(1, int(getattr(expr, "size", 0) or 4)),
                    "data_type": getattr(expr, "data_type", None),
                    "storage_info": getattr(expr, "storage_info", None),
                }
                add_spec(identity, candidate)
                return
            if getattr(expr, "expr_type", None) == ExpressionType.VARIABLE:
                unresolved_symbol = True
                return
            if getattr(expr, "expr_type", None) == ExpressionType.PHI:
                for cond, branch_value in getattr(expr, "value", None) or []:
                    if cond is not None:
                        visit(getattr(cond, "expression", None))
                    visit(branch_value)
                return
            for operand in getattr(expr, "operands", None) or []:
                visit(operand)

        for expr in exprs:
            visit(expr)
        if unresolved_symbol:
            return None

        ordered = sorted(
            specs.values(),
            key=lambda item: (
                self._auxiliary_identity_sort_key(item.get("identity")),
                int(item.get("size", 0) or 0),
            ),
        )
        for ordinal, spec in enumerate(ordered):
            spec["aux_name"] = f"aux_param_{ordinal}"
            spec["aux_index"] = ordinal
        return ordered

    def _prove_intrinsic_equivalence_under_conditions(
        self,
        left: Expression,
        right: Expression,
        conditions: Sequence[Condition],
        parameters: Sequence[Dict[str, Any]],
    ) -> bool:
        query = self._build_intrinsic_equivalence_query(left, right, conditions, parameters)
        if not query:
            return False
        result = Z3Solver(timeout=2, debug=self.debug).check_equivalence_direct(query)
        return result.status == SolverStatus.UNSAT

    def _build_intrinsic_equivalence_query(
        self,
        left: Expression,
        right: Expression,
        conditions: Sequence[Condition],
        parameters: Sequence[Dict[str, Any]],
    ) -> Optional[str]:
        if left is None or right is None:
            return None
        declarations = ["(set-logic QF_BV)"]
        symbol_infos = self._build_auxiliary_parameter_infos(parameters)
        for symbol in symbol_infos:
            declarations.append(f"(declare-const {symbol.smt_name} (_ BitVec {symbol.bit_width}))")

        intrinsic_declarations: List[str] = []
        for expr in (left, right):
            for declaration in collect_intrinsic_smt_declarations(expr):
                if declaration not in intrinsic_declarations:
                    intrinsic_declarations.append(declaration)
        for condition in conditions or []:
            if condition is None:
                continue
            for declaration in collect_intrinsic_smt_declarations(condition.expression):
                if declaration not in intrinsic_declarations:
                    intrinsic_declarations.append(declaration)
        declarations.extend(intrinsic_declarations)

        assertions = []
        for condition in conditions or []:
            if condition is None:
                continue
            rendered_condition = self._render_auxiliary_smt(condition, parameters)
            if rendered_condition is None:
                return None
            assertions.append(f"(assert {rendered_condition})")
        left_smt = self._render_auxiliary_smt(left, parameters)
        right_smt = self._render_auxiliary_smt(right, parameters)
        if left_smt is None or right_smt is None:
            return None
        assertions.append(f"(assert (not (= {left_smt} {right_smt})))")
        return "\n".join(declarations + assertions + ["(check-sat)"])

    def _build_auxiliary_parameter_infos(
        self,
        symbol_specs: Sequence[Dict[str, Any]],
    ) -> List[ParameterInfo]:
        infos: List[ParameterInfo] = []
        for spec in sorted(
            symbol_specs or [],
            key=lambda item: (
                self._auxiliary_identity_sort_key(item.get("identity")),
                int(item.get("size", 0) or 0),
            ),
        ):
            aux_name = str(spec.get("aux_name") or "")
            if not aux_name:
                continue
            infos.append(
                ParameterInfo(
                    original_name=aux_name,
                    smt_name=aux_name,
                    bit_width=max(1, int(spec.get("size", 0) or 4)) * 8,
                    index=int(spec.get("aux_index", -1) or -1),
                    is_signed=bool(spec.get("is_signed", True)),
                )
            )
        return infos

    def _auxiliary_identity_sort_key(self, identity) -> Tuple[int, str]:
        if not isinstance(identity, tuple) or not identity:
            return (9, "")
        kind = identity[0]
        if kind == "parameter_index" and len(identity) >= 2:
            try:
                return (0, f"{int(identity[1]):08d}")
            except (TypeError, ValueError):
                return (0, repr(identity[1]))
        if kind == "parameter_storage" and len(identity) >= 2:
            return (1, repr(identity[1]))
        return (8, repr(identity))

    def _render_auxiliary_smt(
        self,
        node,
        symbol_specs: Sequence[Dict[str, Any]],
    ) -> Optional[str]:
        identity_to_spec = {
            spec.get("identity"): spec
            for spec in symbol_specs or []
            if spec.get("identity") is not None and spec.get("aux_name")
        }
        if isinstance(node, Condition):
            cloned_expr = self._clone_auxiliary_expression_for_smt(
                node.expression,
                identity_to_spec,
            )
            if cloned_expr is None:
                return None
            return Condition(cloned_expr, bool(getattr(node, "negated", False))).to_smt()
        if isinstance(node, Expression):
            cloned_expr = self._clone_auxiliary_expression_for_smt(
                node,
                identity_to_spec,
            )
            return cloned_expr.to_smt() if cloned_expr is not None else None
        return None

    def _clone_auxiliary_expression_for_smt(
        self,
        expr: Optional[Expression],
        identity_to_spec: Dict[Tuple[object, ...], Dict[str, Any]],
    ) -> Optional[Expression]:
        if expr is None:
            return None
        expr_type = getattr(expr, "expr_type", None)
        if expr_type == ExpressionType.PARAMETER:
            identity = parameter_identity_key_from_expression(expr)
            if identity is None:
                return None
            symbol_spec = identity_to_spec.get(identity)
            if symbol_spec is None:
                return None
            aux_name = str(symbol_spec.get("aux_name") or "")
            if not aux_name:
                return None
            try:
                occurrence_size = max(1, int(getattr(expr, "size", 0) or 4))
                symbol_size = max(1, int(symbol_spec.get("size", 0) or occurrence_size))
            except (TypeError, ValueError):
                return None
            if occurrence_size > symbol_size:
                return None
            aux_expr = expr.clone_with(
                name=aux_name,
                value=int(symbol_spec.get("aux_index", -1) or -1),
                size=symbol_size,
            )
            if occurrence_size == symbol_size:
                return aux_expr
            return Expression(
                ExpressionType.BINARY_OP,
                operator="SUBPIECE",
                operands=[
                    aux_expr,
                    Expression.constant(0, size=8),
                ],
                size=occurrence_size,
            )
        if expr_type == ExpressionType.VARIABLE:
            return None
        if expr_type == ExpressionType.PHI:
            branches = []
            for condition, value in getattr(expr, "value", None) or []:
                cloned_condition = None
                if condition is not None:
                    cloned_condition_expr = self._clone_auxiliary_expression_for_smt(
                        condition.expression,
                        identity_to_spec,
                    )
                    if cloned_condition_expr is None:
                        return None
                    cloned_condition = Condition(
                        cloned_condition_expr,
                        bool(getattr(condition, "negated", False)),
                    )
                cloned_value = self._clone_auxiliary_expression_for_smt(value, identity_to_spec)
                if cloned_value is None:
                    return None
                branches.append((cloned_condition, cloned_value))
            return expr.clone_with(value=branches)
        operands = getattr(expr, "operands", None) or []
        if not operands:
            return expr
        cloned_operands = []
        for operand in operands:
            cloned_operand = self._clone_auxiliary_expression_for_smt(
                operand,
                identity_to_spec,
            )
            if cloned_operand is None:
                return None
            cloned_operands.append(cloned_operand)
        return expr.clone_with(operands=cloned_operands)

    def _cases_have_equivalent_summary_conditions(
        self,
        left_case: ReturnCase,
        right_case: ReturnCase,
    ) -> bool:
        left_conditions = left_case.summary_conditions if left_case.summary_conditions is not None else left_case.conditions
        right_conditions = right_case.summary_conditions if right_case.summary_conditions is not None else right_case.conditions
        left_normalized = ConditionSimplifier.simplify_conditions_object_centric(list(left_conditions or []))
        right_normalized = ConditionSimplifier.simplify_conditions_object_centric(list(right_conditions or []))
        if not left_normalized and not right_normalized:
            return True
        parameters = list(getattr(left_case, "parameters", None) or []) + list(
            getattr(right_case, "parameters", None) or []
        )
        return self._condition_set_implies(
            left_normalized,
            right_normalized,
            parameters,
        ) and self._condition_set_implies(
            right_normalized,
            left_normalized,
            parameters,
        )

    def _cases_have_pair_local_summary_guard_compatibility(
        self,
        left_case: ReturnCase,
        right_case: ReturnCase,
    ) -> bool:
        if not self._cases_have_equivalent_summary_conditions(left_case, right_case):
            return False
        return self._case_conditions_cover_runtime_summary_guards(
            left_case,
        ) and self._case_conditions_cover_runtime_summary_guards(right_case)

    def _case_pair_has_runtime_guard_coverage_or_equivalence(
        self,
        left_case: ReturnCase,
        right_case: ReturnCase,
    ) -> bool:
        left_guards, left_complete = self._runtime_summary_guard_conditions_from_expression(
            left_case.value_expr,
        )
        right_guards, right_complete = self._runtime_summary_guard_conditions_from_expression(
            right_case.value_expr,
        )
        if not left_complete or not right_complete:
            return False
        if not left_guards and not right_guards:
            return self._cases_have_equivalent_summary_conditions(left_case, right_case)
        if self._cases_have_pair_local_summary_guard_compatibility(left_case, right_case):
            return True
        if not left_guards or not right_guards:
            return False
        return self._case_conditions_cover_runtime_summary_guards(
            left_case,
        ) and self._case_conditions_cover_runtime_summary_guards(
            right_case,
        )

    def _case_conditions_cover_runtime_summary_guards(
        self,
        case: ReturnCase,
    ) -> bool:
        guards, complete = self._runtime_summary_guard_conditions_from_expression(case.value_expr)
        if not complete:
            return False
        if not guards:
            return False
        return self._condition_set_implies(
            list(getattr(case, "conditions", None) or []),
            guards,
            list(getattr(case, "parameters", None) or []),
        )

    def _runtime_summary_guard_conditions_from_expression(
        self,
        expr: Optional[Expression],
    ) -> tuple[List[Condition], bool]:
        guards: List[Condition] = []
        seen: set[tuple] = set()
        complete = True
        for node in self._iter_expression_nodes(expr):
            runtime_ref = getattr(node, "runtime_ref", None)
            for owner in (
                runtime_ref,
                getattr(runtime_ref, "accumulator_proof", None),
                getattr(runtime_ref, "loop_summary", None),
            ):
                for guard in tuple(getattr(owner, "guard_constraints", ()) or ()):
                    if not isinstance(guard, Condition):
                        complete = False
                        continue
                    key = guard.structural_key(budget=256)
                    if key in seen:
                        continue
                    seen.add(key)
                    guards.append(guard)
        return guards, complete

    def _iter_expression_nodes(self, expr: Optional[Expression]):
        if expr is None:
            return
        yield expr
        if getattr(expr, "expr_type", None) == ExpressionType.PHI:
            for condition, value in getattr(expr, "value", None) or ():
                if condition is not None:
                    yield from self._iter_expression_nodes(getattr(condition, "expression", None))
                yield from self._iter_expression_nodes(value)
            return
        for operand in getattr(expr, "operands", None) or ():
            yield from self._iter_expression_nodes(operand)

    def _case_pair_can_defer_loop_summary_proof(
        self,
        left_case: ReturnCase,
        right_case: ReturnCase,
        reason: str,
    ) -> bool:
        if reason != "loop_summary_guard_mismatch":
            return False
        return self._loop_summary_contracts_match_without_guard(
            left_case.value_expr,
            right_case.value_expr,
        )

    def _loop_summary_contracts_match_without_guard(
        self,
        left: Optional[Expression],
        right: Optional[Expression],
    ) -> bool:
        if left is None or right is None:
            return False
        left_has_loop = self._expression_contains_loop_summary_runtime(left)
        right_has_loop = self._expression_contains_loop_summary_runtime(right)
        if not left_has_loop or not right_has_loop:
            return False
        if left.expr_type == ExpressionType.INTRINSIC and right.expr_type == ExpressionType.INTRINSIC:
            decision = self._runtime_loop_contract_shortcut_decision(
                getattr(left, "runtime_ref", None),
                getattr(right, "runtime_ref", None),
            )
            if decision.equivalent and decision.requires_guard_equivalence:
                return True
        if left.expr_type != right.expr_type:
            return False
        left_operands = list(getattr(left, "operands", []) or [])
        right_operands = list(getattr(right, "operands", []) or [])
        if len(left_operands) != len(right_operands):
            return False
        return any(
            self._loop_summary_contracts_match_without_guard(left_operand, right_operand)
            for left_operand, right_operand in zip(left_operands, right_operands)
        )

    def _resolve_pending_loop_summary_pairs_with_partition_proof(
        self,
        pending_pairs: Sequence[_PendingLoopSummaryPair],
        cases1: Sequence[ReturnCase],
        cases2: Sequence[ReturnCase],
        resolved_pairs: set[tuple[int, int]],
    ) -> set[tuple[int, int]]:
        resolved_pending: set[tuple[int, int]] = set()
        progress = True
        while progress:
            progress = False
            known_resolved = set(resolved_pairs) | resolved_pending
            for pending in pending_pairs:
                pair_key = (pending.i, pending.j)
                if pair_key in resolved_pending:
                    continue
                if not self._pending_loop_summary_pair_has_exact_delta_coverage(
                    pending,
                    cases1,
                    cases2,
                    known_resolved,
                ):
                    continue
                resolved_pending.add(pair_key)
                progress = True
        return resolved_pending

    def _pending_loop_summary_pair_has_exact_delta_coverage(
        self,
        pending: _PendingLoopSummaryPair,
        cases1: Sequence[ReturnCase],
        cases2: Sequence[ReturnCase],
        resolved_pairs: set[tuple[int, int]],
    ) -> bool:
        left_cover_cases = [
            cases1[left_index]
            for left_index, _right_index in sorted(resolved_pairs)
            if _right_index == pending.j
            and left_index != pending.i
            and 0 <= left_index < len(cases1)
            and not self._expression_contains_loop_summary_runtime(cases1[left_index].value_expr)
        ]
        right_cover_cases = [
            cases2[right_index]
            for _left_index, right_index in sorted(resolved_pairs)
            if _left_index == pending.i
            and right_index != pending.j
            and 0 <= right_index < len(cases2)
            and not self._expression_contains_loop_summary_runtime(cases2[right_index].value_expr)
        ]
        return self._condition_delta_region_is_covered_by_cases(
            self._case_summary_condition_basis(pending.left_case),
            self._case_summary_condition_basis(pending.right_case),
            right_cover_cases,
            pending.left_case,
            pending.right_case,
        ) and self._condition_delta_region_is_covered_by_cases(
            self._case_summary_condition_basis(pending.right_case),
            self._case_summary_condition_basis(pending.left_case),
            left_cover_cases,
            pending.right_case,
            pending.left_case,
        )

    def _condition_delta_region_is_covered_by_cases(
        self,
        domain_conditions: Sequence[Condition],
        excluded_conditions: Sequence[Condition],
        covering_cases: Sequence[ReturnCase],
        domain_case: ReturnCase,
        excluded_case: ReturnCase,
    ) -> bool:
        excluded_conjunction = Condition.combine_and(list(excluded_conditions or []))
        if excluded_conjunction is None:
            return True

        proof_conditions: List[Condition] = list(domain_conditions or [])
        proof_conditions.append(excluded_conjunction.negate())

        covering_condition = self._case_union_condition(covering_cases)
        if covering_condition is None:
            return self._condition_region_is_unsat_for_cases(
                proof_conditions,
                [domain_case, excluded_case, *list(covering_cases or [])],
            )
        proof_conditions.append(covering_condition.negate())
        return self._condition_region_is_unsat_for_cases(
            proof_conditions,
            [domain_case, excluded_case, *list(covering_cases or [])],
        )

    def _case_summary_condition_basis(self, case: ReturnCase) -> List[Condition]:
        return list(case.summary_conditions if case.summary_conditions is not None else case.conditions)

    def _case_union_condition(self, cases: Sequence[ReturnCase]) -> Optional[Condition]:
        disjuncts = []
        for case in cases or []:
            case_conditions = list(getattr(case, "conditions", None) or [])
            if not case_conditions:
                return Condition(
                    Expression.binary_op(
                        "INT_EQUAL",
                        Expression.constant(1, size=1),
                        Expression.constant(1, size=1),
                    )
                )
            conjunction = Condition.combine_and(case_conditions)
            if conjunction is not None:
                disjuncts.append(self._condition_as_bool_expression(conjunction))
        if not disjuncts:
            return None
        union_expr = disjuncts[0]
        for disjunct in disjuncts[1:]:
            union_expr = Expression.binary_op("BOOL_OR", union_expr, disjunct)
        return Condition(union_expr)

    def _condition_as_bool_expression(self, condition: Condition) -> Expression:
        if condition.negated:
            return Expression.unary_op("BOOL_NEGATE", condition.expression)
        return condition.expression

    def _condition_region_is_unsat_for_cases(
        self,
        conditions: Sequence[Condition],
        cases: Sequence[ReturnCase],
    ) -> bool:
        parameters: List[Dict[str, Any]] = []
        for case in cases or []:
            parameters.extend(list(getattr(case, "parameters", None) or []))
        identity_conditions = self._conditions_with_object_identity_parameter_symbols(
            conditions,
            parameters,
        )
        solver_result = ConditionSMTOracle.conjunction_is_unsat(identity_conditions)
        if solver_result is not None:
            return solver_result
        return ConditionSimplifier.object_centric_is_contradiction(identity_conditions)

    def _return_cases_have_smt_total_coverage(
        self,
        cases: Sequence[Any],
    ) -> Optional[bool]:
        miss_conditions: List[Condition] = []
        for case in cases or ():
            conditions = list(getattr(case, "conditions", None) or [])
            if not conditions:
                return True
            miss_expr = self._case_miss_expression(conditions)
            if miss_expr is None:
                return None
            miss_conditions.append(Condition(miss_expr, False))
        if not miss_conditions:
            return False

        parameters: List[Dict[str, Any]] = []
        for case in cases or ():
            parameters.extend(list(getattr(case, "parameters", None) or []))
        identity_conditions = self._conditions_with_object_identity_parameter_symbols(
            miss_conditions,
            parameters,
        )
        return ConditionSMTOracle.conjunction_is_unsat(identity_conditions)

    def _condition_set_implies(
        self,
        premises: Sequence[Condition],
        conclusions: Sequence[Condition],
        parameters: Sequence[Dict[str, Any]],
    ) -> bool:
        if not conclusions:
            return True
        for conclusion in conclusions or []:
            implication_conditions = list(premises or []) + [conclusion.negate()]
            identity_conditions = self._conditions_with_object_identity_parameter_symbols(
                implication_conditions,
                parameters,
            )
            solver_result = ConditionSMTOracle.conjunction_is_unsat(identity_conditions)
            if solver_result is not None:
                if not solver_result:
                    return False
                continue
            if not ConditionSimplifier.object_centric_is_contradiction(identity_conditions):
                return False
        return True

    def _conditions_are_semantically_equivalent(
        self,
        left_condition: Condition,
        right_condition: Condition,
    ) -> bool:
        if left_condition.equals(right_condition):
            return True
        return self._condition_implies(left_condition, right_condition) and self._condition_implies(
            right_condition,
            left_condition,
        )

    def _condition_implies(
        self,
        premise: Condition,
        conclusion: Condition,
    ) -> bool:
        implication_conditions = [premise, conclusion.negate()]
        solver_result = ConditionSMTOracle.conjunction_is_unsat(implication_conditions)
        if solver_result is not None:
            return solver_result
        return ConditionSimplifier.object_centric_is_contradiction(implication_conditions)

    def _combined_conditions_imply_reduction_count(
        self,
        exact_case: ReturnCase,
        summary_case: ReturnCase,
        accumulator_proof,
        exact_count: int,
    ) -> bool:
        if exact_count <= 0:
            return False
        count_bits = max(
            self._case_reduction_count_bit_width(exact_case, accumulator_proof),
            self._case_reduction_count_bit_width(summary_case, accumulator_proof),
        )
        count_expr = self._reduction_count_parameter_expression(
            list(getattr(exact_case, "parameters", None) or [])
            + list(getattr(summary_case, "parameters", None) or []),
            accumulator_proof,
            int(count_bits),
        )
        if count_expr is None:
            return False
        equality = Condition(
            Expression.binary_op(
                "INT_EQUAL",
                count_expr,
                Expression.constant(int(exact_count), size=max(1, (int(count_bits) + 7) // 8)),
            ),
            False,
        )
        conditions = self._combined_summary_conditions(exact_case, summary_case)
        implication_conditions = list(conditions or []) + [equality.negate()]
        identity_conditions = self._conditions_with_object_identity_parameter_symbols(
            implication_conditions,
            list(getattr(exact_case, "parameters", None) or [])
            + list(getattr(summary_case, "parameters", None) or []),
        )
        solver_result = ConditionSMTOracle.conjunction_is_unsat(identity_conditions)
        if solver_result is not None:
            return solver_result
        return ConditionSimplifier.object_centric_is_contradiction(identity_conditions)

    def _cases_admit_reduction_count(
        self,
        exact_case: ReturnCase,
        summary_case: ReturnCase,
        accumulator_proof,
        exact_count: int,
    ) -> bool:
        if self._combined_conditions_imply_reduction_count(
            exact_case,
            summary_case,
            accumulator_proof,
            exact_count,
        ):
            return True
        return self._case_implies_reduction_count(exact_case, accumulator_proof, exact_count) and (
            self._case_allows_reduction_count(summary_case, accumulator_proof, exact_count)
        )

    def _case_implies_reduction_count(
        self,
        case: ReturnCase,
        accumulator_proof,
        exact_count: int,
    ) -> bool:
        if self._case_has_direct_reduction_count_equality(
            case,
            accumulator_proof,
            exact_count,
        ):
            return True
        equality = self._reduction_count_equality_condition(case, accumulator_proof, exact_count)
        if equality is None:
            return False
        identity_conditions = self._conditions_with_object_identity_parameter_symbols(
            list(getattr(case, "conditions", None) or []) + [equality.negate()],
            list(getattr(case, "parameters", None) or []),
        )
        solver_result = ConditionSMTOracle.conjunction_is_unsat(identity_conditions)
        if solver_result is not None:
            return solver_result
        if ConditionSimplifier.object_centric_is_contradiction(identity_conditions):
            return True
        return False

    def _case_allows_reduction_count(
        self,
        case: ReturnCase,
        accumulator_proof,
        exact_count: int,
    ) -> bool:
        equality = self._reduction_count_equality_condition(case, accumulator_proof, exact_count)
        if equality is None:
            return False
        identity_conditions = self._conditions_with_object_identity_parameter_symbols(
            list(getattr(case, "conditions", None) or []) + [equality],
            list(getattr(case, "parameters", None) or []),
        )
        solver_result = ConditionSMTOracle.conjunction_is_unsat(identity_conditions)
        if solver_result is not None:
            return not solver_result
        return not ConditionSimplifier.object_centric_is_contradiction(identity_conditions)

    def _reduction_count_equality_condition(
        self,
        case: ReturnCase,
        accumulator_proof,
        exact_count: int,
    ) -> Optional[Condition]:
        if exact_count <= 0:
            return None
        count_bits = self._case_reduction_count_bit_width(case, accumulator_proof)
        count_expr = self._reduction_count_parameter_expression(
            getattr(case, "parameters", None) or [],
            accumulator_proof,
            int(count_bits),
        )
        if count_expr is None:
            return None
        return Condition(
            Expression.binary_op(
                "INT_EQUAL",
                count_expr,
                Expression.constant(int(exact_count), size=max(1, (int(count_bits) + 7) // 8)),
            ),
            False,
        )

    def _reduction_count_parameter_expression(
        self,
        parameters: Sequence[Dict[str, Any]],
        accumulator_proof,
        count_bits: int,
    ) -> Optional[Expression]:
        count_size = max(1, (max(1, int(count_bits)) + 7) // 8)
        descriptor = self._reduction_count_parameter_descriptor(parameters, accumulator_proof)
        proof_index = getattr(accumulator_proof, "count_parameter_index", None)
        count_name = str(getattr(accumulator_proof, "count_parameter_name", None) or "")
        storage_info = None
        if descriptor is None and self._parameters_have_conflicting_reduction_count_storage(
            parameters,
            accumulator_proof,
        ):
            return None
        if descriptor is not None:
            count_name = str(descriptor.get("name") or count_name or "count")
            storage_info = self._storage_info_from_parameter_descriptor(descriptor)
            if proof_index is None:
                proof_index = descriptor.get("index")
        try:
            index = int(proof_index) if proof_index is not None else -1
        except (TypeError, ValueError):
            index = -1
        if index < 0 and storage_info is None:
            return None
        return Expression.parameter(
            count_name or "count",
            index=index,
            size=count_size,
            data_type=descriptor.get("data_type") if descriptor is not None else None,
            data_type_obj=descriptor.get("data_type_obj") if descriptor is not None else None,
            storage_info=storage_info,
        )

    def _reduction_count_parameter_descriptor(
        self,
        parameters: Sequence[Dict[str, Any]],
        accumulator_proof,
    ) -> Optional[Dict[str, Any]]:
        proof_storage = self._reduction_count_storage_identity_key(accumulator_proof)
        proof_index = self._reduction_count_index_identity_key(accumulator_proof)
        if proof_storage is None and proof_index is None:
            return None
        for parameter in parameters or []:
            if self._count_identity_components_compatible(
                proof_storage,
                proof_index,
                self._parameter_descriptor_storage_identity_key(parameter),
                self._parameter_descriptor_index_identity_key(parameter),
            ):
                return parameter
        return None

    def _parameters_have_conflicting_reduction_count_storage(
        self,
        parameters: Sequence[Dict[str, Any]],
        accumulator_proof,
    ) -> bool:
        proof_storage = self._reduction_count_storage_identity_key(accumulator_proof)
        proof_index = self._reduction_count_index_identity_key(accumulator_proof)
        if proof_storage is None or proof_index is None:
            return False
        for parameter in parameters or []:
            parameter_index = self._parameter_descriptor_index_identity_key(parameter)
            parameter_storage = self._parameter_descriptor_storage_identity_key(parameter)
            if parameter_index == proof_index and parameter_storage is not None and parameter_storage != proof_storage:
                return True
        return False

    def _reduction_count_storage_identity_key(self, accumulator_proof) -> Optional[tuple]:
        storage_key = getattr(accumulator_proof, "count_parameter_storage_identity_key", None)
        if storage_key is None:
            return None
        return ("parameter_storage", tuple(storage_key))

    def _reduction_count_index_identity_key(self, accumulator_proof) -> Optional[tuple]:
        index = getattr(accumulator_proof, "count_parameter_index", None)
        try:
            if index is not None and int(index) >= 0:
                return ("parameter", int(index))
        except (TypeError, ValueError):
            return None
        return None

    def _reduction_count_identity_keys(self, accumulator_proof) -> set[tuple]:
        identities: set[tuple] = set()
        identities_fn = getattr(accumulator_proof, "count_parameter_semantic_identities", None)
        if callable(identities_fn):
            try:
                identities.update(tuple(identity) for identity in identities_fn() if identity is not None)
            except (AttributeError, TypeError, ValueError):
                pass
        identity_fn = getattr(accumulator_proof, "count_parameter_semantic_identity", None)
        if callable(identity_fn):
            try:
                identity = identity_fn()
            except (AttributeError, TypeError, ValueError):
                identity = None
            if identity is not None:
                identities.add(tuple(identity))
        storage_key = getattr(accumulator_proof, "count_parameter_storage_identity_key", None)
        if storage_key is not None:
            identities.add(("parameter_storage", tuple(storage_key)))
        index = getattr(accumulator_proof, "count_parameter_index", None)
        try:
            if index is not None and int(index) >= 0:
                identities.add(("parameter", int(index)))
        except (TypeError, ValueError):
            pass
        return identities

    def _storage_info_from_parameter_descriptor(self, parameter: Dict[str, Any]) -> Optional[StorageInfo]:
        storage = parameter.get("storage_info", parameter.get("storage")) if isinstance(parameter, dict) else None
        if isinstance(storage, StorageInfo):
            return storage
        if isinstance(storage, dict):
            try:
                return StorageInfo(**storage)
            except Exception:
                return None
        return None

    def _parameter_descriptor_storage_identity_key(self, parameter: Dict[str, Any]) -> Optional[tuple]:
        storage_info = self._storage_info_from_parameter_descriptor(parameter)
        storage_key_fn = getattr(storage_info, "storage_identity_key", None)
        if not callable(storage_key_fn):
            return None
        try:
            storage_key = storage_key_fn()
        except (AttributeError, TypeError, ValueError):
            return None
        if storage_key is None:
            return None
        return ("parameter_storage", tuple(storage_key))

    def _parameter_descriptor_index_identity_key(self, parameter: Dict[str, Any]) -> Optional[tuple]:
        if not isinstance(parameter, dict):
            return None
        try:
            index = parameter.get("index")
            if index is not None and int(index) >= 0:
                return ("parameter", int(index))
        except (TypeError, ValueError):
            return None
        return None

    def _parameter_descriptor_identity_keys(self, parameter: Dict[str, Any]) -> set[tuple]:
        identities: set[tuple] = set()
        if not isinstance(parameter, dict):
            return identities
        try:
            index = parameter.get("index")
            if index is not None and int(index) >= 0:
                identities.add(("parameter", int(index)))
        except (TypeError, ValueError):
            pass
        storage_info = self._storage_info_from_parameter_descriptor(parameter)
        storage_key_fn = getattr(storage_info, "storage_identity_key", None)
        if callable(storage_key_fn):
            try:
                storage_key = storage_key_fn()
            except (AttributeError, TypeError, ValueError):
                storage_key = None
            if storage_key is not None:
                identities.add(("parameter_storage", tuple(storage_key)))
        return identities

    def _parameter_expression_storage_identity_key(self, expr: Expression) -> Optional[tuple]:
        storage_info = getattr(expr, "storage_info", None)
        storage_key_fn = getattr(storage_info, "storage_identity_key", None)
        if not callable(storage_key_fn):
            return None
        try:
            storage_key = storage_key_fn()
        except (AttributeError, TypeError, ValueError):
            return None
        if storage_key is None:
            return None
        return ("parameter_storage", tuple(storage_key))

    def _parameter_expression_index_identity_key(self, expr: Expression) -> Optional[tuple]:
        try:
            index = getattr(expr, "value", None)
            if index is not None and int(index) >= 0:
                return ("parameter", int(index))
        except (TypeError, ValueError):
            return None
        return None

    def _parameter_expression_identity_keys(self, expr: Expression) -> set[tuple]:
        identities: set[tuple] = set()
        try:
            index = getattr(expr, "value", None)
            if index is not None and int(index) >= 0:
                identities.add(("parameter", int(index)))
        except (TypeError, ValueError):
            pass
        storage_info = getattr(expr, "storage_info", None)
        storage_key_fn = getattr(storage_info, "storage_identity_key", None)
        if callable(storage_key_fn):
            try:
                storage_key = storage_key_fn()
            except (AttributeError, TypeError, ValueError):
                storage_key = None
            if storage_key is not None:
                identities.add(("parameter_storage", tuple(storage_key)))
        return identities

    def _case_has_direct_reduction_count_equality(
        self,
        case: ReturnCase,
        accumulator_proof,
        exact_count: int,
    ) -> bool:
        for condition in list(getattr(case, "conditions", None) or []):
            expr = getattr(condition, "expression", None)
            if (
                expr is None
                or getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP
                or len(getattr(expr, "operands", None) or []) != 2
            ):
                continue
            operator = getattr(expr, "operator", None)
            condition_true = not bool(getattr(condition, "negated", False))
            if operator == "INT_EQUAL" and not condition_true:
                continue
            if operator == "INT_NOTEQUAL" and condition_true:
                continue
            if operator not in {"INT_EQUAL", "INT_NOTEQUAL"}:
                continue
            left, right = expr.operands
            if self._expression_is_full_reduction_count_view(left, case, accumulator_proof):
                const_value = self._exact_reduction_count_constant(right)
            elif self._expression_is_full_reduction_count_view(right, case, accumulator_proof):
                const_value = self._exact_reduction_count_constant(left)
            else:
                const_value = self._solve_reduction_count_affine_equality(
                    left,
                    self._exact_reduction_count_constant(right),
                    operator,
                    not condition_true,
                    case,
                    accumulator_proof,
                )
                if const_value is None:
                    const_value = self._solve_reduction_count_affine_equality(
                        right,
                        self._exact_reduction_count_constant(left),
                        operator,
                        not condition_true,
                        case,
                        accumulator_proof,
                    )
                if const_value is None:
                    const_value = self._solve_reduction_count_affine_equality_between_expressions(
                        left,
                        right,
                        operator,
                        not condition_true,
                        case,
                        accumulator_proof,
                    )
                if const_value is None:
                    continue
            if const_value == int(exact_count):
                return True
        return False

    def _solve_reduction_count_affine_equality(
        self,
        expr: Optional[Expression],
        other_const: Optional[int],
        operator: Optional[str],
        negated: bool,
        case: ReturnCase,
        accumulator_proof,
    ) -> Optional[int]:
        if expr is None or other_const is None or operator not in {"INT_EQUAL", "INT_NOTEQUAL"}:
            return None
        if operator == "INT_EQUAL" and negated:
            return None
        if operator == "INT_NOTEQUAL" and not negated:
            return None
        affine = self._extract_reduction_count_affine(expr, case, accumulator_proof)
        if affine is None:
            return None
        coeff, bias = affine
        if int(coeff) != 1:
            return None
        return int(other_const) - int(bias)

    def _solve_reduction_count_affine_equality_between_expressions(
        self,
        left: Optional[Expression],
        right: Optional[Expression],
        operator: Optional[str],
        negated: bool,
        case: ReturnCase,
        accumulator_proof,
    ) -> Optional[int]:
        """Solve object-level equalities whose operands are affine in the reduction count.

        Ghidra often emits exact finite tail guards as pointer equalities, for
        example PTRADD(PTRADD(base, 3, 4), 1, 4) == PTRADD(base, count, 4).
        Treating those as strings is brittle; instead we lower both sides to a
        base-preserving byte-affine form derived from Expression/PTRADD objects.
        """

        if left is None or right is None or operator not in {"INT_EQUAL", "INT_NOTEQUAL"}:
            return None
        if operator == "INT_EQUAL" and negated:
            return None
        if operator == "INT_NOTEQUAL" and not negated:
            return None

        left_count_affine = self._extract_reduction_count_affine(left, case, accumulator_proof)
        right_count_affine = self._extract_reduction_count_affine(right, case, accumulator_proof)
        if left_count_affine is not None and right_count_affine is not None:
            solved = self._solve_affine_equality(left_count_affine, right_count_affine)
            if solved is not None:
                return solved

        left_addr_affine = self._extract_readonly_address_affine(left, case, accumulator_proof)
        right_addr_affine = self._extract_readonly_address_affine(right, case, accumulator_proof)
        if left_addr_affine is None or right_addr_affine is None:
            return None
        left_base, left_coeff, left_bias = left_addr_affine
        right_base, right_coeff, right_bias = right_addr_affine
        if left_base is None or right_base is None or left_base != right_base:
            return None
        return self._solve_affine_equality(
            (int(left_coeff), int(left_bias)),
            (int(right_coeff), int(right_bias)),
        )

    def _solve_affine_equality(
        self,
        left_affine: tuple[int, int],
        right_affine: tuple[int, int],
    ) -> Optional[int]:
        left_coeff, left_bias = left_affine
        right_coeff, right_bias = right_affine
        coeff_delta = int(left_coeff) - int(right_coeff)
        bias_delta = int(right_bias) - int(left_bias)
        if coeff_delta == 0:
            return None
        if bias_delta % coeff_delta != 0:
            return None
        solved = bias_delta // coeff_delta
        return int(solved) if solved > 0 else None

    def _extract_readonly_address_affine(
        self,
        expr: Optional[Expression],
        case: ReturnCase,
        accumulator_proof,
    ) -> Optional[tuple[Optional[tuple], int, int]]:
        """Return (base_identity, count_coeff_bytes, byte_bias) for address expressions."""

        if expr is None:
            return None
        base_key = self._readonly_pointer_base_identity_key(expr, case, accumulator_proof)
        if base_key is not None:
            return base_key, 0, 0
        if getattr(expr, "expr_type", None) == ExpressionType.CONSTANT:
            const_value = self._exact_reduction_count_constant(expr)
            return (None, 0, int(const_value)) if const_value is not None else None
        if getattr(expr, "expr_type", None) == ExpressionType.INTRINSIC and getattr(expr, "name", None) == "PTRADD":
            operands = list(getattr(expr, "operands", None) or [])
            if len(operands) < 3:
                return None
            base_affine = self._extract_readonly_address_affine(operands[0], case, accumulator_proof)
            index_affine = self._extract_reduction_count_affine(operands[1], case, accumulator_proof)
            scale = self._exact_reduction_count_constant(operands[2])
            if base_affine is None or index_affine is None or scale is None:
                return None
            base, base_coeff, base_bias = base_affine
            index_coeff, index_bias = index_affine
            return (
                base,
                int(base_coeff) + int(index_coeff) * int(scale),
                int(base_bias) + int(index_bias) * int(scale),
            )
        if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP or len(getattr(expr, "operands", None) or []) != 2:
            return None
        operator = getattr(expr, "operator", None)
        left = self._extract_readonly_address_affine(expr.operands[0], case, accumulator_proof)
        right = self._extract_readonly_address_affine(expr.operands[1], case, accumulator_proof)
        if operator == "INT_ADD" and left is not None and right is not None:
            return self._combine_readonly_address_affine(left, right, subtract=False)
        if operator == "INT_SUB" and left is not None and right is not None:
            return self._combine_readonly_address_affine(left, right, subtract=True)
        return None

    def _combine_readonly_address_affine(
        self,
        left: tuple[Optional[tuple], int, int],
        right: tuple[Optional[tuple], int, int],
        *,
        subtract: bool,
    ) -> Optional[tuple[Optional[tuple], int, int]]:
        left_base, left_coeff, left_bias = left
        right_base, right_coeff, right_bias = right
        if left_base is not None and right_base is not None:
            if subtract and left_base == right_base:
                base = None
            else:
                return None
        else:
            base = left_base if left_base is not None else right_base
        sign = -1 if subtract else 1
        return (
            base,
            int(left_coeff) + sign * int(right_coeff),
            int(left_bias) + sign * int(right_bias),
        )

    def _readonly_pointer_base_identity_key(
        self,
        expr: Optional[Expression],
        case: ReturnCase,
        accumulator_proof,
    ) -> Optional[tuple]:
        if expr is None or getattr(expr, "expr_type", None) != ExpressionType.PARAMETER:
            return None
        pointer_ref = getattr(accumulator_proof, "pointer_base_ref", None)
        proof_key = getattr(pointer_ref, "semantic_key", lambda: None)()
        if proof_key is None:
            return None
        expr_keys = set()
        try:
            expr_index = getattr(expr, "value", None)
            if expr_index is not None and int(expr_index) >= 0:
                expr_keys.add(("parameter", int(expr_index)))
        except (TypeError, ValueError):
            pass
        storage_info = getattr(expr, "storage_info", None)
        storage_key_fn = getattr(storage_info, "storage_identity_key", None)
        if callable(storage_key_fn):
            try:
                storage_key = storage_key_fn()
            except (AttributeError, TypeError, ValueError):
                storage_key = None
            if storage_key is not None:
                expr_keys.add(("storage_identity", tuple(storage_key)))
        if proof_key in expr_keys:
            return proof_key
        return None

    def _extract_reduction_count_affine(
        self,
        expr: Optional[Expression],
        case: ReturnCase,
        accumulator_proof,
    ) -> Optional[tuple[int, int]]:
        if expr is None:
            return None
        if self._expression_is_full_reduction_count_view(expr, case, accumulator_proof):
            return 1, 0
        if getattr(expr, "expr_type", None) == ExpressionType.CONSTANT:
            value = self._exact_reduction_count_constant(expr)
            return (0, int(value)) if value is not None else None
        if getattr(expr, "expr_type", None) == ExpressionType.UNARY_OP and len(getattr(expr, "operands", None) or []) == 1:
            operator = getattr(expr, "operator", None)
            if operator in {"INT_ZEXT", "INT_SEXT"}:
                operand = expr.operands[0]
                operand_bits = max(1, int(expression_smt_bit_width(operand) or 0))
                if operand_bits != self._case_reduction_count_bit_width(case, accumulator_proof):
                    return None
                return self._extract_reduction_count_affine(operand, case, accumulator_proof)
            if operator in {"CAST", "COPY"}:
                operand = expr.operands[0]
                expr_bits = max(1, int(expression_smt_bit_width(expr) or 0))
                operand_bits = max(1, int(expression_smt_bit_width(operand) or 0))
                proof_bits = self._case_reduction_count_bit_width(case, accumulator_proof)
                if expr_bits != operand_bits or expr_bits != proof_bits:
                    return None
                return self._extract_reduction_count_affine(expr.operands[0], case, accumulator_proof)
            if operator in {"INT_2COMP", "INT_NEGATE"}:
                operand = self._extract_reduction_count_affine(expr.operands[0], case, accumulator_proof)
                if operand is None:
                    return None
                return -int(operand[0]), -int(operand[1])
            return None
        if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP or len(getattr(expr, "operands", None) or []) != 2:
            return None
        left = self._extract_reduction_count_affine(expr.operands[0], case, accumulator_proof)
        right = self._extract_reduction_count_affine(expr.operands[1], case, accumulator_proof)
        operator = getattr(expr, "operator", None)
        if operator == "INT_ADD" and left is not None and right is not None:
            return int(left[0]) + int(right[0]), int(left[1]) + int(right[1])
        if operator == "INT_SUB" and left is not None and right is not None:
            return int(left[0]) - int(right[0]), int(left[1]) - int(right[1])
        if operator == "INT_MULT":
            left_const = self._exact_reduction_count_constant(expr.operands[0])
            right_const = self._exact_reduction_count_constant(expr.operands[1])
            if left_const is not None and right is not None:
                return int(left_const) * int(right[0]), int(left_const) * int(right[1])
            if right_const is not None and left is not None:
                return int(right_const) * int(left[0]), int(right_const) * int(left[1])
        return None

    def _expression_is_full_reduction_count_view(
        self,
        expr: Optional[Expression],
        case: ReturnCase,
        accumulator_proof,
    ) -> bool:
        if expr is None:
            return False
        if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER:
            expr_bits = max(1, int(expression_smt_bit_width(expr) or 0))
            proof_bits = self._case_reduction_count_bit_width(case, accumulator_proof)
            if expr_bits != proof_bits:
                return False
            return self._parameter_matches_reduction_count_identity(expr, case, accumulator_proof)
        if (
            getattr(expr, "expr_type", None) == ExpressionType.BINARY_OP
            and getattr(expr, "operator", None) == "SUBPIECE"
            and len(getattr(expr, "operands", None) or []) == 2
        ):
            source, offset = expr.operands
            if getattr(offset, "expr_type", None) != ExpressionType.CONSTANT:
                return False
            try:
                if int(getattr(offset, "value", 0) or 0) != 0:
                    return False
            except (TypeError, ValueError):
                return False
            expr_bits = max(1, int(expression_smt_bit_width(expr) or 0))
            proof_bits = self._case_reduction_count_bit_width(case, accumulator_proof)
            if expr_bits != proof_bits:
                return False
            return self._parameter_matches_reduction_count_identity(source, case, accumulator_proof)
        if getattr(expr, "expr_type", None) == ExpressionType.UNARY_OP and len(getattr(expr, "operands", None) or []) == 1:
            operator = getattr(expr, "operator", None)
            if operator in {"CAST", "COPY"}:
                operand = expr.operands[0]
                expr_bits = max(1, int(expression_smt_bit_width(expr) or 0))
                operand_bits = max(1, int(expression_smt_bit_width(operand) or 0))
                proof_bits = self._case_reduction_count_bit_width(case, accumulator_proof)
                if expr_bits != operand_bits or expr_bits != proof_bits:
                    return False
                return self._expression_is_full_reduction_count_view(operand, case, accumulator_proof)
            return False
        return False

    def _parameter_matches_reduction_count_identity(
        self,
        expr: Optional[Expression],
        case: ReturnCase,
        accumulator_proof,
    ) -> bool:
        if expr is None or getattr(expr, "expr_type", None) != ExpressionType.PARAMETER:
            return False
        return self._count_identity_components_compatible(
            self._parameter_expression_storage_identity_key(expr),
            self._parameter_expression_index_identity_key(expr),
            self._reduction_count_storage_identity_key(accumulator_proof),
            self._reduction_count_index_identity_key(accumulator_proof),
        )

    def _case_reduction_count_bit_width(
        self,
        case: ReturnCase,
        accumulator_proof,
    ) -> int:
        proof_bits = self._reduction_count_bit_width(accumulator_proof)
        proof_storage = self._reduction_count_storage_identity_key(accumulator_proof)
        proof_index = self._reduction_count_index_identity_key(accumulator_proof)
        for parameter in getattr(case, "parameters", None) or []:
            if not self._count_identity_components_compatible(
                self._parameter_descriptor_storage_identity_key(parameter),
                self._parameter_descriptor_index_identity_key(parameter),
                proof_storage,
                proof_index,
            ):
                continue
            try:
                size = int(parameter.get("size", 0) or 0)
            except (TypeError, ValueError):
                size = 0
            if size <= 0:
                continue
            candidate_bits = max(1, size * 8)
            if candidate_bits == proof_bits or self._accumulator_proof_supports_count_bit_width(
                case,
                accumulator_proof,
                candidate_bits,
            ):
                return candidate_bits
        return proof_bits

    def _reduction_count_bit_width(self, accumulator_proof) -> int:
        limit_expr = getattr(accumulator_proof, "limit_expr", None)
        return max(1, int(expression_smt_bit_width(limit_expr) or 0))

    def _accumulator_proof_supports_count_bit_width(
        self,
        case: ReturnCase,
        accumulator_proof,
        candidate_bits: int,
    ) -> bool:
        candidate_bits = max(1, int(candidate_bits))
        proof_bits = self._reduction_count_bit_width(accumulator_proof)
        if candidate_bits == proof_bits:
            return True
        if candidate_bits > proof_bits:
            return False
        for expr in self._accumulator_proof_count_surface_expressions(accumulator_proof):
            if self._expression_contains_reduction_count_surface_at_width(
                expr,
                case,
                accumulator_proof,
                candidate_bits,
            ):
                return True
        return False

    def _accumulator_proof_count_surface_expressions(self, accumulator_proof):
        limit_expr = getattr(accumulator_proof, "limit_expr", None)
        if limit_expr is not None:
            yield limit_expr
        for condition in tuple(getattr(accumulator_proof, "guard_constraints", ()) or ()):
            expr = getattr(condition, "expression", condition)
            if expr is not None:
                yield expr

    def _expression_contains_reduction_count_surface_at_width(
        self,
        expr: Optional[Expression],
        case: ReturnCase,
        accumulator_proof,
        width_bits: int,
    ) -> bool:
        if expr is None:
            return False
        expr_bits = max(1, int(expression_smt_bit_width(expr) or 0))
        if (
            expr_bits == int(width_bits)
            and self._parameter_matches_reduction_count_identity(expr, case, accumulator_proof)
        ):
            return True
        if (
            getattr(expr, "expr_type", None) == ExpressionType.BINARY_OP
            and getattr(expr, "operator", None) == "SUBPIECE"
            and len(getattr(expr, "operands", None) or []) == 2
        ):
            source, offset = expr.operands
            try:
                offset_is_low = (
                    getattr(offset, "expr_type", None) == ExpressionType.CONSTANT
                    and int(getattr(offset, "value", 0) or 0) == 0
                )
            except (TypeError, ValueError):
                offset_is_low = False
            if (
                offset_is_low
                and expr_bits == int(width_bits)
                and self._parameter_matches_reduction_count_identity(source, case, accumulator_proof)
            ):
                return True
        if (
            getattr(expr, "expr_type", None) == ExpressionType.UNARY_OP
            and getattr(expr, "operator", None) in {"CAST", "COPY"}
            and len(getattr(expr, "operands", None) or []) == 1
            and expr_bits == int(width_bits)
            and self._parameter_matches_reduction_count_identity(expr.operands[0], case, accumulator_proof)
        ):
            return True
        for operand in getattr(expr, "operands", None) or ():
            if self._expression_contains_reduction_count_surface_at_width(
                operand,
                case,
                accumulator_proof,
                width_bits,
            ):
                return True
        if getattr(expr, "expr_type", None) == ExpressionType.PHI and getattr(expr, "value", None):
            for condition, value in expr.value:
                if condition is not None and self._expression_contains_reduction_count_surface_at_width(
                    getattr(condition, "expression", None),
                    case,
                    accumulator_proof,
                    width_bits,
                ):
                    return True
                if self._expression_contains_reduction_count_surface_at_width(
                    value,
                    case,
                    accumulator_proof,
                    width_bits,
                ):
                    return True
        return False

    def _exact_reduction_count_constant(self, expr: Optional[Expression]) -> Optional[int]:
        if expr is None or getattr(expr, "expr_type", None) != ExpressionType.CONSTANT:
            return None
        try:
            return int(getattr(expr, "value", None))
        except (TypeError, ValueError):
            return None

    def _conditions_with_object_identity_parameter_symbols(
        self,
        conditions: Sequence[Condition],
        parameters: Sequence[Dict[str, Any]] = (),
    ) -> List[Condition]:
        symbol_by_identity: Dict[tuple, str] = {}

        def parameter_symbol(expr: Expression) -> str:
            key = self._parameter_object_identity_key(expr, parameters)
            if key is None:
                key = self._opaque_parameter_object_identity_key(expr)
            symbol = symbol_by_identity.get(key)
            if symbol is None:
                symbol = f"__phase3_param_{len(symbol_by_identity)}"
                symbol_by_identity[key] = symbol
            return symbol

        def clone_value(value):
            if isinstance(value, Expression):
                return clone_expr(value)
            if isinstance(value, Condition):
                return Condition(clone_expr(value.expression), value.negated)
            if isinstance(value, tuple):
                return tuple(clone_value(item) for item in value)
            if isinstance(value, list):
                return [clone_value(item) for item in value]
            return value

        def clone_expr(expr: Expression) -> Expression:
            expr_type = getattr(expr, "expr_type", None)
            expr_kind = getattr(expr_type, "__class__", None)
            if expr_type is not None and expr_kind is not None and expr_type == expr_kind.PARAMETER:
                return expr.clone_with(name=parameter_symbol(expr), runtime_ref=None)
            cloned_operands = [clone_expr(operand) for operand in (getattr(expr, "operands", None) or [])]
            cloned_value = clone_value(getattr(expr, "value", None))
            return expr.clone_with(operands=cloned_operands, value=cloned_value)

        return [
            Condition(clone_expr(condition.expression), bool(getattr(condition, "negated", False)))
            for condition in conditions or []
            if condition is not None and getattr(condition, "expression", None) is not None
        ]

    def _parameter_object_identity_key(
        self,
        expr: Expression,
        parameters: Sequence[Dict[str, Any]] = (),
    ) -> Optional[tuple]:
        size_bits = max(1, int(expression_smt_bit_width(expr) or getattr(expr, "get_bit_width", lambda: 0)() or 0))
        try:
            index = int(getattr(expr, "value", -1))
        except (TypeError, ValueError):
            index = -1
        if index >= 0:
            return ("parameter_index", index, size_bits)
        storage_info = getattr(expr, "storage_info", None)
        storage_key_fn = getattr(storage_info, "storage_identity_key", None)
        if callable(storage_key_fn):
            storage_key = storage_key_fn()
            if storage_key is not None:
                return ("parameter_storage", storage_key, size_bits)
        return None

    def _opaque_parameter_object_identity_key(self, expr: Expression) -> tuple:
        size_bits = max(1, int(expression_smt_bit_width(expr) or getattr(expr, "get_bit_width", lambda: 0)() or 0))
        return ("unresolved_parameter_object", id(expr), size_bits)

    def _extract_readonly_reduction_terms_from_expression(
        self,
        expr: Optional[Expression],
        parameters: Sequence[Dict[str, Any]],
        pointer_base_ref,
        *,
        program_is_big_endian: Optional[bool] = None,
    ) -> Optional[tuple[ReadonlyReductionTermRef, ...]]:
        extracted = self._extract_readonly_reduction_terms_and_bias_from_expression(
            expr,
            parameters,
            pointer_base_ref,
            program_is_big_endian=program_is_big_endian,
        )
        if extracted is None:
            return None
        terms, bias = extracted
        if int(bias) != 0:
            return None
        return terms

    def _extract_readonly_reduction_terms_and_bias_from_expression(
        self,
        expr: Optional[Expression],
        parameters: Sequence[Dict[str, Any]],
        pointer_base_ref,
        *,
        program_is_big_endian: Optional[bool] = None,
    ) -> Optional[tuple[tuple[ReadonlyReductionTermRef, ...], int]]:
        if expr is None or pointer_base_ref is None:
            return None
        extracted: List[ReadonlyReductionTermRef] = []
        constant_bias = 0
        for sign, term in self._flatten_readonly_add_terms(expr):
            if getattr(term, "expr_type", None) == ExpressionType.CONSTANT:
                value = self._raw_constant_value(term)
                if value is None:
                    return None
                constant_bias += int(sign) * int(value)
                continue
            if sign != 1:
                return None
            descriptor = self._extract_readonly_reduction_term_descriptor(
                term,
                parameters,
                pointer_base_ref,
                program_is_big_endian=program_is_big_endian,
            )
            if descriptor is None:
                return None
            extracted.append(descriptor)
        if not extracted:
            return None
        extracted.sort(key=lambda item: (int(item.byte_offset), int(item.access_size)))
        return tuple(extracted), int(constant_bias)

    def _normalize_constant_bias(self, value: int, result_size: int) -> int:
        bits = max(1, int(result_size or 0)) * 8
        return int(value) % (1 << bits)

    def _flatten_readonly_add_terms(
        self,
        expr: Expression,
        sign: int = 1,
    ) -> List[tuple[int, Expression]]:
        if getattr(expr, "expr_type", None) == ExpressionType.BINARY_OP and len(getattr(expr, "operands", []) or []) == 2:
            if getattr(expr, "operator", None) == "INT_ADD":
                return self._flatten_readonly_add_terms(expr.operands[0], sign) + self._flatten_readonly_add_terms(
                    expr.operands[1],
                    sign,
                )
            if getattr(expr, "operator", None) == "INT_SUB":
                return self._flatten_readonly_add_terms(expr.operands[0], sign) + self._flatten_readonly_add_terms(
                    expr.operands[1],
                    -sign,
                )
        return [(sign, expr)]

    def _extract_readonly_reduction_term_descriptor(
        self,
        expr: Optional[Expression],
        parameters: Sequence[Dict[str, Any]],
        pointer_base_ref,
        *,
        lsb_byte_offset: int = 0,
        narrowed_size: Optional[int] = None,
        program_is_big_endian: Optional[bool] = None,
    ) -> Optional[ReadonlyReductionTermRef]:
        if expr is None:
            return None

        if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
            if expr.operator == "INT_SEXT":
                return None
            if expr.operator in {"INT_ZEXT", "CAST", "COPY"}:
                return self._extract_readonly_reduction_term_descriptor(
                    expr.operands[0],
                    parameters,
                    pointer_base_ref,
                    lsb_byte_offset=lsb_byte_offset,
                    narrowed_size=narrowed_size,
                    program_is_big_endian=program_is_big_endian,
                )

        if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
            if expr.operator == "SUBPIECE":
                byte_offset = self._raw_constant_value(expr.operands[1])
                if byte_offset is None or byte_offset < 0:
                    return None
                return self._extract_readonly_reduction_term_descriptor(
                    expr.operands[0],
                    parameters,
                    pointer_base_ref,
                    lsb_byte_offset=lsb_byte_offset + int(byte_offset),
                    narrowed_size=max(1, int(expr.size or 0)),
                    program_is_big_endian=program_is_big_endian,
                )
            if expr.operator == "INT_RIGHT":
                shift_bits = self._raw_constant_value(expr.operands[1])
                if shift_bits is None or shift_bits < 0 or (int(shift_bits) % 8) != 0:
                    return None
                return self._extract_readonly_reduction_term_descriptor(
                    expr.operands[0],
                    parameters,
                    pointer_base_ref,
                    lsb_byte_offset=lsb_byte_offset + (int(shift_bits) // 8),
                    narrowed_size=narrowed_size or max(1, int(expr.size or 0)),
                    program_is_big_endian=program_is_big_endian,
                )
            if expr.operator == "INT_AND":
                mask_width = self._low_mask_width_bytes(expr.operands[0], expr.operands[1])
                value_expr = expr.operands[0]
                if mask_width is None:
                    mask_width = self._low_mask_width_bytes(expr.operands[1], expr.operands[0])
                    value_expr = expr.operands[1]
                if mask_width is not None:
                    return self._extract_readonly_reduction_term_descriptor(
                        value_expr,
                        parameters,
                        pointer_base_ref,
                        lsb_byte_offset=lsb_byte_offset,
                        narrowed_size=narrowed_size or mask_width,
                        program_is_big_endian=program_is_big_endian,
                    )

        if expr.expr_type != ExpressionType.MEMORY or not expr.operands:
            return None
        load_size = max(1, int(expr.size or 0))
        access_size = max(1, int(narrowed_size or load_size))
        if lsb_byte_offset < 0 or access_size > load_size or lsb_byte_offset + access_size > load_size:
            return None
        if (int(lsb_byte_offset) != 0 or access_size != load_size) and program_is_big_endian is None:
            return None
        location = canonicalize_location(expr.operands[0], parameters, size=load_size)
        if location is None:
            return None
        base_ref = getattr(location, "base_ref", None)
        if base_ref is None:
            return None
        base_key = getattr(base_ref, "semantic_key", lambda: None)()
        proof_base_key = getattr(pointer_base_ref, "semantic_key", lambda: None)()
        if base_key is None or proof_base_key is None or base_key != proof_base_key:
            return None
        if program_is_big_endian is True:
            byte_offset = int(location.offset) + (load_size - access_size - int(lsb_byte_offset))
        else:
            byte_offset = int(location.offset) + int(lsb_byte_offset)
        return ReadonlyReductionTermRef(byte_offset=byte_offset, access_size=access_size)

    def _raw_constant_value(self, expr: Optional[Expression]) -> Optional[int]:
        if expr is None or getattr(expr, "expr_type", None) != ExpressionType.CONSTANT:
            return None
        try:
            return int(expr.value)
        except (TypeError, ValueError):
            return None

    def _low_mask_width_bytes(
        self,
        value_expr: Optional[Expression],
        mask_expr: Optional[Expression],
    ) -> Optional[int]:
        del value_expr
        mask = self._raw_constant_value(mask_expr)
        if mask is None or mask < 0:
            return None
        width = 0
        current = int(mask)
        while current & 0xFF == 0xFF:
            width += 1
            current >>= 8
        if current != 0 or width <= 0:
            return None
        return width

    def _readonly_reduction_values_equivalent(
        self,
        left: Expression,
        right: Expression,
    ) -> bool:
        return self._intrinsic_runtime_values_equivalent(left, right)

    def _expressions_share_object_centric_structure(
        self,
        left: Optional[Expression],
        right: Optional[Expression],
    ) -> bool:
        if left is None or right is None:
            return False
        if left.expr_type == ExpressionType.INTRINSIC or right.expr_type == ExpressionType.INTRINSIC:
            return self._intrinsic_runtime_values_equivalent(left, right)
        equivalent, _reason = are_structurally_equivalent(left, right, debug=self.debug)
        return equivalent

    def _try_normalization_equivalence(
        self,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        param_replace_fn1,
        param_replace_fn2,
        pair_id: str
    ) -> QueryResult:
        return try_normalization_equivalence(
            self,
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            pair_id,
            normalize_expression_fn=normalize_expression,
            normalization_context_cls=NormalizationContext,
            sign_facts_cls=SignFacts,
            extract_min_excluded_params_fn=extract_min_excluded_params,
            extract_upper_bound_facts_fn=extract_upper_bound_facts,
            extract_sign_facts_fn=extract_sign_facts,
            contains_udiv_fn=contains_udiv,
            normalize_udiv_with_guard_fn=normalize_udiv_with_guard,
            are_structurally_equivalent_fn=are_structurally_equivalent,
            get_structural_summary_fn=get_structural_summary,
            normalization_rule_application_cls=NormalizationRuleApplication,
        )

    def _try_solver_proven_rewrite_equivalence(
        self,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        param_replace_fn1,
        param_replace_fn2,
        pair_id: str,
    ) -> QueryResult:
        return try_solver_proven_rewrite_equivalence(
            self,
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            pair_id,
        )

    def _solve_query_internal(
        self,
        query: str,
        pair_id: str,
        stage: str = "full",
        use_hard_timeout: bool = False
    ) -> QueryResult:
        return solve_query_internal(
            self,
            query,
            pair_id,
            stage=stage,
            use_hard_timeout=use_hard_timeout,
        )

    def _build_condition_only_query(
        self,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        param_replace_fn1,
        param_replace_fn2,
        pair_id: str
    ) -> str:
        return build_condition_only_query(
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            pair_id,
        )

    def _save_unknown_query(self, query: str, pair_id: str, stage: str) -> None:
        save_unknown_query(self._debug_print, query, pair_id, stage, self.unknown_query_dir)

    def _extract_return_cases(
        self,
        analysis: FunctionReturnAnalysis
    ) -> List[ReturnCase]:
        return extract_return_cases(
            analysis,
            normalization_settings=self.normalization_settings,
        )

    def _build_single_case_condition_query(
        self,
        base_ctx: Dict[str, Any],
        case: ReturnCase,
        param_replace_fn,
        label: str,
    ) -> str:
        return build_single_case_condition_query(
            base_ctx,
            case,
            param_replace_fn,
            label,
        )

    def _prune_unreachable_cases(
        self,
        cases: List[ReturnCase],
        base_ctx: Dict[str, Any],
        param_replace_fn,
        label: str,
    ) -> List[ReturnCase]:
        if not cases:
            return cases

        reachable_cases: List[ReturnCase] = []
        pruned_count = 0

        for case in cases:
            if ConditionSimplifier.is_contradiction(case.conditions):
                pruned_count += 1
                self._debug_print(
                    f"  {label}[{case.index}]: pruned by contradiction precheck"
                )
                continue

            if not self._case_contains_unresolved_expression(
                case,
                own_render_fn=param_replace_fn,
                base_ctx=base_ctx,
                query_label=f"{label}[{case.index}]",
            ):
                reachable_cases.append(case)
                continue

            if not case.conditions:
                reachable_cases.append(case)
                continue

            if any(
                self._expression_contains_unresolved(cond.expression)
                for cond in case.conditions
            ):
                reachable_cases.append(case)
                continue

            query = self._build_single_case_condition_query(
                base_ctx,
                case,
                param_replace_fn,
                label,
            )
            result = self._solve_query_internal(
                query,
                f"{label}[{case.index}]",
                stage="case-feasible",
                use_hard_timeout=False,
            )

            if result.is_equivalent is True:
                pruned_count += 1
                self._debug_print(
                    f"  {label}[{case.index}]: pruned as unreachable by SMT"
                )
                continue

            reachable_cases.append(case)

        if reachable_cases:
            return reachable_cases

        if pruned_count > 0:
            self._debug_print(
                f"  {label}: pruning removed every case; keeping originals conservatively"
            )
        return cases

    def _build_pair_query(
        self,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        param_replace_fn1,
        param_replace_fn2,
        pair_id: str
    ) -> str:
        return build_pair_query(
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            pair_id,
        )

    def _build_normalized_inequality_query(
        self,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        param_replace_fn1,
        param_replace_fn2,
        value1_norm_expr,
        value2_norm_expr,
        value1_smt_norm: str,
        value2_smt_norm: str,
        pair_id: str
    ) -> str:
        return build_normalized_inequality_query(
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            value1_norm_expr,
            value2_norm_expr,
            value1_smt_norm,
            value2_smt_norm,
            pair_id,
        )

    def _create_aggregate_result(
        self,
        is_equivalent: Optional[bool],
        elapsed_time: float,
        counterexample_raw: Optional[Dict]
    ) -> ParallelResult:
        status_map = {
            True: SolverStatus.UNSAT,
            False: SolverStatus.SAT,
            None: SolverStatus.UNKNOWN,
        }
        status = status_map.get(is_equivalent, SolverStatus.UNKNOWN)
        solver_result = SolverResult(
            solver_name="pairwise_aggregate",
            status=status,
            elapsed_time=elapsed_time,
            model=counterexample_raw,
        )
        return ParallelResult(results=[solver_result])

    def _cases_are_contradictory(
        self,
        case1: ReturnCase,
        case2: ReturnCase,
    ) -> bool:
        combined_conditions = list(case1.conditions) + list(case2.conditions)
        if not combined_conditions:
            return False
        identity_conditions = self._conditions_with_object_identity_parameter_symbols(
            combined_conditions,
            list(getattr(case1, "parameters", None) or [])
            + list(getattr(case2, "parameters", None) or []),
        )
        solver_result = ConditionSMTOracle.conjunction_is_unsat(identity_conditions)
        if solver_result is not None:
            return solver_result
        return ConditionSimplifier.object_centric_is_contradiction(identity_conditions)

    def _case_contains_unresolved_expression(
        self,
        case: ReturnCase,
        extra_conditions: Optional[List[Condition]] = None,
        *,
        own_render_fn=None,
        extra_render_fn=None,
        base_ctx: Optional[Dict[str, Any]] = None,
        query_label: str = "case",
    ) -> bool:
        return self._get_expression_safety_checker(base_ctx).case_contains_unresolved(
            case,
            own_render_fn=own_render_fn,
            extra_conditions=extra_conditions,
            extra_render_fn=extra_render_fn,
            query_label=query_label,
        )

    def _case_value_contains_unresolved(
        self,
        case: ReturnCase,
        extra_conditions: Optional[List[Condition]] = None,
        *,
        own_render_fn=None,
        extra_render_fn=None,
        base_ctx: Optional[Dict[str, Any]] = None,
        query_label: str = "value",
    ) -> bool:
        return self._get_expression_safety_checker(base_ctx).value_contains_unresolved(
            case,
            own_render_fn=own_render_fn,
            extra_conditions=extra_conditions,
            extra_render_fn=extra_render_fn,
            query_label=query_label,
        )

    def _get_expression_safety_checker(
        self,
        base_ctx: Optional[Dict[str, Any]] = None,
    ) -> ExpressionSafetyChecker:
        active = getattr(self, "_active_safety_checker", None)
        if active is not None:
            return active
        return ExpressionSafetyChecker(
            solver_runner=self.solver_runner,
            debug_print=self._debug_print,
            per_query_timeout=self.per_query_timeout,
            base_ctx=base_ctx,
        )

    def _expression_contains_unresolved(self, expr) -> bool:
        if expr is None:
            return False

        if expr.expr_type == ExpressionType.UNKNOWN:
            return True
        if expression_contains_unsupported_smt_ops(expr):
            return True

        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None and self._expression_contains_unresolved(cond.expression):
                    return True
                if self._expression_contains_unresolved(value):
                    return True
            return False

        for operand in getattr(expr, "operands", []) or []:
            if self._expression_contains_unresolved(operand):
                return True

        return False

    def _create_empty_result(self) -> StrategyResult:
        return StrategyResult(
            is_equivalent=None,
            solver_results=ParallelResult(results=[]),
            total_pairs=0,
            unsat_pairs=0,
            sat_pairs=0,
            unknown_pairs=0,
            error_pairs=0,
            unknown_reasons=[
                make_unknown_reason(
                    UnknownReasonId.EMPTY_RETURN_CASES,
                    stage="S_PAIRWISE",
                )
            ],
        )

    def _debug_symbol_mapping(self, base_ctx: Dict[str, Any]) -> None:
        self._debug_print("Symbol replacement mapping:")
        self._debug_print("  Function 1:")
        for param in base_ctx["params1"]:
            self._debug_print(f"    {param.original_name} -> {param.smt_name}")
        for var in base_ctx.get("extra_vars1", []):
            self._debug_print(f"    {var.original_name} -> {var.smt_name}")
        self._debug_print("  Function 2:")
        for param in base_ctx["params2"]:
            self._debug_print(f"    {param.original_name} -> {param.smt_name}")
        for var in base_ctx.get("extra_vars2", []):
            self._debug_print(f"    {var.original_name} -> {var.smt_name}")

    def _rewrite_cases_with_parameter_fragments(
        self,
        cases: List[ReturnCase],
        extra_vars: List[Any],
    ) -> None:
        fragment_map = {}
        for extra in extra_vars or []:
            analysis = getattr(extra, "analysis", None)
            if analysis is None or not analysis.is_parameter_fragment() or analysis.fragment_info is None:
                continue
            fragment_map[extra.original_name] = analysis.fragment_info

        if not fragment_map:
            return

        for case in cases:
            changed = False

            rewritten_conditions: List[Condition] = []
            for cond in case.conditions:
                rewritten_expr = self._rewrite_expr_with_parameter_fragments(
                    cond.expression,
                    fragment_map,
                )
                rewritten_conditions.append(Condition(rewritten_expr, cond.negated))
                changed = changed or (rewritten_expr is not cond.expression)

            rewritten_value = self._rewrite_expr_with_parameter_fragments(
                case.value_expr,
                fragment_map,
            )
            changed = changed or (rewritten_value is not case.value_expr)

            if not changed:
                continue

            case.update_conditions(rewritten_conditions, summary_conditions=rewritten_conditions)
            case.value_expr = rewritten_value
            case.normalized_value_expr = normalize_expression(
                rewritten_value,
                NormalizationContext(settings=self.normalization_settings),
            )
            case._value_smt_cache.clear()

    def _rewrite_expr_with_parameter_fragments(
        self,
        expr: Expression,
        fragment_map: Dict[str, Any],
    ) -> Expression:
        if expr is None:
            return expr

        if expr.expr_type == ExpressionType.PHI and expr.value:
            changed = False
            branches = []
            for cond, value in expr.value:
                rewritten_cond = None
                if cond is not None:
                    rewritten_cond_expr = self._rewrite_expr_with_parameter_fragments(
                        cond.expression,
                        fragment_map,
                    )
                    rewritten_cond = Condition(rewritten_cond_expr, cond.negated)
                    changed = changed or (rewritten_cond_expr is not cond.expression)
                rewritten_value = self._rewrite_expr_with_parameter_fragments(value, fragment_map)
                changed = changed or (rewritten_value is not value)
                branches.append((rewritten_cond, rewritten_value))

            if not changed:
                return expr
            rebuilt = Expression.phi(branches)
            rebuilt.size = expr.size
            return rebuilt

        operands = getattr(expr, "operands", None) or []
        rewritten_operands = [
            self._rewrite_expr_with_parameter_fragments(operand, fragment_map)
            for operand in operands
        ]
        operands_changed = any(new is not old for new, old in zip(rewritten_operands, operands))

        candidate = expr
        if operands_changed:
            candidate = Expression(
                expr_type=expr.expr_type,
                value=expr.value,
                operator=expr.operator,
                operands=rewritten_operands,
                size=expr.size,
                name=expr.name,
                data_type=expr.data_type,
                data_type_obj=getattr(expr, "data_type_obj", None),
                storage_info=expr.storage_info,
                read_order_key=expr.read_order_key,
                runtime_ref=getattr(expr, "runtime_ref", None),
                opcode=getattr(expr, "opcode", None),
            )

        collapsed = self._collapse_parameter_fragment_extension(candidate, fragment_map)
        return collapsed

    def _collapse_parameter_fragment_extension(
        self,
        expr: Expression,
        fragment_map: Dict[str, Any],
    ) -> Expression:
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP:
            return expr

        if expr.operator == "PIECE" and len(expr.operands) == 2:
            high, low = expr.operands
            collapsed = self._build_fragment_extension_expr(high, low, fragment_map)
            if collapsed is not None:
                return collapsed
            return expr

        if expr.operator != "INT_OR" or len(expr.operands) != 2:
            return expr

        left, right = expr.operands
        collapsed = self._match_shift_or_fragment_expr(left, right, fragment_map)
        if collapsed is not None:
            return collapsed
        collapsed = self._match_shift_or_fragment_expr(right, left, fragment_map)
        if collapsed is not None:
            return collapsed
        return expr

    def _match_shift_or_fragment_expr(
        self,
        shifted_expr: Expression,
        low_expr: Expression,
        fragment_map: Dict[str, Any],
    ) -> Optional[Expression]:
        if (
            shifted_expr.expr_type != ExpressionType.BINARY_OP
            or shifted_expr.operator != "INT_LEFT"
            or len(shifted_expr.operands) != 2
        ):
            return None

        shift_amount = shifted_expr.operands[1]
        if shift_amount.expr_type != ExpressionType.CONSTANT:
            return None

        return self._build_fragment_extension_expr(
            shifted_expr.operands[0],
            low_expr,
            fragment_map,
            expected_shift_bits=int(shift_amount.value),
        )

    def _build_fragment_extension_expr(
        self,
        high_expr: Expression,
        low_expr: Expression,
        fragment_map: Dict[str, Any],
        expected_shift_bits: Optional[int] = None,
    ) -> Optional[Expression]:
        if high_expr.expr_type != ExpressionType.VARIABLE or not high_expr.name:
            return None

        fragment_info = fragment_map.get(high_expr.name)
        if fragment_info is None:
            return None

        if low_expr.expr_type not in {ExpressionType.PARAMETER, ExpressionType.VARIABLE}:
            return None
        if low_expr.name != fragment_info.parent_param_name:
            return None

        if expected_shift_bits is not None and expected_shift_bits != fragment_info.parent_param_bit_width:
            return None

        ext_op = "INT_SEXT" if fragment_info.extension_type.name == "SIGN_EXTEND" else "INT_ZEXT"
        rebuilt = Expression.unary_op(ext_op, low_expr)
        rebuilt.size = max(1, fragment_info.base_register_size_bits // 8)
        rebuilt.data_type = getattr(low_expr, "data_type", None)
        return rebuilt
