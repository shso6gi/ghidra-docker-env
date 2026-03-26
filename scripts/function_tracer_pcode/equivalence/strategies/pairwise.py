# -*- coding: utf-8 -*-
"""Pairwise戦略（分岐ペア分割方式・二段階チェック対応）"""

from typing import Any, Dict, List, Optional
import time

from ...model import FunctionReturnAnalysis
from ...analysis.condition.simplifier import ConditionSimplifier
from ...smt import ParallelResult, SolverResult, SolverStatus
from .base import CheckStrategy, StrategyResult
from .pairwise_models import QueryResult, ReturnCase
from .pairwise_normalization import try_normalization_equivalence
from .pairwise_query_builder import (
    build_condition_only_query,
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
from ..formula.symbol_replace import build_symbol_replacer
from ..normalize import (
    SignFacts,
    normalize_expression,
    NormalizationContext,
    extract_min_excluded_params,
    extract_upper_bound_facts,
    extract_sign_facts,
    normalize_udiv_with_guard,
    contains_udiv,
    are_structurally_equivalent,
    get_structural_summary,
)
from ..debug_trace import NormalizationRuleApplication


class PairwiseStrategy(CheckStrategy):
    """
    Pairwise戦略（分岐ペア分割方式・二段階チェック）

    各ペア(i,j)に対して：
    1. Stage 1: 条件のみチェック（C1_i ∧ C2_j）
    2. Stage 2: 値不等式を追加してチェック（C1_i ∧ C2_j ∧ V1_i≠V2_j）
    3. Stage 3: 正規化 fallback
    """

    def __init__(self, formula_builder, solver_runner, debug: bool = False):
        super().__init__(formula_builder, solver_runner, debug)
        self.per_query_timeout = 5
        self.per_query_timeout_hard = 30
        self.save_unknown_queries = False
        self.unknown_query_dir = "/tmp"

    def check(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        save_formula: bool = False
    ) -> StrategyResult:
        start_time = time.time()

        cases1 = self._extract_return_cases(analysis1)
        cases2 = self._extract_return_cases(analysis2)
        total_pairs = len(cases1) * len(cases2)

        self._debug_print("=" * 60)
        self._debug_print("Pairwise strategy (two-stage check):")
        self._debug_print(f"  Function 1: {len(cases1)} return cases")
        self._debug_print(f"  Function 2: {len(cases2)} return cases")
        self._debug_print(f"  Total pairs to check: {total_pairs}")
        self._debug_print(f"  Per-query timeout (stage1): {self.per_query_timeout}s")
        self._debug_print(f"  Per-query timeout (stage2 hard): {self.per_query_timeout_hard}s")
        self._debug_print("=" * 60)

        if total_pairs == 0:
            self._debug_print("No return cases to check")
            return self._create_empty_result()

        base_ctx = self.formula_builder.build_base_context(analysis1, analysis2)
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

        unsat_count = 0
        sat_count = 0
        unknown_count = 0
        error_count = 0
        sat_pair_info = None
        counterexample_raw = None
        last_formula = None
        all_normalization_rules = []
        normalization_stats = {
            "timeout_fallback_attempts": 0,
            "changed_pairs": 0,
            "no_change_pairs": 0,
            "unsat_results": 0,
            "sat_results": 0,
            "unknown_results": 0,
        }
        self._active_normalization_stats = normalization_stats

        for i, case1 in enumerate(cases1):
            for j, case2 in enumerate(cases2):
                pair_id = f"({i},{j})"
                if self._cases_are_contradictory(case1, case2):
                    unsat_count += 1
                    if self.debug and (unsat_count % 10 == 0 or unsat_count <= 5):
                        self._debug_print(
                            f"  Pair {pair_id}: CONTRADICTION PRECHECK -> UNSAT ({unsat_count}/{total_pairs})"
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
                    if self.debug and (unsat_count % 10 == 0 or unsat_count <= 5):
                        self._debug_print(f"  Pair {pair_id}: UNSAT ({unsat_count}/{total_pairs})")
                    continue

                unknown_count += 1
                self._debug_print(f"  Pair {pair_id}: final result UNKNOWN/TIMEOUT")

            if sat_count > 0:
                break

        elapsed_time = time.time() - start_time
        if sat_count > 0:
            final_is_equiv = False
            self._debug_print("=" * 60)
            self._debug_print("Result: NOT EQUIVALENT (found SAT pair)")
        elif unknown_count > 0:
            final_is_equiv = None
            self._debug_print("=" * 60)
            self._debug_print(f"Result: UNKNOWN (timeout/unknown in {unknown_count} pairs)")
        elif unsat_count == total_pairs:
            final_is_equiv = True
            self._debug_print("=" * 60)
            self._debug_print("Result: EQUIVALENT (all pairs UNSAT)")
        else:
            final_is_equiv = None
            error_count = total_pairs - unsat_count - sat_count - unknown_count
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
            )
        finally:
            self._active_normalization_stats = None

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
        return extract_return_cases(analysis)

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
        return ConditionSimplifier.is_contradiction(combined_conditions)

    def _create_empty_result(self) -> StrategyResult:
        return StrategyResult(
            is_equivalent=None,
            solver_results=ParallelResult(results=[]),
            total_pairs=0,
            unsat_pairs=0,
            sat_pairs=0,
            unknown_pairs=0,
            error_pairs=0,
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
