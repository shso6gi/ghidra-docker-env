# -*- coding: utf-8 -*-
"""Pairwise戦略（分岐ペア分割方式・二段階チェック対応）"""

from typing import Any, Dict, List, Optional, Sequence
import time

from ...model import (
    COUNTED_LOOP_SUM_OPCODE,
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
)
from ...model.render_smt import (
    collect_intrinsic_smt_declarations,
    expression_contains_unsupported_smt_ops,
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
from ..param_semantics import infer_parameter_semantics
from ..semantic_width import normalize_analysis_semantic_width
from ..debug_trace import NormalizationRuleApplication


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

        base_ctx = self.formula_builder.build_base_context(
            solver_analysis1,
            solver_analysis2,
        )
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
        sat_unsafety_reasons.extend(
            self._collect_return_coverage_unsafety_reasons(
                base_ctx,
                cases1,
                cases2,
                symbol_replace_fn1,
                symbol_replace_fn2,
            )
        )
        if "function1:return_coverage_gap" in sat_unsafety_reasons:
            if "return_case_coverage_gap" not in analysis1.analysis_notes:
                analysis1.analysis_notes.append("return_case_coverage_gap")
        if "function2:return_coverage_gap" in sat_unsafety_reasons:
            if "return_case_coverage_gap" not in analysis2.analysis_notes:
                analysis2.analysis_notes.append("return_case_coverage_gap")
        total_pairs = len(cases1) * len(cases2)

        if self._cases_form_equivalent_partition(
            cases1,
            cases2,
            base_ctx=base_ctx,
            render_fn1=symbol_replace_fn1,
            render_fn2=symbol_replace_fn2,
            sat_unsafety_reasons=sat_unsafety_reasons,
        ):
            elapsed_time = time.time() - start_time
            self._debug_print("=" * 60)
            self._debug_print("Result: EQUIVALENT (object-centric return partition match)")
            self._debug_print(f"  Total pairs: {total_pairs}")
            self._debug_print("=" * 60)
            aggregate_result = self._create_aggregate_result(
                True,
                elapsed_time,
                None,
            )
            try:
                return StrategyResult(
                    is_equivalent=True,
                    solver_results=aggregate_result,
                    smt_formula=None,
                    counterexample_raw=None,
                    return_var1="return_1",
                    return_var2="return_2",
                    constrained_fragments=base_ctx.get("constrained_fragments", []),
                    total_pairs=total_pairs,
                    unsat_pairs=total_pairs,
                    sat_pairs=0,
                    unknown_pairs=0,
                    error_pairs=0,
                    sat_pair_info=None,
                    normalization_rules=[],
                    pairwise_debug_stats={
                        "solver_proven_rewrite_attempts": 0,
                        "solver_proven_rewrite_successes": 0,
                        "solver_proven_rewrite_failures": 0,
                        "timeout_fallback_attempts": 0,
                        "changed_pairs": 0,
                        "no_change_pairs": 0,
                        "unsat_results": total_pairs,
                        "sat_results": 0,
                        "unknown_results": 0,
                    },
                )
            finally:
                self._active_safety_checker = None
                self._active_normalization_stats = None

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
                if self._cases_have_equivalent_runtime_reductions(case1, case2):
                    unsat_count += 1
                    if self.debug and (unsat_count % 10 == 0 or unsat_count <= 5):
                        self._debug_print(
                            f"  Pair {pair_id}: object-centric readonly reduction match -> UNSAT "
                            f"({unsat_count}/{total_pairs})"
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
            self._active_safety_checker = None
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

    def _cases_have_equivalent_runtime_reductions(
        self,
        case1: ReturnCase,
        case2: ReturnCase,
    ) -> bool:
        return self._intrinsic_runtime_values_equivalent(
            case1.value_expr,
            case2.value_expr,
            left_case=case1,
            right_case=case2,
        )

    def _cases_form_equivalent_partition(
        self,
        left_cases: Sequence[ReturnCase],
        right_cases: Sequence[ReturnCase],
        *,
        base_ctx: Dict[str, Any],
        render_fn1,
        render_fn2,
        sat_unsafety_reasons: Sequence[str],
    ) -> bool:
        if sat_unsafety_reasons:
            return False
        if not left_cases or not right_cases:
            return False
        if len(left_cases) != len(right_cases):
            return False

        left_unmatched = list(left_cases)
        right_unmatched = list(right_cases)
        if any(
            self._case_partition_contains_unresolved(
                case,
                render_fn=render_fn1,
                base_ctx=base_ctx,
                label=f"partition:left[{case.index}]",
            )
            for case in left_unmatched
        ):
            return False
        if any(
            self._case_partition_contains_unresolved(
                case,
                render_fn=render_fn2,
                base_ctx=base_ctx,
                label=f"partition:right[{case.index}]",
            )
            for case in right_unmatched
        ):
            return False

        matched_right: set[int] = set()
        for left_case in left_unmatched:
            candidate_index: Optional[int] = None
            for idx, right_case in enumerate(right_unmatched):
                if idx in matched_right:
                    continue
                if not self._cases_have_equivalent_summary_conditions(left_case, right_case):
                    continue
                if not self._case_values_share_partition_semantics(left_case, right_case):
                    continue
                if candidate_index is not None:
                    return False
                candidate_index = idx
            if candidate_index is None:
                return False
            matched_right.add(candidate_index)

        return len(matched_right) == len(right_unmatched)

    def _case_partition_contains_unresolved(
        self,
        case: ReturnCase,
        *,
        render_fn,
        base_ctx: Dict[str, Any],
        label: str,
    ) -> bool:
        if self._case_contains_unresolved_expression(
            case,
            own_render_fn=render_fn,
            base_ctx=base_ctx,
            query_label=label,
        ):
            return True
        summary_conditions = case.summary_conditions if case.summary_conditions is not None else case.conditions
        if summary_conditions is case.conditions:
            return False
        summary_case = ReturnCase(
            index=case.index,
            conditions=list(summary_conditions or []),
            value_expr=case.value_expr,
            return_info=case.return_info,
            normalized_value_expr=case.normalized_value_expr,
            return_type=case.return_type,
            return_type_obj=case.return_type_obj,
            source_indices=list(case.source_indices),
            parameters=list(case.parameters or []),
            effect_summary=case.effect_summary,
            comparison_surface=case.comparison_surface,
            summary_conditions=list(summary_conditions or []),
        )
        return self._case_contains_unresolved_expression(
            summary_case,
            own_render_fn=render_fn,
            base_ctx=base_ctx,
            query_label=f"{label}:summary",
        )

    def _case_values_share_partition_semantics(
        self,
        left_case: ReturnCase,
        right_case: ReturnCase,
    ) -> bool:
        if self._cases_have_equivalent_runtime_reductions(left_case, right_case):
            return True
        left_value = getattr(left_case, "normalized_value_expr", None) or left_case.value_expr
        right_value = getattr(right_case, "normalized_value_expr", None) or right_case.value_expr
        equivalent, _reason = are_structurally_equivalent(left_value, right_value, debug=False)
        return equivalent

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
        if getattr(left, "opcode", None) != getattr(right, "opcode", None):
            return False
        if (getattr(left, "name", None) or "") != (getattr(right, "name", None) or ""):
            return False
        refs_equivalent, requires_guard_equivalence = self._runtime_refs_share_shortcut_semantics(
            getattr(left, "runtime_ref", None),
            getattr(right, "runtime_ref", None),
        )
        if not refs_equivalent:
            if self._counted_loop_values_are_provably_equivalent(
                left,
                right,
                left_case=left_case,
                right_case=right_case,
            ):
                return True
            return False
        if requires_guard_equivalence and (
            left_case is None
            or right_case is None
            or not self._cases_have_equivalent_summary_conditions(left_case, right_case)
        ):
            if self._counted_loop_values_are_provably_equivalent(
                left,
                right,
                left_case=left_case,
                right_case=right_case,
            ):
                return True
            return False
        if len(left.operands) != len(right.operands):
            return False
        return all(
            self._expressions_share_object_centric_structure(left_operand, right_operand)
            for left_operand, right_operand in zip(left.operands, right.operands)
        )

    def _runtime_refs_share_shortcut_semantics(self, left_ref, right_ref) -> tuple[bool, bool]:
        if left_ref is None or right_ref is None:
            return False, False

        left_exact_key_fn = getattr(left_ref, "pairwise_exact_key", None)
        right_exact_key_fn = getattr(right_ref, "pairwise_exact_key", None)
        if callable(left_exact_key_fn) and callable(right_exact_key_fn):
            try:
                if left_exact_key_fn() == right_exact_key_fn():
                    return True, False
            except Exception:
                pass

        left_semantic_key_fn = getattr(left_ref, "pairwise_semantic_key", None)
        right_semantic_key_fn = getattr(right_ref, "pairwise_semantic_key", None)
        if not callable(left_semantic_key_fn) or not callable(right_semantic_key_fn):
            return False, False
        try:
            left_semantic_key = left_semantic_key_fn()
            right_semantic_key = right_semantic_key_fn()
        except Exception:
            return False, False
        if left_semantic_key is None or right_semantic_key is None:
            return False, False
        if left_semantic_key != right_semantic_key:
            return False, False

        left_guard_fn = getattr(left_ref, "pairwise_requires_guard_equivalence", None)
        right_guard_fn = getattr(right_ref, "pairwise_requires_guard_equivalence", None)
        requires_guard_equivalence = bool(callable(left_guard_fn) and left_guard_fn()) or bool(
            callable(right_guard_fn) and right_guard_fn()
        )
        return True, requires_guard_equivalence

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
        if not self._counted_loop_refs_match_ignoring_signedness(left_ref, right_ref):
            return False
        if not all(
            self._expressions_share_object_centric_structure(left_operand, right_operand)
            for left_operand, right_operand in zip(left.operands, right.operands)
        ):
            return False
        conditions = self._combined_summary_conditions(left_case, right_case)
        parameters = self._collect_intrinsic_parameter_specs(left_case, right_case, left, right)
        if bool(getattr(left_ref, "signed_loop", False)) == bool(getattr(right_ref, "signed_loop", False)):
            return True
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

    def _counted_loop_refs_match_ignoring_signedness(self, left_ref, right_ref) -> bool:
        if left_ref is None or right_ref is None:
            return False
        left_kind = type(left_ref).__name__
        right_kind = type(right_ref).__name__
        if left_kind != "CountedLoopSummaryRef" or right_kind != "CountedLoopSummaryRef":
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
        seen_params = set()
        for parameter in parameters or []:
            name = str(parameter.get("name") or "")
            if not name or name in seen_params:
                continue
            param_width = max(1, int(parameter.get("size", 0) or 4)) * 8
            declarations.append(f"(declare-const {name} (_ BitVec {param_width}))")
            seen_params.add(name)

        intrinsic_declarations: List[str] = []
        for item in [expr, *(condition.expression for condition in conditions or [] if condition is not None)]:
            for declaration in collect_intrinsic_smt_declarations(item):
                if declaration not in intrinsic_declarations:
                    intrinsic_declarations.append(declaration)
        declarations.extend(intrinsic_declarations)

        assertions = [
            f"(assert {condition.to_smt()})"
            for condition in conditions or []
            if condition is not None
        ]
        expr_smt = expr.to_smt()
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
    ) -> List[Dict[str, Any]]:
        specs: Dict[str, Dict[str, Any]] = {}
        for case in (left_case, right_case):
            for parameter in list(getattr(case, "parameters", None) or []):
                name = str(parameter.get("name") or "")
                if not name:
                    continue
                size = max(1, int(parameter.get("size", 0) or 4))
                candidate = dict(parameter)
                candidate["name"] = name
                candidate["size"] = size
                existing = specs.get(name)
                if existing is None or int(existing.get("size", 0) or 0) < size:
                    specs[name] = candidate

        def visit(expr: Optional[Expression]) -> None:
            if expr is None:
                return
            if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER:
                name = str(getattr(expr, "name", None) or "")
                if not name:
                    return
                size = max(1, int(getattr(expr, "size", 0) or 4))
                candidate = {
                    "name": name,
                    "index": int(getattr(expr, "value", -1) or -1),
                    "size": size,
                    "data_type": getattr(expr, "data_type", None),
                }
                existing = specs.get(name)
                if existing is None or int(existing.get("size", 0) or 0) < size:
                    specs[name] = candidate
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

        ordered = sorted(
            specs.values(),
            key=lambda item: (
                int(item.get("index", -1)) if int(item.get("index", -1)) >= 0 else 1_000_000,
                item.get("name") or "",
            ),
        )
        for fallback_index, spec in enumerate(ordered):
            if int(spec.get("index", -1)) < 0:
                spec["index"] = fallback_index
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
        seen_params = set()
        for parameter in parameters or []:
            name = str(parameter.get("name") or "")
            if not name or name in seen_params:
                continue
            width_bits = max(1, int(parameter.get("size", 0) or 4)) * 8
            declarations.append(f"(declare-const {name} (_ BitVec {width_bits}))")
            seen_params.add(name)

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
            assertions.append(f"(assert {condition.to_smt()})")
        assertions.append(f"(assert (not (= {left.to_smt()} {right.to_smt()})))")
        return "\n".join(declarations + assertions + ["(check-sat)"])

    def _cases_have_equivalent_summary_conditions(
        self,
        left_case: ReturnCase,
        right_case: ReturnCase,
    ) -> bool:
        left_conditions = left_case.summary_conditions if left_case.summary_conditions is not None else left_case.conditions
        right_conditions = right_case.summary_conditions if right_case.summary_conditions is not None else right_case.conditions
        left_normalized = ConditionSimplifier.simplify_conditions_object_centric(list(left_conditions or []))
        right_normalized = ConditionSimplifier.simplify_conditions_object_centric(list(right_conditions or []))
        if len(left_normalized) != len(right_normalized):
            return False
        if not left_normalized and not right_normalized:
            return True

        matched_right: set[int] = set()
        for left_condition in left_normalized:
            candidate_index: Optional[int] = None
            for idx, right_condition in enumerate(right_normalized):
                if idx in matched_right:
                    continue
                if not self._conditions_are_semantically_equivalent(left_condition, right_condition):
                    continue
                if candidate_index is not None:
                    return False
                candidate_index = idx
            if candidate_index is None:
                return False
            matched_right.add(candidate_index)
        return len(matched_right) == len(right_normalized)

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
        return ConditionSimplifier.object_centric_is_contradiction(combined_conditions)

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
