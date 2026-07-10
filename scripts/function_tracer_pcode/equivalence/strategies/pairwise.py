# -*- coding: utf-8 -*-
"""Pairwise戦略（分岐ペア分割方式・二段階チェック対応）"""

from dataclasses import dataclass, replace
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple
import hashlib
import json
import time

from ...model import (
    COUNTED_LOOP_SUM_OPCODE,
    COUNTED_STATE_TRANSITION_VALUE_OPCODE,
    Condition,
    CountedStateTransitionLoopSummaryRef,
    CountedLoopSummaryRef,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    LoopSummaryRef,
    LoopTermDescriptorRef,
    LoopSummaryComparisonResult,
    ReadonlyReductionRef,
    ReadonlyReductionTermRef,
    StorageInfo,
    compare_loop_summaries,
)
from ...model.runtime_refs import _loop_summary_term_at_index
from ...analysis.effect_summary import canonicalize_location
from ...model.render_smt import (
    collect_float_predicate_smt_declarations,
    collect_intrinsic_smt_declarations,
    collect_unknown_smt_declarations,
    expression_contains_unsupported_smt_ops,
    expression_uses_smt_float_theory,
    expression_uses_smt_uf,
    expression_smt_bit_width,
    smt_logic_name,
    _counted_loop_sum_has_exact_lowering,
)
from ...analysis.condition.simplifier import ConditionSimplifier
from ...analysis.condition.normalizer import ConditionNormalizer
from ...analysis.condition.smt_oracle import ConditionSMTOracle
from ...smt import ParallelResult, SolverResult, SolverStatus
from ...smt.solvers.z3 import Z3Solver
from .base import CheckStrategy, StrategyResult
from .pairwise_models import QueryResult, ReturnCase
from .pairwise_normalization import try_normalization_equivalence
from .pairwise_solver_proven_rewrite import try_solver_proven_rewrite_equivalence
from .pairwise_query_builder import (
    build_condition_only_query,
    build_return_width_bridge_high_bit_query,
    build_return_width_bridge_narrow_query,
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
from ..formula.params import build_parameter_semantic_constraints
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
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    UnknownRecoveryProofObligation,
    UnknownReasonId,
    build_unknown_recovery_actions,
    make_unknown_reason,
)


@dataclass(frozen=True)
class _RuntimeShortcutDecision:
    equivalent: bool
    requires_guard_equivalence: bool
    reason: str = "unknown"


@dataclass(frozen=True)
class _UnresolvedDeferredCallLowering:
    assertions: Tuple[str, ...]
    evidence: Tuple[Any, ...]


@dataclass(frozen=True)
class _ExactReadonlyReductionProof:
    """Object proof that an exact load-sum denotes one or more reduction counts."""

    exact_terms: tuple[ReadonlyReductionTermRef, ...]
    constant_bias: int
    result_size: int
    count_value: int
    expected_terms: tuple[ReadonlyReductionTermRef, ...]
    evidence: str
    count_values: Tuple[int, ...] = ()


@dataclass(frozen=True)
class _MethodBCoveringCaseProof:
    """Object proof for one Method-B exact-vs-summary covering case."""

    exact_side: str
    summary_side: str
    exact_case: ReturnCase
    summary_case: ReturnCase
    accumulator_proof: Any
    exact_proof: _ExactReadonlyReductionProof


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
        enable_completed_recovery_proofs: bool = True,
    ):
        super().__init__(
            formula_builder,
            solver_runner,
            debug,
            enable_completed_recovery_proofs=enable_completed_recovery_proofs,
        )
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
        semantic_parameter_sources = self._auxiliary_semantic_parameter_sources(base_ctx)
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
            float_mode="fp",
        )
        symbol_replace_fn2 = build_symbol_replacer(
            base_ctx["params2"],
            base_ctx.get("extra_vars2", []),
            float_mode="fp",
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
                readonly_contract_assertions = self._readonly_contract_pairwise_extra_assertions(
                    case1,
                    case2,
                    symbol_replace_fn1,
                    symbol_replace_fn2,
                )
                if readonly_contract_assertions:
                    self._register_pairwise_extra_assertions(
                        base_ctx,
                        pair_id,
                        readonly_contract_assertions,
                    )
                else:
                    self._clear_pairwise_extra_assertions(base_ctx, pair_id)
                if self._cases_have_equivalent_runtime_reductions(
                    case1,
                    case2,
                    semantic_parameter_sources=semantic_parameter_sources,
                ):
                    unsat_count += 1
                    resolved_pairs.add((i, j))
                    if self.debug and (unsat_count % 10 == 0 or unsat_count <= 5):
                        self._debug_print(
                            f"  Pair {pair_id}: object-centric runtime summary match -> UNSAT "
                            f"({unsat_count}/{total_pairs})"
                        )
                    continue
                if self._case_pair_counted_loop_summary_matches_closed_expression(case1, case2, base_ctx=base_ctx):
                    unsat_count += 1
                    resolved_pairs.add((i, j))
                    if self.debug and (unsat_count % 10 == 0 or unsat_count <= 5):
                        self._debug_print(
                            f"  Pair {pair_id}: counted loop summary closed by SMT expression proof "
                            f"-> UNSAT ({unsat_count}/{total_pairs})"
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
                    reason_id = self._unknown_reason_id_for_loop_fallback(loop_fallback_reason)
                    object_target_key = None
                    evidence_kind = None
                    if reason_id == UnknownReasonId.READONLY_IDENTITY_MISSING:
                        object_target_key = self._readonly_identity_object_target_key(
                            base_ctx=base_ctx,
                            case1=case1,
                            case2=case2,
                            pair_id=pair_id,
                        )
                        evidence_kind = "object_storage_identity"
                    elif reason_id == UnknownReasonId.METHOD_B_CLOSURE_BLOCKED:
                        object_target_key = self._method_b_closure_object_target_key(
                            base_ctx=base_ctx,
                            case1=case1,
                            case2=case2,
                            pair_id=pair_id,
                        )
                    reason_record = make_unknown_reason(
                        reason_id,
                        stage="S_PAIRWISE",
                        pair_or_case=pair_id,
                        evidence_refs=(loop_fallback_reason,),
                        evidence_kind=evidence_kind,
                        object_target_key=object_target_key,
                        detail=loop_fallback_reason,
                    )
                    if reason_id == UnknownReasonId.METHOD_B_CLOSURE_BLOCKED:
                        self._record_completed_method_b_covering_case_proof_if_safe(
                            reason_record,
                            analysis1,
                            case1,
                            case2,
                        )
                        self._record_completed_method_b_dual_summary_solver_proof_if_safe(
                            reason_record,
                            analysis1,
                            case1,
                            case2,
                        )
                        if self._method_b_closure_proof_is_complete(reason_record, analysis1, analysis2):
                            unsat_count += 1
                            resolved_pairs.add((i, j))
                            self._debug_print(
                                f"  Pair {pair_id}: Method-B closure proof completed in current run "
                                f"-> UNSAT ({unsat_count}/{total_pairs})"
                            )
                            continue
                    elif reason_id == UnknownReasonId.READONLY_IDENTITY_MISSING:
                        self._record_completed_readonly_identity_projection_proof_if_safe(
                            reason_record,
                            analysis1,
                            analysis2,
                            case1,
                            case2,
                        )
                        if self._readonly_identity_proof_is_complete(reason_record, analysis1, analysis2):
                            unsat_count += 1
                            resolved_pairs.add((i, j))
                            self._debug_print(
                                f"  Pair {pair_id}: readonly identity projection proof completed in current run "
                                f"-> UNSAT ({unsat_count}/{total_pairs})"
                            )
                            continue
                    if self._case_pair_counted_loop_summaries_match_by_closed_values(
                        case1,
                        case2,
                        base_ctx=base_ctx,
                    ) or self._counted_loop_values_are_provably_equivalent(
                        case1.value_expr,
                        case2.value_expr,
                        left_case=case1,
                        right_case=case2,
                        semantic_parameter_sources=semantic_parameter_sources,
                    ):
                        unsat_count += 1
                        resolved_pairs.add((i, j))
                        if self.debug and (unsat_count % 10 == 0 or unsat_count <= 5):
                            self._debug_print(
                                f"  Pair {pair_id}: counted loop summaries closed by SMT value proof "
                                f"-> UNSAT ({unsat_count}/{total_pairs})"
                            )
                        continue
                    unknown_count += 1
                    unknown_reasons.append(reason_record)
                    self._debug_print(
                        f"  Pair {pair_id}: loop summary requires semantic proof "
                        f"({loop_fallback_reason}) -> UNKNOWN"
                    )
                    continue
                case1_has_unresolved = self._case_contains_unresolved_expression(
                    case1,
                    case2.conditions,
                    own_render_fn=symbol_replace_fn1,
                    extra_render_fn=symbol_replace_fn2,
                    base_ctx=base_ctx,
                    query_label=f"{pair_id}:case1",
                )
                case2_has_unresolved = self._case_contains_unresolved_expression(
                    case2,
                    case1.conditions,
                    own_render_fn=symbol_replace_fn2,
                    extra_render_fn=symbol_replace_fn1,
                    base_ctx=base_ctx,
                    query_label=f"{pair_id}:case2",
                )
                if case1_has_unresolved or case2_has_unresolved:
                    lowering = self._try_build_unresolved_deferred_call_lowering(
                        base_ctx=base_ctx,
                        case1=case1,
                        case2=case2,
                        pair_id=pair_id,
                    )
                    object_target_key = None
                    completed_proof_evidence = None
                    if lowering is None:
                        object_target_key = self._unresolved_expression_object_target_key(
                            base_ctx=base_ctx,
                            case1=case1,
                            case2=case2,
                            pair_id=pair_id,
                        )
                    if lowering is None and object_target_key is not None:
                        completed_proof_evidence = (
                            self._unresolved_expression_phi_circular_full_shape_diagnostic_evidence(
                                object_target_key
                            )
                        )
                    if lowering is not None:
                        self._register_pairwise_extra_assertions(
                            base_ctx,
                            pair_id,
                            lowering.assertions,
                        )
                        self._debug_print(
                            f"  Pair {pair_id}: unresolved runtime unknown "
                            "lowered with object-derived equality evidence"
                        )
                    else:
                        self._clear_pairwise_extra_assertions(base_ctx, pair_id)
                        unknown_count += 1
                        if object_target_key is None:
                            object_target_key = self._unresolved_expression_object_target_key(
                                base_ctx=base_ctx,
                                case1=case1,
                                case2=case2,
                                pair_id=pair_id,
                            )
                        if self._unresolved_expression_target_uses_generic_pending_census(
                            object_target_key
                        ):
                            completed_proof_evidence = (
                                self._unresolved_expression_generic_diagnostic_evidence(
                                    object_target_key
                                )
                            )
                        if completed_proof_evidence is None:
                            completed_proof_evidence = (
                                self._unresolved_expression_phi_circular_full_shape_diagnostic_evidence(
                                    object_target_key
                                )
                            )
                        if completed_proof_evidence is None:
                            completed_proof_evidence = (
                                self._unresolved_expression_deferred_call_diagnostic_evidence(
                                    object_target_key
                                )
                            )
                        if completed_proof_evidence is None:
                            completed_proof_evidence = (
                                self._unresolved_expression_opaque_unknown_diagnostic_evidence(
                                    object_target_key
                                )
                            )
                        if completed_proof_evidence is None:
                            completed_proof_evidence = (
                                self._unresolved_expression_generic_diagnostic_evidence(
                                    object_target_key
                                )
                            )
                        unknown_reasons.append(
                            make_unknown_reason(
                                UnknownReasonId.UNRESOLVED_EXPRESSION,
                                stage="S_PAIRWISE",
                                pair_or_case=pair_id,
                                evidence_refs=(f"{pair_id}:case1", f"{pair_id}:case2"),
                                recovery_proof_obligations=(
                                    self._unresolved_expression_recovery_proof_obligations(object_target_key)
                                ),
                                evidence_kind="unresolved_expression_safety",
                                object_target_key=object_target_key,
                                object_evidence=completed_proof_evidence,
                                action_status=self._unresolved_expression_action_status(
                                    object_target_key,
                                    completed_proof_evidence,
                                ),
                                detail="pairwise case contains solver-unresolved expression evidence",
                            )
                        )
                        self._debug_print(
                            f"  Pair {pair_id}: unresolved expression detected -> UNKNOWN"
                        )
                        continue
                else:
                    if not readonly_contract_assertions:
                        self._clear_pairwise_extra_assertions(base_ctx, pair_id)

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
                        sat_unsafety_reason = self._make_sat_unsafety_unknown_reason(
                            sat_unsafety_reasons,
                            analysis1,
                            analysis2,
                            case1=case1,
                            case2=case2,
                            pair_id=pair_id,
                            stage="S_PAIRWISE",
                        )
                        if not self._sat_unsafety_resolution_proof_is_complete(
                            sat_unsafety_reason,
                            analysis1,
                            analysis2,
                            current_counterexample_raw=result.counterexample_raw,
                        ):
                            unknown_count += 1
                            unknown_reasons.append(sat_unsafety_reason)
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
                            self._make_sat_counterexample_ambiguous_unknown_reason(
                                (result.pair_stage or "unknown",),
                                analysis1,
                                analysis2,
                                case1=case1,
                                case2=case2,
                                pair_id=pair_id,
                                stage="S_PAIRWISE",
                            )
                        )
                        self._debug_print(
                            f"  Pair {pair_id}: SAT counterexample was ambiguous -> downgraded to UNKNOWN"
                        )
                        continue

                    same_function_replay_reasons = self._same_function_counterexample_replay_reasons(
                        analysis1,
                        analysis2,
                    )
                    if same_function_replay_reasons:
                        sat_replay_reason = self._make_sat_unsafety_unknown_reason(
                            same_function_replay_reasons,
                            analysis1,
                            analysis2,
                            case1=case1,
                            case2=case2,
                            pair_id=pair_id,
                            stage="S_PAIRWISE",
                        )
                        if not self._sat_unsafety_resolution_proof_is_complete(
                            sat_replay_reason,
                            analysis1,
                            analysis2,
                            current_counterexample_raw=result.counterexample_raw,
                        ):
                            unknown_count += 1
                            unknown_reasons.append(sat_replay_reason)
                            self._debug_print(
                                "  Pair "
                                f"{pair_id}: SAT downgraded to UNKNOWN until same-function "
                                "counterexample replay is completed"
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

                if result.blocking_reason == UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value:
                    completed_bridge_result = self._solve_return_width_bridge_with_completed_proof(
                        base_ctx,
                        case1,
                        case2,
                        symbol_replace_fn1,
                        symbol_replace_fn2,
                        pair_id,
                        object_target_key=getattr(result, "object_target_key", None),
                        blocking_detail=str(result.blocking_detail or ""),
                    )
                    if completed_bridge_result is not None and completed_bridge_result.is_equivalent is True:
                        unsat_count += 1
                        resolved_pairs.add((i, j))
                        last_formula = completed_bridge_result.last_query or last_formula
                        self._debug_print(
                            f"  Pair {pair_id}: return-width bridge proof -> UNSAT "
                            f"({unsat_count}/{total_pairs})"
                        )
                        continue
                    pending_bridge_evidence = getattr(
                        self,
                        "_last_return_width_bridge_pending_evidence",
                        None,
                    )
                    if pending_bridge_evidence is not None:
                        result.object_evidence = pending_bridge_evidence

                unknown_count += 1
                unknown_reasons.append(
                    make_unknown_reason(
                        result.blocking_reason or UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT,
                        stage="S_PAIRWISE",
                        pair_or_case=pair_id,
                        evidence_refs=(result.pair_stage or "unknown", result.blocking_detail),
                        evidence_kind=getattr(result, "evidence_kind", None),
                        object_target_key=getattr(result, "object_target_key", None),
                        recovery_proof_obligations=getattr(
                            result,
                            "recovery_proof_obligations",
                            None,
                        ),
                        proof_obligation_id=getattr(result, "proof_obligation_id", None),
                        object_evidence=getattr(result, "object_evidence", None),
                        action_status=getattr(result, "action_status", None),
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
        coverage_unknown_reasons = self._unresolved_return_coverage_unknown_reasons(
            coverage_unsafety_reasons,
            analysis1,
            analysis2,
            stage="S_PAIRWISE",
        )
        equivalence_unknown_reasons = self._unresolved_equivalence_blocking_unknown_reasons(
            equivalence_blocking_reasons,
            analysis1,
            analysis2,
            stage="S_PAIRWISE",
        )
        blocking_unknown_reasons = coverage_unknown_reasons + equivalence_unknown_reasons
        blocking_reasons_replace_pair_unknowns = (
            self._blocking_unknown_reasons_should_replace_pair_unknowns(
                unknown_reasons,
                coverage_unknown_reasons,
                equivalence_unknown_reasons,
            )
        )

        if sat_count > 0:
            final_is_equiv = False
            self._debug_print("=" * 60)
            self._debug_print("Result: NOT EQUIVALENT (found SAT pair)")
        elif (
            blocking_unknown_reasons
            and unknown_count > 0
            and blocking_reasons_replace_pair_unknowns
        ):
            final_is_equiv = None
            unknown_reasons = blocking_unknown_reasons
            blocking_reasons = coverage_unsafety_reasons + equivalence_blocking_reasons
            self._debug_print("=" * 60)
            self._debug_print(
                "Result: UNKNOWN (equivalence proof is blocked by incomplete analysis: "
                f"{', '.join(blocking_reasons)})"
            )
        elif unknown_count > 0:
            final_is_equiv = None
            if blocking_unknown_reasons:
                unknown_reasons = self._append_blocking_unknown_reasons(
                    unknown_reasons,
                    blocking_unknown_reasons,
                )
            self._debug_print("=" * 60)
            self._debug_print(f"Result: UNKNOWN (timeout/unknown in {unknown_count} pairs)")
        elif blocking_unknown_reasons:
            final_is_equiv = None
            unknown_reasons = blocking_unknown_reasons
            blocking_reasons = coverage_unsafety_reasons + equivalence_blocking_reasons
            self._debug_print("=" * 60)
            self._debug_print(
                "Result: UNKNOWN (equivalence proof is blocked by incomplete analysis: "
                f"{', '.join(blocking_reasons)})"
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

        self._merge_completed_recovery_proofs_from_solver_analyses(
            analysis1,
            solver_analysis1,
            analysis2,
            solver_analysis2,
        )

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

    @staticmethod
    def _merge_completed_recovery_proofs_from_solver_analyses(
        analysis1: FunctionReturnAnalysis,
        solver_analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        solver_analysis2: FunctionReturnAnalysis,
    ) -> None:
        for target, source in (
            (analysis1, solver_analysis1),
            (analysis2, solver_analysis2),
        ):
            source_records = [
                dict(record)
                for record in getattr(source, "completed_recovery_proof_evidence", ()) or ()
                if isinstance(record, Mapping)
            ]
            if not source_records:
                continue
            target_records = [
                dict(record)
                for record in getattr(target, "completed_recovery_proof_evidence", ()) or ()
                if isinstance(record, Mapping)
            ]
            existing_ids = {record.get("proof_obligation_id") for record in target_records}
            changed = False
            for record in source_records:
                proof_id = record.get("proof_obligation_id")
                if proof_id is not None and proof_id in existing_ids:
                    continue
                target_records.append(record)
                if proof_id is not None:
                    existing_ids.add(proof_id)
                changed = True
            if changed:
                target.completed_recovery_proof_evidence = tuple(target_records)

    @staticmethod
    def _blocking_unknown_reasons_should_replace_pair_unknowns(
        pair_unknown_reasons: Sequence[Any],
        coverage_unknown_reasons: Sequence[Any],
        equivalence_unknown_reasons: Sequence[Any],
    ) -> bool:
        """Return whether global blockers should replace pair-local reasons."""

        if not pair_unknown_reasons:
            return True
        if not coverage_unknown_reasons and not equivalence_unknown_reasons:
            return False

        replaceable_pair_reasons = {
            UnknownReasonId.UNRESOLVED_EXPRESSION.value,
            UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT.value,
            UnknownReasonId.SOLVER_PROVEN_REWRITE_PROOF_FAILED.value,
            UnknownReasonId.SOLVER_PROVEN_REWRITE_NO_CHANGE.value,
            UnknownReasonId.NORMALIZATION_NO_CHANGE.value,
            UnknownReasonId.UNKNOWN.value,
        }
        pair_reason_ids = {
            getattr(reason, "reason_id", None)
            for reason in pair_unknown_reasons
        }
        return bool(pair_reason_ids) and pair_reason_ids <= replaceable_pair_reasons

    @classmethod
    def _append_blocking_unknown_reasons(
        cls,
        pair_unknown_reasons: Sequence[Any],
        blocking_unknown_reasons: Sequence[Any],
    ) -> List[Any]:
        result = list(pair_unknown_reasons)
        seen = {cls._unknown_reason_dedup_key(reason) for reason in result}
        for reason in blocking_unknown_reasons:
            key = cls._unknown_reason_dedup_key(reason)
            if key in seen:
                continue
            result.append(reason)
            seen.add(key)
        return result

    @staticmethod
    def _unknown_reason_dedup_key(reason: Any) -> Tuple[Any, ...]:
        return (
            getattr(reason, "reason_id", None),
            getattr(reason, "stage", None),
            getattr(reason, "pair_or_case", None),
            tuple(getattr(reason, "evidence_refs", ()) or ()),
            getattr(reason, "evidence_kind", None),
            getattr(reason, "proof_obligation_id", None),
        )

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
        *,
        semantic_parameter_sources: Sequence[ParameterInfo] = (),
    ) -> bool:
        if self._intrinsic_runtime_values_equivalent(
            case1.value_expr,
            case2.value_expr,
            left_case=case1,
            right_case=case2,
            semantic_parameter_sources=semantic_parameter_sources,
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
        proof_result_size = max(1, int(getattr(accumulator_proof, "result_size", 0) or 0))
        if max(1, int(getattr(summary_ref, "result_size", 0) or 0)) != proof_result_size:
            return None
        if self._normalize_constant_bias(
            int(getattr(summary_ref, "constant_bias", 0) or 0),
            proof_result_size,
        ) != self._normalize_constant_bias(
            int(getattr(accumulator_proof, "constant_bias", 0) or 0),
            proof_result_size,
        ):
            return None
        exact_bits = int(expression_smt_bit_width(exact_case.value_expr) or 0)
        if exact_bits <= 0 or exact_bits % 8 != 0:
            return None
        result_size = exact_bits // 8
        if result_size > proof_result_size:
            return None
        contract_key_fn = getattr(accumulator_proof, "readonly_term_sequence_contract_key", None)
        if not callable(contract_key_fn):
            return None
        try:
            contract_key = contract_key_fn(result_size=result_size)
        except (AttributeError, TypeError, ValueError):
            contract_key = None
        if contract_key is None:
            return None
        extracted = self._extract_readonly_reduction_terms_and_bias_from_expression(
            exact_case.value_expr,
            exact_case.parameters,
            getattr(accumulator_proof, "pointer_base_ref", None),
            program_is_big_endian=getattr(exact_case, "program_is_big_endian", None),
        )
        if extracted is None and str(getattr(accumulator_proof, "reduction_kind", "") or "") == "fp_int2float_div_count_sum":
            extracted = self._extract_fp_count_one_readonly_terms_and_bias_from_expression(
                exact_case.value_expr,
                exact_case.parameters,
                getattr(accumulator_proof, "pointer_base_ref", None),
                accumulator_proof=accumulator_proof,
                program_is_big_endian=getattr(exact_case, "program_is_big_endian", None),
            )
        if extracted is None:
            return None
        extracted_terms, extracted_bias = extracted
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
                    count_values=(count_value,),
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

    def _extract_fp_count_one_readonly_terms_and_bias_from_expression(
        self,
        expr: Optional[Expression],
        parameters: Sequence[Dict[str, Any]],
        pointer_base_ref,
        *,
        accumulator_proof,
        program_is_big_endian: Optional[bool] = None,
    ) -> Optional[tuple[tuple[ReadonlyReductionTermRef, ...], int]]:
        if expr is None or pointer_base_ref is None or accumulator_proof is None:
            return None
        terms = self._extract_fp_count_one_readonly_terms_from_expression(
            expr,
            parameters,
            pointer_base_ref,
            accumulator_proof=accumulator_proof,
            program_is_big_endian=program_is_big_endian,
        )
        if terms is None:
            return None
        normalized_terms = tuple(sorted(terms, key=lambda item: (int(item.byte_offset), int(item.access_size))))
        if not normalized_terms:
            return None
        return normalized_terms, 0

    def _extract_fp_count_one_readonly_terms_from_expression(
        self,
        expr: Optional[Expression],
        parameters: Sequence[Dict[str, Any]],
        pointer_base_ref,
        *,
        accumulator_proof,
        program_is_big_endian: Optional[bool] = None,
    ) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        if expr is None:
            return None
        if getattr(expr, "expr_type", None) == ExpressionType.CONSTANT:
            return () if self._raw_constant_value(expr) == 0 else None
        if getattr(expr, "expr_type", None) == ExpressionType.UNARY_OP and getattr(expr, "operands", None):
            if getattr(expr, "operator", None) in {"INT2FLOAT", "INT_ZEXT", "INT_SEXT", "CAST", "COPY"}:
                return self._extract_fp_count_one_readonly_terms_from_expression(
                    expr.operands[0],
                    parameters,
                    pointer_base_ref,
                    accumulator_proof=accumulator_proof,
                    program_is_big_endian=program_is_big_endian,
                )
        if getattr(expr, "expr_type", None) == ExpressionType.BINARY_OP and len(getattr(expr, "operands", ()) or ()) == 2:
            if getattr(expr, "operator", None) == "FLOAT_ADD":
                left = self._extract_fp_count_one_readonly_terms_from_expression(
                    expr.operands[0],
                    parameters,
                    pointer_base_ref,
                    accumulator_proof=accumulator_proof,
                    program_is_big_endian=program_is_big_endian,
                )
                right = self._extract_fp_count_one_readonly_terms_from_expression(
                    expr.operands[1],
                    parameters,
                    pointer_base_ref,
                    accumulator_proof=accumulator_proof,
                    program_is_big_endian=program_is_big_endian,
                )
                if left is None or right is None:
                    return None
                return tuple(left) + tuple(right)
            if getattr(expr, "operator", None) == "FLOAT_DIV":
                if not self._fp_denominator_matches_reduction_count(
                    expr.operands[1],
                    parameters,
                    accumulator_proof,
                ):
                    return None
                return self._extract_fp_count_one_readonly_terms_from_expression(
                    expr.operands[0],
                    parameters,
                    pointer_base_ref,
                    accumulator_proof=accumulator_proof,
                    program_is_big_endian=program_is_big_endian,
                )
        descriptor = self._extract_readonly_reduction_term_descriptor(
            expr,
            parameters,
            pointer_base_ref,
            program_is_big_endian=program_is_big_endian,
        )
        if descriptor is None:
            return None
        return (descriptor,)

    def _fp_denominator_matches_reduction_count(
        self,
        expr: Optional[Expression],
        parameters: Sequence[Dict[str, Any]],
        accumulator_proof,
    ) -> bool:
        if expr is None or accumulator_proof is None:
            return False
        if getattr(expr, "expr_type", None) == ExpressionType.UNARY_OP and getattr(expr, "operands", None):
            if getattr(expr, "operator", None) in {"INT2FLOAT", "INT_ZEXT", "INT_SEXT", "CAST", "COPY"}:
                return self._fp_denominator_matches_reduction_count(
                    expr.operands[0],
                    parameters,
                    accumulator_proof,
                )
        if getattr(expr, "expr_type", None) == ExpressionType.BINARY_OP and len(getattr(expr, "operands", ()) or ()) == 2:
            if getattr(expr, "operator", None) == "SUBPIECE":
                return self._fp_denominator_matches_reduction_count(
                    expr.operands[0],
                    parameters,
                    accumulator_proof,
                )
        if getattr(expr, "expr_type", None) != ExpressionType.PARAMETER:
            return False
        expr_storage = self._parameter_expression_storage_identity_key(expr)
        expr_index = self._parameter_expression_index_identity_key(expr)
        proof_storage = self._reduction_count_storage_identity_key(accumulator_proof)
        proof_index = self._reduction_count_index_identity_key(accumulator_proof)
        expr_identity = parameter_identity_key_from_expression(expr)
        proof_identities = self._reduction_count_identity_keys(accumulator_proof)
        if self._fp_denominator_count_identity_matches(
            expr_storage,
            expr_index,
            proof_storage,
            proof_index,
        ):
            return True
        if expr_identity is not None and proof_identities:
            return expr_identity is not None and tuple(expr_identity) in proof_identities
        expr_has_identity = expr_storage is not None or expr_index is not None or expr_identity is not None
        if expr_has_identity:
            return False
        return self._fp_denominator_name_fallback_matches_unique_count(
            expr,
            parameters,
            accumulator_proof,
        )

    @staticmethod
    def _fp_denominator_count_identity_matches(
        expr_storage: Optional[tuple],
        expr_index: Optional[tuple],
        proof_storage: Optional[tuple],
        proof_index: Optional[tuple],
    ) -> bool:
        if expr_storage is not None and proof_storage is not None:
            if expr_storage == proof_storage:
                return True
            if expr_index is None or proof_index is None:
                return False
        if expr_index is not None and proof_index is not None:
            return expr_index == proof_index
        return False

    def _fp_denominator_name_fallback_matches_unique_count(
        self,
        expr: Expression,
        parameters: Sequence[Dict[str, Any]],
        accumulator_proof,
    ) -> bool:
        count_parameter_name = str(getattr(accumulator_proof, "count_parameter_name", "") or "")
        expr_name = str(getattr(expr, "name", "") or "")
        if not count_parameter_name or expr_name != count_parameter_name:
            return False
        matching_parameters = tuple(
            parameter
            for parameter in parameters or ()
            if isinstance(parameter, dict) and str(parameter.get("name") or "") == count_parameter_name
        )
        if len(matching_parameters) != 1:
            return False
        descriptor = matching_parameters[0]
        descriptor_storage = self._parameter_descriptor_storage_identity_key(descriptor)
        descriptor_index = self._parameter_descriptor_index_identity_key(descriptor)
        proof_storage = self._reduction_count_storage_identity_key(accumulator_proof)
        proof_index = self._reduction_count_index_identity_key(accumulator_proof)
        if proof_storage is not None and descriptor_storage != proof_storage:
            return False
        if proof_index is not None and descriptor_index != proof_index:
            return False
        return proof_storage is not None or proof_index is not None

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
                    count_values=(int(count_value),),
                )
        return None

    def _prove_exact_load_sum_covers_readonly_loop_summary(
        self,
        exact_case: ReturnCase,
        summary_case: ReturnCase,
        summary_ref: ReadonlyReductionRef,
    ) -> Optional[Tuple[_ExactReadonlyReductionProof, _ReadonlyLoopSummaryProofAdapter]]:
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
        matching_count_values: List[int] = []
        first_expected_terms: Optional[Tuple[ReadonlyReductionTermRef, ...]] = None
        for count_value in range(1, max_count + 1):
            expected_terms = adapter.full_terms_for_count_value(count_value)
            if expected_terms is None:
                continue
            if extracted_key != tuple(term.stable_key() for term in expected_terms):
                continue
            matching_count_values.append(int(count_value))
            if first_expected_terms is None:
                first_expected_terms = tuple(expected_terms)
        if matching_count_values and first_expected_terms is not None:
            return (
                _ExactReadonlyReductionProof(
                    exact_terms=tuple(extracted_terms),
                    constant_bias=self._normalize_constant_bias(extracted_bias, result_size),
                    result_size=result_size,
                    count_value=int(matching_count_values[0]),
                    expected_terms=first_expected_terms,
                    evidence="method_b_covering_materialized_terms",
                    count_values=tuple(matching_count_values),
                ),
                adapter,
            )
        return None

    def _method_b_covering_case_proof(
        self,
        case1: ReturnCase,
        case2: ReturnCase,
    ) -> Optional[_MethodBCoveringCaseProof]:
        right_ref = self._method_b_readonly_summary_ref(getattr(case2, "value_expr", None))
        if right_ref is not None:
            proven = self._prove_exact_load_sum_covers_readonly_loop_summary(case1, case2, right_ref)
            if proven is not None:
                proof, adapter = proven
                return _MethodBCoveringCaseProof("left", "right", case1, case2, adapter, proof)
        left_ref = self._method_b_readonly_summary_ref(getattr(case1, "value_expr", None))
        if left_ref is not None:
            proven = self._prove_exact_load_sum_covers_readonly_loop_summary(case2, case1, left_ref)
            if proven is not None:
                proof, adapter = proven
                return _MethodBCoveringCaseProof("right", "left", case2, case1, adapter, proof)
        return None

    def _record_completed_method_b_covering_case_proof_if_safe(
        self,
        reason_record,
        analysis: FunctionReturnAnalysis,
        case1: ReturnCase,
        case2: ReturnCase,
    ) -> None:
        if not self.enable_completed_recovery_proofs:
            return
        if reason_record.reason_id != UnknownReasonId.METHOD_B_CLOSURE_BLOCKED.value:
            return
        object_target_key = self._normalize_nested_tuple(reason_record.object_target_key)
        if not isinstance(object_target_key, tuple) or len(object_target_key) != 5:
            return
        covering = self._method_b_covering_case_proof(case1, case2)
        if covering is None:
            return
        proof = covering.exact_proof
        relation = self._normalize_nested_tuple(object_target_key[4])
        if not self._method_b_covering_relation_matches_proof(
            relation,
            exact_side=covering.exact_side,
            summary_side=covering.summary_side,
            proof=proof,
        ):
            return
        actions = tuple(build_unknown_recovery_actions([reason_record]))
        records: List[Dict[str, Any]] = [
            dict(item)
            for item in getattr(analysis, "completed_recovery_proof_evidence", ()) or ()
            if isinstance(item, dict)
        ]
        existing_ids = {
            self._normalize_nested_tuple(item.get("proof_obligation_id"))
            for item in records
        }
        changed = self._append_completed_method_b_covering_case_evidence(
            records,
            existing_ids,
            actions,
            object_target_key=object_target_key,
            covering=covering,
        )
        count_values = tuple(int(value) for value in (proof.count_values or (proof.count_value,)) if int(value) > 0)
        if self._cases_admit_reduction_count_values(
            covering.exact_case,
            covering.summary_case,
            covering.accumulator_proof,
            count_values,
        ):
            changed = self._append_completed_method_b_guard_partition_evidence(
                records,
                existing_ids,
                actions,
                object_target_key=object_target_key,
                covering=covering,
            ) or changed
        if changed:
            analysis.completed_recovery_proof_evidence = tuple(records)

    def _append_completed_method_b_covering_case_evidence(
        self,
        records: List[Dict[str, Any]],
        existing_ids: set,
        actions: Sequence[Any],
        *,
        object_target_key: Tuple[Any, ...],
        covering: _MethodBCoveringCaseProof,
    ) -> bool:
        action = self._method_b_recovery_action(
            actions,
            proof_kind=UnknownRecoveryProofKind.PROOF_BACKED_COVERING_CASE.value,
            proof_stage="method_b_covering_case",
        )
        if action is None:
            return False
        proof_id = self._normalize_nested_tuple(action.proof_obligation_id)
        if proof_id is None or proof_id in existing_ids:
            return False
        proof = covering.exact_proof
        count_values = tuple(int(value) for value in (proof.count_values or (proof.count_value,)) if int(value) > 0)
        records.append(
            {
                "object_derived": True,
                "status": "complete",
                "reason_id": UnknownReasonId.METHOD_B_CLOSURE_BLOCKED.value,
                "proof_kind": action.proof_kind,
                "recovery_proof_kind": action.proof_kind,
                "proof_stage": action.proof_stage,
                "evidence_kind": action.evidence_kind,
                "required_evidence": tuple(action.required_evidence),
                "object_target_key": object_target_key,
                "proof_obligation_id": proof_id,
                "proof_source": "method_b_one_sided_summary_exact_terms",
                "proof_content": {
                    "object_derived": True,
                    "object_target_key": object_target_key,
                    "seed_compensation": "proven",
                    "term_sequence": "matched",
                    "pure_side_effect_profile": "proven",
                    "exact_side": covering.exact_side,
                    "summary_side": covering.summary_side,
                    "count_value": int(proof.count_value),
                    "count_values": count_values,
                    "exact_terms": tuple(term.stable_key() for term in proof.exact_terms),
                    "expected_terms": tuple(term.stable_key() for term in proof.expected_terms),
                    "constant_bias": int(proof.constant_bias),
                    "result_size": int(proof.result_size),
                    "covering_evidence": proof.evidence,
                },
            }
        )
        existing_ids.add(proof_id)
        return True

    def _append_completed_method_b_guard_partition_evidence(
        self,
        records: List[Dict[str, Any]],
        existing_ids: set,
        actions: Sequence[Any],
        *,
        object_target_key: Tuple[Any, ...],
        covering: _MethodBCoveringCaseProof,
    ) -> bool:
        action = self._method_b_recovery_action(
            actions,
            proof_kind=UnknownRecoveryProofKind.GUARD_PARTITION_COMPLETION.value,
            proof_stage="method_b_guard_partition",
        )
        if action is None:
            return False
        proof_id = self._normalize_nested_tuple(action.proof_obligation_id)
        if proof_id is None or proof_id in existing_ids:
            return False
        proof = covering.exact_proof
        count_values = tuple(int(value) for value in (proof.count_values or (proof.count_value,)) if int(value) > 0)
        guard_evidence = (
            "reduction_count_implication"
            if len(count_values) == 1
            else "reduction_count_membership_implication"
        )
        records.append(
            {
                "object_derived": True,
                "status": "complete",
                "reason_id": UnknownReasonId.METHOD_B_CLOSURE_BLOCKED.value,
                "proof_kind": action.proof_kind,
                "recovery_proof_kind": action.proof_kind,
                "proof_stage": action.proof_stage,
                "evidence_kind": action.evidence_kind,
                "required_evidence": tuple(action.required_evidence),
                "object_target_key": object_target_key,
                "proof_obligation_id": proof_id,
                "proof_source": "method_b_reduction_count_guard_partition",
                "proof_content": {
                    "object_derived": True,
                    "object_target_key": object_target_key,
                    "guard_partition": "proven",
                    "partition_coverage_proof": "covered",
                    "exact_side": covering.exact_side,
                    "summary_side": covering.summary_side,
                    "count_value": int(proof.count_value),
                    "count_values": count_values,
                    "guard_evidence": guard_evidence,
                },
            }
        )
        existing_ids.add(proof_id)
        return True

    def _record_completed_method_b_dual_summary_solver_proof_if_safe(
        self,
        reason_record,
        analysis: FunctionReturnAnalysis,
        case1: ReturnCase,
        case2: ReturnCase,
    ) -> None:
        if not self.enable_completed_recovery_proofs:
            return
        if reason_record.reason_id != UnknownReasonId.METHOD_B_CLOSURE_BLOCKED.value:
            return
        object_target_key = self._normalize_nested_tuple(reason_record.object_target_key)
        if not self._method_b_closure_target_is_specific(object_target_key):
            return
        relation = self._normalize_nested_tuple(object_target_key[4])
        relation_fields = {
            item[0]: item[1]
            for item in relation[1:]
            if isinstance(item, tuple) and len(item) == 2
        } if isinstance(relation, tuple) and len(relation) >= 2 else {}
        if relation_fields.get("kind") != "dual_summary":
            return
        left_ref = self._method_b_summary_runtime_ref(getattr(case1, "value_expr", None))
        right_ref = self._method_b_summary_runtime_ref(getattr(case2, "value_expr", None))
        if left_ref is None or right_ref is None:
            return
        left_profile = self._method_b_summary_profile_key(left_ref)
        right_profile = self._method_b_summary_profile_key(right_ref)
        if relation_fields.get("left_summary") != left_profile or relation_fields.get("right_summary") != right_profile:
            return
        if not self._case_pair_loop_summaries_solver_equivalent(
            left_ref,
            right_ref,
            left_case=case1,
            right_case=case2,
        ):
            return
        actions = tuple(build_unknown_recovery_actions([reason_record]))
        records: List[Dict[str, Any]] = [
            dict(item)
            for item in getattr(analysis, "completed_recovery_proof_evidence", ()) or ()
            if isinstance(item, Mapping)
        ]
        existing_ids = {
            self._normalize_nested_tuple(item.get("proof_obligation_id"))
            for item in records
        }
        changed = False
        for action in actions:
            proof_id = self._normalize_nested_tuple(action.proof_obligation_id)
            if proof_id is None or proof_id in existing_ids:
                continue
            proof_content = self._method_b_dual_summary_solver_proof_content(
                action.proof_stage,
                object_target_key=object_target_key,
                left_profile=left_profile,
                right_profile=right_profile,
            )
            if proof_content is None:
                continue
            records.append(
                {
                    "object_derived": True,
                    "status": "complete",
                    "reason_id": UnknownReasonId.METHOD_B_CLOSURE_BLOCKED.value,
                    "proof_kind": action.proof_kind,
                    "recovery_proof_kind": action.proof_kind,
                    "proof_stage": action.proof_stage,
                    "evidence_kind": action.evidence_kind,
                    "required_evidence": tuple(action.required_evidence),
                    "object_target_key": object_target_key,
                    "proof_obligation_id": proof_id,
                    "proof_source": "method_b_dual_summary_case_local_solver_equality",
                    "proof_content": proof_content,
                }
            )
            existing_ids.add(proof_id)
            changed = True
        if changed:
            analysis.completed_recovery_proof_evidence = tuple(records)

    def _method_b_dual_summary_solver_proof_content(
        self,
        proof_stage: str,
        *,
        object_target_key: Tuple[Any, ...],
        left_profile: Tuple[Any, ...],
        right_profile: Tuple[Any, ...],
    ) -> Optional[Dict[str, Any]]:
        common = {
            "object_derived": True,
            "object_target_key": object_target_key,
            "relation_kind": "dual_summary",
            "left_summary": left_profile,
            "right_summary": right_profile,
            "summary_value_equivalence": "unsat",
            "solver_equality_proof": "unsat",
            "guard_coverage": "proven",
            "seed_compensation": "vacuous",
            "term_sequence": "proven",
            "pure_side_effect_profile": "proven",
        }
        if proof_stage == "method_b_covering_case":
            return common
        if proof_stage == "method_b_guard_partition":
            return {
                **common,
                "guard_partition": "proven",
                "partition_coverage_proof": "covered",
            }
        return None

    @staticmethod
    def _method_b_recovery_action(
        actions: Sequence[Any],
        *,
        proof_kind: str,
        proof_stage: str,
    ):
        return next(
            (
                candidate
                for candidate in actions
                if candidate.proof_stage == proof_stage and candidate.proof_kind == proof_kind
            ),
            None,
        )

    @staticmethod
    def _method_b_covering_relation_matches_proof(
        relation: Any,
        *,
        exact_side: str,
        summary_side: str,
        proof: _ExactReadonlyReductionProof,
    ) -> bool:
        if not isinstance(relation, tuple) or relation[0] != "method_b_closure_relation":
            return False
        fields = {
            item[0]: item[1]
            for item in relation[1:]
            if isinstance(item, tuple) and len(item) == 2
        }
        if fields.get("kind") != "one_sided_summary":
            return False
        if fields.get("exact_side") != exact_side or fields.get("summary_side") != summary_side:
            return False
        exact_terms = fields.get("exact_terms")
        if not isinstance(exact_terms, tuple) or not exact_terms:
            return False
        if tuple(exact_terms) != tuple(term.stable_key() for term in proof.exact_terms):
            return False
        try:
            exact_constant_bias = int(fields.get("exact_constant_bias"))
        except (TypeError, ValueError):
            return False
        return exact_constant_bias == int(proof.constant_bias)

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
                    count_values=(int(count_value),),
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
        semantic_parameter_sources: Sequence[ParameterInfo] = (),
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
            if (
                isinstance(left_ref, ReadonlyReductionRef)
                or isinstance(right_ref, ReadonlyReductionRef)
            ) and str(getattr(shortcut_decision, "reason", "") or "").startswith("readonly_contract_"):
                return False
            if self._case_pair_loop_summaries_solver_equivalent(
                left_ref,
                right_ref,
                left_case=left_case,
                right_case=right_case,
                semantic_parameter_sources=semantic_parameter_sources,
            ):
                return True
            if self._counted_loop_values_are_provably_equivalent(
                left,
                right,
                left_case=left_case,
                right_case=right_case,
                semantic_parameter_sources=semantic_parameter_sources,
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

    def _case_pair_loop_summaries_solver_equivalent(
        self,
        left_ref,
        right_ref,
        *,
        left_case: Optional[ReturnCase],
        right_case: Optional[ReturnCase],
        semantic_parameter_sources: Sequence[ParameterInfo] = (),
    ) -> bool:
        if left_case is None or right_case is None:
            return False
        left_summary = getattr(left_ref, "loop_summary", None)
        right_summary = getattr(right_ref, "loop_summary", None)
        if left_summary is None or right_summary is None:
            return False
        if (
            isinstance(left_ref, CountedLoopSummaryRef)
            and isinstance(right_ref, CountedLoopSummaryRef)
            and not self._counted_loop_summary_wrapper_semantics_match(left_ref, right_ref)
        ):
            return self._case_pair_loop_summaries_solver_equivalent_core(
                left_ref,
                right_ref,
                left_case=left_case,
                right_case=right_case,
                semantic_parameter_sources=semantic_parameter_sources,
            )
        def solver_prover(obligation) -> LoopSummaryComparisonResult:
            if getattr(obligation, "proof_kind", None) != "case_aware_loop_summary_solver_equality":
                return LoopSummaryComparisonResult("unknown", "unsupported loop-summary proof obligation")
            if self._case_pair_loop_summaries_solver_equivalent_core(
                left_ref,
                right_ref,
                left_case=left_case,
                right_case=right_case,
                semantic_parameter_sources=semantic_parameter_sources,
            ):
                return LoopSummaryComparisonResult(
                    "equivalent",
                    "loop summaries proved by case-aware solver",
                    proof_obligation=obligation,
                )
            return LoopSummaryComparisonResult(
                "unknown",
                "case-aware loop-summary solver proof failed",
                proof_obligation=obligation,
            )

        result = compare_loop_summaries(
            left_summary,
            right_summary,
            solver_prover=solver_prover,
        )
        return result.is_equivalent() is True and self._case_pair_has_runtime_guard_coverage_or_equivalence(
            left_case,
            right_case,
        )

    def _case_pair_loop_summaries_solver_equivalent_core(
        self,
        left_ref,
        right_ref,
        *,
        left_case: ReturnCase,
        right_case: ReturnCase,
        semantic_parameter_sources: Sequence[ParameterInfo] = (),
    ) -> bool:
        left_summary = getattr(left_ref, "loop_summary", None)
        right_summary = getattr(right_ref, "loop_summary", None)
        if left_summary is None or right_summary is None:
            return False
        for summary in (left_summary, right_summary):
            requires_effect_proof = getattr(summary, "requires_effect_proof", None)
            if callable(requires_effect_proof) and requires_effect_proof():
                return False
            requires_path_proof = getattr(summary, "requires_path_proof", None)
            if callable(requires_path_proof) and requires_path_proof():
                return False
        if self._loop_summary_surface_blocks_solver_equality(left_summary, right_summary):
            return False
        if self._loop_summary_constant_bias(left_summary) != self._loop_summary_constant_bias(right_summary):
            return False
        if not self._counted_loop_summary_wrapper_semantics_match(left_ref, right_ref):
            return self._case_pair_counted_loop_summaries_closed_values_equivalent(
                left_ref,
                right_ref,
                left_case=left_case,
                right_case=right_case,
                semantic_parameter_sources=semantic_parameter_sources,
            )
        left_term_key = self._loop_term_descriptor_semantic_key(left_summary)
        right_term_key = self._loop_term_descriptor_semantic_key(right_summary)
        if left_term_key is None or right_term_key is None or left_term_key != right_term_key:
            return False
        left_seed = tuple(getattr(left_summary, "seed_terms", ()) or ())
        right_seed = tuple(getattr(right_summary, "seed_terms", ()) or ())
        if len(left_seed) != len(right_seed):
            return False
        if getattr(left_summary, "seed_term_count", None) != getattr(right_summary, "seed_term_count", None):
            return False
        conditions = self._combined_summary_conditions(left_case, right_case)
        expr_pairs = (
            (getattr(left_summary, "start_expr", None), getattr(right_summary, "start_expr", None)),
            (getattr(left_summary, "limit_expr", None), getattr(right_summary, "limit_expr", None)),
            (getattr(left_summary, "step_expr", None), getattr(right_summary, "step_expr", None)),
        )
        seed_expr_pairs: List[Tuple[Expression, Expression]] = []
        for left_term, right_term in zip(left_seed, right_seed):
            if isinstance(left_term, Expression) and isinstance(right_term, Expression):
                seed_expr_pairs.append((left_term, right_term))
                continue
            if left_term != right_term:
                return False
        exprs = [expr for pair in expr_pairs for expr in pair if expr is not None]
        exprs.extend(expr for pair in seed_expr_pairs for expr in pair)
        exprs.extend(condition.expression for condition in conditions or [] if condition is not None)
        parameters = self._collect_intrinsic_parameter_specs(
            left_case,
            right_case,
            *exprs,
            semantic_parameter_sources=semantic_parameter_sources,
        )
        if parameters is None:
            return False
        if self._condition_set_is_unsat(conditions, parameters):
            return True
        for left_expr, right_expr in expr_pairs:
            if left_expr is None or right_expr is None:
                return False
            if not self._prove_intrinsic_equivalence_under_conditions(
                left_expr,
                right_expr,
                conditions,
                parameters,
            ):
                return False
        for left_expr, right_expr in seed_expr_pairs:
            if not self._prove_intrinsic_equivalence_under_conditions(
                left_expr,
                right_expr,
                conditions,
                parameters,
            ):
                return False
        if not self._case_pair_has_runtime_guard_coverage_or_equivalence(left_case, right_case):
            return False
        return True

    def _case_pair_counted_loop_summaries_closed_values_equivalent(
        self,
        left_ref,
        right_ref,
        *,
        left_case: ReturnCase,
        right_case: ReturnCase,
        semantic_parameter_sources: Sequence[ParameterInfo] = (),
    ) -> bool:
        left_expr = getattr(left_case, "value_expr", None)
        right_expr = getattr(right_case, "value_expr", None)
        if getattr(left_expr, "runtime_ref", None) is not left_ref:
            return False
        if getattr(right_expr, "runtime_ref", None) is not right_ref:
            return False
        if not isinstance(left_ref, CountedLoopSummaryRef) or not isinstance(right_ref, CountedLoopSummaryRef):
            return False
        result_size = self._case_pair_comparison_result_size(left_case, right_case)
        if result_size is None:
            return False
        if not self._counted_loop_refs_allow_affine_value_proof(left_ref, right_ref):
            return False
        conditions = self._combined_summary_conditions(left_case, right_case)
        left_guards, left_guards_complete = self._runtime_summary_guard_conditions_from_expression(left_expr)
        right_guards, right_guards_complete = self._runtime_summary_guard_conditions_from_expression(right_expr)
        if not left_guards_complete or not right_guards_complete:
            return False
        for guard in tuple(left_guards) + tuple(right_guards):
            if guard not in conditions:
                conditions.append(guard)
        exprs = [left_expr, right_expr]
        exprs.extend(condition.expression for condition in conditions or [] if condition is not None)
        parameters = self._collect_intrinsic_parameter_specs(
            left_case,
            right_case,
            *exprs,
            semantic_parameter_sources=semantic_parameter_sources,
        )
        if parameters is None:
            return False
        if not self._counted_loop_affine_widths_are_safe(left_expr, right_expr, result_size, parameters):
            return False
        left_closed = self._counted_loop_affine_closed_expression(
            left_expr,
            result_size=result_size,
            conditions=conditions,
            parameters=parameters,
        )
        right_closed = self._counted_loop_affine_closed_expression(
            right_expr,
            result_size=result_size,
            conditions=conditions,
            parameters=parameters,
        )
        if left_closed is None or right_closed is None:
            return False
        if not self._case_pair_has_runtime_guard_coverage_or_equivalence(left_case, right_case):
            return False
        return self._prove_intrinsic_equivalence_under_conditions(
            left_closed,
            right_closed,
            conditions,
            parameters,
        )

    def _loop_summary_constant_bias(self, summary) -> int:
        result_size = int(getattr(summary, "result_size", 0) or 0)
        if result_size <= 0:
            descriptor = getattr(summary, "term_descriptor", None)
            result_size = int(getattr(descriptor, "result_size", 0) or 0)
        result_size = max(1, result_size or 4)
        bits = max(1, result_size * 8)
        mask = (1 << bits) - 1
        try:
            return int(getattr(summary, "constant_bias", 0) or 0) & mask
        except (TypeError, ValueError):
            return 0

    def _counted_loop_summary_wrapper_semantics_match(self, left_ref, right_ref) -> bool:
        if not isinstance(left_ref, CountedLoopSummaryRef) or not isinstance(right_ref, CountedLoopSummaryRef):
            return True
        left_bias = self._counted_loop_ref_constant_bias(left_ref)
        right_bias = self._counted_loop_ref_constant_bias(right_ref)
        return (
            int(getattr(left_ref, "induction_step", 0) or 0)
            == int(getattr(right_ref, "induction_step", 0) or 0)
            and max(1, int(getattr(left_ref, "result_size", 0) or 0))
            == max(1, int(getattr(right_ref, "result_size", 0) or 0))
            and bool(getattr(left_ref, "signed_loop", False)) == bool(getattr(right_ref, "signed_loop", False))
            and tuple(getattr(left_ref, "residue_cases", ()) or ())
            == tuple(getattr(right_ref, "residue_cases", ()) or ())
            and tuple(getattr(left_ref, "residue_bias_terms", ()) or ())
            == tuple(getattr(right_ref, "residue_bias_terms", ()) or ())
            and left_bias == right_bias
        )

    def _counted_loop_ref_constant_bias(self, ref) -> int:
        result_size = max(1, int(getattr(ref, "result_size", 0) or 4))
        bits = max(1, result_size * 8)
        mask = (1 << bits) - 1
        try:
            return int(getattr(ref, "constant_bias", 0) or 0) & mask
        except (TypeError, ValueError):
            return 0

    def _loop_summary_surface_blocks_solver_equality(self, left_summary, right_summary) -> bool:
        if getattr(left_summary, "loop_var_unit", None) != getattr(right_summary, "loop_var_unit", None):
            return True
        left_profile = getattr(left_summary, "side_effect_profile", None)
        right_profile = getattr(right_summary, "side_effect_profile", None)
        if left_profile is None or right_profile is None:
            return True
        left_profile_key = left_profile.stable_key()
        right_profile_key = right_profile.stable_key()
        if left_profile_key is None or right_profile_key is None or left_profile_key != right_profile_key:
            return True
        left_cases = tuple(getattr(left_summary, "cases", ()) or ())
        right_cases = tuple(getattr(right_summary, "cases", ()) or ())
        if len(left_cases) != len(right_cases):
            return True
        left_case_keys = tuple(case.stable_key() for case in left_cases)
        right_case_keys = tuple(case.stable_key() for case in right_cases)
        if any(key is None for key in left_case_keys + right_case_keys):
            return True
        return left_case_keys != right_case_keys

    def _loop_term_descriptor_semantic_key(self, summary) -> Optional[Tuple[Any, ...]]:
        descriptor = getattr(summary, "term_descriptor", None)
        semantic_key = getattr(descriptor, "semantic_key", None)
        if callable(semantic_key):
            try:
                key = semantic_key()
            except Exception:
                return None
            return key
        return None

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
            } and (
                isinstance(left_ref, ReadonlyReductionRef)
                or isinstance(right_ref, ReadonlyReductionRef)
            ):
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

    def _case_pair_readonly_contract_result_size(
        self,
        left_case: Optional[ReturnCase],
        right_case: Optional[ReturnCase],
    ) -> Optional[int]:
        common_size = self._case_pair_comparison_result_size(left_case, right_case)
        if common_size is not None:
            return common_size
        left_bits = self._case_comparison_bit_width(left_case)
        right_bits = self._case_comparison_bit_width(right_case)
        if (
            left_bits is None
            or right_bits is None
            or left_bits <= 0
            or right_bits <= 0
            or left_bits % 8 != 0
            or right_bits % 8 != 0
        ):
            return None
        left_ref = getattr(getattr(left_case, "value_expr", None), "runtime_ref", None)
        right_ref = getattr(getattr(right_case, "value_expr", None), "runtime_ref", None)
        if not isinstance(left_ref, ReadonlyReductionRef) or not isinstance(right_ref, ReadonlyReductionRef):
            return None
        narrow_size = min(int(left_bits), int(right_bits)) // 8
        if narrow_size <= 0:
            return None
        if (
            self._readonly_reduction_term_sequence_contract_key(left_ref, result_size=narrow_size) is None
            or self._readonly_reduction_term_sequence_contract_key(right_ref, result_size=narrow_size) is None
        ):
            return None
        return narrow_size

    def _readonly_contract_pairwise_extra_assertions(
        self,
        left_case: ReturnCase,
        right_case: ReturnCase,
        left_param_replace_fn,
        right_param_replace_fn,
    ) -> Tuple[str, ...]:
        result_size = self._case_pair_readonly_contract_result_size(left_case, right_case)
        if result_size is None:
            return ()
        left_ref = getattr(getattr(left_case, "value_expr", None), "runtime_ref", None)
        right_ref = getattr(getattr(right_case, "value_expr", None), "runtime_ref", None)
        if not isinstance(left_ref, ReadonlyReductionRef) or not isinstance(right_ref, ReadonlyReductionRef):
            return ()
        decision = self._runtime_loop_contract_shortcut_decision(
            left_ref,
            right_ref,
            result_size=result_size,
        )
        if not decision.equivalent:
            return ()
        if decision.requires_guard_equivalence and not self._case_pair_has_runtime_guard_coverage_or_equivalence(
            left_case,
            right_case,
        ):
            return ()
        target_bits = int(result_size) * 8
        left_value = left_case.get_value_smt(
            left_param_replace_fn,
            target_bits=target_bits,
            use_sign_extension=left_case.should_sign_extend_value(),
        )
        right_value = right_case.get_value_smt(
            right_param_replace_fn,
            target_bits=target_bits,
            use_sign_extension=right_case.should_sign_extend_value(),
        )
        if not left_value or not right_value:
            return ()
        return (
            "; readonly reduction contract equality at proven narrow return surface",
            f"(assert (= {left_value} {right_value}))",
        )

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
            or not self._readonly_contract_count_identities_compatible(left_ref, right_ref)
            or self._normalize_constant_bias(int(getattr(left_ref, "constant_bias", 0) or 0), effective_result_size)
            != self._normalize_constant_bias(int(getattr(right_ref, "constant_bias", 0) or 0), effective_result_size)
        ):
            if self.debug:
                print(
                    "[PairwiseStrategy] readonly contract surface mismatch: "
                    f"left_kind={getattr(left_ref, 'reduction_kind', None)}, "
                    f"right_kind={getattr(right_ref, 'reduction_kind', None)}, "
                    f"left_base={left_base_key}, right_base={right_base_key}, "
                    f"left_count_identities={tuple(sorted(self._readonly_count_identity_keys(left_ref), key=repr))}, "
                    f"right_count_identities={tuple(sorted(self._readonly_count_identity_keys(right_ref), key=repr))}, "
                    f"count_compatible={self._readonly_contract_count_identities_compatible(left_ref, right_ref)}, "
                    f"left_bias={self._normalize_constant_bias(int(getattr(left_ref, 'constant_bias', 0) or 0), effective_result_size)}, "
                    f"right_bias={self._normalize_constant_bias(int(getattr(right_ref, 'constant_bias', 0) or 0), effective_result_size)}"
                )
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
        if left_key[:3] != right_key[:3] or left_key[5:] != right_key[5:]:
            return False
        if not self._readonly_contract_count_identities_compatible(left_ref, right_ref):
            return False
        if not self._readonly_contract_limit_keys_compatible(left_key[4], right_key[4], left_ref, right_ref):
            return False
        return tuple(left_key[3]) in self._readonly_count_identity_keys(left_ref) and tuple(
            right_key[3]
        ) in self._readonly_count_identity_keys(right_ref)

    def _readonly_contract_limit_keys_compatible(
        self,
        left_limit_key: tuple,
        right_limit_key: tuple,
        left_ref: ReadonlyReductionRef,
        right_ref: ReadonlyReductionRef,
    ) -> bool:
        if left_limit_key == right_limit_key:
            return True
        left_limit = tuple(left_limit_key or ())
        right_limit = tuple(right_limit_key or ())
        if self._loop_limit_storage_key_is_legacy_index_compatible(left_limit, right_limit, left_ref, right_ref):
            return True
        if self._loop_limit_storage_key_is_legacy_index_compatible(right_limit, left_limit, right_ref, left_ref):
            return True
        return False

    def _readonly_projection_contract_limit_keys_compatible(
        self,
        left_limit_key: tuple,
        right_limit_key: tuple,
        left_ref: ReadonlyReductionRef,
        right_ref: ReadonlyReductionRef,
    ) -> bool:
        if self._readonly_contract_limit_keys_compatible(left_limit_key, right_limit_key, left_ref, right_ref):
            return True
        left_limit = tuple(left_limit_key or ())
        right_limit = tuple(right_limit_key or ())
        left_storage = self._loop_limit_storage_identity_key(left_limit)
        right_storage = self._loop_limit_storage_identity_key(right_limit)
        if left_storage is None or right_storage is None:
            return False
        if left_storage != self._readonly_count_storage_identity_key(left_ref):
            return False
        if right_storage != self._readonly_count_storage_identity_key(right_ref):
            return False
        return self._readonly_contract_count_projection_compatible(left_ref, right_ref)

    def _loop_limit_storage_identity_key(self, limit_key: tuple) -> Optional[tuple]:
        normalized = tuple(limit_key or ())
        if len(normalized) != 2:
            return None
        tag, value = normalized
        if tag == "loop_limit_parameter_storage":
            value_tuple = tuple(value or ())
            if len(value_tuple) == 2 and value_tuple[0] == "storage_identity":
                return ("parameter_storage", tuple(value_tuple[1]))
            return ("parameter_storage", value_tuple)
        if tag == "loop_limit_count_storage_identity":
            return ("parameter_storage", tuple(value or ()))
        return None

    def _loop_limit_storage_key_is_legacy_index_compatible(
        self,
        storage_limit_key: tuple,
        index_limit_key: tuple,
        storage_ref: ReadonlyReductionRef,
        index_ref: ReadonlyReductionRef,
    ) -> bool:
        if not storage_limit_key or storage_limit_key[0] not in {
            "loop_limit_parameter_storage",
            "loop_limit_count_storage_identity",
        }:
            return False
        if len(index_limit_key) != 2 or index_limit_key[0] != "loop_limit_parameter":
            return False
        if self._readonly_count_storage_identity_key(index_ref) is not None:
            return False
        storage_index = self._readonly_count_index_identity_key(storage_ref)
        index_identity = self._readonly_count_index_identity_key(index_ref)
        try:
            limit_index_identity = ("parameter", int(index_limit_key[1]))
        except (TypeError, ValueError):
            return False
        return (
            storage_index is not None
            and index_identity is not None
            and storage_index == index_identity
            and storage_index == limit_index_identity
        )

    def _readonly_contract_count_identities_compatible(
        self,
        left_ref: ReadonlyReductionRef,
        right_ref: ReadonlyReductionRef,
    ) -> bool:
        return self._readonly_count_identities_compatible(left_ref, right_ref)

    def _readonly_projection_contract_count_identities_compatible(
        self,
        left_ref: ReadonlyReductionRef,
        right_ref: ReadonlyReductionRef,
    ) -> bool:
        if self._readonly_count_identities_compatible(left_ref, right_ref):
            return True
        return self._readonly_contract_count_projection_compatible(left_ref, right_ref)

    def _readonly_contract_count_projection_compatible(
        self,
        left_ref: ReadonlyReductionRef,
        right_ref: ReadonlyReductionRef,
    ) -> bool:
        left_storage = self._readonly_count_storage_identity_key(left_ref)
        right_storage = self._readonly_count_storage_identity_key(right_ref)
        left_index = self._readonly_count_index_identity_key(left_ref)
        right_index = self._readonly_count_index_identity_key(right_ref)
        if (
            left_storage is None
            or right_storage is None
            or left_index is None
            or right_index is None
            or left_index != right_index
        ):
            return False
        left_register = self._register_storage_identity_components(left_storage)
        right_register = self._register_storage_identity_components(right_storage)
        if left_register is None or right_register is None:
            return False
        if left_register[:3] != right_register[:3]:
            return False
        left_low, left_size = int(left_register[3]), int(left_register[4])
        right_low, right_size = int(right_register[3]), int(right_register[4])
        if left_size == right_size:
            return False
        left_high = left_low + left_size
        right_high = right_low + right_size
        return (
            left_low <= right_low and right_high <= left_high
        ) or (
            right_low <= left_low and left_high <= right_high
        )

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
                identities.add(("parameter_index", int(index)))
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
        left_storage = self._readonly_count_storage_identity_key(left_ref)
        right_storage = self._readonly_count_storage_identity_key(right_ref)
        left_index = self._readonly_count_index_identity_key(left_ref)
        right_index = self._readonly_count_index_identity_key(right_ref)
        if left_storage is not None and right_storage is not None:
            if left_storage == right_storage:
                return True
            return self._count_identity_components_compatible(
                left_storage,
                left_index,
                right_storage,
                right_index,
            )
        return self._count_identity_components_compatible(
            left_storage,
            left_index,
            right_storage,
            right_index,
        )

    def _record_completed_readonly_identity_projection_proof_if_safe(
        self,
        reason_record,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        case1: ReturnCase,
        case2: ReturnCase,
    ) -> None:
        if not self.enable_completed_recovery_proofs:
            return
        if reason_record.reason_id != UnknownReasonId.READONLY_IDENTITY_MISSING.value:
            return
        object_target_key = self._normalize_nested_tuple(reason_record.object_target_key)
        if not self._readonly_identity_target_is_specific(object_target_key):
            return
        left_ref = getattr(getattr(case1, "value_expr", None), "runtime_ref", None)
        right_ref = getattr(getattr(case2, "value_expr", None), "runtime_ref", None)
        if not isinstance(left_ref, ReadonlyReductionRef) or not isinstance(right_ref, ReadonlyReductionRef):
            return
        relation = self._readonly_identity_storage_relation_from_target(object_target_key)
        if not isinstance(relation, tuple) or not relation or relation[0] != "same_register_base_projection":
            return
        if not self._readonly_projection_term_contracts_match(left_ref, right_ref):
            return
        if not self._readonly_projection_semantic_witnesses_match(left_ref, right_ref):
            return
        if not self._case_pair_has_runtime_guard_coverage_or_equivalence(case1, case2):
            return
        extension_evidence = self._readonly_projection_parameter_extension_evidence(
            analysis1,
            analysis2,
            left_ref,
            right_ref,
            relation,
        )
        if extension_evidence is None:
            return

        actions = tuple(build_unknown_recovery_actions([reason_record]))
        if len(actions) != 1:
            return
        action = actions[0]
        proof_id = self._normalize_nested_tuple(action.proof_obligation_id)
        if proof_id is None:
            return
        records: List[Dict[str, Any]] = [
            dict(item)
            for item in getattr(analysis1, "completed_recovery_proof_evidence", ()) or ()
            if isinstance(item, Mapping)
        ]
        existing_ids = {
            self._normalize_nested_tuple(item.get("proof_obligation_id"))
            for item in records
        }
        if proof_id in existing_ids:
            return
        proof_content = {
            "object_derived": True,
            "object_target_key": object_target_key,
            "left_side": object_target_key[2],
            "right_side": object_target_key[3],
            "object_storage_identity": "matched",
            "count_identity": "matched",
            "guard_implication": "proven",
            "finite_witness": "checked",
            "storage_relation": relation,
            "term_contract_relation": {
                "object_derived": True,
                "status": "matched",
                "relation": "same_except_count_storage_projection",
                "left_term_contract": self._readonly_reduction_term_sequence_contract_key(
                    left_ref,
                    result_size=getattr(left_ref, "result_size", None),
                ),
                "right_term_contract": self._readonly_reduction_term_sequence_contract_key(
                    right_ref,
                    result_size=getattr(right_ref, "result_size", None),
                ),
            },
            "parameter_extension": extension_evidence,
        }
        records.append(
            {
                "object_derived": True,
                "status": "complete",
                "reason_id": UnknownReasonId.READONLY_IDENTITY_MISSING.value,
                "proof_kind": action.proof_kind,
                "recovery_proof_kind": action.proof_kind,
                "proof_stage": action.proof_stage,
                "evidence_kind": action.evidence_kind,
                "required_evidence": tuple(action.required_evidence),
                "object_target_key": object_target_key,
                "proof_obligation_id": proof_id,
                "proof_source": "readonly_same_register_projection_semantic_extension",
                "proof_content": proof_content,
            }
        )
        analysis1.completed_recovery_proof_evidence = tuple(records)

    def _readonly_projection_term_contracts_match(
        self,
        left_ref: ReadonlyReductionRef,
        right_ref: ReadonlyReductionRef,
    ) -> bool:
        left_key = self._readonly_reduction_term_sequence_contract_key(
            left_ref,
            result_size=getattr(left_ref, "result_size", None),
        )
        right_key = self._readonly_reduction_term_sequence_contract_key(
            right_ref,
            result_size=getattr(right_ref, "result_size", None),
        )
        if not isinstance(left_key, tuple) or not isinstance(right_key, tuple):
            return False
        if left_key == right_key:
            return True
        if (
            len(left_key) != len(right_key)
            or len(left_key) < 5
            or left_key[0] != "readonly_reduction_term_sequence_contract"
            or right_key[0] != "readonly_reduction_term_sequence_contract"
        ):
            return False
        return (
            left_key[:3] == right_key[:3]
            and left_key[5:] == right_key[5:]
            and self._readonly_projection_contract_count_identities_compatible(left_ref, right_ref)
            and self._readonly_projection_contract_limit_keys_compatible(left_key[4], right_key[4], left_ref, right_ref)
        )

    def _readonly_projection_semantic_witnesses_match(
        self,
        left_ref: ReadonlyReductionRef,
        right_ref: ReadonlyReductionRef,
    ) -> bool:
        left_witnesses = self._readonly_semantic_witness_keys(left_ref)
        right_witnesses = self._readonly_semantic_witness_keys(right_ref)
        return bool(left_witnesses) and left_witnesses == right_witnesses

    def _readonly_semantic_witness_keys(self, readonly_ref: ReadonlyReductionRef) -> Tuple[Any, ...]:
        witnesses = getattr(readonly_ref, "semantic_witnesses", None)
        if witnesses is None:
            proof = getattr(readonly_ref, "accumulator_proof", None)
            witnesses = getattr(proof, "semantic_witnesses", None)
        keys: List[Any] = []
        for witness in witnesses or ():
            if hasattr(witness, "stable_key"):
                keys.append(witness.stable_key())
                continue
            try:
                keys.append(tuple(witness))
            except TypeError:
                return ()
        return tuple(keys)

    def _readonly_projection_parameter_extension_evidence(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        left_ref: ReadonlyReductionRef,
        right_ref: ReadonlyReductionRef,
        relation: Tuple[Any, ...],
    ) -> Optional[Dict[str, Any]]:
        try:
            left_bits = self._readonly_projection_span(relation, "left_bits")
            right_bits = self._readonly_projection_span(relation, "right_bits")
        except (TypeError, ValueError):
            return None
        if left_bits is None or right_bits is None:
            return None
        left_low, left_size = left_bits
        right_low, right_size = right_bits
        if left_size == right_size:
            return None
        if left_size > right_size:
            wide_side, narrow_side = "left", "right"
            wide_bits, narrow_bits = left_size, right_size
            wide_low, narrow_low = left_low, right_low
            wide_analysis, narrow_analysis = analysis1, analysis2
            wide_ref, narrow_ref = left_ref, right_ref
        else:
            wide_side, narrow_side = "right", "left"
            wide_bits, narrow_bits = right_size, left_size
            wide_low, narrow_low = right_low, left_low
            wide_analysis, narrow_analysis = analysis2, analysis1
            wide_ref, narrow_ref = right_ref, left_ref
        shared_index = self._readonly_shared_parameter_index(left_ref, right_ref)
        if shared_index is None:
            return None
        signedness = self._readonly_declared_narrow_parameter_signedness(
            wide_analysis,
            shared_index,
            narrow_bits,
            wide_bits,
        )
        source = (
            "declared_parameter_narrow_type_on_wide_storage"
            if signedness is not None
            else None
        )
        if signedness is None:
            return None
        if self._readonly_declared_parameter_bits(narrow_analysis, shared_index) != narrow_bits:
            return None
        if not self._readonly_projection_ref_storage_matches(
            wide_ref,
            wide_bits=wide_bits,
            low_bit=wide_low,
        ):
            return None
        if not self._readonly_projection_ref_storage_matches(
            narrow_ref,
            wide_bits=wide_bits,
            low_bit=narrow_low,
            size_bits=narrow_bits,
        ):
            return None
        return {
            "object_derived": True,
            "status": "proven",
            "relation": "same_register_base_projection_semantic_extension",
            "projection_relation": relation,
            "wide_side": wide_side,
            "narrow_side": narrow_side,
            "parameter_index": shared_index,
            "signedness": signedness,
            "narrow_bits": narrow_bits,
            "wide_bits": wide_bits,
            "extension": "sign_extend" if signedness == "signed" else "zero_extend",
            "proof_source": source,
        }

    @staticmethod
    def _readonly_projection_span(relation: Tuple[Any, ...], tag: str) -> Optional[Tuple[int, int]]:
        for item in relation:
            if isinstance(item, tuple) and len(item) == 3 and item[0] == tag:
                return int(item[1]), int(item[2])
        return None

    def _readonly_shared_parameter_index(
        self,
        left_ref: ReadonlyReductionRef,
        right_ref: ReadonlyReductionRef,
    ) -> Optional[int]:
        left_index = self._readonly_count_index_identity_key(left_ref)
        right_index = self._readonly_count_index_identity_key(right_ref)
        if (
            isinstance(left_index, tuple)
            and isinstance(right_index, tuple)
            and len(left_index) == 2
            and len(right_index) == 2
            and left_index[0] == "parameter"
            and right_index[0] == "parameter"
            and left_index[1] == right_index[1]
        ):
            return int(left_index[1])
        return None

    @staticmethod
    def _readonly_declared_parameter_bits(
        analysis: FunctionReturnAnalysis,
        index: int,
    ) -> Optional[int]:
        for param in getattr(analysis, "parameters", ()) or ():
            try:
                if int(param.get("index", -1)) != int(index):
                    continue
                return int(param.get("size", 0)) * 8
            except (TypeError, ValueError):
                return None
        return None

    def _readonly_declared_narrow_parameter_signedness(
        self,
        analysis: FunctionReturnAnalysis,
        index: int,
        narrow_bits: int,
        wide_bits: int,
    ) -> Optional[str]:
        for param in getattr(analysis, "parameters", ()) or ():
            try:
                if int(param.get("index", -1)) != int(index):
                    continue
                size_bits = int(param.get("size", 0)) * 8
            except (TypeError, ValueError):
                return None
            storage_info = param.get("storage_info") or param.get("storage")
            storage_key_fn = getattr(storage_info, "storage_identity_key", None)
            storage_key = storage_key_fn() if callable(storage_key_fn) else None
            if size_bits != int(narrow_bits):
                continue
            if storage_key is None:
                continue
            components = self._register_storage_identity_components(("parameter_storage", tuple(storage_key)))
            if components is None or components[2] != int(wide_bits):
                continue
            signedness = self._readonly_parameter_declared_signedness(param)
            if signedness is None:
                return None
            return signedness
        return None

    @staticmethod
    def _readonly_parameter_declared_signedness(param: Mapping[str, Any]) -> Optional[str]:
        if "is_signed" in param:
            explicit_signedness = param.get("is_signed")
            if explicit_signedness is True:
                return "signed"
            if explicit_signedness is False:
                return "unsigned"
            return None
        data_type_obj = param.get("data_type_obj")
        if data_type_obj is None:
            return None
        is_signed = getattr(data_type_obj, "isSigned", None)
        if not callable(is_signed):
            return None
        try:
            signed_value = is_signed()
        except Exception:
            return None
        if signed_value is True:
            return "signed"
        if signed_value is False:
            return "unsigned"
        return None

    def _readonly_projection_ref_storage_matches(
        self,
        readonly_ref: ReadonlyReductionRef,
        *,
        wide_bits: int,
        low_bit: int,
        size_bits: Optional[int] = None,
    ) -> bool:
        storage = self._readonly_count_storage_identity_key(readonly_ref)
        components = self._register_storage_identity_components(storage)
        if components is None:
            return False
        _, _, base_bits, ref_low, ref_size = components
        expected_size = int(size_bits) if size_bits is not None else int(wide_bits)
        return base_bits == int(wide_bits) and ref_low == int(low_bit) and ref_size == expected_size

    def _readonly_identity_object_target_key(
        self,
        *,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        pair_id: str,
    ) -> Tuple[Any, ...]:
        """Object-derived target key for readonly operand identity proof backlog."""

        return (
            "readonly_identity",
            ("pair", pair_id),
            self._readonly_identity_side_object_key(
                "left",
                base_ctx.get("analysis1"),
                case1,
            ),
            self._readonly_identity_side_object_key(
                "right",
                base_ctx.get("analysis2"),
                case2,
            ),
            self._readonly_identity_relation_object_key(case1, case2),
        )

    def _readonly_identity_relation_object_key(
        self,
        case1: ReturnCase,
        case2: ReturnCase,
    ) -> Tuple[Any, ...]:
        left_ref = getattr(getattr(case1, "value_expr", None), "runtime_ref", None)
        right_ref = getattr(getattr(case2, "value_expr", None), "runtime_ref", None)
        if not isinstance(left_ref, ReadonlyReductionRef) or not isinstance(right_ref, ReadonlyReductionRef):
            return ("readonly_identity_relation", ("kind", "missing_readonly_ref"))
        left_identities = self._readonly_count_identity_keys(left_ref)
        right_identities = self._readonly_count_identity_keys(right_ref)
        shared_identities = tuple(sorted(left_identities & right_identities, key=repr))
        return (
            "readonly_identity_relation",
            ("shared_count_identities", shared_identities),
            (
                "count_storage_relation",
                self._readonly_count_storage_relation_key(left_ref, right_ref),
            ),
        )

    def _readonly_count_storage_relation_key(
        self,
        left_ref: ReadonlyReductionRef,
        right_ref: ReadonlyReductionRef,
    ) -> Tuple[Any, ...]:
        left_storage = self._readonly_count_storage_identity_key(left_ref)
        right_storage = self._readonly_count_storage_identity_key(right_ref)
        if left_storage is None or right_storage is None:
            return ("missing_storage_identity", left_storage, right_storage)
        if left_storage == right_storage:
            return ("same_storage_identity", left_storage)
        left_register = self._register_storage_identity_components(left_storage)
        right_register = self._register_storage_identity_components(right_storage)
        if left_register is None or right_register is None:
            return ("different_storage_identity", left_storage, right_storage)
        if left_register[:3] != right_register[:3]:
            return ("different_register_base", left_storage, right_storage)
        left_low, left_size = left_register[3], left_register[4]
        right_low, right_size = right_register[3], right_register[4]
        left_high = left_low + left_size
        right_high = right_low + right_size
        contains = None
        if left_low <= right_low and right_high <= left_high:
            contains = "left_contains_right"
        elif right_low <= left_low and left_high <= right_high:
            contains = "right_contains_left"
        return (
            "same_register_base_projection",
            ("base", left_register[:3]),
            ("left_bits", left_low, left_size),
            ("right_bits", right_low, right_size),
            ("projection", contains or "overlap_or_disjoint"),
        )

    def _register_storage_identity_components(
        self,
        storage_identity: Optional[tuple],
    ) -> Optional[Tuple[int, int, int, int, int]]:
        normalized = tuple(storage_identity or ())
        if (
            len(normalized) == 2
            and normalized[0] == "parameter_storage"
            and isinstance(normalized[1], tuple)
        ):
            normalized = tuple(normalized[1])
        if len(normalized) != 6 or normalized[0] != "register_storage":
            return None
        try:
            return (
                int(normalized[1]),
                int(normalized[2]),
                int(normalized[3]),
                int(normalized[4]),
                int(normalized[5]),
            )
        except (TypeError, ValueError):
            return None

    def _method_b_closure_object_target_key(
        self,
        *,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        pair_id: str,
    ) -> Tuple[Any, ...]:
        """Object-derived target key for Method-B covering/guard proof backlog."""

        return (
            "method_b_closure",
            ("pair", pair_id),
            self._method_b_closure_side_object_key(
                "left",
                base_ctx.get("analysis1"),
                case1,
            ),
            self._method_b_closure_side_object_key(
                "right",
                base_ctx.get("analysis2"),
                case2,
            ),
            self._method_b_closure_relation_object_key(case1, case2),
        )

    def _method_b_closure_relation_object_key(
        self,
        case1: ReturnCase,
        case2: ReturnCase,
    ) -> Tuple[Any, ...]:
        left_readonly_ref = self._method_b_readonly_summary_ref(getattr(case1, "value_expr", None))
        right_readonly_ref = self._method_b_readonly_summary_ref(getattr(case2, "value_expr", None))
        left_summary_ref = self._method_b_summary_runtime_ref(getattr(case1, "value_expr", None))
        right_summary_ref = self._method_b_summary_runtime_ref(getattr(case2, "value_expr", None))
        if left_readonly_ref is not None and right_summary_ref is None:
            return self._method_b_one_sided_summary_relation(
                summary_side="left",
                summary_ref=left_readonly_ref,
                exact_side="right",
                exact_case=case2,
            )
        if right_readonly_ref is not None and left_summary_ref is None:
            return self._method_b_one_sided_summary_relation(
                summary_side="right",
                summary_ref=right_readonly_ref,
                exact_side="left",
                exact_case=case1,
            )
        if left_summary_ref is not None and right_summary_ref is not None:
            return (
                "method_b_closure_relation",
                ("kind", "dual_summary"),
                ("left_summary", self._method_b_summary_profile_key(left_summary_ref)),
                ("right_summary", self._method_b_summary_profile_key(right_summary_ref)),
            )
        return ("method_b_closure_relation", ("kind", "missing_method_b_summary"))

    def _method_b_summary_runtime_ref(self, expr: Optional[Expression]):
        runtime_ref = getattr(expr, "runtime_ref", None)
        if isinstance(runtime_ref, (ReadonlyReductionRef, CountedLoopSummaryRef)) and getattr(
            runtime_ref,
            "loop_summary",
            None,
        ) is not None:
            return runtime_ref
        return None

    def _method_b_readonly_summary_ref(self, expr: Optional[Expression]) -> Optional[ReadonlyReductionRef]:
        runtime_ref = getattr(expr, "runtime_ref", None)
        if isinstance(runtime_ref, ReadonlyReductionRef) and getattr(runtime_ref, "loop_summary", None) is not None:
            return runtime_ref
        return None

    def _method_b_one_sided_summary_relation(
        self,
        *,
        summary_side: str,
        summary_ref: ReadonlyReductionRef,
        exact_side: str,
        exact_case: ReturnCase,
    ) -> Tuple[Any, ...]:
        extracted = self._extract_readonly_reduction_terms_and_bias_from_expression(
            getattr(exact_case, "value_expr", None),
            getattr(exact_case, "parameters", ()) or (),
            getattr(summary_ref, "pointer_base_ref", None),
            program_is_big_endian=getattr(exact_case, "program_is_big_endian", None),
        )
        exact_terms_key: Any = ("exact_terms_unavailable",)
        exact_bias: Any = None
        if extracted is not None:
            exact_terms, exact_bias = extracted
            exact_terms_key = tuple(term.stable_key() for term in exact_terms)
        return (
            "method_b_closure_relation",
            ("kind", "one_sided_summary"),
            ("summary_side", summary_side),
            ("exact_side", exact_side),
            ("summary", self._method_b_summary_profile_key(summary_ref)),
            ("exact_terms", exact_terms_key),
            ("exact_constant_bias", exact_bias),
        )

    def _method_b_summary_profile_key(self, summary_ref) -> Tuple[Any, ...]:
        if isinstance(summary_ref, CountedLoopSummaryRef):
            runtime_ref_key = self._counted_loop_summary_runtime_profile_key(summary_ref)
            loop_summary_key = self._counted_loop_summary_loop_profile_key(getattr(summary_ref, "loop_summary", None))
            term_contract = self._counted_loop_summary_contract_key(summary_ref)
            count_identities = self._counted_loop_summary_count_identities(summary_ref)
        else:
            runtime_ref_key = self._semantic_key_or_stable_key_or_none(summary_ref)
            loop_summary_key = self._semantic_key_or_stable_key_or_none(getattr(summary_ref, "loop_summary", None))
            term_contract = self._readonly_reduction_term_sequence_contract_key(
                summary_ref,
                result_size=getattr(summary_ref, "result_size", None),
            )
            term_contract = self._method_b_normalized_term_contract_key(summary_ref, term_contract)
            count_identities = tuple(sorted(self._readonly_count_identity_keys(summary_ref), key=repr))
        return (
            "method_b_summary_profile",
            ("runtime_ref", runtime_ref_key),
            ("loop_summary", loop_summary_key),
            ("term_contract", term_contract),
            ("count_identities", tuple(sorted(count_identities, key=repr))),
        )

    def _counted_loop_summary_runtime_profile_key(self, counted_ref: CountedLoopSummaryRef) -> Tuple[Any, ...]:
        return (
            "counted_loop_summary_profile_ref",
            max(1, int(getattr(counted_ref, "result_size", 0) or 0)),
            int(getattr(counted_ref, "induction_step", 0) or 0),
            bool(getattr(counted_ref, "signed_loop", False)),
            tuple(getattr(counted_ref, "residue_cases", ()) or ()),
            tuple(
                (
                    int(modulus),
                    int(residue),
                    self._method_b_value_key_or_none(bias_expr),
                )
                for modulus, residue, bias_expr in tuple(getattr(counted_ref, "residue_bias_terms", ()) or ())
            ),
            self._counted_loop_ref_constant_bias(counted_ref),
        )

    def _counted_loop_summary_loop_profile_key(self, loop_summary: Optional[LoopSummaryRef]) -> Optional[Tuple[Any, ...]]:
        if loop_summary is None:
            return None
        descriptor = getattr(loop_summary, "term_descriptor", None)
        descriptor_key = self._method_b_key_with_explicit_optional_none(
            self._semantic_key_or_stable_key_or_none(descriptor)
        )
        side_effect_key = self._method_b_key_with_explicit_optional_none(
            self._semantic_key_or_stable_key_or_none(getattr(loop_summary, "side_effect_profile", None))
        )
        if descriptor_key is None or side_effect_key is None:
            return None
        return (
            "counted_loop_summary_loop_profile",
            getattr(loop_summary, "loop_var_unit", None) or "unknown_loop_var_unit",
            self._method_b_value_key_or_none(getattr(loop_summary, "start_expr", None)),
            self._method_b_value_key_or_none(getattr(loop_summary, "limit_expr", None)),
            self._method_b_value_key_or_none(getattr(loop_summary, "step_expr", None)),
            descriptor_key,
            side_effect_key,
            tuple(
                self._method_b_key_with_explicit_optional_none(
                    getattr(case, "stable_key", lambda: None)()
                )
                for case in tuple(getattr(loop_summary, "cases", ()) or ())
            ),
        )

    def _counted_loop_summary_contract_key(self, counted_ref: CountedLoopSummaryRef) -> Optional[Tuple[Any, ...]]:
        runtime_key = self._counted_loop_summary_runtime_profile_key(counted_ref)
        loop_summary = getattr(counted_ref, "loop_summary", None)
        loop_key = self._counted_loop_summary_loop_profile_key(loop_summary)
        if runtime_key is None or loop_key is None:
            return None
        residue_bias_terms = tuple(
            (
                int(modulus),
                int(residue),
                self._method_b_value_key_or_none(bias_expr),
            )
            for modulus, residue, bias_expr in tuple(getattr(counted_ref, "residue_bias_terms", ()) or ())
        )
        if any(term[2] is None for term in residue_bias_terms):
            return None
        return (
            "counted_loop_summary_contract",
            runtime_key,
            loop_key,
            max(1, int(getattr(counted_ref, "result_size", 0) or 0)),
            int(getattr(counted_ref, "induction_step", 0) or 0),
            bool(getattr(counted_ref, "signed_loop", False)),
            tuple(getattr(counted_ref, "residue_cases", ()) or ()),
            residue_bias_terms,
            self._counted_loop_ref_constant_bias(counted_ref),
            tuple(case.stable_key() for case in tuple(getattr(loop_summary, "cases", ()) or ())),
        )

    def _counted_loop_summary_count_identities(self, counted_ref: CountedLoopSummaryRef) -> Tuple[Tuple[Any, ...], ...]:
        identities: List[Tuple[Any, ...]] = []
        for value in (
            getattr(counted_ref, "start_expr", None),
            getattr(counted_ref, "limit_expr", None),
            getattr(counted_ref, "step_expr", None),
        ):
            key = self._method_b_value_key_or_none(value)
            if key is not None:
                identities.append(("expression", key))
        loop_summary = getattr(counted_ref, "loop_summary", None)
        for value in (
            getattr(loop_summary, "start_expr", None),
            getattr(loop_summary, "limit_expr", None),
            getattr(loop_summary, "step_expr", None),
        ):
            key = self._method_b_value_key_or_none(value)
            if key is not None:
                identities.append(("loop_expression", key))
        return tuple(dict.fromkeys(identities))

    def _method_b_value_key_or_none(self, value: Any):
        key = self._semantic_key_or_stable_key_or_none(value)
        if key is not None:
            return self._method_b_key_with_explicit_optional_none(key)
        structural_key = getattr(value, "structural_key", None)
        if callable(structural_key):
            try:
                return self._method_b_key_with_explicit_optional_none(structural_key(budget=256))
            except (AttributeError, TypeError, ValueError, RecursionError):
                return None
        return None

    def _method_b_key_with_explicit_optional_none(self, value: Any):
        if value is None:
            return ("optional_none",)
        if isinstance(value, tuple):
            return tuple(self._method_b_key_with_explicit_optional_none(item) for item in value)
        if isinstance(value, list):
            return tuple(self._method_b_key_with_explicit_optional_none(item) for item in value)
        return value

    def _method_b_normalized_term_contract_key(
        self,
        readonly_ref: ReadonlyReductionRef,
        term_contract: Optional[tuple],
    ) -> Optional[tuple]:
        if not isinstance(term_contract, tuple) or not term_contract:
            return term_contract
        if term_contract[0] != "loop_summary_method_b" or len(term_contract) < 9:
            return term_contract
        pointer_base = self._semantic_key_or_stable_key_or_none(getattr(readonly_ref, "pointer_base_ref", None))
        count_identities = tuple(sorted(self._readonly_count_identity_keys(readonly_ref), key=repr))
        count_identity = count_identities[0] if count_identities else None
        if pointer_base is None or count_identity is None:
            return term_contract
        term_sequence = term_contract[5]
        if not isinstance(term_sequence, tuple) or len(term_sequence) < 7:
            return term_contract
        try:
            result_size = max(1, int(getattr(readonly_ref, "result_size", 0) or term_sequence[6]))
        except (TypeError, ValueError):
            return term_contract
        return (
            "readonly_reduction_term_sequence_contract",
            str(getattr(readonly_ref, "reduction_kind", None) or "memory_sum"),
            pointer_base,
            count_identity,
            term_contract[3],
            result_size,
            term_sequence[3],
            term_contract[4],
            getattr(readonly_ref, "constant_bias", 0),
            term_sequence[5],
            bool(getattr(readonly_ref, "signed_counter", False)),
            term_contract[6],
            term_contract[7],
            term_contract[8],
        )

    def _unresolved_expression_object_target_key(
        self,
        *,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        pair_id: str,
    ) -> Tuple[Any, ...]:
        """Object-derived target key for unresolved-expression diagnostics."""

        target: List[Any] = [
            "unresolved_expression",
            ("pair", pair_id),
            self._unresolved_expression_side_object_key(
                "left",
                base_ctx.get("analysis1"),
                case1,
            ),
            self._unresolved_expression_side_object_key(
                "right",
                base_ctx.get("analysis2"),
                case2,
            ),
        ]
        lowering_diagnostic = self._unresolved_expression_pair_lowering_diagnostic(
            case1,
            case2,
        )
        if lowering_diagnostic is not None:
            target.append(lowering_diagnostic)
        return tuple(target)

    def _solver_rewrite_candidate_object_target_key(
        self,
        *,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        pair_id: str,
    ) -> Tuple[Any, ...]:
        """Object-derived target key for solver rewrite candidate generation."""

        return (
            "solver_rewrite_candidate",
            ("pair", pair_id),
            ("rewrite_stage", "rewrite_candidate_generation"),
            self._solver_rewrite_side_object_key(
                "left",
                base_ctx.get("analysis1"),
                case1,
            ),
            self._solver_rewrite_side_object_key(
                "right",
                base_ctx.get("analysis2"),
                case2,
            ),
        )

    def _solver_rewrite_proof_object_target_key(
        self,
        *,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        pair_id: str,
        rewrite_side: str,
        original_expr: Any,
        rewritten_expr: Any,
        rewrite_label: str,
    ) -> Tuple[Any, ...]:
        """Object-derived target key for solver rewrite proof recheck backlog."""

        return (
            "solver_rewrite_proof",
            ("pair", pair_id),
            ("rewrite_side", rewrite_side),
            ("rewrite_stage", rewrite_label),
            self._solver_rewrite_side_object_key(
                "left",
                base_ctx.get("analysis1"),
                case1,
            ),
            self._solver_rewrite_side_object_key(
                "right",
                base_ctx.get("analysis2"),
                case2,
            ),
            ("original_expression", self._expression_runtime_object_key(original_expr)),
            ("rewritten_expression", self._expression_runtime_object_key(rewritten_expr)),
        )

    def _solver_rewrite_side_object_key(
        self,
        side_label: str,
        analysis: Optional[FunctionReturnAnalysis],
        case: ReturnCase,
    ) -> Tuple[Any, ...]:
        target = (
            "solver_rewrite_side",
            side_label,
            self._analysis_entry_key(analysis) if analysis is not None else None,
            self._return_storage_object_key(analysis) if analysis is not None else None,
            self._return_case_partition_member_object_key(
                case,
                getattr(case, "return_info", None),
            ),
            ("typed_expression_key", self._expression_runtime_object_key(getattr(case, "value_expr", None))),
            (
                "guards",
                tuple(
                    self._return_condition_object_key(condition)
                    for condition in (getattr(case, "conditions", None) or ())
                ),
            ),
        )
        if analysis is not None:
            return self._artifact_stable_key_for_analysis(target, analysis)
        return target

    def _unresolved_expression_side_object_key(
        self,
        side_label: str,
        analysis: Optional[FunctionReturnAnalysis],
        case: ReturnCase,
    ) -> Tuple[Any, ...]:
        target = (
            "unresolved_expression_side",
            side_label,
            self._analysis_entry_key(analysis) if analysis is not None else None,
            self._return_storage_object_key(analysis) if analysis is not None else None,
            self._return_case_partition_member_object_key(
                case,
                getattr(case, "return_info", None),
            ),
            (
                "unresolved_locations",
                tuple(self._unresolved_expression_locations(case)),
            ),
        )
        if analysis is not None:
            return self._artifact_stable_key_for_analysis(target, analysis)
        return target

    def _unresolved_expression_locations(self, case: ReturnCase) -> Tuple[Any, ...]:
        locations: List[Tuple[Any, ...]] = []
        value_expr = getattr(case, "value_expr", None)
        if self._expression_contains_unresolved(value_expr):
            locations.append(
                (
                    "unresolved_location",
                    "return_value",
                    self._unresolved_expression_location_classification(
                        value_expr,
                        "return_value",
                    ),
                    self._expression_runtime_object_key(value_expr),
                    self._unresolved_expression_typed_lowering_evidence(
                        value_expr,
                        "return_value",
                        case_value_expr=value_expr,
                    ),
                )
            )
        case_value_expr = getattr(case, "value_expr", None)
        for index, condition in enumerate(getattr(case, "conditions", None) or ()):
            expression = getattr(condition, "expression", None)
            if not self._expression_contains_unresolved(expression):
                continue
            locations.append(
                (
                    "unresolved_location",
                    "guard_condition",
                    int(index),
                    bool(getattr(condition, "negated", False)),
                    self._unresolved_expression_location_classification(
                        expression,
                        "guard_condition",
                    ),
                    self._return_condition_object_key(condition),
                    self._unresolved_expression_typed_lowering_evidence(
                        expression,
                        "guard_condition",
                        condition=condition,
                        case_value_expr=case_value_expr,
                    ),
                )
            )
        return tuple(locations)

    def _unresolved_expression_typed_lowering_evidence(
        self,
        expr: Any,
        location_scope: str,
        *,
        condition: Any = None,
        case_value_expr: Any = None,
    ) -> Tuple[Any, ...]:
        expr_type = getattr(expr, "expr_type", None)
        expr_kind = getattr(expr_type, "name", None)
        try:
            bits = int(expression_smt_bit_width(expr) or 0)
        except (AttributeError, TypeError, ValueError, RecursionError):
            bits = 0
        if bits <= 0:
            try:
                bits = int(getattr(expr, "get_bit_width", lambda: 0)() or 0)
            except (AttributeError, TypeError, ValueError, RecursionError):
                bits = 0
        unsupported = bool(expression_contains_unsupported_smt_ops(expr))
        if expr_type == ExpressionType.UNKNOWN:
            status = "blocked_unknown_expression"
        elif unsupported:
            status = "blocked_unsupported_smt_op"
        else:
            status = "blocked_nested_unresolved_expression"
        evidence: List[Any] = [
            "typed_lowering_evidence",
            ("location_scope", str(location_scope)),
            ("expression_kind", str(expr_kind or "missing")),
            ("expression_bits", bits if bits > 0 else None),
            ("typed_expression_key", self._expression_runtime_object_key(expr)),
            ("contains_unsupported_smt_ops", unsupported),
            ("lowering_status", status),
        ]
        phi_evidence = self._phi_circular_typed_lowering_evidence(
            expr,
            location_scope,
            condition=condition,
            case_value_expr=case_value_expr,
        )
        if phi_evidence is not None:
            evidence.append(phi_evidence)
        return tuple(evidence)

    def _phi_circular_typed_lowering_evidence(
        self,
        expr: Any,
        location_scope: str,
        *,
        condition: Any = None,
        case_value_expr: Any = None,
    ) -> Optional[Tuple[Any, ...]]:
        phi_origins = self._collect_phi_circular_origin_details(expr)
        if not phi_origins:
            return None
        guard_condition_key = (
            self._return_condition_object_key(condition)
            if condition is not None
            else None
        )
        summary_parameter_refs = self._collect_summary_parameter_refs(
            expr,
            case_value_expr,
        )
        return (
            "phi_circular_evidence",
            ("location_scope", str(location_scope)),
            ("phi_origins", phi_origins),
            ("guard_condition_key", guard_condition_key),
            (
                "guard_condition_literals",
                self._phi_circular_condition_literals(condition)
                if condition is not None
                else (),
            ),
            ("summary_parameter_refs", summary_parameter_refs),
            ("relation_status", "pending_guard_summary_relation_proof"),
        )

    def _unresolved_expression_pair_lowering_diagnostic(
        self,
        case1: ReturnCase,
        case2: ReturnCase,
    ) -> Optional[Tuple[Any, ...]]:
        left_shape, left_unknowns = self._phi_circular_case_shape_and_unknowns(case1)
        right_shape, right_unknowns = self._phi_circular_case_shape_and_unknowns(case2)
        if left_shape is None and right_shape is None:
            return None
        if not left_unknowns and not right_unknowns:
            return None

        left_value = self._phi_circular_case_value_shape(left_shape)
        right_value = self._phi_circular_case_value_shape(right_shape)
        left_literals = self._phi_circular_case_condition_literals(case1)
        right_literals = self._phi_circular_case_condition_literals(case2)
        left_unknown_count = len(left_unknowns)
        right_unknown_count = len(right_unknowns)
        origin_shape_relation = self._phi_circular_origin_shape_relation(
            left_unknowns,
            right_unknowns,
        )
        contradictions = self._phi_circular_opposing_condition_literals(
            left_literals,
            right_literals,
        )
        if left_shape is not None and right_shape is not None and left_shape == right_shape:
            status = "full_shape_match"
        elif left_value is not None and right_value is not None and left_value != right_value:
            status = "value_shape_mismatch"
        elif contradictions:
            status = "guard_literal_conflict"
        elif left_shape is None or right_shape is None:
            status = "shape_unavailable"
        else:
            status = "condition_shape_mismatch"

        return (
            "pair_lowering_diagnostic",
            ("candidate_kind", "phi_circular_guard_summary_relation"),
            ("status", status),
            ("left_unknown_count", left_unknown_count),
            ("right_unknown_count", right_unknown_count),
            (
                "unknown_count_relation",
                self._phi_circular_unknown_count_relation(
                    left_unknown_count,
                    right_unknown_count,
                ),
            ),
            ("left_value_shape", left_value),
            ("right_value_shape", right_value),
            (
                "value_shape_relation",
                self._phi_circular_value_shape_relation(left_value, right_value),
            ),
            ("phi_origin_shape_relation", origin_shape_relation),
            ("left_guard_literals", left_literals),
            ("right_guard_literals", right_literals),
            ("opposing_guard_literals", contradictions),
            ("required_evidence", ("guard_condition_pair", "summary_parameter_binding")),
        )

    def _unresolved_expression_phi_circular_full_shape_diagnostic_evidence(
        self,
        object_target_key: Tuple[Any, ...],
    ) -> Optional[Tuple[Any, ...]]:
        diagnostic = self._find_pair_lowering_diagnostic(object_target_key)
        if diagnostic is None:
            return None
        fields = {
            item[0]: item[1]
            for item in diagnostic[1:]
            if isinstance(item, tuple) and len(item) == 2 and isinstance(item[0], str)
        }
        if fields.get("candidate_kind") != "phi_circular_guard_summary_relation":
            return None
        if fields.get("status") != "full_shape_match":
            return None
        if int(fields.get("left_unknown_count") or 0) <= 0:
            return None
        if int(fields.get("right_unknown_count") or 0) <= 0:
            return None
        if int(fields.get("left_unknown_count") or 0) != int(fields.get("right_unknown_count") or 0):
            return None
        if fields.get("left_value_shape") != fields.get("right_value_shape"):
            return None
        origin_relation = fields.get("phi_origin_shape_relation")
        if not (
            isinstance(origin_relation, tuple)
            and ("relation", "exact_match") in origin_relation
        ):
            return None
        if fields.get("left_guard_literals") != fields.get("right_guard_literals"):
            return None
        if fields.get("opposing_guard_literals"):
            return None
        stage_evidence = self._phi_circular_semantic_recurrence_stage_evidence(
            object_target_key=object_target_key,
            diagnostic=diagnostic,
            diagnostic_fields=fields,
        )
        if not stage_evidence:
            return None
        return (
            "unresolved_expression_diagnostic_evidence",
            ("object_derived", True),
            ("status", "object_evidence_collected"),
            ("diagnostic_rule", "phi_circular_full_shape_match"),
            (
                "pending_stages",
                (
                    "phi_circular_guard_condition_lowering",
                    "recursive_summary_guard_equivalence",
                ),
            ),
            (
                "required_semantic_proof",
                (
                    "phi_incoming_values",
                    "guard_transition_relation",
                    "recursive_summary_parameter_binding",
                    "loop_summary_recurrence_semantics",
                ),
            ),
            ("object_target_key", object_target_key),
            ("pair_lowering_diagnostic", diagnostic),
            ("stage_evidence", stage_evidence),
        )

    def _unresolved_expression_deferred_call_diagnostic_evidence(
        self,
        object_target_key: Tuple[Any, ...],
    ) -> Optional[Tuple[Any, ...]]:
        if not self._object_target_contains_deferred_call_unknown(object_target_key):
            return None
        call_evidence = self._deferred_call_object_evidence_from_target(object_target_key)
        if call_evidence is None:
            return None
        stage_evidence = self._deferred_call_unresolved_expression_stage_evidence(
            object_target_key=object_target_key,
            call_evidence=call_evidence,
        )
        if not stage_evidence:
            return None
        return (
            "unresolved_expression_diagnostic_evidence",
            ("object_derived", True),
            ("status", "object_evidence_collected"),
            ("diagnostic_rule", "deferred_call_object_proof_content"),
            (
                "pending_stages",
                (
                    "deferred_call_return_resolution",
                    "deferred_call_result_equivalence",
                ),
            ),
            (
                "required_semantic_proof",
                (
                    "deferred_call_site",
                    "callee_identity",
                    "call_effect_summary",
                    "argument_binding",
                    "return_width_policy",
                ),
            ),
            ("object_target_key", object_target_key),
            ("deferred_call_evidence", call_evidence),
            ("stage_evidence", stage_evidence),
        )

    def _unresolved_expression_opaque_unknown_diagnostic_evidence(
        self,
        object_target_key: Tuple[Any, ...],
    ) -> Optional[Tuple[Any, ...]]:
        if not self._object_target_contains_void_opaque_unknown(object_target_key):
            return None
        opaque_evidence = self._opaque_unknown_return_object_evidence_from_target(
            object_target_key
        )
        if opaque_evidence is None:
            return None
        stage_evidence = self._opaque_unknown_unresolved_expression_stage_evidence(
            object_target_key=object_target_key,
            opaque_evidence=opaque_evidence,
        )
        if not stage_evidence:
            return None
        return (
            "unresolved_expression_diagnostic_evidence",
            ("object_derived", True),
            ("status", "object_evidence_collected"),
            ("diagnostic_rule", "opaque_unknown_return_object_proof_content"),
            (
                "pending_stages",
                (
                    "opaque_unknown_return_origin_resolution",
                    "opaque_unknown_return_value_equivalence",
                ),
            ),
            (
                "required_semantic_proof",
                (
                    "opaque_unknown_ref",
                    "return_case_origin",
                    "guard_condition_pair",
                    "return_width_policy",
                ),
            ),
            ("object_target_key", object_target_key),
            ("opaque_unknown_evidence", opaque_evidence),
            ("stage_evidence", stage_evidence),
        )

    def _unresolved_expression_generic_diagnostic_evidence(
        self,
        object_target_key: Tuple[Any, ...],
    ) -> Optional[Tuple[Any, ...]]:
        cause = self._unresolved_expression_target_cause(object_target_key)
        if cause not in {
            "mixed_float_call_read_recurrence",
            "multiple_or_nested_unresolved",
            "readonly_memory_read",
            "opaque_unknown",
        }:
            return None
        stage_evidence = self._generic_unresolved_expression_stage_evidence(
            object_target_key=object_target_key,
            cause=cause,
        )
        return (
            "unresolved_expression_diagnostic_evidence",
            ("object_derived", True),
            ("status", "object_evidence_collected"),
            ("diagnostic_rule", f"{cause}_pending_census"),
            ("unresolved_cause", cause),
            ("pending_stages", ("typed_expression_lowering", "type_normalization")),
            (
                "required_semantic_proof",
                (
                    "typed_expression_key",
                    "normalization_policy",
                    "return_width_policy",
                ),
            ),
            ("object_target_key", object_target_key),
            ("stage_evidence", stage_evidence),
        )

    @classmethod
    def _unresolved_expression_target_uses_generic_pending_census(
        cls,
        object_target_key: Any,
    ) -> bool:
        return cls._unresolved_expression_target_cause(object_target_key) in {
            "mixed_float_call_read_recurrence",
            "multiple_or_nested_unresolved",
            "readonly_memory_read",
        }

    def _generic_unresolved_expression_stage_evidence(
        self,
        *,
        object_target_key: Tuple[Any, ...],
        cause: str,
    ) -> Tuple[Any, ...]:
        return (
            (
                "unresolved_expression_stage_evidence",
                ("proof_stage", "typed_expression_lowering"),
                ("status", "object_evidence_collected"),
                ("object_target_key", object_target_key),
                ("unresolved_cause", cause),
                ("semantic_proof_status", "pending_semantic_proof"),
                ("completed_proof_allowed", False),
                (
                    "required_semantic_proof",
                    (
                        "typed_expression_key",
                        "unresolved_location",
                        "unresolved_cause",
                    ),
                ),
            ),
            (
                "unresolved_expression_stage_evidence",
                ("proof_stage", "type_normalization"),
                ("status", "object_evidence_collected"),
                ("object_target_key", object_target_key),
                ("unresolved_cause", cause),
                ("semantic_proof_status", "pending_semantic_proof"),
                ("completed_proof_allowed", False),
                (
                    "required_semantic_proof",
                    (
                        "normalization_policy",
                        "return_width_policy",
                    ),
                ),
            ),
        )

    def _opaque_unknown_unresolved_expression_stage_evidence(
        self,
        *,
        object_target_key: Tuple[Any, ...],
        opaque_evidence: Tuple[Any, ...],
    ) -> Tuple[Any, ...]:
        origin_query = self._semantic_recurrence_query_plan(
            query_id="opaque_unknown_return_origin_resolution",
            query_stage="opaque_unknown_return_origin_resolution",
            assertion_kind="opaque_unknown_return_origin_resolution",
            object_target_key=object_target_key,
            object_content=(("opaque_unknown_evidence", opaque_evidence),),
        )
        value_query = self._semantic_recurrence_query_plan(
            query_id="opaque_unknown_return_value_equivalence",
            query_stage="opaque_unknown_return_value_equivalence",
            assertion_kind="opaque_unknown_return_value_equivalence",
            object_target_key=object_target_key,
            object_content=(("opaque_unknown_evidence", opaque_evidence),),
        )
        return (
            (
                "unresolved_expression_stage_evidence",
                ("proof_stage", "opaque_unknown_return_origin_resolution"),
                ("status", "object_evidence_collected"),
                ("object_target_key", object_target_key),
                ("opaque_unknown_evidence", opaque_evidence),
                ("origin_resolution_status", "pending_semantic_proof"),
                ("proof_query_plan", (origin_query,)),
                (
                    "required_semantic_proof",
                    (
                        "opaque_unknown_ref",
                        "return_case_origin",
                    ),
                ),
            ),
            (
                "unresolved_expression_stage_evidence",
                ("proof_stage", "opaque_unknown_return_value_equivalence"),
                ("status", "object_evidence_collected"),
                ("object_target_key", object_target_key),
                ("opaque_unknown_evidence", opaque_evidence),
                ("value_equivalence_status", "pending_semantic_proof"),
                ("proof_query_plan", (value_query,)),
                (
                    "required_semantic_proof",
                    (
                        "left_return_value",
                        "right_return_value",
                        "guard_condition_pair",
                        "return_width_policy",
                    ),
                ),
            ),
        )

    def _opaque_unknown_return_object_evidence_from_target(
        self,
        object_target_key: Tuple[Any, ...],
    ) -> Optional[Tuple[Any, ...]]:
        target = self._normalize_nested_tuple(object_target_key)
        if not isinstance(target, tuple) or len(target) < 4:
            return None
        sides = []
        opaque_refs: List[Any] = []
        seen_refs = set()
        for side in target[2:4]:
            side_tuple = self._normalize_nested_tuple(side)
            if not isinstance(side_tuple, tuple) or len(side_tuple) < 6:
                return None
            side_label = side_tuple[1]
            function_ref = side_tuple[2]
            return_storage = side_tuple[3]
            partition_member = side_tuple[4]
            unresolved_locations = side_tuple[5]
            side_refs = self._opaque_unknown_refs_from_value(
                (partition_member, unresolved_locations)
            )
            for ref in side_refs:
                key = repr(ref)
                if key not in seen_refs:
                    seen_refs.add(key)
                    opaque_refs.append(ref)
            sides.append(
                (
                    "return_side",
                    ("side", side_label),
                    ("function_ref", function_ref),
                    ("return_storage", return_storage),
                    ("return_case_origin", partition_member),
                    ("unresolved_locations", unresolved_locations),
                    ("opaque_unknown_refs", side_refs),
                )
            )
        if not opaque_refs:
            return None
        return (
            "opaque_unknown_return_object_evidence",
            ("opaque_unknown_refs", tuple(sorted(opaque_refs, key=repr))),
            ("return_sides", tuple(sides)),
            ("return_width_policy", tuple(side[3] for side in target[2:4] if isinstance(side, tuple) and len(side) >= 4)),
            ("evidence_status", "object_evidence_collected"),
        )

    @classmethod
    def _opaque_unknown_refs_from_value(cls, value: Any) -> Tuple[Any, ...]:
        refs: List[Any] = []
        seen = set()

        def visit(node: Any) -> None:
            normalized = cls._normalize_nested_tuple(node)
            if isinstance(normalized, tuple):
                if (
                    len(normalized) == 2
                    and normalized[0] in {"runtime_ref", "unknown_runtime_ref"}
                    and isinstance(normalized[1], tuple)
                    and len(normalized[1]) >= 2
                    and normalized[1][0] == "opaque_unknown"
                    and normalized[1][1] == "void"
                ):
                    key = repr(normalized)
                    if key not in seen:
                        seen.add(key)
                        refs.append(normalized)
                for item in normalized:
                    visit(item)
            elif isinstance(normalized, list):
                for item in normalized:
                    visit(item)
            elif isinstance(normalized, dict):
                for key, item in normalized.items():
                    visit(key)
                    visit(item)

        visit(value)
        return tuple(sorted(refs, key=repr))

    def _deferred_call_unresolved_expression_stage_evidence(
        self,
        *,
        object_target_key: Tuple[Any, ...],
        call_evidence: Tuple[Any, ...],
    ) -> Tuple[Any, ...]:
        resolution_query = self._semantic_recurrence_query_plan(
            query_id="deferred_call_return_resolution",
            query_stage="deferred_call_return_resolution",
            assertion_kind="deferred_call_return_resolution",
            object_target_key=object_target_key,
            object_content=(("deferred_call_evidence", call_evidence),),
        )
        result_query = self._semantic_recurrence_query_plan(
            query_id="deferred_call_result_equivalence",
            query_stage="deferred_call_result_equivalence",
            assertion_kind="deferred_call_result_equivalence",
            object_target_key=object_target_key,
            object_content=(("deferred_call_evidence", call_evidence),),
        )
        return (
            (
                "unresolved_expression_stage_evidence",
                ("proof_stage", "deferred_call_return_resolution"),
                ("status", "object_evidence_collected"),
                ("object_target_key", object_target_key),
                ("deferred_call_evidence", call_evidence),
                ("call_resolution_status", "pending_semantic_proof"),
                ("proof_query_plan", (resolution_query,)),
                (
                    "required_semantic_proof",
                    (
                        "deferred_call_site",
                        "callee_identity",
                        "call_effect_summary",
                    ),
                ),
            ),
            (
                "unresolved_expression_stage_evidence",
                ("proof_stage", "deferred_call_result_equivalence"),
                ("status", "object_evidence_collected"),
                ("object_target_key", object_target_key),
                ("deferred_call_evidence", call_evidence),
                ("result_equivalence_status", "pending_semantic_proof"),
                ("proof_query_plan", (result_query,)),
                (
                    "required_semantic_proof",
                    (
                        "left_return_value",
                        "right_return_value",
                        "argument_binding",
                        "return_width_policy",
                    ),
                ),
            ),
        )

    def _deferred_call_object_evidence_from_target(
        self,
        object_target_key: Tuple[Any, ...],
    ) -> Optional[Tuple[Any, ...]]:
        target = self._normalize_nested_tuple(object_target_key)
        if not isinstance(target, tuple) or len(target) < 4:
            return None
        left_refs = self._deferred_call_runtime_refs_from_value(target[2])
        right_refs = self._deferred_call_runtime_refs_from_value(target[3])
        if not left_refs and not right_refs:
            return None
        left_semantic_refs = self._deferred_call_semantic_refs(left_refs)
        right_semantic_refs = self._deferred_call_semantic_refs(right_refs)
        return (
            "deferred_call_object_evidence",
            ("left_deferred_call_refs", left_refs),
            ("right_deferred_call_refs", right_refs),
            ("left_deferred_call_semantic_refs", left_semantic_refs),
            ("right_deferred_call_semantic_refs", right_semantic_refs),
            (
                "deferred_call_ref_relation",
                self._deferred_call_ref_relation(left_refs, right_refs),
            ),
            (
                "deferred_call_semantic_ref_relation",
                self._deferred_call_ref_relation(left_semantic_refs, right_semantic_refs),
            ),
            ("evidence_status", "object_evidence_collected"),
        )

    @classmethod
    def _deferred_call_runtime_refs_from_value(cls, value: Any) -> Tuple[Any, ...]:
        refs: List[Any] = []
        seen = set()

        def visit(node: Any) -> None:
            normalized = cls._normalize_nested_tuple(node)
            if isinstance(normalized, tuple):
                if (
                    len(normalized) == 2
                    and normalized[0] in {"unknown_runtime_ref", "runtime_ref"}
                    and isinstance(normalized[1], tuple)
                    and normalized[1]
                    and normalized[1][0] == "deferred_call"
                ):
                    key = json.dumps(cls._semantic_recurrence_jsonable(normalized), sort_keys=True)
                    if key not in seen:
                        seen.add(key)
                        refs.append(normalized)
                    return
                for item in normalized:
                    visit(item)
            elif isinstance(normalized, list):
                for item in normalized:
                    visit(item)
            elif isinstance(normalized, dict):
                for key, item in sorted(normalized.items(), key=lambda item: str(item[0])):
                    visit(key)
                    visit(item)

        visit(value)
        return tuple(refs)

    @classmethod
    def _deferred_call_semantic_refs(cls, refs: Tuple[Any, ...]) -> Tuple[Any, ...]:
        grouped: Dict[str, Dict[str, Any]] = {}
        for ref in refs:
            normalized = cls._normalize_nested_tuple(ref)
            if (
                not isinstance(normalized, tuple)
                or len(normalized) != 2
                or normalized[0] not in {"unknown_runtime_ref", "runtime_ref"}
                or not isinstance(normalized[1], tuple)
                or not normalized[1]
                or normalized[1][0] != "deferred_call"
            ):
                continue
            payload = normalized[1]
            key = json.dumps(cls._semantic_recurrence_jsonable(payload), sort_keys=True)
            entry = grouped.setdefault(
                key,
                {
                    "payload": payload,
                    "forms": set(),
                },
            )
            entry["forms"].add(normalized[0])
        semantic_refs = []
        for key in sorted(grouped):
            entry = grouped[key]
            semantic_refs.append(
                (
                    "deferred_call_semantic_ref",
                    ("deferred_call_payload", entry["payload"]),
                    ("ref_forms", tuple(sorted(entry["forms"]))),
                )
            )
        return tuple(semantic_refs)

    @staticmethod
    def _deferred_call_ref_relation(
        left_refs: Tuple[Any, ...],
        right_refs: Tuple[Any, ...],
    ) -> Tuple[Any, ...]:
        if left_refs and right_refs:
            relation = "both_sides_deferred_call_unknown"
        elif left_refs:
            relation = "left_deferred_call_unknown_only"
        else:
            relation = "right_deferred_call_unknown_only"
        return (
            "deferred_call_ref_relation",
            ("relation", relation),
            ("left_count", len(left_refs)),
            ("right_count", len(right_refs)),
        )

    def _phi_circular_semantic_recurrence_stage_evidence(
        self,
        *,
        object_target_key: Tuple[Any, ...],
        diagnostic: Tuple[Any, ...],
        diagnostic_fields: Dict[str, Any],
    ) -> Tuple[Any, ...]:
        origin_relation = diagnostic_fields.get("phi_origin_shape_relation")
        guard_pair = (
            "guard_condition_pair",
            ("left_guard_literals", diagnostic_fields.get("left_guard_literals")),
            ("right_guard_literals", diagnostic_fields.get("right_guard_literals")),
            ("relation", "exact_match"),
        )
        summary_binding = (
            "summary_parameter_binding",
            ("left_value_shape", diagnostic_fields.get("left_value_shape")),
            ("right_value_shape", diagnostic_fields.get("right_value_shape")),
            ("value_shape_relation", diagnostic_fields.get("value_shape_relation")),
            ("binding_status", "object_evidence_collected"),
        )
        phi_origin_pair = (
            "phi_origin_pair",
            ("relation", "exact_match"),
            ("phi_origin_shape_relation", origin_relation),
        )
        guard_transition = (
            "guard_transition_relation",
            ("relation", "exact_match"),
            ("transition_status", "object_evidence_collected"),
            ("phi_origin_pair", phi_origin_pair),
            ("guard_condition_pair", guard_pair),
            ("left_value_shape", diagnostic_fields.get("left_value_shape")),
            ("right_value_shape", diagnostic_fields.get("right_value_shape")),
            ("value_shape_relation", diagnostic_fields.get("value_shape_relation")),
        )
        recurrence_relation = (
            "recurrence_relation",
            ("relation", "exact_match"),
            ("recurrence_status", "object_evidence_collected"),
            ("summary_parameter_binding", summary_binding),
            ("guard_transition_relation", guard_transition),
            ("left_value_shape", diagnostic_fields.get("left_value_shape")),
            ("right_value_shape", diagnostic_fields.get("right_value_shape")),
            ("value_shape_relation", diagnostic_fields.get("value_shape_relation")),
        )
        guard_query = self._semantic_recurrence_query_plan(
            query_id="phi_circular_guard_transition",
            query_stage="phi_circular_guard_condition_lowering",
            assertion_kind="guard_transition_equivalence",
            object_target_key=object_target_key,
            object_content=(
                ("guard_transition_relation", guard_transition),
            ),
        )
        recurrence_query = self._semantic_recurrence_query_plan(
            query_id="recursive_summary_recurrence",
            query_stage="recursive_summary_guard_equivalence",
            assertion_kind="summary_recurrence_equivalence",
            object_target_key=object_target_key,
            object_content=(
                ("summary_parameter_binding", summary_binding),
                ("recurrence_relation", recurrence_relation),
            ),
        )
        return (
            (
                "unresolved_expression_stage_evidence",
                ("proof_stage", "phi_circular_guard_condition_lowering"),
                ("status", "object_evidence_collected"),
                ("object_target_key", object_target_key),
                ("pair_lowering_diagnostic", diagnostic),
                ("phi_origin_pair", phi_origin_pair),
                ("guard_condition_pair", guard_pair),
                ("guard_transition_relation", guard_transition),
                ("typed_lowering_rule", "phi_circular_guard_shape_preserving"),
                (
                    "proof_query_plan",
                    (guard_query,),
                ),
                (
                    "required_semantic_proof",
                    (
                        "phi_incoming_values",
                        "guard_transition_relation",
                    ),
                ),
            ),
            (
                "unresolved_expression_stage_evidence",
                ("proof_stage", "recursive_summary_guard_equivalence"),
                ("status", "object_evidence_collected"),
                ("object_target_key", object_target_key),
                ("pair_lowering_diagnostic", diagnostic),
                ("phi_origin_pair", phi_origin_pair),
                ("guard_condition_pair", guard_pair),
                ("summary_parameter_binding", summary_binding),
                ("recurrence_relation", recurrence_relation),
                (
                    "proof_query_plan",
                    (recurrence_query,),
                ),
                (
                    "required_semantic_proof",
                    (
                        "recursive_summary_parameter_binding",
                        "loop_summary_recurrence_semantics",
                    ),
                ),
            ),
        )

    @classmethod
    def _semantic_recurrence_query_plan(
        cls,
        *,
        query_id: str,
        query_stage: str,
        assertion_kind: str,
        object_target_key: Tuple[Any, ...],
        object_content: Tuple[Tuple[str, Any], ...],
    ) -> Tuple[Any, ...]:
        query_body = (
            ("query_id", query_id),
            ("query_stage", query_stage),
            ("expected_solver_result", "unsat"),
            ("assertion_kind", assertion_kind),
            ("object_target_key", object_target_key),
            ("object_content", object_content),
        )
        query_hash = cls._stable_semantic_recurrence_hash(query_body)
        return (
            "semantic_recurrence_query",
            ("query_id", query_id),
            ("query_stage", query_stage),
            ("query_status", "planned"),
            ("expected_solver_result", "unsat"),
            ("proof_source", "object_derived_query_plan"),
            ("assertion_kind", assertion_kind),
            ("query_hash", query_hash),
            ("object_content", object_content),
            *object_content,
        )

    @staticmethod
    def _stable_semantic_recurrence_hash(value: Any) -> str:
        canonical = json.dumps(
            PairwiseStrategy._semantic_recurrence_jsonable(value),
            sort_keys=True,
            separators=(",", ":"),
        )
        return hashlib.sha256(canonical.encode("utf-8")).hexdigest()

    @staticmethod
    def _semantic_recurrence_jsonable(value: Any) -> Any:
        if isinstance(value, tuple):
            return [PairwiseStrategy._semantic_recurrence_jsonable(item) for item in value]
        if isinstance(value, list):
            return [PairwiseStrategy._semantic_recurrence_jsonable(item) for item in value]
        if isinstance(value, dict):
            return {
                str(key): PairwiseStrategy._semantic_recurrence_jsonable(item)
                for key, item in sorted(value.items(), key=lambda entry: str(entry[0]))
            }
        stable_key = getattr(value, "stable_key", None)
        if callable(stable_key):
            try:
                return PairwiseStrategy._semantic_recurrence_jsonable(stable_key())
            except Exception:
                pass
        to_dict = getattr(value, "to_dict", None)
        if callable(to_dict):
            try:
                return PairwiseStrategy._semantic_recurrence_jsonable(to_dict())
            except Exception:
                pass
        if isinstance(value, (str, int, float, bool)) or value is None:
            return value
        return repr(value)

    @classmethod
    def _phi_circular_origin_shape_relation(
        cls,
        left_unknowns: Tuple[Any, ...],
        right_unknowns: Tuple[Any, ...],
    ) -> Tuple[Any, ...]:
        left_shapes = tuple(
            cls._phi_circular_unknown_origin_shape_key(unknown)
            for unknown in left_unknowns
        )
        right_shapes = tuple(
            cls._phi_circular_unknown_origin_shape_key(unknown)
            for unknown in right_unknowns
        )
        if not left_shapes or not right_shapes:
            relation = "origin_shape_unavailable"
        elif any(shape is None for shape in left_shapes + right_shapes):
            relation = "origin_shape_unavailable"
        elif left_shapes == right_shapes:
            relation = "exact_match"
        else:
            relation = "origin_shape_mismatch"
        return (
            "phi_origin_shape_relation",
            ("relation", relation),
            ("left_origin_shapes", left_shapes),
            ("right_origin_shapes", right_shapes),
        )

    @classmethod
    def _phi_circular_unknown_origin_shape_key(cls, unknown: Any) -> Optional[Tuple[Any, ...]]:
        if not cls._unknown_expression_is_originated_phi_circular(unknown):
            return None
        runtime_ref = getattr(unknown, "runtime_ref", None)
        origin_key = cls._stable_key_or_none(getattr(runtime_ref, "origin_ref", None))
        return cls._pcode_origin_cross_binary_shape_key(origin_key)

    @staticmethod
    def _pcode_origin_cross_binary_shape_key(origin_key: Any) -> Optional[Tuple[Any, ...]]:
        if not (isinstance(origin_key, tuple) and origin_key and origin_key[0] == "pcode_op"):
            return None
        if (
            len(origin_key) >= 8
            and isinstance(origin_key[2], tuple)
            and len(origin_key[2]) == 3
            and origin_key[2][0] == "function_entry"
            and isinstance(origin_key[3], tuple)
            and len(origin_key[3]) == 3
            and origin_key[3][0] == "seq_target"
        ):
            try:
                relative_target = int(origin_key[3][2]) - int(origin_key[2][2])
                seq_time = int(origin_key[4])
                seq_order = int(origin_key[5])
                local_op_ordinal = int(origin_key[7])
            except (TypeError, ValueError):
                return None
            return (
                "pcode_op_cross_binary_shape",
                ("function_entry_space", origin_key[2][1]),
                ("target_space", origin_key[3][1]),
                ("relative_target_offset", relative_target),
                ("seq_time", seq_time),
                ("seq_order", seq_order),
                ("opcode", origin_key[6]),
                ("local_op_ordinal", local_op_ordinal),
            )
        if len(origin_key) >= 6:
            return (
                "pcode_op_cross_binary_shape",
                ("address_offset", origin_key[1]),
                ("seq_time", origin_key[2]),
                ("seq_order", origin_key[3]),
                ("block_index", origin_key[4]),
                ("mnemonic", origin_key[5]),
            )
        return None

    @classmethod
    def _find_pair_lowering_diagnostic(cls, value: Any) -> Optional[Tuple[Any, ...]]:
        normalized = cls._normalize_nested_tuple(value)
        if isinstance(normalized, tuple):
            if normalized and normalized[0] == "pair_lowering_diagnostic":
                return normalized
            for item in normalized:
                found = cls._find_pair_lowering_diagnostic(item)
                if found is not None:
                    return found
        if isinstance(normalized, list):
            for item in normalized:
                found = cls._find_pair_lowering_diagnostic(item)
                if found is not None:
                    return found
        if isinstance(normalized, dict):
            for item in normalized.values():
                found = cls._find_pair_lowering_diagnostic(item)
                if found is not None:
                    return found
        return None

    @classmethod
    def _find_phi_origin_shape_relation(cls, value: Any) -> Optional[Tuple[Any, ...]]:
        normalized = cls._normalize_nested_tuple(value)
        if isinstance(normalized, tuple):
            if normalized and normalized[0] == "phi_origin_shape_relation":
                if (
                    len(normalized) == 2
                    and isinstance(normalized[1], tuple)
                    and normalized[1]
                    and normalized[1][0] == "phi_origin_shape_relation"
                ):
                    return normalized[1]
                return normalized
            for item in normalized:
                found = cls._find_phi_origin_shape_relation(item)
                if found is not None:
                    return found
        if isinstance(normalized, list):
            for item in normalized:
                found = cls._find_phi_origin_shape_relation(item)
                if found is not None:
                    return found
        if isinstance(normalized, dict):
            for item in normalized.values():
                found = cls._find_phi_origin_shape_relation(item)
                if found is not None:
                    return found
        return None

    @staticmethod
    def _phi_circular_case_value_shape(
        case_shape: Optional[Tuple[Any, ...]],
    ) -> Optional[Any]:
        if not case_shape or len(case_shape) < 2:
            return None
        value_item = case_shape[1]
        if isinstance(value_item, tuple) and len(value_item) == 2 and value_item[0] == "value":
            return value_item[1]
        return None

    @staticmethod
    def _phi_circular_unknown_count_relation(
        left_count: int,
        right_count: int,
    ) -> Tuple[Any, ...]:
        relation = "equal" if int(left_count) == int(right_count) else "count_mismatch"
        return (
            "unknown_count_relation",
            ("relation", relation),
            ("left_count", int(left_count)),
            ("right_count", int(right_count)),
        )

    @classmethod
    def _phi_circular_value_shape_relation(
        cls,
        left_value: Optional[Any],
        right_value: Optional[Any],
    ) -> Tuple[Any, ...]:
        left_summary_index = cls._phi_circular_summary_parameter_index(left_value)
        right_summary_index = cls._phi_circular_summary_parameter_index(right_value)
        left_constant = cls._phi_circular_constant_value(left_value)
        right_constant = cls._phi_circular_constant_value(right_value)
        if left_value is None or right_value is None:
            relation = "shape_unavailable"
        elif left_value == right_value:
            relation = "exact_match"
        elif left_summary_index is not None and right_summary_index is not None:
            relation = "summary_parameter_shift"
        elif left_summary_index is not None and right_constant is not None:
            relation = "left_summary_parameter_right_constant"
        elif left_constant is not None and right_summary_index is not None:
            relation = "left_constant_right_summary_parameter"
        else:
            relation = "shape_mismatch"
        return (
            "value_shape_relation",
            ("relation", relation),
            ("left_kind", cls._phi_circular_shape_kind(left_value)),
            ("right_kind", cls._phi_circular_shape_kind(right_value)),
            ("left_summary_parameter_index", left_summary_index),
            ("right_summary_parameter_index", right_summary_index),
            ("left_constant_value", left_constant),
            ("right_constant_value", right_constant),
        )

    @staticmethod
    def _phi_circular_shape_kind(value: Optional[Any]) -> str:
        if isinstance(value, tuple) and value:
            return str(value[0])
        return "unavailable"

    @staticmethod
    def _phi_circular_summary_parameter_index(value: Optional[Any]) -> Optional[int]:
        if not (isinstance(value, tuple) and len(value) == 4 and value[0] == "parameter"):
            return None
        name = str(value[1] or "")
        if not name.startswith("summary_rec_"):
            return None
        try:
            index = int(value[2])
        except (TypeError, ValueError):
            return None
        return index if index >= 0 else None

    @staticmethod
    def _phi_circular_constant_value(value: Optional[Any]) -> Optional[int]:
        if not (isinstance(value, tuple) and len(value) == 3 and value[0] == "const"):
            return None
        try:
            return int(value[1])
        except (TypeError, ValueError):
            return None

    def _phi_circular_case_condition_literals(
        self,
        case: ReturnCase,
    ) -> Tuple[Any, ...]:
        literals: List[Any] = []
        for condition in getattr(case, "conditions", None) or ():
            literals.extend(self._phi_circular_condition_literals(condition))
        return tuple(sorted(literals, key=repr))

    def _phi_circular_condition_literals(self, condition: Any) -> Tuple[Any, ...]:
        if condition is None:
            return ()
        unknowns: List[Any] = []
        shape = self._phi_circular_expression_shape_key(
            getattr(condition, "expression", None),
            unknowns,
        )
        if shape is None:
            return ()
        return tuple(
            sorted(
                self._phi_circular_boolean_literals_from_shape(
                    shape,
                    polarity=not bool(getattr(condition, "negated", False)),
                ),
                key=repr,
            )
        )

    def _phi_circular_boolean_literals_from_shape(
        self,
        shape: Any,
        *,
        polarity: bool,
    ) -> Tuple[Any, ...]:
        if (
            isinstance(shape, tuple)
            and len(shape) == 5
            and shape[0] == "binary"
            and shape[1] == "BOOL_AND"
            and polarity
        ):
            return (
                *self._phi_circular_boolean_literals_from_shape(shape[3], polarity=True),
                *self._phi_circular_boolean_literals_from_shape(shape[4], polarity=True),
            )
        if (
            isinstance(shape, tuple)
            and len(shape) == 4
            and shape[0] == "unary"
            and shape[1] == "BOOL_NEGATE"
        ):
            return self._phi_circular_boolean_literals_from_shape(
                shape[3],
                polarity=not polarity,
            )
        return (("guard_literal", bool(polarity), shape),)

    @staticmethod
    def _phi_circular_opposing_condition_literals(
        left_literals: Tuple[Any, ...],
        right_literals: Tuple[Any, ...],
    ) -> Tuple[Any, ...]:
        left_by_atom = {
            item[2]: bool(item[1])
            for item in left_literals
            if isinstance(item, tuple) and len(item) == 3 and item[0] == "guard_literal"
        }
        opposing: List[Any] = []
        for item in right_literals:
            if not (isinstance(item, tuple) and len(item) == 3 and item[0] == "guard_literal"):
                continue
            atom = item[2]
            right_polarity = bool(item[1])
            if atom in left_by_atom and left_by_atom[atom] != right_polarity:
                opposing.append(("opposing_guard_literal", atom))
        return tuple(sorted(opposing, key=repr))

    def _collect_phi_circular_origin_details(self, expr: Any) -> Tuple[Any, ...]:
        details: List[Tuple[Any, ...]] = []
        seen = set()
        for unknown in self._collect_unknown_expression_nodes(expr):
            runtime_ref = getattr(unknown, "runtime_ref", None)
            if getattr(runtime_ref, "kind", None) != "opaque_unknown":
                continue
            if getattr(runtime_ref, "reason", None) != "phi_circular":
                continue
            if getattr(runtime_ref, "origin_kind", None) != "multiequal_pcode_op":
                continue
            origin_key = self._stable_key_or_none(getattr(runtime_ref, "origin_ref", None))
            if origin_key is None:
                continue
            item = (
                "phi_origin",
                ("runtime_ref", self._diagnostic_key_or_semantic_key_or_stable_key_or_none(runtime_ref)),
                ("origin_kind", "multiequal_pcode_op"),
                ("pcode_op_ref", origin_key),
                ("unknown_expression", self._expression_runtime_object_key(unknown)),
                ("bit_width", int(expression_smt_bit_width(unknown) or 0) or None),
            )
            if item in seen:
                continue
            seen.add(item)
            details.append(item)
        return tuple(sorted(details, key=repr))

    def _collect_summary_parameter_refs(self, *expressions: Any) -> Tuple[Any, ...]:
        refs: List[Tuple[Any, ...]] = []
        seen = set()
        for expr in expressions:
            for parameter in self._collect_parameter_expression_nodes(expr):
                name = str(getattr(parameter, "name", "") or "")
                raw_index = getattr(parameter, "value", None)
                try:
                    index = int(raw_index)
                except (TypeError, ValueError):
                    index = None
                if not (name.startswith("summary_rec_") or (index is not None and index >= 10000)):
                    continue
                item = (
                    "summary_parameter",
                    ("index", index),
                    ("name", name or None),
                    ("bit_width", int(expression_smt_bit_width(parameter) or 0) or None),
                    ("expression", self._expression_runtime_object_key(parameter)),
                )
                if item in seen:
                    continue
                seen.add(item)
                refs.append(item)
        return tuple(sorted(refs, key=repr))

    def _collect_parameter_expression_nodes(self, expr: Any) -> Tuple[Any, ...]:
        result: List[Any] = []
        self._collect_parameter_expression_nodes_into(expr, result)
        return tuple(result)

    def _collect_parameter_expression_nodes_into(self, expr: Any, result: List[Any]) -> None:
        if expr is None or getattr(expr, "expr_type", None) is None:
            return
        if expr.expr_type == ExpressionType.PARAMETER:
            result.append(expr)
            return
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for condition, value in expr.value:
                if condition is not None:
                    self._collect_parameter_expression_nodes_into(condition.expression, result)
                self._collect_parameter_expression_nodes_into(value, result)
            return
        for operand in getattr(expr, "operands", []) or []:
            self._collect_parameter_expression_nodes_into(operand, result)

    def _unresolved_expression_location_classification(
        self,
        expr: Any,
        location_scope: str,
    ) -> Tuple[Any, ...]:
        kinds: set[Any] = set()
        unknown_refs: set[Any] = set()
        unsupported_ops: set[Any] = set()
        self._collect_unresolved_expression_classification(
            expr,
            kinds=kinds,
            unknown_refs=unknown_refs,
            unsupported_ops=unsupported_ops,
        )
        location = self._unresolved_expression_location_taxonomy(location_scope)
        cause = self._unresolved_expression_cause_taxonomy(
            expr,
            unresolved_kinds=kinds,
            unknown_refs=unknown_refs,
            unsupported_ops=unsupported_ops,
        )
        return (
            "unresolved_classification",
            ("location_scope", str(location_scope)),
            ("unresolved_location", location),
            ("unresolved_cause", cause),
            ("unresolved_substage", self._unresolved_expression_substage(location, cause)),
            ("unresolved_kinds", tuple(sorted(kinds, key=repr))),
            ("unknown_refs", tuple(sorted(unknown_refs, key=repr))),
            ("unsupported_ops", tuple(sorted(unsupported_ops, key=repr))),
        )

    @staticmethod
    def _unresolved_expression_location_taxonomy(location_scope: str) -> str:
        if location_scope == "return_value":
            return "return_value_unresolved"
        if location_scope == "guard_condition":
            return "return_guard_unresolved"
        if location_scope == "path_guard":
            return "path_guard_unresolved"
        if location_scope == "call_argument":
            return "call_argument_unresolved"
        if location_scope == "memory_address":
            return "memory_address_unresolved"
        if location_scope == "effect_surface":
            return "effect_surface_unresolved"
        return f"{location_scope or 'unknown'}_unresolved"

    def _unresolved_expression_cause_taxonomy(
        self,
        expr: Any,
        *,
        unresolved_kinds: set[Any],
        unknown_refs: set[Any],
        unsupported_ops: set[Any],
    ) -> str:
        has_phi = any(self._value_contains_originated_phi_circular(ref) for ref in unknown_refs)
        has_deferred_call = (
            "deferred_call_unknown" in unresolved_kinds
            or any(self._value_contains_deferred_call_ref(ref) for ref in unknown_refs)
        )
        has_readonly = any(self._value_contains_readonly_ref(ref) for ref in unknown_refs)
        has_float = self._expression_uses_float_or_float_op(expr)
        has_memory_or_effect = self._unsupported_ops_include_memory_or_effect(unsupported_ops)
        unresolved_count = len(unknown_refs)

        if (
            has_float
            and (has_phi or has_deferred_call or has_readonly or has_memory_or_effect or unresolved_count > 1)
        ):
            return "mixed_float_call_read_recurrence"
        if unresolved_count > 1 or ("phi_unresolved" in unresolved_kinds and not has_phi):
            return "multiple_or_nested_unresolved"
        if has_phi:
            if has_float or has_deferred_call or has_readonly or has_memory_or_effect:
                return "multiple_or_nested_unresolved"
            return "phi_circular_integer"
        if has_deferred_call:
            return "deferred_call_return"
        if has_readonly:
            return "readonly_memory_read"
        if "unsupported_smt_op" in unresolved_kinds:
            return "opaque_unknown"
        return "opaque_unknown"

    @staticmethod
    def _unresolved_expression_substage(location: str, cause: str) -> str:
        if cause == "phi_circular_integer" and location in {
            "return_guard_unresolved",
            "path_guard_unresolved",
        }:
            return "integer_phi_circular_guard_pending"
        if cause == "phi_circular_integer" and location == "return_value_unresolved":
            return "integer_phi_circular_value_pending"
        if cause == "deferred_call_return" and location == "return_value_unresolved":
            return "deferred_call_return_value_pending"
        if cause == "readonly_memory_read":
            return "readonly_memory_read_subnode_pending"
        if cause == "mixed_float_call_read_recurrence":
            return "mixed_float_call_read_recurrence_deferred"
        if cause == "multiple_or_nested_unresolved":
            return "multiple_or_nested_unresolved_deferred"
        return "typed_lowering_pending"

    @classmethod
    def _value_contains_originated_phi_circular(cls, value: Any) -> bool:
        normalized = cls._normalize_nested_tuple(value)
        if isinstance(normalized, tuple):
            if cls._tuple_is_originated_phi_circular_runtime_ref(normalized):
                return True
            return any(cls._value_contains_originated_phi_circular(item) for item in normalized)
        if isinstance(normalized, list):
            return any(cls._value_contains_originated_phi_circular(item) for item in normalized)
        if isinstance(normalized, dict):
            return any(
                cls._value_contains_originated_phi_circular(key)
                or cls._value_contains_originated_phi_circular(item)
                for key, item in normalized.items()
            )
        return False

    @classmethod
    def _value_contains_deferred_call_ref(cls, value: Any) -> bool:
        normalized = cls._normalize_nested_tuple(value)
        if isinstance(normalized, tuple):
            if normalized and normalized[0] == "deferred_call":
                return True
            return any(cls._value_contains_deferred_call_ref(item) for item in normalized)
        if isinstance(normalized, list):
            return any(cls._value_contains_deferred_call_ref(item) for item in normalized)
        if isinstance(normalized, dict):
            return any(
                cls._value_contains_deferred_call_ref(key)
                or cls._value_contains_deferred_call_ref(item)
                for key, item in normalized.items()
            )
        return False

    @classmethod
    def _value_contains_readonly_ref(cls, value: Any) -> bool:
        normalized = cls._normalize_nested_tuple(value)
        if isinstance(normalized, tuple):
            if normalized and isinstance(normalized[0], str) and normalized[0].startswith("readonly"):
                return True
            if "observed_memory_read" in normalized:
                return True
            return any(cls._value_contains_readonly_ref(item) for item in normalized)
        if isinstance(normalized, list):
            return any(cls._value_contains_readonly_ref(item) for item in normalized)
        if isinstance(normalized, dict):
            return any(
                cls._value_contains_readonly_ref(key)
                or cls._value_contains_readonly_ref(item)
                for key, item in normalized.items()
            )
        return False

    @staticmethod
    def _unsupported_ops_include_memory_or_effect(unsupported_ops: set[Any]) -> bool:
        for op in unsupported_ops:
            if not isinstance(op, tuple):
                continue
            rendered = repr(op)
            if any(marker in rendered for marker in ("LOAD", "STORE", "CALL", "INDIRECT", "MULTIEQUAL")):
                return True
        return False

    @staticmethod
    def _expression_uses_float_or_float_op(expr: Any) -> bool:
        if expr is None:
            return False
        try:
            if expression_uses_smt_float_theory(expr):
                return True
        except (AttributeError, TypeError, RecursionError):
            pass
        expr_type = getattr(expr, "expr_type", None)
        type_name = str(getattr(expr_type, "name", "") or "")
        operator = str(getattr(expr, "operator", "") or "")
        name = str(getattr(expr, "name", "") or "")
        if any(token in type_name.upper() for token in ("FLOAT", "F")):
            return True
        if any(token in operator.upper() for token in ("FLOAT", "FADD", "FSUB", "FMUL", "FDIV")):
            return True
        if name.lower() in {"log", "exp", "sqrt", "sin", "cos", "pow"}:
            return True
        for operand in getattr(expr, "operands", []) or ():
            if PairwiseStrategy._expression_uses_float_or_float_op(operand):
                return True
        if getattr(expr, "expr_type", None) == ExpressionType.PHI and getattr(expr, "value", None):
            for condition, value in expr.value:
                if condition is not None and PairwiseStrategy._expression_uses_float_or_float_op(condition.expression):
                    return True
                if PairwiseStrategy._expression_uses_float_or_float_op(value):
                    return True
        return False

    def _collect_unresolved_expression_classification(
        self,
        expr: Any,
        *,
        kinds: set[Any],
        unknown_refs: set[Any],
        unsupported_ops: set[Any],
    ) -> None:
        if expr is None or getattr(expr, "expr_type", None) is None:
            return
        if expression_contains_unsupported_smt_ops(expr):
            unsupported_ops.update(self._unsupported_smt_op_keys(expr))
            if unsupported_ops:
                kinds.add("unsupported_smt_op")
        if expr.expr_type == ExpressionType.UNKNOWN:
            kind, ref_key = self._unknown_expression_classification_key(expr)
            kinds.add(kind)
            unknown_refs.add(ref_key)
            return
        if expr.expr_type == ExpressionType.PHI and expr.value:
            branch_had_unresolved = False
            for condition, value in expr.value:
                if condition is not None and self._expression_contains_unresolved(condition.expression):
                    branch_had_unresolved = True
                    self._collect_unresolved_expression_classification(
                        condition.expression,
                        kinds=kinds,
                        unknown_refs=unknown_refs,
                        unsupported_ops=unsupported_ops,
                    )
                if self._expression_contains_unresolved(value):
                    branch_had_unresolved = True
                    self._collect_unresolved_expression_classification(
                        value,
                        kinds=kinds,
                        unknown_refs=unknown_refs,
                        unsupported_ops=unsupported_ops,
                    )
            if branch_had_unresolved:
                kinds.add("phi_unresolved")
            return
        for operand in getattr(expr, "operands", []) or []:
            self._collect_unresolved_expression_classification(
                operand,
                kinds=kinds,
                unknown_refs=unknown_refs,
                unsupported_ops=unsupported_ops,
            )

    def _unknown_expression_classification_key(self, expr: Any) -> Tuple[str, Tuple[Any, ...]]:
        runtime_ref = getattr(expr, "runtime_ref", None)
        if getattr(runtime_ref, "deferred_call_ref", None) is not None:
            kind = "deferred_call_unknown"
        else:
            raw_kind = getattr(runtime_ref, "kind", None)
            kind = str(raw_kind or "opaque_unknown")
        runtime_key = self._diagnostic_key_or_semantic_key_or_stable_key_or_none(runtime_ref)
        if runtime_key is not None:
            ref_key = ("unknown_runtime_ref", runtime_key)
        else:
            ref_key = ("unknown_expression", self._expression_runtime_object_key(expr))
        return kind, ref_key

    def _unsupported_smt_op_keys(self, expr: Any) -> Tuple[Any, ...]:
        if expr is None or getattr(expr, "expr_type", None) is None:
            return ()
        result: List[Tuple[Any, ...]] = []
        expr_type = expr.expr_type
        expr_kind = expr_type.__class__
        if expr_type == expr_kind.CALL:
            result.append(
                (
                    "unsupported_smt_op",
                    "CALL",
                    str(getattr(expr, "name", "") or "<anonymous>"),
                    None,
                )
            )
        elif expr_type in {expr_kind.BINARY_OP, expr_kind.UNARY_OP}:
            if expression_contains_unsupported_smt_ops(expr.clone_with(operands=[])):
                result.append(
                    (
                        "unsupported_smt_op",
                        expr_type.name,
                        str(getattr(expr, "operator", "") or "<missing>"),
                        None,
                    )
                )
        elif expr_type == expr_kind.INTRINSIC:
            if expression_contains_unsupported_smt_ops(expr.clone_with(operands=[])):
                result.append(
                    (
                        "unsupported_smt_op",
                        "INTRINSIC",
                        str(getattr(expr, "name", "") or "<anonymous>"),
                        None if getattr(expr, "opcode", None) is None else int(getattr(expr, "opcode")),
                    )
                )
        for operand in getattr(expr, "operands", []) or []:
            result.extend(self._unsupported_smt_op_keys(operand))
        if expr_type == expr_kind.PHI and expr.value:
            for condition, value in expr.value:
                if condition is not None:
                    result.extend(self._unsupported_smt_op_keys(condition.expression))
                result.extend(self._unsupported_smt_op_keys(value))
        return tuple(result)

    def _unresolved_expression_recovery_proof_obligations(
        self,
        object_target_key: Tuple[Any, ...],
    ) -> Optional[Tuple[UnknownRecoveryProofObligation, ...]]:
        target_cause = self._unresolved_expression_target_cause(object_target_key)
        if target_cause in {
            "mixed_float_call_read_recurrence",
            "multiple_or_nested_unresolved",
            "readonly_memory_read",
        }:
            return self._generic_unresolved_expression_proof_obligations(target_cause)
        if self._object_target_contains_originated_phi_circular(object_target_key):
            return (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                    "phi_circular_guard_condition_lowering",
                    required_evidence=(
                        "object_target_key",
                        "multiequal_pcode_op_ref",
                        "guard_condition_key",
                        "guard_condition_literals",
                        "pair_lowering_diagnostic",
                        "unknown_count_relation",
                        "typed_lowering_rule",
                    ),
                    description=(
                        "Lower a PHI-circular guard only when its MULTIEQUAL origin "
                        "and guard-condition provenance are preserved."
                    ),
                ),
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                    "recursive_summary_guard_equivalence",
                    required_evidence=(
                        "left_phi_origin",
                        "right_phi_origin",
                        "guard_condition_pair",
                        "pair_lowering_diagnostic",
                        "summary_parameter_binding",
                        "value_shape_relation",
                    ),
                    description=(
                        "Prove the recursive-summary guard relation before allowing "
                        "the unresolved PHI-circular guard to affect equivalence."
                    ),
                ),
            )
        if self._object_target_contains_deferred_call_unknown(object_target_key):
            return (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                    "deferred_call_return_resolution",
                    required_evidence=(
                        "object_target_key",
                        "deferred_call_site",
                        "callee_identity",
                        "call_effect_summary",
                    ),
                    description=(
                        "Resolve the deferred call return expression before lowering "
                        "the unresolved value into SMT."
                    ),
                ),
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                    "deferred_call_result_equivalence",
                    required_evidence=(
                        "left_return_value",
                        "right_return_value",
                        "argument_binding",
                        "return_width_policy",
                    ),
                    description=(
                        "Prove the deferred-call result is equivalent to the peer "
                        "return value under the active guard and ABI width policy."
                    ),
                ),
            )
        if self._object_target_contains_void_opaque_unknown(object_target_key):
            return (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                    "opaque_unknown_return_origin_resolution",
                    required_evidence=(
                        "object_target_key",
                        "opaque_unknown_ref",
                        "return_storage",
                        "return_case_origin",
                    ),
                    description=(
                        "Resolve the opaque return-value origin before lowering the "
                        "unknown value into SMT."
                    ),
                ),
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                    "opaque_unknown_return_value_equivalence",
                    required_evidence=(
                        "left_return_value",
                        "right_return_value",
                        "guard_condition_pair",
                        "return_width_policy",
                    ),
                    description=(
                        "Prove the opaque return value is equivalent to the peer "
                        "return value under the active guard and width policy."
                    ),
                ),
            )
        return None

    def _generic_unresolved_expression_proof_obligations(
        self,
        cause: str,
    ) -> Tuple[UnknownRecoveryProofObligation, ...]:
        return (
            UnknownRecoveryProofObligation.create(
                UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                "typed_expression_lowering",
                required_evidence=(
                    "object_target_key",
                    "unresolved_location",
                    "unresolved_cause",
                    "typed_expression_key",
                ),
                description=(
                    "Classify and lower the unresolved expression before retrying SMT."
                ),
            ),
            UnknownRecoveryProofObligation.create(
                UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                "type_normalization",
                required_evidence=(
                    "object_target_key",
                    "unresolved_cause",
                    "return_width_policy",
                    "normalization_policy",
                ),
                description=(
                    f"Normalize the {cause} expression only after its semantic "
                    "dependencies have been proven."
                ),
            ),
        )

    @classmethod
    def _unresolved_expression_target_cause(cls, object_target_key: Any) -> Optional[str]:
        causes: List[str] = []

        def visit(value: Any) -> None:
            normalized = cls._normalize_nested_tuple(value)
            if isinstance(normalized, tuple):
                if (
                    len(normalized) == 2
                    and normalized[0] == "unresolved_cause"
                    and isinstance(normalized[1], str)
                ):
                    causes.append(normalized[1])
                    return
                for item in normalized:
                    visit(item)
            elif isinstance(normalized, list):
                for item in normalized:
                    visit(item)
            elif isinstance(normalized, dict):
                for key, item in normalized.items():
                    visit(key)
                    visit(item)

        visit(object_target_key)
        unique_causes = tuple(sorted(set(causes)))
        if not unique_causes:
            return None
        if "mixed_float_call_read_recurrence" in unique_causes:
            return "mixed_float_call_read_recurrence"
        if len(unique_causes) > 1:
            return "multiple_or_nested_unresolved"
        return unique_causes[0]

    def _unresolved_expression_action_status(
        self,
        object_target_key: Optional[Tuple[Any, ...]],
        object_evidence: Any,
    ) -> Optional[UnknownRecoveryActionStatus]:
        if object_evidence is not None:
            return UnknownRecoveryActionStatus.PENDING_PROOF
        if object_target_key is None:
            return None
        if self._unresolved_expression_recovery_proof_obligations(object_target_key):
            return UnknownRecoveryActionStatus.PLANNED
        return None

    @classmethod
    def _object_target_contains_void_opaque_unknown(cls, value: Any) -> bool:
        normalized = cls._normalize_nested_tuple(value)
        if isinstance(normalized, tuple):
            if (
                len(normalized) >= 2
                and normalized[0] == "opaque_unknown"
                and normalized[1] == "void"
            ):
                return True
            return any(cls._object_target_contains_void_opaque_unknown(item) for item in normalized)
        if isinstance(normalized, list):
            return any(cls._object_target_contains_void_opaque_unknown(item) for item in normalized)
        if isinstance(normalized, dict):
            return any(
                cls._object_target_contains_void_opaque_unknown(key)
                or cls._object_target_contains_void_opaque_unknown(item)
                for key, item in normalized.items()
            )
        return False

    @classmethod
    def _object_target_contains_deferred_call_unknown(cls, value: Any) -> bool:
        normalized = cls._normalize_nested_tuple(value)
        if isinstance(normalized, tuple):
            if (
                len(normalized) >= 4
                and normalized[0] == "deferred_call"
                and normalized[1] == "call_out_of_scope"
            ):
                return True
            if (
                len(normalized) >= 2
                and normalized[0] == "unresolved_kinds"
                and isinstance(normalized[1], tuple)
                and "deferred_call_unknown" in normalized[1]
            ):
                return True
            return any(cls._object_target_contains_deferred_call_unknown(item) for item in normalized)
        if isinstance(normalized, list):
            return any(cls._object_target_contains_deferred_call_unknown(item) for item in normalized)
        if isinstance(normalized, dict):
            return any(
                cls._object_target_contains_deferred_call_unknown(key)
                or cls._object_target_contains_deferred_call_unknown(item)
                for key, item in normalized.items()
            )
        return False

    @classmethod
    def _object_target_contains_originated_phi_circular(cls, value: Any) -> bool:
        if isinstance(value, tuple):
            if cls._tuple_is_originated_phi_circular_runtime_ref(value):
                return True
            return any(cls._object_target_contains_originated_phi_circular(item) for item in value)
        if isinstance(value, list):
            return any(cls._object_target_contains_originated_phi_circular(item) for item in value)
        if isinstance(value, dict):
            return any(
                cls._object_target_contains_originated_phi_circular(key)
                or cls._object_target_contains_originated_phi_circular(item)
                for key, item in value.items()
            )
        return False

    @staticmethod
    def _tuple_is_originated_phi_circular_runtime_ref(value: Tuple[Any, ...]) -> bool:
        return (
            len(value) >= 6
            and value[0] == "opaque_unknown"
            and value[1] == "phi_circular"
            and value[4] == "multiequal_pcode_op"
            and value[5] is not None
        )

    def _method_b_closure_side_object_key(
        self,
        side_label: str,
        analysis: Optional[FunctionReturnAnalysis],
        case: ReturnCase,
    ) -> Tuple[Any, ...]:
        value_expr = getattr(case, "value_expr", None)
        return (
            "method_b_closure_side",
            side_label,
            self._analysis_entry_key(analysis) if analysis is not None else None,
            self._readonly_return_case_partition_member_object_key(case),
            (
                "loop_value",
                self._method_b_loop_value_object_key(value_expr),
            ),
            (
                "guards",
                tuple(
                    self._return_condition_object_key(condition)
                    for condition in (getattr(case, "conditions", None) or ())
                ),
            ),
        )

    def _method_b_loop_value_object_key(self, expr: Any) -> Tuple[Any, ...]:
        runtime_ref = getattr(expr, "runtime_ref", None)
        loop_summary = getattr(runtime_ref, "loop_summary", None)
        return (
            "method_b_loop_value",
            self._semantic_key_or_stable_key_or_none(runtime_ref),
            self._semantic_key_or_stable_key_or_none(loop_summary),
            self._method_b_expression_runtime_object_key(expr),
        )

    def _method_b_expression_runtime_object_key(self, expr: Any) -> Tuple[Any, ...]:
        runtime_ref = getattr(expr, "runtime_ref", None)
        if runtime_ref is not None:
            return ("runtime_ref", self._semantic_key_or_stable_key_or_none(runtime_ref))
        return self._expression_runtime_object_key(expr)

    @staticmethod
    def _semantic_key_or_stable_key_or_none(value: Any):
        for name in ("pairwise_semantic_key", "semantic_key", "stable_key"):
            key_fn = getattr(value, name, None)
            if callable(key_fn):
                try:
                    key = key_fn()
                except (AttributeError, TypeError, ValueError, RecursionError):
                    key = None
                if key is not None:
                    return key
        return None

    @staticmethod
    def _diagnostic_key_or_semantic_key_or_stable_key_or_none(value: Any):
        for name in ("diagnostic_key", "pairwise_semantic_key", "semantic_key", "stable_key"):
            key_fn = getattr(value, name, None)
            if callable(key_fn):
                try:
                    key = key_fn()
                except (AttributeError, TypeError, ValueError, RecursionError):
                    key = None
                if key is not None:
                    return key
        return None

    def _readonly_identity_side_object_key(
        self,
        side_label: str,
        analysis: Optional[FunctionReturnAnalysis],
        case: ReturnCase,
    ) -> Tuple[Any, ...]:
        value_expr = getattr(case, "value_expr", None)
        readonly_ref = getattr(value_expr, "runtime_ref", None)
        return (
            "readonly_identity_side",
            side_label,
            self._analysis_entry_key(analysis) if analysis is not None else None,
            self._readonly_return_case_partition_member_object_key(case),
            self._readonly_reduction_ref_object_key(readonly_ref),
            (
                "guards",
                tuple(
                    self._return_condition_object_key(condition)
                    for condition in (getattr(case, "conditions", None) or ())
                ),
            ),
            ("value", self._readonly_value_object_key(value_expr)),
        )

    def _readonly_return_case_partition_member_object_key(self, case: ReturnCase) -> Tuple[Any, ...]:
        return_info = getattr(case, "return_info", None)
        case_index = getattr(case, "index", None)
        try:
            normalized_case_index = int(case_index)
        except (TypeError, ValueError):
            normalized_case_index = None
        source_indices = []
        for source_index in getattr(case, "source_indices", ()) or ():
            try:
                source_indices.append(int(source_index))
            except (TypeError, ValueError):
                continue
        surface = getattr(case, "comparison_surface", None)
        return (
            "readonly_return_case_partition_member",
            normalized_case_index,
            tuple(source_indices),
            (
                "return_case",
                normalized_case_index,
                getattr(return_info, "address", None),
                self._stable_key_or_none(getattr(return_info, "pcode_op_ref", None)),
                getattr(return_info, "pcode_identity", None),
                getattr(return_info, "pcode_order", None),
            ),
            (
                "comparison_surface",
                getattr(surface, "kind", None),
                getattr(surface, "explicit_bit_width", None),
                getattr(surface, "use_sign_extension", None),
            ),
            ("value", self._readonly_value_object_key(getattr(case, "value_expr", None))),
            (
                "guards",
                tuple(
                    self._return_condition_object_key(condition)
                    for condition in (getattr(case, "conditions", None) or ())
                ),
            ),
        )

    def _readonly_value_object_key(self, expr: Any) -> Tuple[Any, ...]:
        readonly_ref = getattr(expr, "runtime_ref", None)
        if isinstance(readonly_ref, ReadonlyReductionRef):
            return ("readonly_value", self._readonly_reduction_ref_object_key(readonly_ref))
        return ("expression", self._expression_runtime_object_key(expr))

    def _readonly_reduction_ref_object_key(self, readonly_ref: Any) -> Tuple[Any, ...]:
        if not isinstance(readonly_ref, ReadonlyReductionRef):
            return ("readonly_reduction_ref", None)
        semantic_key = None
        semantic_key_fn = getattr(readonly_ref, "semantic_key", None)
        if callable(semantic_key_fn):
            try:
                semantic_key = semantic_key_fn()
            except (AttributeError, TypeError, ValueError, RecursionError):
                semantic_key = None
        pointer_base_identity = None
        pointer_semantic_key_fn = getattr(getattr(readonly_ref, "pointer_base_ref", None), "semantic_key", None)
        if callable(pointer_semantic_key_fn):
            try:
                pointer_base_identity = pointer_semantic_key_fn()
            except (AttributeError, TypeError, ValueError, RecursionError):
                pointer_base_identity = None
        witness_keys = []
        for witness in getattr(readonly_ref, "semantic_witnesses", ()) or ():
            witness_key_fn = getattr(witness, "stable_key", None)
            if not callable(witness_key_fn):
                continue
            try:
                witness_keys.append(witness_key_fn())
            except (AttributeError, TypeError, ValueError, RecursionError):
                continue
        return (
            "readonly_reduction_ref",
            getattr(readonly_ref, "reduction_kind", None),
            ("semantic_key", semantic_key),
            ("pointer_base_identity", pointer_base_identity),
            ("count_identities", tuple(sorted(self._readonly_count_identity_keys(readonly_ref), key=repr))),
            (
                "term_contract",
                self._readonly_reduction_term_sequence_contract_key(
                    readonly_ref,
                    result_size=getattr(readonly_ref, "result_size", None),
                ),
            ),
            ("result_size", getattr(readonly_ref, "result_size", None)),
            ("stride", getattr(readonly_ref, "stride", None)),
            ("element_size", getattr(readonly_ref, "element_size", None)),
            ("start_offset", getattr(readonly_ref, "start_offset", None)),
            ("constant_bias", getattr(readonly_ref, "constant_bias", None)),
            ("semantic_witnesses", tuple(witness_keys)),
        )

    def _count_identity_components_compatible(
        self,
        left_storage: Optional[tuple],
        left_index: Optional[tuple],
        right_storage: Optional[tuple],
        right_index: Optional[tuple],
    ) -> bool:
        if left_storage is not None and right_storage is not None:
            if left_storage == right_storage:
                return True
            return False
        return left_index is not None and right_index is not None and left_index == right_index

    def _count_storage_low_projection_compatible(
        self,
        left_storage: tuple,
        right_storage: tuple,
    ) -> bool:
        left_register = self._register_storage_identity_components(left_storage)
        right_register = self._register_storage_identity_components(right_storage)
        if left_register is None or right_register is None:
            return False
        if left_register[:3] != right_register[:3]:
            return False
        left_low, left_size = int(left_register[3]), int(left_register[4])
        right_low, right_size = int(right_register[3]), int(right_register[4])
        if left_low != right_low:
            return False
        return left_size <= right_size or right_size <= left_size

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
                result_size=self._case_pair_readonly_contract_result_size(left_case, right_case),
            )
            if self.debug and not loop_contract_decision.equivalent:
                self._debug_print(
                    "readonly loop contract shortcut declined: "
                    f"{loop_contract_decision.reason}"
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
            if (
                left_case is not None
                and right_case is not None
                and self._case_pair_has_one_sided_counted_loop_summary(left, right, left_case, right_case)
            ):
                return "counted_loop_summary_expression_proof_missing"
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
                    result_size=self._case_pair_readonly_contract_result_size(left_case, right_case),
                )
                if self.debug and not decision.equivalent:
                    self._debug_print(
                        "runtime refs shortcut declined: "
                        f"{decision.reason}"
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

    def _case_pair_counted_loop_summary_matches_closed_expression(
        self,
        left_case: ReturnCase,
        right_case: ReturnCase,
        *,
        base_ctx: Optional[Mapping[str, Any]] = None,
    ) -> bool:
        left = getattr(left_case, "value_expr", None)
        right = getattr(right_case, "value_expr", None)
        left_counted = self._is_provable_counted_loop_summary_value(left, left_case)
        right_counted = self._is_provable_counted_loop_summary_value(right, right_case)
        if left_counted == right_counted:
            if self.debug and (left_counted or right_counted or self._expression_contains_loop_summary_runtime(left) or self._expression_contains_loop_summary_runtime(right)):
                self._debug_print(f"counted-vs-closed proof skipped: left_counted={left_counted}, right_counted={right_counted}")
            return False
        closed_expr = right if left_counted else left
        if self._expression_contains_loop_summary_runtime(closed_expr):
            return False
        comparison_result_size = self._case_pair_comparison_result_size(left_case, right_case)
        if comparison_result_size is None:
            return False

        conditions = self._combined_summary_conditions(left_case, right_case)
        for case in (left_case, right_case):
            for guard in self._runtime_summary_guard_conditions_from_expression(case.value_expr)[0]:
                if guard not in conditions:
                    conditions.append(guard)
        parameters = self._collect_intrinsic_parameter_specs(
            left_case,
            right_case,
            left,
            right,
            *(condition.expression for condition in conditions or [] if condition is not None),
            semantic_parameter_sources=self._auxiliary_semantic_parameter_sources(base_ctx),
        )
        if parameters is None:
            if self.debug:
                self._debug_print("counted-vs-closed proof skipped: missing parameter specs")
            return False
        if self._condition_set_is_unsat(conditions, parameters):
            return True
        if self._prove_counted_loop_closed_expression_candidates(
            counted=left if left_counted else right,
            closed=right if left_counted else left,
            counted_case=left_case if left_counted else right_case,
            result_size=comparison_result_size,
            conditions=conditions,
            parameters=parameters,
        ):
            if self.debug:
                self._debug_print("counted-vs-closed proof discharged by SMT candidate")
            return True
        proved = self._prove_intrinsic_equivalence_under_conditions(
            left,
            right,
            conditions,
            parameters,
        )
        if self.debug:
            self._debug_print(f"counted-vs-closed proof SMT result: {proved}")
        return proved

    def _case_pair_counted_loop_summaries_match_by_closed_values(
        self,
        left_case: ReturnCase,
        right_case: ReturnCase,
        *,
        base_ctx: Optional[Mapping[str, Any]] = None,
    ) -> bool:
        left = getattr(left_case, "value_expr", None)
        right = getattr(right_case, "value_expr", None)
        if not self._is_provable_counted_loop_summary_value(left, left_case):
            return False
        if not self._is_provable_counted_loop_summary_value(right, right_case):
            return False
        comparison_result_size = self._case_pair_comparison_result_size(left_case, right_case)
        if comparison_result_size is None:
            return False

        conditions = self._combined_summary_conditions(left_case, right_case)
        any_runtime_guard = False
        for case in (left_case, right_case):
            guards, guards_complete = self._runtime_summary_guard_conditions_from_expression(case.value_expr)
            if not guards_complete:
                return False
            if guards:
                any_runtime_guard = True
            for guard in guards:
                if guard not in conditions:
                    conditions.append(guard)
        if not any_runtime_guard:
            if self.debug:
                self._debug_print("counted-vs-counted value proof skipped: no runtime summary guards")
            return False
        parameters = self._collect_intrinsic_parameter_specs(
            left_case,
            right_case,
            left,
            right,
            *(condition.expression for condition in conditions or [] if condition is not None),
            semantic_parameter_sources=self._auxiliary_semantic_parameter_sources(base_ctx),
        )
        if parameters is None:
            if self.debug:
                self._debug_print("counted-vs-counted value proof skipped: missing parameter specs")
            return False
        if self._condition_set_is_unsat(conditions, parameters):
            return True
        if self._composed_counted_state_transition_summaries_match(left, right):
            if self.debug:
                self._debug_print("counted-vs-counted proof discharged by composed state-transition semantic key")
            return True

        left_candidates = self._counted_loop_closed_expression_candidates(
            left,
            counted_case=left_case,
            result_size=comparison_result_size,
            conditions=conditions,
            parameters=parameters,
        )
        right_candidates = self._counted_loop_closed_expression_candidates(
            right,
            counted_case=right_case,
            result_size=comparison_result_size,
            conditions=conditions,
            parameters=parameters,
        )
        if not left_candidates or not right_candidates:
            if self.debug:
                self._debug_print(
                    "counted-vs-counted value proof skipped: no closed candidates "
                    f"(left={len(left_candidates)}, right={len(right_candidates)})"
                )
            direct_proved = self._prove_intrinsic_equivalence_under_conditions(
                left,
                right,
                conditions,
                parameters,
                timeout=10,
            )
            if self.debug:
                self._debug_print(f"counted-vs-counted direct SMT proof result: {direct_proved}")
            return direct_proved
        for left_candidate in left_candidates:
            for right_candidate in right_candidates:
                if self._prove_intrinsic_equivalence_under_conditions(
                    left_candidate,
                    right_candidate,
                    conditions,
                    parameters,
                ):
                    if self.debug:
                        self._debug_print("counted-vs-counted proof discharged by SMT candidate pair")
                    return True
        if self._prove_intrinsic_equivalence_under_conditions(
            left,
            right,
            conditions,
            parameters,
            timeout=10,
        ):
            if self.debug:
                self._debug_print("counted-vs-counted proof discharged by direct SMT summary equality")
            return True
        if self.debug:
            self._debug_print("counted-vs-counted proof failed for all candidate pairs")
            self._debug_print(
                "counted-vs-counted failed context: "
                f"left_case={getattr(left_case, 'index', None)}:"
                f"{getattr(left_case, 'branch_index', None)} "
                f"right_case={getattr(right_case, 'index', None)}:"
                f"{getattr(right_case, 'branch_index', None)} "
                f"conditions={ConditionNormalizer.conditions_signature(tuple(conditions))}"
            )
        return False

    def _composed_counted_state_transition_summaries_match(
        self,
        left: Expression,
        right: Expression,
    ) -> bool:
        left_key = self._composed_counted_state_transition_summary_key(left)
        right_key = self._composed_counted_state_transition_summary_key(right)
        return left_key is not None and left_key == right_key

    def _composed_counted_state_transition_summary_key(
        self,
        expr: Expression,
    ) -> Optional[Tuple[Any, ...]]:
        if getattr(expr, "opcode", None) != COUNTED_LOOP_SUM_OPCODE:
            return None
        operands = list(getattr(expr, "operands", ()) or ())
        if len(operands) != 3:
            return None
        base, start, limit = operands
        if getattr(base, "opcode", None) != COUNTED_STATE_TRANSITION_VALUE_OPCODE:
            return None
        counted_ref = getattr(expr, "runtime_ref", None)
        state_ref = getattr(base, "runtime_ref", None)
        if not isinstance(counted_ref, CountedLoopSummaryRef):
            return None
        if not isinstance(state_ref, CountedStateTransitionLoopSummaryRef):
            return None
        outer_side_effect_key = self._counted_loop_outer_side_effect_key(counted_ref)
        if outer_side_effect_key is None:
            return None
        if not self._counted_state_transition_value_operands_match_ref(
            getattr(base, "operands", None) or (),
            state_ref,
        ):
            return None
        if not self._counted_state_transition_cases_allow_bounded_unroll(state_ref):
            return None
        state_key = self._counted_state_transition_semantic_core_key(state_ref)
        if state_key is None:
            return None
        residue_cases = tuple(
            (
                int(modulus),
                int(residue),
                int(coeff),
                int(bias),
            )
            for modulus, residue, coeff, bias in tuple(getattr(counted_ref, "residue_cases", ()) or ())
        )
        residue_bias_terms = tuple(getattr(counted_ref, "residue_bias_terms", ()) or ())
        if residue_bias_terms:
            return None
        start_key = self._canonical_counted_state_transition_outer_start_key(start, residue_cases)
        if start_key is None:
            return None
        try:
            limit_key = ConditionNormalizer.expression_signature(limit)
        except Exception:
            return None
        return (
            "composed_counted_state_transition_sum",
            state_key,
            int(getattr(counted_ref, "induction_step", 0) or 0),
            max(1, int(getattr(counted_ref, "result_size", 0) or 0)),
            bool(getattr(counted_ref, "signed_loop", False)),
            outer_side_effect_key,
            residue_cases,
            start_key,
            limit_key,
        )

    def _counted_loop_outer_side_effect_key(
        self,
        counted_ref: CountedLoopSummaryRef,
    ) -> Optional[Tuple[Any, ...]]:
        loop_summary = getattr(counted_ref, "loop_summary", None)
        if loop_summary is None:
            return None
        profile = getattr(loop_summary, "side_effect_profile", None)
        if profile is None:
            return None
        if getattr(profile, "requires_effect_proof", lambda: True)():
            return None
        try:
            profile_key = profile.stable_key()
        except Exception:
            return None
        if profile_key is None:
            return None
        return ("outer_loop_side_effect_profile", profile_key)

    def _counted_state_transition_semantic_core_key(
        self,
        state_ref: CountedStateTransitionLoopSummaryRef,
    ) -> Optional[Tuple[Any, ...]]:
        profile = getattr(state_ref, "side_effect_profile", None)
        if profile is None:
            return None
        effectful_flags = (
            "memory_reads",
            "memory_writes",
            "calls",
            "escapes",
            "context_memory_writes",
            "context_calls",
            "context_escapes",
        )
        if any(bool(getattr(profile, flag, False)) for flag in effectful_flags):
            return None
        placeholder = getattr(state_ref, "state_placeholder", None)
        transition_expr = getattr(state_ref, "transition_expr", None)
        if not isinstance(placeholder, Expression) or not isinstance(transition_expr, Expression):
            return None
        canonical_state = Expression.variable(
            "__state",
            size=max(1, int(getattr(placeholder, "size", 0) or getattr(state_ref, "state_size", 0) or 4)),
        )
        normalized_transition = self._replace_expression_node(
            transition_expr,
            placeholder,
            canonical_state,
        )
        try:
            transition_key = ConditionNormalizer.expression_signature(normalized_transition)
            init_key = ConditionNormalizer.expression_signature(getattr(state_ref, "initial_state", None))
            start_key = ConditionNormalizer.expression_signature(getattr(state_ref, "start_expr", None))
            limit_key = ConditionNormalizer.expression_signature(getattr(state_ref, "limit_expr", None))
            step_key = ConditionNormalizer.expression_signature(getattr(state_ref, "step_expr", None))
            guard_keys = tuple(
                ConditionNormalizer.conditions_signature((guard,))
                for guard in tuple(getattr(state_ref, "guard_constraints", ()) or ())
            )
        except Exception:
            return None
        return (
            "counted_state_transition_core",
            init_key,
            start_key,
            limit_key,
            step_key,
            transition_key,
            max(1, int(getattr(state_ref, "state_size", 0) or 0)),
            max(1, int(getattr(state_ref, "result_size", 0) or 0)),
            bool(getattr(state_ref, "signed_loop", False)),
            guard_keys,
        )

    def _canonical_counted_state_transition_outer_start_key(
        self,
        start: Expression,
        residue_cases: Tuple[Tuple[int, int, int, int], ...],
    ) -> Optional[Tuple[Any, ...]]:
        start_value = self._raw_constant_value(start)
        if start_value is None:
            try:
                return ConditionNormalizer.expression_signature(start)
            except Exception:
                return None
        if int(start_value) == 0:
            return ("const", 0)
        if int(start_value) == 1 and self._counted_residue_term_at_zero_is_zero(residue_cases):
            return ("const", 0)
        return ("const", int(start_value))

    @staticmethod
    def _counted_residue_term_at_zero_is_zero(
        residue_cases: Tuple[Tuple[int, int, int, int], ...],
    ) -> bool:
        if not residue_cases:
            return False
        for modulus, residue, _coeff, bias in residue_cases:
            if int(modulus) <= 0:
                return False
            if 0 % int(modulus) == int(residue) and int(bias) != 0:
                return False
        return True

    def _case_pair_has_one_sided_counted_loop_summary(
        self,
        left: Expression,
        right: Expression,
        left_case: ReturnCase,
        right_case: ReturnCase,
    ) -> bool:
        left_counted = self._is_provable_counted_loop_summary_value(left, left_case)
        right_counted = self._is_provable_counted_loop_summary_value(right, right_case)
        if left_counted == right_counted:
            return False
        closed_expr = right if left_counted else left
        return not self._expression_contains_loop_summary_runtime(closed_expr)

    def _is_provable_counted_loop_summary_value(
        self,
        expr: Optional[Expression],
        case: ReturnCase,
    ) -> bool:
        if expr is None:
            return False
        if getattr(expr, "expr_type", None) != ExpressionType.INTRINSIC:
            return False
        if getattr(expr, "opcode", None) != COUNTED_LOOP_SUM_OPCODE and getattr(expr, "name", None) != "COUNTED_LOOP_SUM":
            return False
        runtime_ref = getattr(expr, "runtime_ref", None)
        if not isinstance(runtime_ref, CountedLoopSummaryRef):
            return False
        loop_summary = getattr(runtime_ref, "loop_summary", None)
        if loop_summary is None:
            return False
        requires_effect_proof = getattr(loop_summary, "requires_effect_proof", None)
        if callable(requires_effect_proof) and requires_effect_proof():
            return False
        requires_path_proof = getattr(loop_summary, "requires_path_proof", None)
        if callable(requires_path_proof) and requires_path_proof():
            return False
        if not _counted_loop_sum_has_exact_lowering(expr):
            if self.debug:
                self._debug_print("counted loop summary not provable: no exact lowering")
            return False
        guards, complete = self._runtime_summary_guard_conditions_from_expression(expr)
        if not complete:
            if self.debug:
                self._debug_print("counted loop summary not provable: incomplete guards")
            return False
        profile = getattr(loop_summary, "side_effect_profile", None)
        has_control_obligation = bool(
            getattr(profile, "conditional_guards", False)
            or getattr(profile, "context_conditional_guards", False)
            or tuple(getattr(loop_summary, "cases", ()) or ())
        )
        if guards:
            covered = self._case_conditions_cover_runtime_summary_guards(case)
            if self.debug and not covered:
                self._debug_print("counted loop summary not provable: guard coverage missing")
            return covered
        if has_control_obligation:
            if self.debug:
                self._debug_print("counted loop summary not provable: control obligation without guards")
            return False
        return True

    def _prove_counted_loop_closed_expression_candidates(
        self,
        *,
        counted: Expression,
        closed: Expression,
        counted_case: ReturnCase,
        result_size: int,
        conditions: Sequence[Condition],
        parameters: Sequence[Dict[str, Any]],
    ) -> bool:
        candidates = self._counted_loop_closed_expression_candidates(
            counted,
            counted_case=counted_case,
            result_size=result_size,
            conditions=conditions,
            parameters=parameters,
        )
        if not candidates:
            return False
        for candidate in candidates:
            if self._prove_intrinsic_equivalence_under_conditions(
                candidate,
                closed,
                conditions,
                parameters,
            ):
                return True
        return False

    def _counted_loop_closed_expression_candidates(
        self,
        counted: Expression,
        *,
        counted_case: ReturnCase,
        result_size: int,
        conditions: Sequence[Condition],
        parameters: Sequence[Dict[str, Any]],
    ) -> Tuple[Expression, ...]:
        counted_closed = self._counted_loop_positive_closed_expression(
            counted,
            counted_case=counted_case,
            result_size=result_size,
            conditions=conditions,
            parameters=parameters,
        )
        shifted_closed = self._counted_loop_positive_closed_expression(
            counted,
            counted_case=counted_case,
            result_size=result_size,
            conditions=conditions,
            parameters=parameters,
            shifted_progression=True,
        )
        affine_closed = self._counted_loop_affine_closed_expression_candidate(
            counted,
            result_size=result_size,
            conditions=conditions,
            parameters=parameters,
        )
        bounded_state_closed = self._counted_loop_bounded_state_transition_base_candidate(
            counted,
            result_size=result_size,
            conditions=conditions,
            parameters=parameters,
        )
        candidates = [
            candidate
            for candidate in (counted_closed, shifted_closed, affine_closed, bounded_state_closed)
            if candidate is not None
        ]
        return tuple(candidates)

    def _counted_loop_bounded_state_transition_base_candidate(
        self,
        counted: Expression,
        *,
        result_size: int,
        conditions: Sequence[Condition],
        parameters: Sequence[Dict[str, Any]],
    ) -> Optional[Expression]:
        operands = getattr(counted, "operands", None) or []
        if len(operands) != 3:
            return None
        base, start, limit = operands
        if getattr(base, "opcode", None) != COUNTED_STATE_TRANSITION_VALUE_OPCODE:
            return None
        runtime_ref = getattr(base, "runtime_ref", None)
        if not isinstance(runtime_ref, CountedStateTransitionLoopSummaryRef):
            return None
        if not self._counted_state_transition_side_effects_allow_bounded_unroll(runtime_ref):
            return None
        if not self._counted_state_transition_value_operands_match_ref(
            getattr(base, "operands", None) or (),
            runtime_ref,
        ):
            return None
        if not self._counted_state_transition_cases_allow_bounded_unroll(runtime_ref):
            return None
        iteration_count = self._bounded_state_transition_iteration_count_from_conditions(
            runtime_ref,
            conditions=conditions,
            parameters=parameters,
            max_iterations=32,
        )
        if iteration_count is None:
            return None
        unrolled_base = self._unroll_counted_state_transition_value(runtime_ref, iteration_count)
        if unrolled_base is None:
            return None
        unrolled_base = self._coerce_expression_to_size(
            unrolled_base,
            max(1, int(getattr(base, "size", 0) or result_size or 0)),
            signed=bool(getattr(runtime_ref, "signed_loop", False)),
        )
        candidate = counted.clone_with(operands=[unrolled_base, start, limit])
        candidate.size = max(1, int(getattr(counted, "size", 0) or result_size or 0))
        return candidate

    def _counted_state_transition_side_effects_allow_bounded_unroll(
        self,
        runtime_ref: CountedStateTransitionLoopSummaryRef,
    ) -> bool:
        profile = getattr(runtime_ref, "side_effect_profile", None)
        if profile is None:
            return False
        requires_effect_proof = getattr(profile, "requires_effect_proof", None)
        if callable(requires_effect_proof):
            try:
                if requires_effect_proof():
                    return False
            except Exception:
                return False
        guarded_or_effectful_flags = (
            "memory_reads",
            "memory_writes",
            "calls",
            "escapes",
            "context_memory_writes",
            "context_calls",
            "context_escapes",
            "context_conditional_guards",
        )
        if any(bool(getattr(profile, flag, False)) for flag in guarded_or_effectful_flags):
            return False
        effect_descriptors = tuple(getattr(profile, "effect_descriptors", ()) or ())
        if any(getattr(effect, "kind", None) != "conditional_guard" for effect in effect_descriptors):
            return False
        if int(getattr(profile, "effect_count", 0) or 0) > len(effect_descriptors):
            return False
        if tuple(getattr(profile, "context_descriptors", ()) or ()):
            return False
        return True

    def _counted_state_transition_value_operands_match_ref(
        self,
        operands: Sequence[Expression],
        runtime_ref: CountedStateTransitionLoopSummaryRef,
    ) -> bool:
        if len(operands) != 3:
            return False
        expected = (
            getattr(runtime_ref, "initial_state", None),
            getattr(runtime_ref, "start_expr", None),
            getattr(runtime_ref, "limit_expr", None),
        )
        for actual, expected_expr in zip(operands, expected):
            if not isinstance(actual, Expression) or not isinstance(expected_expr, Expression):
                return False
            try:
                if not actual.equals(expected_expr):
                    return False
            except Exception:
                return False
        return True

    def _bounded_state_transition_iteration_count_from_conditions(
        self,
        runtime_ref: CountedStateTransitionLoopSummaryRef,
        *,
        conditions: Sequence[Condition],
        parameters: Sequence[Dict[str, Any]],
        max_iterations: int,
    ) -> Optional[int]:
        start = getattr(runtime_ref, "start_expr", None)
        limit = getattr(runtime_ref, "limit_expr", None)
        step = getattr(runtime_ref, "step_expr", None)
        if not isinstance(start, Expression) or not isinstance(limit, Expression) or not isinstance(step, Expression):
            return None
        if getattr(step, "expr_type", None) != ExpressionType.CONSTANT:
            return None
        try:
            step_value = int(getattr(step, "value", 0) or 0)
        except (TypeError, ValueError):
            return None
        if step_value <= 0:
            return None
        expr_size = max(
            1,
            int(getattr(start, "size", 0) or 0),
            int(getattr(limit, "size", 0) or 0),
            int(getattr(step, "size", 0) or 0),
        )
        start_sized = self._coerce_expression_to_size(
            start,
            expr_size,
            signed=bool(getattr(runtime_ref, "signed_loop", False)),
        )
        limit_sized = self._coerce_expression_to_size(
            limit,
            expr_size,
            signed=bool(getattr(runtime_ref, "signed_loop", False)),
        )
        for iteration_count in range(0, int(max_iterations) + 1):
            offset = Expression.constant(step_value * iteration_count, size=expr_size)
            expected_limit = Expression.binary_op("INT_ADD", start_sized, offset)
            expected_limit.size = expr_size
            equality = Condition(Expression.binary_op("INT_EQUAL", limit_sized, expected_limit))
            if self._condition_set_implies(conditions, [equality], parameters) and self._bounded_state_transition_trip_count_is_proved(
                runtime_ref,
                iteration_count,
                start_value=self._raw_constant_value(start),
                step_value=step_value,
                limit_sized=limit_sized,
                expr_size=expr_size,
                conditions=conditions,
                parameters=parameters,
            ):
                return iteration_count
        return None

    def _bounded_state_transition_trip_count_is_proved(
        self,
        runtime_ref: CountedStateTransitionLoopSummaryRef,
        iteration_count: int,
        *,
        start_value: Optional[int],
        step_value: int,
        limit_sized: Expression,
        expr_size: int,
        conditions: Sequence[Condition],
        parameters: Sequence[Dict[str, Any]],
    ) -> bool:
        if start_value is None or step_value <= 0 or iteration_count < 0:
            return False
        bits = max(1, int(expr_size or 0) * 8)
        if bool(getattr(runtime_ref, "signed_loop", False)):
            min_value = 0
            max_value = (1 << (bits - 1)) - 1
            guard_op = "INT_SLESS"
        else:
            min_value = 0
            max_value = (1 << bits) - 1
            guard_op = "INT_LESS"
        concrete_values: List[int] = []
        for index in range(int(iteration_count) + 1):
            value = int(start_value) + int(step_value) * index
            if value < min_value or value > max_value:
                return False
            concrete_values.append(value)
        guard_conclusions: List[Condition] = []
        for value in concrete_values[: int(iteration_count)]:
            current = Expression.constant(value, size=expr_size)
            guard = Expression.binary_op(guard_op, current, limit_sized)
            guard.size = 1
            guard_conclusions.append(Condition(guard))
        exit_value = Expression.constant(concrete_values[int(iteration_count)], size=expr_size)
        exit_equality = Expression.binary_op("INT_EQUAL", exit_value, limit_sized)
        exit_equality.size = 1
        guard_conclusions.append(Condition(exit_equality))
        return self._condition_set_implies(conditions, guard_conclusions, parameters)

    def _counted_state_transition_cases_allow_bounded_unroll(
        self,
        runtime_ref: CountedStateTransitionLoopSummaryRef,
    ) -> bool:
        transition_cases = getattr(runtime_ref, "transition_cases", None)
        if not transition_cases:
            return False
        cases = tuple(transition_cases)
        if len(cases) != 1:
            return False
        only_case = cases[0]
        if not isinstance(only_case, tuple) or len(only_case) != 2:
            return False
        condition_signature, transition_signature = only_case
        if condition_signature is not None and condition_signature != () and condition_signature != (("none",),):
            return False
        transition_expr = getattr(runtime_ref, "transition_expr", None)
        if not isinstance(transition_expr, Expression):
            return False
        try:
            expected_transition_signature = ConditionNormalizer.expression_signature(transition_expr)
        except Exception:
            return False
        if transition_signature != expected_transition_signature:
            return False
        return True

    def _unroll_counted_state_transition_value(
        self,
        runtime_ref: CountedStateTransitionLoopSummaryRef,
        iteration_count: int,
    ) -> Optional[Expression]:
        if iteration_count < 0:
            return None
        state_placeholder = getattr(runtime_ref, "state_placeholder", None)
        transition_expr = getattr(runtime_ref, "transition_expr", None)
        value = getattr(runtime_ref, "initial_state", None)
        if not isinstance(state_placeholder, Expression) or not isinstance(transition_expr, Expression) or not isinstance(value, Expression):
            return None
        for _ in range(int(iteration_count)):
            value = self._replace_expression_node(transition_expr, state_placeholder, value)
            value.size = max(1, int(getattr(runtime_ref, "result_size", 0) or getattr(value, "size", 0) or 0))
        return value

    def _replace_expression_node(
        self,
        expr: Expression,
        target: Expression,
        replacement: Expression,
    ) -> Expression:
        if expr.equals(target):
            return replacement
        if getattr(expr, "expr_type", None) == ExpressionType.PHI:
            branches = []
            for cond, value in getattr(expr, "value", None) or []:
                new_cond = cond
                if cond is not None and getattr(cond, "expression", None) is not None:
                    new_cond = Condition(
                        self._replace_expression_node(cond.expression, target, replacement),
                        getattr(cond, "negated", False),
                    )
                branches.append((new_cond, self._replace_expression_node(value, target, replacement)))
            return expr.clone_with(value=branches)
        operands = getattr(expr, "operands", None) or []
        if not operands:
            return expr
        return expr.clone_with(
            operands=[
                self._replace_expression_node(operand, target, replacement)
                for operand in operands
            ]
        )

    def _counted_loop_affine_closed_expression_candidate(
        self,
        counted: Expression,
        *,
        result_size: int,
        conditions: Sequence[Condition],
        parameters: Sequence[Dict[str, Any]],
    ) -> Optional[Expression]:
        runtime_ref = getattr(counted, "runtime_ref", None)
        if not self._counted_loop_refs_allow_affine_value_proof(runtime_ref, runtime_ref):
            return None
        if not self._counted_loop_affine_widths_are_safe(counted, counted, result_size, parameters):
            return None
        return self._counted_loop_affine_closed_expression(
            counted,
            result_size=result_size,
            conditions=conditions,
            parameters=parameters,
        )

    def _counted_loop_positive_closed_expression(
        self,
        counted: Expression,
        *,
        counted_case: ReturnCase,
        result_size: int,
        conditions: Sequence[Condition],
        parameters: Sequence[Dict[str, Any]],
        shifted_progression: bool = False,
    ) -> Optional[Expression]:
        runtime_ref = getattr(counted, "runtime_ref", None)
        if not isinstance(runtime_ref, CountedLoopSummaryRef):
            return None
        if int(getattr(runtime_ref, "induction_step", 0) or 0) != 1:
            return None
        residue_cases = tuple(getattr(runtime_ref, "residue_cases", ()) or ())
        if len(residue_cases) != 1:
            return None
        modulus, residue, coeff, bias = residue_cases[0]
        if int(modulus) != 1 or int(residue) != 0:
            return None
        operands = list(getattr(counted, "operands", ()) or ())
        if len(operands) != 3:
            return None
        base, start, limit = operands
        if getattr(start, "expr_type", None) != ExpressionType.CONSTANT:
            return None
        if int(getattr(start, "value", 0) or 0) != 0:
            return None
        guard_operator = "INT_SLESS" if bool(getattr(runtime_ref, "signed_loop", False)) else "INT_LESS"
        positive_span = Condition(Expression.binary_op(guard_operator, start, limit))
        if not self._condition_set_implies(conditions, [positive_span], parameters):
            return None

        target_size = max(1, int(result_size or 0))
        limit_size = max(1, int(getattr(limit, "size", 0) or 0))
        start_size = max(1, int(getattr(start, "size", 0) or 0))
        count_size = max(target_size, limit_size, start_size)
        limit_count = self._coerce_expression_to_size(
            limit,
            count_size,
            signed=bool(getattr(runtime_ref, "signed_loop", False)),
        )
        limit_result = self._coerce_expression_to_size(
            limit,
            target_size,
            signed=bool(getattr(runtime_ref, "signed_loop", False)),
        )
        wide_size = max(8, count_size * 2)
        wide_limit = Expression.unary_op("INT_ZEXT", limit_count)
        wide_limit.size = wide_size
        limit_minus_one_count = Expression.binary_op(
            "INT_SUB",
            limit_count,
            Expression.constant(1, size=count_size),
        )
        limit_minus_one_count.size = count_size
        limit_minus_one_result = self._coerce_expression_to_size(
            limit_minus_one_count,
            target_size,
            signed=False,
        )
        if shifted_progression:
            limit_minus_two_count = Expression.binary_op(
                "INT_SUB",
                limit_count,
                Expression.constant(2, size=count_size),
            )
            limit_minus_two_count.size = count_size
            progression_left = Expression.unary_op("INT_ZEXT", limit_minus_one_count)
            progression_left.size = wide_size
            progression_right = Expression.unary_op("INT_ZEXT", limit_minus_two_count)
            progression_right.size = wide_size
        else:
            progression_left = wide_limit
            progression_right = Expression.binary_op(
                "INT_SUB",
                wide_limit,
                Expression.constant(1, size=wide_size),
            )
            progression_right.size = wide_size
        product = Expression.binary_op("INT_MULT", progression_left, progression_right)
        half = Expression.binary_op("INT_RIGHT", product, Expression.constant(1, size=wide_size))
        triangular = Expression.binary_op("SUBPIECE", half, Expression.constant(0, size=4))
        triangular.size = target_size
        terms: List[Expression] = []
        coeff = int(coeff)
        if coeff != 0:
            if coeff == 1:
                coeff_term = triangular
            else:
                coeff_term = Expression.binary_op(
                    "INT_MULT",
                    triangular,
                    Expression.constant(coeff, size=target_size),
                )
                coeff_term.size = target_size
            terms.append(coeff_term)
            if shifted_progression:
                if coeff == 1:
                    shifted_linear = limit_minus_one_result
                else:
                    shifted_linear = Expression.binary_op(
                        "INT_MULT",
                        limit_minus_one_result,
                        Expression.constant(coeff, size=target_size),
                    )
                    shifted_linear.size = target_size
                terms.append(shifted_linear)
        bias = int(bias)
        if bias != 0:
            bias_term = Expression.binary_op(
                "INT_MULT",
                limit_result,
                Expression.constant(bias, size=target_size),
            )
            bias_term.size = target_size
            terms.append(bias_term)
        for bias_modulus, bias_residue, bias_expr in tuple(getattr(runtime_ref, "residue_bias_terms", ()) or ()):
            if int(bias_modulus) != 1 or int(bias_residue) != 0:
                return None
            term_bias = self._coerce_expression_to_size(
                bias_expr,
                target_size,
                signed=self._expression_prefers_signed_extension(bias_expr),
            )
            bias_expr_term = Expression.binary_op("INT_MULT", limit_result, term_bias)
            bias_expr_term.size = target_size
            terms.append(bias_expr_term)
        base_low = base
        if getattr(base, "expr_type", None) == ExpressionType.CONSTANT and int(getattr(base, "value", 0) or 0) == 0:
            base_low = None
        else:
            base_low = self._coerce_expression_to_size(
                base,
                target_size,
                signed=self._expression_prefers_signed_extension(base),
            )
        if base_low is not None:
            terms.insert(0, base_low)
        if not terms:
            return Expression.constant(0, size=target_size)
        total = terms[0]
        for term in terms[1:]:
            total = Expression.binary_op("INT_ADD", total, term)
            total.size = target_size
        total.size = target_size
        return total

    def _coerce_expression_to_size(
        self,
        expr: Expression,
        target_size: int,
        *,
        signed: bool = False,
    ) -> Expression:
        target_size = max(1, int(target_size or 0))
        expr_size = int(getattr(expr, "size", 0) or 0)
        if expr_size <= 0:
            expr_bits = int(expression_smt_bit_width(expr) or 0)
            expr_size = max(1, (expr_bits + 7) // 8) if expr_bits > 0 else target_size
        if expr_size == target_size:
            return expr
        if expr_size > target_size:
            narrowed = Expression.binary_op("SUBPIECE", expr, Expression.constant(0, size=4))
            narrowed.size = target_size
            return narrowed
        widened = Expression.unary_op("INT_SEXT" if signed else "INT_ZEXT", expr)
        widened.size = target_size
        return widened

    def _expression_prefers_signed_extension(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        data_type = str(getattr(expr, "data_type", "") or "").lower()
        if "unsigned" in data_type or data_type.startswith("u"):
            return False
        if any(token in data_type for token in ("signed", "int", "long", "short", "char")):
            return True
        return False

    def _counted_loop_values_are_provably_equivalent(
        self,
        left: Expression,
        right: Expression,
        *,
        left_case: Optional[ReturnCase],
        right_case: Optional[ReturnCase],
        semantic_parameter_sources: Sequence[ParameterInfo] = (),
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
            if self._counted_loop_affine_values_are_provably_equivalent(
                left,
                right,
                left_case=left_case,
                right_case=right_case,
                semantic_parameter_sources=semantic_parameter_sources,
            ):
                return True
            return False
        if self._counted_loop_affine_values_are_provably_equivalent(
            left,
            right,
            left_case=left_case,
            right_case=right_case,
            semantic_parameter_sources=semantic_parameter_sources,
        ):
            return True
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

    def _counted_loop_affine_values_are_provably_equivalent(
        self,
        left: Expression,
        right: Expression,
        *,
        left_case: ReturnCase,
        right_case: ReturnCase,
        semantic_parameter_sources: Sequence[ParameterInfo] = (),
    ) -> bool:
        left_ref = getattr(left, "runtime_ref", None)
        right_ref = getattr(right, "runtime_ref", None)
        if not self._counted_loop_refs_allow_affine_value_proof(left_ref, right_ref):
            return False

        left_guards, left_guards_complete = self._runtime_summary_guard_conditions_from_expression(left)
        right_guards, right_guards_complete = self._runtime_summary_guard_conditions_from_expression(right)
        if not left_guards_complete or not right_guards_complete:
            return False
        if not left_guards and not right_guards:
            return False

        conditions = self._combined_summary_conditions(left_case, right_case)
        for guard in tuple(left_guards) + tuple(right_guards):
            if guard not in conditions:
                conditions.append(guard)
        parameters = self._collect_intrinsic_parameter_specs(
            left_case,
            right_case,
            left,
            right,
            *(condition.expression for condition in conditions or [] if condition is not None),
            semantic_parameter_sources=semantic_parameter_sources,
        )
        if parameters is None:
            return False
        if self._condition_set_is_unsat(conditions, parameters):
            return True

        result_size = self._case_pair_comparison_result_size(left_case, right_case)
        if result_size is None:
            return False
        if not self._counted_loop_affine_widths_are_safe(left, right, result_size, parameters):
            return False
        left_closed = self._counted_loop_affine_closed_expression(
            left,
            result_size=result_size,
            conditions=conditions,
            parameters=parameters,
        )
        right_closed = self._counted_loop_affine_closed_expression(
            right,
            result_size=result_size,
            conditions=conditions,
            parameters=parameters,
        )
        if left_closed is None or right_closed is None:
            return False
        return self._prove_intrinsic_equivalence_under_conditions(
            left_closed,
            right_closed,
            conditions,
            parameters,
        )

    def _counted_loop_affine_widths_are_safe(
        self,
        left: Expression,
        right: Expression,
        result_size: int,
        parameters: Sequence[Dict[str, Any]],
    ) -> bool:
        target_bits = max(1, int(result_size or 0) * 8)
        by_identity = {
            tuple(spec.get("identity")): spec
            for spec in parameters or []
            if isinstance(spec.get("identity"), tuple)
        }

        def visit(expr: Optional[Expression]) -> bool:
            if expr is None:
                return True
            if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER:
                expr_bits = max(1, int(getattr(expr, "size", 0) or 4) * 8)
                if expr_bits <= target_bits:
                    return True
                identity = parameter_identity_key_from_expression(expr)
                spec = by_identity.get(identity)
                if spec is None:
                    return False
                try:
                    narrow_bits = int(spec.get("semantic_narrow_bits"))
                except (TypeError, ValueError):
                    return False
                if narrow_bits != target_bits:
                    return False
                return spec.get("semantic_signedness") in {"signed", "unsigned"}
            if getattr(expr, "expr_type", None) == ExpressionType.PHI:
                for cond, branch_value in getattr(expr, "value", None) or []:
                    if cond is not None and not visit(getattr(cond, "expression", None)):
                        return False
                    if not visit(branch_value):
                        return False
                return True
            return all(visit(operand) for operand in getattr(expr, "operands", None) or [])

        for counted in (left, right):
            if not visit(counted):
                return False
            runtime_ref = getattr(counted, "runtime_ref", None)
            for _, _, bias_expr in tuple(getattr(runtime_ref, "residue_bias_terms", ()) or ()):
                if not visit(bias_expr):
                    return False
        return True

    def _counted_loop_refs_allow_affine_value_proof(self, left_ref, right_ref) -> bool:
        if not isinstance(left_ref, CountedLoopSummaryRef) or not isinstance(right_ref, CountedLoopSummaryRef):
            return False
        for loop_summary in (getattr(left_ref, "loop_summary", None), getattr(right_ref, "loop_summary", None)):
            if loop_summary is None:
                return False
            requires_effect_proof = getattr(loop_summary, "requires_effect_proof", None)
            if callable(requires_effect_proof) and requires_effect_proof():
                return False
            requires_path_proof = getattr(loop_summary, "requires_path_proof", None)
            if callable(requires_path_proof) and requires_path_proof():
                return False
        if max(1, int(getattr(left_ref, "result_size", 0) or 0)) != max(
            1, int(getattr(right_ref, "result_size", 0) or 0)
        ):
            return False
        return True

    def _counted_loop_affine_closed_expression(
        self,
        counted: Expression,
        *,
        result_size: int,
        conditions: Sequence[Condition],
        parameters: Sequence[Dict[str, Any]],
    ) -> Optional[Expression]:
        runtime_ref = getattr(counted, "runtime_ref", None)
        if not isinstance(runtime_ref, CountedLoopSummaryRef):
            return None
        residue_cases = tuple(getattr(runtime_ref, "residue_cases", ()) or ())
        if len(residue_cases) != 1:
            return None
        modulus, residue, coeff, bias = residue_cases[0]
        if int(modulus) != 1 or int(residue) != 0:
            return None
        operands = list(getattr(counted, "operands", ()) or ())
        if len(operands) != 3:
            return None
        base, start, limit = operands
        step = int(getattr(runtime_ref, "induction_step", 0) or 0)
        if step <= 0:
            return None

        trip_count = self._counted_loop_affine_trip_count_expression(
            start,
            limit,
            step,
            conditions=conditions,
            parameters=parameters,
        )
        if trip_count is None:
            return None
        if not self._expression_is_provably_nonnegative_under_conditions(trip_count, conditions, parameters):
            return None

        target_size = max(1, int(result_size or 0))
        count_size = max(
            target_size,
            max(1, int(getattr(start, "size", 0) or 0)),
            max(1, int(getattr(limit, "size", 0) or 0)),
            max(1, int(getattr(trip_count, "size", 0) or 0)),
        )
        count = self._coerce_expression_to_size(
            trip_count,
            count_size,
            signed=bool(getattr(runtime_ref, "signed_loop", False)),
        )
        start_count = self._coerce_expression_to_size(
            start,
            count_size,
            signed=self._expression_prefers_signed_extension(start),
        )
        wide_size = max(8, count_size * 2, target_size * 2)
        wide_count = Expression.unary_op("INT_ZEXT", count)
        wide_count.size = wide_size
        wide_start = Expression.unary_op("INT_ZEXT", start_count)
        wide_start.size = wide_size

        count_minus_one = Expression.binary_op(
            "INT_SUB",
            wide_count,
            Expression.constant(1, size=wide_size),
        )
        count_minus_one.size = wide_size
        triangular_product = Expression.binary_op("INT_MULT", wide_count, count_minus_one)
        triangular_product.size = wide_size
        triangular = Expression.binary_op(
            "INT_RIGHT",
            triangular_product,
            Expression.constant(1, size=wide_size),
        )
        triangular.size = wide_size

        progression_sum = Expression.binary_op(
            "INT_ADD",
            Expression.binary_op("INT_MULT", wide_count, wide_start),
            Expression.binary_op("INT_MULT", Expression.constant(step, size=wide_size), triangular),
        )
        progression_sum.size = wide_size

        terms: List[Expression] = []
        coeff = int(coeff)
        if coeff != 0:
            coeff_term = progression_sum
            if coeff != 1:
                coeff_term = Expression.binary_op(
                    "INT_MULT",
                    progression_sum,
                    Expression.constant(coeff, size=wide_size),
                )
                coeff_term.size = wide_size
            terms.append(coeff_term)

        bias = int(bias)
        if bias != 0:
            bias_term = Expression.binary_op(
                "INT_MULT",
                wide_count,
                Expression.constant(bias, size=wide_size),
            )
            bias_term.size = wide_size
            terms.append(bias_term)

        for bias_modulus, bias_residue, bias_expr in tuple(getattr(runtime_ref, "residue_bias_terms", ()) or ()):
            if int(bias_modulus) != 1 or int(bias_residue) != 0:
                return None
            bias_wide = self._coerce_expression_to_size(
                bias_expr,
                wide_size,
                signed=self._expression_prefers_signed_extension(bias_expr),
            )
            bias_expr_term = Expression.binary_op("INT_MULT", wide_count, bias_wide)
            bias_expr_term.size = wide_size
            terms.append(bias_expr_term)

        base_wide = None
        if not (
            getattr(base, "expr_type", None) == ExpressionType.CONSTANT
            and int(getattr(base, "value", 0) or 0) == 0
        ):
            base_wide = self._coerce_expression_to_size(
                base,
                wide_size,
                signed=self._expression_prefers_signed_extension(base),
            )
        if base_wide is not None:
            terms.insert(0, base_wide)
        if not terms:
            return Expression.constant(0, size=target_size)

        total = terms[0]
        for term in terms[1:]:
            total = Expression.binary_op("INT_ADD", total, term)
            total.size = wide_size
        low = Expression.binary_op("SUBPIECE", total, Expression.constant(0, size=4))
        low.size = target_size
        return low

    def _counted_loop_affine_trip_count_expression(
        self,
        start: Expression,
        limit: Expression,
        step: int,
        *,
        conditions: Sequence[Condition],
        parameters: Sequence[Dict[str, Any]],
    ) -> Optional[Expression]:
        if step <= 0:
            return None
        if step == 1 and self._expression_is_zero(start):
            return limit
        candidate = self._extract_affine_limit_trip_count_candidate(start, limit, step)
        if candidate is None:
            return None
        if not self._counted_loop_limit_matches_start_plus_step_count(
            start,
            limit,
            step,
            candidate,
            conditions,
            parameters,
        ):
            return None
        return candidate

    def _extract_affine_limit_trip_count_candidate(
        self,
        start: Expression,
        limit: Expression,
        step: int,
    ) -> Optional[Expression]:
        if getattr(limit, "expr_type", None) != ExpressionType.BINARY_OP or getattr(limit, "operator", None) != "INT_ADD":
            return None
        left, right = list(getattr(limit, "operands", ()) or ())
        for maybe_start, maybe_scaled in ((left, right), (right, left)):
            if not self._expressions_same_shape_ignoring_runtime(maybe_start, start):
                continue
            candidate = self._extract_constant_scaled_expression(maybe_scaled, step)
            if candidate is not None:
                return candidate
        return None

    def _extract_constant_scaled_expression(self, expr: Expression, factor: int) -> Optional[Expression]:
        if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP or getattr(expr, "operator", None) != "INT_MULT":
            return None
        left, right = list(getattr(expr, "operands", ()) or ())
        for maybe_const, candidate in ((left, right), (right, left)):
            if getattr(maybe_const, "expr_type", None) != ExpressionType.CONSTANT:
                continue
            try:
                if int(getattr(maybe_const, "value", 0) or 0) == int(factor):
                    return candidate
            except (TypeError, ValueError):
                continue
        return None

    def _counted_loop_limit_matches_start_plus_step_count(
        self,
        start: Expression,
        limit: Expression,
        step: int,
        count: Expression,
        conditions: Sequence[Condition],
        parameters: Sequence[Dict[str, Any]],
    ) -> bool:
        size = max(
            1,
            int(getattr(start, "size", 0) or 0),
            int(getattr(limit, "size", 0) or 0),
            int(getattr(count, "size", 0) or 0),
        )
        start_sized = self._coerce_expression_to_size(
            start,
            size,
            signed=self._expression_prefers_signed_extension(start),
        )
        count_sized = self._coerce_expression_to_size(
            count,
            size,
            signed=self._expression_prefers_signed_extension(count),
        )
        limit_sized = self._coerce_expression_to_size(
            limit,
            size,
            signed=self._expression_prefers_signed_extension(limit),
        )
        scaled = Expression.binary_op(
            "INT_MULT",
            Expression.constant(step, size=size),
            count_sized,
        )
        scaled.size = size
        expected_limit = Expression.binary_op("INT_ADD", start_sized, scaled)
        expected_limit.size = size
        if self._expressions_same_shape_ignoring_runtime(expected_limit, limit_sized):
            return True
        equality = Condition(Expression.binary_op("INT_EQUAL", limit_sized, expected_limit))
        return self._condition_set_implies(conditions, [equality], parameters)

    def _expression_is_zero(self, expr: Expression) -> bool:
        if getattr(expr, "expr_type", None) != ExpressionType.CONSTANT:
            return False
        try:
            return int(getattr(expr, "value", 0) or 0) == 0
        except (TypeError, ValueError):
            return False

    def _expressions_same_shape_ignoring_runtime(self, left: Expression, right: Expression) -> bool:
        if left is None or right is None:
            return False
        return left.structural_key(include_semantic_runtime_refs=False) == right.structural_key(
            include_semantic_runtime_refs=False
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
        declarations = [f"(set-logic {self._auxiliary_smt_logic([expr], conditions)})"]
        symbol_infos = self._build_auxiliary_parameter_infos(parameters)
        for symbol in symbol_infos:
            declarations.append(f"(declare-const {symbol.smt_name} (_ BitVec {symbol.bit_width}))")

        intrinsic_declarations: List[str] = []
        for item in [expr, *(condition.expression for condition in conditions or [] if condition is not None)]:
            for declaration in collect_intrinsic_smt_declarations(item):
                if declaration not in intrinsic_declarations:
                    intrinsic_declarations.append(declaration)
        declarations.extend(intrinsic_declarations)
        declarations.extend(self._collect_auxiliary_float_declarations([expr], conditions))

        assertions = []
        assertions.extend(build_parameter_semantic_constraints(symbol_infos))
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
        semantic_parameter_sources: Sequence[ParameterInfo] = (),
    ) -> Optional[List[Dict[str, Any]]]:
        specs: Dict[Tuple[object, ...], Dict[str, Any]] = {}
        unresolved_symbol = False
        semantic_by_index = self._auxiliary_semantic_hints_by_index(semantic_parameter_sources)

        def add_spec(identity: Optional[Tuple[object, ...]], candidate: Dict[str, Any]) -> None:
            if identity is None:
                return
            size = max(1, int(candidate.get("size", 0) or 4))
            self._apply_auxiliary_semantic_hint(candidate, size=size, semantic_by_index=semantic_by_index)
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
                    "is_signed": self._expression_prefers_signed_extension(expr),
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

    def _auxiliary_semantic_parameter_sources(
        self,
        base_ctx: Optional[Mapping[str, Any]],
    ) -> Tuple[ParameterInfo, ...]:
        if not isinstance(base_ctx, Mapping):
            return ()
        sources: List[ParameterInfo] = []
        for key in ("params1", "params2"):
            for param in base_ctx.get(key, ()) or ():
                if isinstance(param, ParameterInfo):
                    sources.append(param)
        return tuple(sources)

    def _auxiliary_semantic_hints_by_index(
        self,
        semantic_parameter_sources: Sequence[ParameterInfo],
    ) -> Dict[int, Tuple[int, str, int]]:
        hints: Dict[int, Tuple[int, str, int]] = {}
        for source in semantic_parameter_sources or ():
            try:
                index = int(getattr(source, "index"))
                bit_width = int(getattr(source, "bit_width"))
                narrow_bits = getattr(source, "semantic_narrow_bits", None)
                narrow_bits = int(narrow_bits) if narrow_bits is not None else None
            except (TypeError, ValueError):
                continue
            signedness = getattr(source, "semantic_signedness", None)
            if bit_width <= 0 or narrow_bits is None or narrow_bits <= 0:
                continue
            if narrow_bits >= bit_width or signedness not in {"signed", "unsigned"}:
                continue
            current = hints.get(index)
            if current is None or bit_width > current[2]:
                hints[index] = (narrow_bits, signedness, bit_width)
        return hints

    def _apply_auxiliary_semantic_hint(
        self,
        candidate: Dict[str, Any],
        *,
        size: int,
        semantic_by_index: Mapping[int, Tuple[int, str, int]],
    ) -> None:
        try:
            index = int(candidate.get("index"))
            bit_width = max(1, int(size)) * 8
        except (TypeError, ValueError):
            return
        hint = semantic_by_index.get(index)
        if hint is None:
            return
        narrow_bits, signedness, source_bit_width = hint
        if source_bit_width != bit_width or narrow_bits >= bit_width:
            return
        candidate["semantic_narrow_bits"] = int(narrow_bits)
        candidate["semantic_signedness"] = signedness

    def _prove_intrinsic_equivalence_under_conditions(
        self,
        left: Expression,
        right: Expression,
        conditions: Sequence[Condition],
        parameters: Sequence[Dict[str, Any]],
        *,
        timeout: int = 2,
    ) -> bool:
        query = self._build_intrinsic_equivalence_query(left, right, conditions, parameters)
        if not query:
            return False
        result = Z3Solver(timeout=max(1, int(timeout)), debug=self.debug).check_equivalence_direct(query)
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
        declarations = [f"(set-logic {self._auxiliary_smt_logic([left, right], conditions)})"]
        symbol_infos = self._build_auxiliary_parameter_infos(parameters)
        for symbol in symbol_infos:
            declarations.append(f"(declare-const {symbol.smt_name} (_ BitVec {symbol.bit_width}))")
        semantic_constraints = build_parameter_semantic_constraints(symbol_infos)

        intrinsic_declarations: List[str] = []
        for expr in (left, right):
            for declaration in collect_intrinsic_smt_declarations(expr):
                if declaration not in intrinsic_declarations:
                    intrinsic_declarations.append(declaration)
            for name, bit_width in collect_unknown_smt_declarations(expr):
                declaration = f"(declare-const {name} (_ BitVec {int(bit_width)}))"
                if declaration not in intrinsic_declarations:
                    intrinsic_declarations.append(declaration)
        for condition in conditions or []:
            if condition is None:
                continue
            for declaration in collect_intrinsic_smt_declarations(condition.expression):
                if declaration not in intrinsic_declarations:
                    intrinsic_declarations.append(declaration)
            for name, bit_width in collect_unknown_smt_declarations(condition.expression):
                declaration = f"(declare-const {name} (_ BitVec {int(bit_width)}))"
                if declaration not in intrinsic_declarations:
                    intrinsic_declarations.append(declaration)
        declarations.extend(intrinsic_declarations)
        declarations.extend(self._collect_auxiliary_float_declarations([left, right], conditions))

        assertions = []
        assertions.extend(semantic_constraints)
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
                    semantic_narrow_bits=(
                        int(spec["semantic_narrow_bits"])
                        if spec.get("semantic_narrow_bits") is not None
                        else None
                    ),
                    semantic_signedness=spec.get("semantic_signedness"),
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
            return Condition(cloned_expr, bool(getattr(node, "negated", False))).to_smt(float_mode="fp")
        if isinstance(node, Expression):
            cloned_expr = self._clone_auxiliary_expression_for_smt(
                node,
                identity_to_spec,
            )
            return cloned_expr.to_smt(float_mode="fp") if cloned_expr is not None else None
        return None

    def _auxiliary_smt_logic(
        self,
        expressions: Sequence[Optional[Expression]],
        conditions: Sequence[Condition],
    ) -> str:
        uses_float_theory = any(expression_uses_smt_float_theory(expr) for expr in expressions if expr is not None)
        uses_uf = any(expression_uses_smt_uf(expr, float_mode="fp") for expr in expressions if expr is not None)
        for condition in conditions or []:
            if condition is not None and expression_uses_smt_float_theory(condition.expression):
                uses_float_theory = True
            if condition is not None and expression_uses_smt_uf(condition.expression, float_mode="fp"):
                uses_uf = True
            if uses_float_theory and uses_uf:
                break
        return smt_logic_name(uses_float_theory=uses_float_theory, uses_uf=uses_uf)

    def _collect_auxiliary_float_declarations(
        self,
        expressions: Sequence[Optional[Expression]],
        conditions: Sequence[Condition],
    ) -> List[str]:
        declarations: List[str] = []
        for expr in expressions:
            for declaration in collect_float_predicate_smt_declarations(expr, float_mode="fp"):
                if declaration not in declarations:
                    declarations.append(declaration)
        for condition in conditions or []:
            if condition is None:
                continue
            for declaration in collect_float_predicate_smt_declarations(condition.expression, float_mode="fp"):
                if declaration not in declarations:
                    declarations.append(declaration)
        return declarations

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
            cloned_runtime_ref = self._clone_auxiliary_runtime_ref_for_smt(
                getattr(expr, "runtime_ref", None),
                identity_to_spec,
            )
            if cloned_runtime_ref is None and getattr(expr, "runtime_ref", None) is not None:
                return None
            return expr.clone_with(runtime_ref=cloned_runtime_ref) if cloned_runtime_ref is not None else expr
        cloned_operands = []
        for operand in operands:
            cloned_operand = self._clone_auxiliary_expression_for_smt(
                operand,
                identity_to_spec,
            )
            if cloned_operand is None:
                return None
            cloned_operands.append(cloned_operand)
        cloned_runtime_ref = self._clone_auxiliary_runtime_ref_for_smt(
            getattr(expr, "runtime_ref", None),
            identity_to_spec,
        )
        if cloned_runtime_ref is None and getattr(expr, "runtime_ref", None) is not None:
            return None
        if cloned_runtime_ref is not None:
            return expr.clone_with(operands=cloned_operands, runtime_ref=cloned_runtime_ref)
        return expr.clone_with(operands=cloned_operands)

    def _clone_auxiliary_runtime_ref_for_smt(
        self,
        runtime_ref: Any,
        identity_to_spec: Dict[Tuple[object, ...], Dict[str, Any]],
    ) -> Any:
        if runtime_ref is None:
            return None
        if isinstance(runtime_ref, CountedLoopSummaryRef):
            return self._clone_auxiliary_counted_loop_summary_ref(runtime_ref, identity_to_spec)
        return runtime_ref

    def _clone_auxiliary_counted_loop_summary_ref(
        self,
        runtime_ref: CountedLoopSummaryRef,
        identity_to_spec: Dict[Tuple[object, ...], Dict[str, Any]],
    ) -> Optional[CountedLoopSummaryRef]:
        cloned_bias_terms = self._clone_auxiliary_residue_bias_terms(
            tuple(getattr(runtime_ref, "residue_bias_terms", ()) or ()),
            identity_to_spec,
        )
        if cloned_bias_terms is None:
            return None
        loop_summary = getattr(runtime_ref, "loop_summary", None)
        cloned_loop_summary = loop_summary
        if isinstance(loop_summary, LoopSummaryRef):
            cloned_loop_summary = self._clone_auxiliary_loop_summary_ref(loop_summary, identity_to_spec)
            if cloned_loop_summary is None:
                return None
        return replace(
            runtime_ref,
            residue_bias_terms=cloned_bias_terms,
            loop_summary=cloned_loop_summary,
        )

    def _clone_auxiliary_loop_summary_ref(
        self,
        loop_summary: LoopSummaryRef,
        identity_to_spec: Dict[Tuple[object, ...], Dict[str, Any]],
    ) -> Optional[LoopSummaryRef]:
        term_descriptor = getattr(loop_summary, "term_descriptor", None)
        if not isinstance(term_descriptor, LoopTermDescriptorRef):
            return loop_summary
        cloned_bias_terms = self._clone_auxiliary_residue_bias_terms(
            tuple(getattr(term_descriptor, "residue_bias_terms", ()) or ()),
            identity_to_spec,
        )
        if cloned_bias_terms is None:
            return None
        return replace(
            loop_summary,
            term_descriptor=replace(term_descriptor, residue_bias_terms=cloned_bias_terms),
        )

    def _clone_auxiliary_residue_bias_terms(
        self,
        bias_terms: Sequence[Tuple[int, int, Any]],
        identity_to_spec: Dict[Tuple[object, ...], Dict[str, Any]],
    ) -> Optional[Tuple[Tuple[int, int, Any], ...]]:
        cloned_terms = []
        for modulus, residue, bias_expr in bias_terms:
            cloned_bias_expr = self._clone_auxiliary_expression_for_smt(
                bias_expr,
                identity_to_spec,
            )
            if cloned_bias_expr is None:
                return None
            cloned_terms.append((int(modulus), int(residue), cloned_bias_expr))
        return tuple(cloned_terms)

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
        if reason == "loop_summary_guard_mismatch":
            return self._loop_summary_contracts_match_without_guard(
                left_case.value_expr,
                right_case.value_expr,
            )
        return False

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

    def _condition_set_is_unsat(
        self,
        conditions: Sequence[Condition],
        parameters: Sequence[Dict[str, Any]],
    ) -> bool:
        if self._conditions_have_parameter_mask_constant_conflict(list(conditions or ())):
            return True
        identity_conditions = self._conditions_with_object_identity_parameter_symbols(
            list(conditions or []),
            parameters,
        )
        if self._conditions_have_parameter_mask_constant_conflict(identity_conditions):
            return True
        solver_result = ConditionSMTOracle.conjunction_is_unsat(identity_conditions)
        if solver_result is not None:
            return solver_result
        return ConditionSimplifier.object_centric_is_contradiction(identity_conditions)

    def _conditions_have_parameter_mask_constant_conflict(
        self,
        conditions: Sequence[Condition],
    ) -> bool:
        constants: Dict[Tuple[Any, ...], Tuple[int, int]] = {}
        mask_equalities: List[Tuple[Tuple[Any, ...], int, int, int]] = []
        for condition in conditions or ():
            equality = self._condition_positive_equality_operands(condition)
            if equality is None:
                continue
            left, right = equality
            constant_equality = self._parameter_constant_equality(left, right)
            if constant_equality is None:
                constant_equality = self._parameter_constant_equality(right, left)
            if constant_equality is not None:
                key, value, bits = constant_equality
                previous = constants.get(key)
                if previous is not None and previous != (value, bits):
                    return True
                constants[key] = (value, bits)
                continue
            mask_equality = self._parameter_mask_equality(left, right)
            if mask_equality is None:
                mask_equality = self._parameter_mask_equality(right, left)
            if mask_equality is not None:
                mask_equalities.append(mask_equality)
        for key, mask, expected, bits in mask_equalities:
            known = constants.get(key)
            if known is None:
                continue
            known_value, known_bits = known
            width_bits = max(1, int(bits or known_bits or 0))
            width_mask = (1 << width_bits) - 1
            if (known_value & mask & width_mask) != (expected & width_mask):
                return True
        return False

    def _condition_positive_equality_operands(
        self,
        condition: Condition,
    ) -> Optional[Tuple[Expression, Expression]]:
        expr = getattr(condition, "expression", None)
        if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
            return None
        operator = getattr(expr, "operator", None)
        negated = bool(getattr(condition, "negated", False))
        if operator == "INT_NOTEQUAL" and negated:
            pass
        elif operator == "INT_EQUAL" and not negated:
            pass
        else:
            return None
        operands = list(getattr(expr, "operands", ()) or ())
        if len(operands) != 2:
            return None
        return operands[0], operands[1]

    def _parameter_constant_equality(
        self,
        maybe_param_expr: Expression,
        maybe_const_expr: Expression,
    ) -> Optional[Tuple[Tuple[Any, ...], int, int]]:
        const_value = self._raw_constant_value(maybe_const_expr)
        if const_value is None:
            return None
        affine = self._parameter_plus_constant_affine(maybe_param_expr)
        if affine is None:
            return None
        key, offset, bits = affine
        width_mask = (1 << max(1, bits)) - 1
        return key, (int(const_value) - int(offset)) & width_mask, bits

    def _parameter_mask_equality(
        self,
        maybe_mask_expr: Expression,
        maybe_const_expr: Expression,
    ) -> Optional[Tuple[Tuple[Any, ...], int, int, int]]:
        const_value = self._raw_constant_value(maybe_const_expr)
        if const_value is None:
            return None
        mask_expr = maybe_mask_expr
        if (
            getattr(mask_expr, "expr_type", None) == ExpressionType.BINARY_OP
            and getattr(mask_expr, "operator", None) == "INT_SUB"
        ):
            operands = list(getattr(mask_expr, "operands", ()) or ())
            if len(operands) != 2:
                return None
            sub_const = self._raw_constant_value(operands[1])
            if sub_const is None:
                return None
            mask_expr = operands[0]
            const_value = int(const_value) + int(sub_const)
        if getattr(mask_expr, "expr_type", None) != ExpressionType.BINARY_OP:
            return None
        if getattr(mask_expr, "operator", None) != "INT_AND":
            return None
        operands = list(getattr(mask_expr, "operands", ()) or ())
        if len(operands) != 2:
            return None
        for maybe_mask, maybe_param in ((operands[0], operands[1]), (operands[1], operands[0])):
            mask_value = self._raw_constant_value(maybe_mask)
            key = self._parameter_expression_key(maybe_param)
            if mask_value is None or key is None:
                continue
            bits = max(1, int(getattr(maybe_param, "size", 0) or getattr(mask_expr, "size", 0) or 4) * 8)
            width_mask = (1 << bits) - 1
            return key, int(mask_value) & width_mask, int(const_value) & width_mask, bits
        return None

    def _parameter_plus_constant_affine(
        self,
        expr: Expression,
    ) -> Optional[Tuple[Tuple[Any, ...], int, int]]:
        key = self._parameter_expression_key(expr)
        if key is not None:
            bits = max(1, int(getattr(expr, "size", 0) or 4) * 8)
            return key, 0, bits
        if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
            return None
        operator = getattr(expr, "operator", None)
        operands = list(getattr(expr, "operands", ()) or ())
        if len(operands) != 2:
            return None
        bits = max(1, int(getattr(expr, "size", 0) or 4) * 8)
        width_mask = (1 << bits) - 1
        if operator == "INT_ADD":
            for left, right in ((operands[0], operands[1]), (operands[1], operands[0])):
                affine = self._parameter_plus_constant_affine(left)
                const_value = self._raw_constant_value(right)
                if affine is None or const_value is None:
                    continue
                key, offset, affine_bits = affine
                return key, (int(offset) + int(const_value)) & width_mask, max(bits, affine_bits)
        if operator == "INT_SUB":
            affine = self._parameter_plus_constant_affine(operands[0])
            const_value = self._raw_constant_value(operands[1])
            if affine is None or const_value is None:
                return None
            key, offset, affine_bits = affine
            return key, (int(offset) - int(const_value)) & width_mask, max(bits, affine_bits)
        return None

    def _parameter_expression_key(self, expr: Expression) -> Optional[Tuple[Any, ...]]:
        if getattr(expr, "expr_type", None) != ExpressionType.PARAMETER:
            return None
        return (
            "parameter",
            str(getattr(expr, "name", "") or ""),
            int(getattr(expr, "value", -1) or -1),
            max(1, int(getattr(expr, "size", 0) or 4)),
        )

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

    def _cases_admit_reduction_count_values(
        self,
        exact_case: ReturnCase,
        summary_case: ReturnCase,
        accumulator_proof,
        exact_counts: Sequence[int],
    ) -> bool:
        count_values = tuple(sorted({int(value) for value in exact_counts if int(value) > 0}))
        if not count_values:
            return False
        if len(count_values) == 1:
            return self._cases_admit_reduction_count(
                exact_case,
                summary_case,
                accumulator_proof,
                count_values[0],
            )
        return self._combined_conditions_imply_reduction_count_values(
            exact_case,
            summary_case,
            accumulator_proof,
            count_values,
        )

    def _combined_conditions_imply_reduction_count_values(
        self,
        exact_case: ReturnCase,
        summary_case: ReturnCase,
        accumulator_proof,
        exact_counts: Sequence[int],
    ) -> bool:
        count_values = tuple(sorted({int(value) for value in exact_counts if int(value) > 0}))
        if not count_values:
            return False
        if len(count_values) == 1:
            return self._combined_conditions_imply_reduction_count(
                exact_case,
                summary_case,
                accumulator_proof,
                count_values[0],
            )
        count_bits = max(
            self._case_reduction_count_bit_width(exact_case, accumulator_proof),
            self._case_reduction_count_bit_width(summary_case, accumulator_proof),
        )
        parameters = (
            list(getattr(exact_case, "parameters", None) or [])
            + list(getattr(summary_case, "parameters", None) or [])
        )
        count_expr = self._reduction_count_parameter_expression(
            parameters,
            accumulator_proof,
            int(count_bits),
        )
        if count_expr is None:
            return False
        membership = self._reduction_count_membership_condition(
            count_expr,
            count_values,
            int(count_bits),
        )
        if membership is None:
            return False
        implication_conditions = list(self._combined_summary_conditions(exact_case, summary_case) or [])
        implication_conditions.append(membership.negate())
        identity_conditions = self._conditions_with_object_identity_parameter_symbols(
            implication_conditions,
            parameters,
        )
        solver_result = ConditionSMTOracle.conjunction_is_unsat(identity_conditions)
        if solver_result is not None:
            return solver_result
        return ConditionSimplifier.object_centric_is_contradiction(identity_conditions)

    def _reduction_count_membership_condition(
        self,
        count_expr: Expression,
        count_values: Sequence[int],
        count_bits: int,
    ) -> Optional[Condition]:
        values = tuple(sorted({int(value) for value in count_values if int(value) > 0}))
        if not values:
            return None
        count_size = max(1, (max(1, int(count_bits)) + 7) // 8)
        equalities = [
            Expression.binary_op(
                "INT_EQUAL",
                count_expr,
                Expression.constant(value, size=count_size),
            )
            for value in values
        ]
        membership_expr = equalities[0]
        for equality in equalities[1:]:
            membership_expr = Expression.binary_op("BOOL_OR", membership_expr, equality)
        return Condition(membership_expr, False)

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
        projected_candidates = []
        if proof_storage is not None and proof_index is not None:
            for parameter in parameters or []:
                parameter_index = self._parameter_descriptor_index_identity_key(parameter)
                parameter_storage = self._parameter_descriptor_storage_identity_key(parameter)
                if (
                    parameter_index == proof_index
                    and parameter_storage is not None
                    and self._count_storage_low_projection_compatible(
                        proof_storage,
                        parameter_storage,
                    )
                ):
                    projected_candidates.append(parameter)
        if len(projected_candidates) == 1:
            return projected_candidates[0]
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
                identities.add(("parameter_index", int(index)))
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
                    const_value = self._solve_reduction_count_masked_equality(
                        left,
                        self._exact_reduction_count_constant(right),
                        operator,
                        not condition_true,
                        case,
                        accumulator_proof,
                    )
                if const_value is None:
                    const_value = self._solve_reduction_count_masked_equality(
                        right,
                        self._exact_reduction_count_constant(left),
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

    def _solve_reduction_count_masked_equality(
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
        affine = self._extract_full_width_masked_reduction_count_affine(
            expr,
            case,
            accumulator_proof,
        )
        if affine is None:
            return None
        coeff, bias = affine
        if int(coeff) != 1:
            return None
        solved = int(other_const) - int(bias)
        return int(solved) if solved > 0 else None

    def _extract_full_width_masked_reduction_count_affine(
        self,
        expr: Optional[Expression],
        case: ReturnCase,
        accumulator_proof,
    ) -> Optional[tuple[int, int]]:
        if expr is None:
            return None
        masked = self._extract_full_width_masked_reduction_count_view(expr, case, accumulator_proof)
        if masked is not None:
            return 1, 0
        if getattr(expr, "expr_type", None) == ExpressionType.CONSTANT:
            value = self._exact_reduction_count_constant(expr)
            return (0, int(value)) if value is not None else None
        if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP or len(getattr(expr, "operands", None) or []) != 2:
            return None
        left = self._extract_full_width_masked_reduction_count_affine(expr.operands[0], case, accumulator_proof)
        right = self._extract_full_width_masked_reduction_count_affine(expr.operands[1], case, accumulator_proof)
        operator = getattr(expr, "operator", None)
        if operator == "INT_ADD" and left is not None and right is not None:
            return int(left[0]) + int(right[0]), int(left[1]) + int(right[1])
        if operator == "INT_SUB" and left is not None and right is not None:
            return int(left[0]) - int(right[0]), int(left[1]) - int(right[1])
        return None

    def _extract_full_width_masked_reduction_count_view(
        self,
        expr: Optional[Expression],
        case: ReturnCase,
        accumulator_proof,
    ) -> Optional[Expression]:
        if (
            expr is None
            or getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP
            or getattr(expr, "operator", None) != "INT_AND"
            or len(getattr(expr, "operands", None) or []) != 2
        ):
            return None
        left, right = expr.operands
        candidates = ((left, right), (right, left))
        for source, mask_expr in candidates:
            mask = self._exact_reduction_count_constant(mask_expr)
            if mask is None:
                continue
            if not self._expression_is_full_reduction_count_view(source, case, accumulator_proof):
                if self._expression_is_projected_reduction_count_mask_view(
                    source,
                    int(mask),
                    case,
                    accumulator_proof,
                ):
                    return source
                continue
            source_bits = max(1, int(expression_smt_bit_width(source) or 0))
            expr_bits = max(1, int(expression_smt_bit_width(expr) or source_bits))
            if expr_bits != source_bits:
                continue
            if int(mask) != (1 << int(source_bits)) - 1:
                if self._expression_is_projected_reduction_count_mask_view(
                    source,
                    int(mask),
                    case,
                    accumulator_proof,
                ):
                    return source
                continue
            return source
        return None

    def _expression_is_projected_reduction_count_mask_view(
        self,
        source: Optional[Expression],
        mask: int,
        case: ReturnCase,
        accumulator_proof,
    ) -> bool:
        if source is None or getattr(source, "expr_type", None) != ExpressionType.PARAMETER:
            return False
        descriptor = self._reduction_count_parameter_descriptor(
            getattr(case, "parameters", None) or [],
            accumulator_proof,
        )
        if descriptor is None:
            return False
        descriptor_storage = self._parameter_descriptor_storage_identity_key(descriptor)
        proof_storage = self._reduction_count_storage_identity_key(accumulator_proof)
        if descriptor_storage is None or proof_storage is None:
            return False
        if not self._count_storage_low_projection_compatible(descriptor_storage, proof_storage):
            return False
        source_storage = self._parameter_expression_storage_identity_key(source)
        if source_storage is not None and not self._count_storage_low_projection_compatible(
            descriptor_storage,
            source_storage,
        ):
            return False
        descriptor_index = self._parameter_descriptor_index_identity_key(descriptor)
        source_index = self._parameter_expression_index_identity_key(source)
        proof_index = self._reduction_count_index_identity_key(accumulator_proof)
        if descriptor_index is None or source_index is None or proof_index is None:
            return False
        if descriptor_index != source_index or descriptor_index != proof_index:
            return False
        try:
            descriptor_bits = int(descriptor.get("size", 0) or 0) * 8
        except (TypeError, ValueError):
            descriptor_bits = 0
        if descriptor_bits <= 0:
            return False
        source_bits = max(1, int(expression_smt_bit_width(source) or 0))
        if source_bits < descriptor_bits:
            return False
        if int(mask) != (1 << int(descriptor_bits)) - 1:
            return False
        return True

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

    def _register_pairwise_extra_assertions(
        self,
        base_ctx: Dict[str, Any],
        pair_id: str,
        assertions: Sequence[str],
    ) -> None:
        if not assertions:
            self._clear_pairwise_extra_assertions(base_ctx, pair_id)
            return
        by_pair = base_ctx.setdefault("pairwise_extra_assertions_by_pair", {})
        by_pair[pair_id] = tuple(str(item) for item in assertions if str(item).strip())

    def _clear_pairwise_extra_assertions(
        self,
        base_ctx: Dict[str, Any],
        pair_id: str,
    ) -> None:
        by_pair = base_ctx.get("pairwise_extra_assertions_by_pair")
        if isinstance(by_pair, dict):
            by_pair.pop(pair_id, None)
        evidence_by_pair = base_ctx.get("pairwise_unresolved_deferred_call_lowering_evidence_by_pair")
        if isinstance(evidence_by_pair, dict):
            evidence_by_pair.pop(pair_id, None)
        lowered_keys_by_pair = base_ctx.get("pairwise_unresolved_deferred_call_lowered_unknown_keys_by_pair")
        if isinstance(lowered_keys_by_pair, dict):
            lowered_keys_by_pair.pop(pair_id, None)

    def _try_build_unresolved_phi_circular_lowering(
        self,
        *,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        pair_id: str,
    ) -> Optional[_UnresolvedDeferredCallLowering]:
        # A phi-circular equality assertion is a semantic proof obligation, not
        # a syntactic lowering. Keep this disabled until completed proof
        # evidence can be checked here.
        return None

    def _try_build_unresolved_deferred_call_lowering(
        self,
        *,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        pair_id: str,
    ) -> Optional[_UnresolvedDeferredCallLowering]:
        analysis1 = base_ctx.get("analysis1")
        analysis2 = base_ctx.get("analysis2")
        if analysis1 is None or analysis2 is None:
            return None
        value1 = getattr(case1, "value_expr", None)
        value2 = getattr(case2, "value_expr", None)
        if self._expression_has_unsupported_smt_op_excluding_unknowns(value1):
            return None
        if self._expression_has_unsupported_smt_op_excluding_unknowns(value2):
            return None
        if self._case_conditions_have_unsupported_smt_op_excluding_unknowns(case1):
            return None
        if self._case_conditions_have_unsupported_smt_op_excluding_unknowns(case2):
            return None
        value_bits1 = int(expression_smt_bit_width(value1) or 0)
        value_bits2 = int(expression_smt_bit_width(value2) or 0)
        if value_bits1 <= 0 or value_bits2 <= 0 or value_bits1 != value_bits2:
            return None

        left_unknowns = self._collect_case_unknown_expression_nodes(case1)
        right_unknowns = self._collect_case_unknown_expression_nodes(case2)
        if not left_unknowns or not right_unknowns or len(left_unknowns) != len(right_unknowns):
            return None

        left_items = []
        right_items = []
        for expr in left_unknowns:
            item = self._deferred_call_unknown_lowering_item(
                analysis1,
                expr,
                side_label="function1",
            )
            if item is None:
                return None
            left_items.append(item)
        for expr in right_unknowns:
            item = self._deferred_call_unknown_lowering_item(
                analysis2,
                expr,
                side_label="function2",
            )
            if item is None:
                return None
            right_items.append(item)

        unmatched_right = list(right_items)
        assertions: List[str] = [
            f"; unresolved_expression runtime-unknown equality lowering for pair {pair_id}",
            "; object evidence: pairwise_runtime_unknown_lowering",
        ]
        evidence: List[Tuple[Any, ...]] = []
        lowered_left_unknown_keys: List[Any] = []
        lowered_right_unknown_keys: List[Any] = []
        for left_expr, left_info, left_key, left_kind, left_match_key in left_items:
            if left_kind != "deferred_call":
                return None
            proof_content = self._matched_deferred_call_argument_proof_content(
                left_key,
                analysis1,
                analysis1,
                analysis2,
            )
            if proof_content is None:
                return None
            expected_peer_key = self._normalize_nested_tuple(
                proof_content.get("peer_object_target_key")
            )
            candidates = [
                item
                for item in unmatched_right
                if (
                    item[3] == left_kind
                    and self._normalize_nested_tuple(item[2]) == expected_peer_key
                )
            ]
            if len(candidates) != 1:
                return None
            right_expr, right_info, right_key, right_kind, right_match_key = candidates[0]
            left_bits = int(expression_smt_bit_width(left_expr) or 0)
            right_bits = int(expression_smt_bit_width(right_expr) or 0)
            if left_bits <= 0 or right_bits <= 0 or left_bits != right_bits:
                return None
            unmatched_right.remove(candidates[0])
            assertions.append(
                f"(assert (= {left_expr.to_smt(float_mode='fp')} {right_expr.to_smt(float_mode='fp')}))"
            )
            lowered_left_unknown_keys.append(self._expression_runtime_object_key(left_expr))
            lowered_right_unknown_keys.append(self._expression_runtime_object_key(right_expr))
            evidence.append(
                (
                    "matched_deferred_call_runtime_unknown",
                    ("left_unknown", self._expression_runtime_object_key(left_expr)),
                    ("right_unknown", self._expression_runtime_object_key(right_expr)),
                    ("left_object_target", left_key),
                    ("right_object_target", right_key),
                    ("lowering_kind", left_kind),
                    ("match_key", left_match_key),
                    ("bit_width", left_bits),
                    (
                        "left_recovery_status",
                        getattr(left_info, "call_argument_recovery_status", None),
                    ),
                    (
                        "right_recovery_status",
                        getattr(right_info, "call_argument_recovery_status", None),
                    ),
                )
            )
        if unmatched_right:
            return None

        evidence_by_pair = base_ctx.setdefault(
            "pairwise_unresolved_deferred_call_lowering_evidence_by_pair",
            {},
        )
        evidence_by_pair[pair_id] = tuple(evidence)
        lowered_keys_by_pair = base_ctx.setdefault(
            "pairwise_unresolved_deferred_call_lowered_unknown_keys_by_pair",
            {},
        )
        lowered_keys_by_pair[pair_id] = {
            "left": tuple(lowered_left_unknown_keys),
            "right": tuple(lowered_right_unknown_keys),
        }
        return _UnresolvedDeferredCallLowering(
            assertions=tuple(assertions),
            evidence=tuple(evidence),
        )

    def _phi_circular_case_shape_and_unknowns(
        self,
        case: ReturnCase,
    ) -> Tuple[Optional[Tuple[Any, ...]], Tuple[Any, ...]]:
        unknowns: List[Any] = []
        value_shape = self._phi_circular_expression_shape_key(
            getattr(case, "value_expr", None),
            unknowns,
        )
        if value_shape is None:
            return None, ()
        condition_shapes: List[Tuple[Any, ...]] = []
        for condition in getattr(case, "conditions", None) or ():
            expression = getattr(condition, "expression", None)
            condition_shape = self._phi_circular_expression_shape_key(expression, unknowns)
            if condition_shape is None:
                return None, ()
            condition_shapes.append(
                (
                    "condition",
                    bool(getattr(condition, "negated", False)),
                    condition_shape,
                )
            )
        return (
            (
                "phi_circular_case_shape",
                ("value", value_shape),
                ("conditions", tuple(condition_shapes)),
            ),
            tuple(unknowns),
        )

    def _phi_circular_expression_shape_key(
        self,
        expr: Any,
        unknowns: List[Any],
    ) -> Optional[Tuple[Any, ...]]:
        if expr is None or getattr(expr, "expr_type", None) is None:
            return None
        expr_type = expr.expr_type
        if expr_type == ExpressionType.UNKNOWN:
            if not self._unknown_expression_is_originated_phi_circular(expr):
                return None
            bits = int(expression_smt_bit_width(expr) or 0)
            if bits <= 0:
                return None
            unknowns.append(expr)
            return ("unknown", "phi_circular", bits)
        if self._expression_node_is_unsupported_smt_op(expr):
            return None
        bits = int(expression_smt_bit_width(expr) or 0)
        if expr_type == ExpressionType.CONSTANT:
            return ("const", int(getattr(expr, "value", 0) or 0), bits)
        if expr_type == ExpressionType.LITERAL:
            return ("literal", repr(getattr(expr, "value", None)), bits)
        if expr_type == ExpressionType.PARAMETER:
            raw_value = getattr(expr, "value", None)
            return (
                "parameter",
                str(getattr(expr, "name", "") or ""),
                -1 if raw_value is None else int(raw_value),
                bits,
            )
        if expr_type == ExpressionType.VARIABLE:
            return None
        if expr_type == ExpressionType.UNARY_OP:
            operands = getattr(expr, "operands", None) or ()
            if len(operands) != 1:
                return None
            operand = self._phi_circular_expression_shape_key(operands[0], unknowns)
            if operand is None:
                return None
            return ("unary", str(getattr(expr, "operator", "") or ""), bits, operand)
        if expr_type == ExpressionType.BINARY_OP:
            operands = getattr(expr, "operands", None) or ()
            if len(operands) != 2:
                return None
            left = self._phi_circular_expression_shape_key(operands[0], unknowns)
            right = self._phi_circular_expression_shape_key(operands[1], unknowns)
            if left is None or right is None:
                return None
            return (
                "binary",
                str(getattr(expr, "operator", "") or ""),
                bits,
                left,
                right,
            )
        if expr_type == ExpressionType.INTRINSIC:
            operands = []
            for operand_expr in getattr(expr, "operands", None) or ():
                operand = self._phi_circular_expression_shape_key(operand_expr, unknowns)
                if operand is None:
                    return None
                operands.append(operand)
            return (
                "intrinsic",
                str(getattr(expr, "name", "") or ""),
                None if getattr(expr, "opcode", None) is None else int(getattr(expr, "opcode")),
                bits,
                tuple(operands),
            )
        return None

    @classmethod
    def _unknown_expression_is_originated_phi_circular(cls, expr: Any) -> bool:
        if getattr(expr, "expr_type", None) != ExpressionType.UNKNOWN:
            return False
        runtime_ref = getattr(expr, "runtime_ref", None)
        if getattr(runtime_ref, "kind", None) != "opaque_unknown":
            return False
        if getattr(runtime_ref, "reason", None) != "phi_circular":
            return False
        if getattr(runtime_ref, "origin_kind", None) != "multiequal_pcode_op":
            return False
        return cls._stable_key_or_none(getattr(runtime_ref, "origin_ref", None)) is not None

    def _case_conditions_have_unsupported_smt_op_excluding_unknowns(self, case: ReturnCase) -> bool:
        for condition in getattr(case, "conditions", None) or ():
            expression = getattr(condition, "expression", None)
            if self._expression_has_unsupported_smt_op_excluding_unknowns(expression):
                return True
        return False

    def _case_conditions_contain_unresolved(self, case: ReturnCase) -> bool:
        for condition in getattr(case, "conditions", None) or ():
            expression = getattr(condition, "expression", None)
            if self._expression_contains_unresolved(expression):
                return True
        return False

    def _collect_case_unknown_expression_nodes(self, case: ReturnCase) -> Tuple[Any, ...]:
        result: List[Any] = []
        seen = set()

        def add_from(expr: Any) -> None:
            for unknown in self._collect_unknown_expression_nodes(expr):
                key = self._expression_runtime_object_key(unknown)
                if key in seen:
                    continue
                seen.add(key)
                result.append(unknown)

        add_from(getattr(case, "value_expr", None))
        for condition in getattr(case, "conditions", None) or ():
            add_from(getattr(condition, "expression", None))
        return tuple(result)

    def _collect_unknown_expression_nodes(self, expr: Any) -> Tuple[Any, ...]:
        result: List[Any] = []
        self._collect_unknown_expression_nodes_into(expr, result)
        return tuple(result)

    def _collect_unknown_expression_nodes_into(self, expr: Any, result: List[Any]) -> None:
        if expr is None or getattr(expr, "expr_type", None) is None:
            return
        if expr.expr_type == ExpressionType.UNKNOWN:
            result.append(expr)
            return
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for condition, value in expr.value:
                if condition is not None:
                    self._collect_unknown_expression_nodes_into(condition.expression, result)
                self._collect_unknown_expression_nodes_into(value, result)
            return
        for operand in getattr(expr, "operands", []) or []:
            self._collect_unknown_expression_nodes_into(operand, result)

    def _expression_has_unsupported_smt_op_excluding_unknowns(self, expr: Any) -> bool:
        if expr is None or getattr(expr, "expr_type", None) is None:
            return True
        if expr.expr_type == ExpressionType.UNKNOWN:
            return False
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for condition, value in expr.value:
                if condition is not None and self._expression_contains_unresolved(condition.expression):
                    return True
                if self._expression_has_unsupported_smt_op_excluding_unknowns(value):
                    return True
            return False
        if self._expression_node_is_unsupported_smt_op(expr):
            return True
        for operand in getattr(expr, "operands", []) or []:
            if self._expression_has_unsupported_smt_op_excluding_unknowns(operand):
                return True
        return False

    def _expression_node_is_unsupported_smt_op(self, expr: Any) -> bool:
        if expr is None or getattr(expr, "expr_type", None) is None:
            return True
        if expr.expr_type == ExpressionType.UNKNOWN:
            return False
        try:
            node_only = expr.clone_with(operands=[])
        except (AttributeError, TypeError, ValueError):
            return False
        return bool(expression_contains_unsupported_smt_ops(node_only))

    def _deferred_call_unknown_lowering_item(
        self,
        analysis: FunctionReturnAnalysis,
        expr: Any,
        *,
        side_label: str,
    ) -> Optional[Tuple[Any, Any, Tuple[Any, ...], str, Tuple[Any, ...]]]:
        runtime_ref = getattr(expr, "runtime_ref", None)
        deferred_ref = getattr(runtime_ref, "deferred_call_ref", None)
        if deferred_ref is not None:
            info = self._deferred_call_info_for_ref(analysis, deferred_ref)
            if info is None:
                return None
            object_target_key = self._deferred_call_object_target_key(
                info,
                analysis=analysis,
                side_label=side_label,
            )
            if not self._call_effect_target_expression_key_is_present(
                self._cross_binary_call_effect_component_key(
                    self._deferred_call_target_expression_key(object_target_key)
                )
            ):
                return None
            if not self._call_effect_argument_keys_are_present(
                self._cross_binary_call_effect_component_key(
                    self._deferred_call_argument_keys(object_target_key)
                )
            ):
                return None
            return expr, info, object_target_key, "deferred_call", ()
        return None

    def _deferred_call_info_for_ref(
        self,
        analysis: FunctionReturnAnalysis,
        deferred_ref: Any,
    ) -> Optional[Any]:
        try:
            ref_key = deferred_ref.stable_key()
        except (AttributeError, TypeError, ValueError):
            return None
        deferred_calls = getattr(analysis, "deferred_calls", None) or {}
        direct = deferred_calls.get(ref_key) if hasattr(deferred_calls, "get") else None
        if direct is not None:
            return direct
        for info in getattr(deferred_calls, "values", lambda: ())():
            candidate_ref = getattr(info, "deferred_call_ref", None)
            try:
                if candidate_ref is not None and candidate_ref.stable_key() == ref_key:
                    return info
            except (AttributeError, TypeError, ValueError):
                continue
        return None

    def _solve_return_width_bridge_with_completed_proof(
        self,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        param_replace_fn1,
        param_replace_fn2,
        pair_id: str,
        *,
        object_target_key: Tuple[Any, ...],
        blocking_detail: str,
    ) -> Optional[QueryResult]:
        self._last_return_width_bridge_pending_evidence = None
        analysis1 = base_ctx.get("analysis1")
        analysis2 = base_ctx.get("analysis2")
        if analysis1 is None or analysis2 is None:
            self._set_return_width_bridge_pending_evidence(
                object_target_key=object_target_key,
                subreason="analysis_context_unavailable",
                detail="analysis context missing",
                pair_id=pair_id,
            )
            self._debug_print(
                f"  Pair {pair_id} return-width bridge proof skipped: analysis context missing"
            )
            return None
        target = self._normalize_nested_tuple(object_target_key)
        if not isinstance(target, tuple):
            self._set_return_width_bridge_pending_evidence(
                object_target_key=None,
                subreason="object_target_unavailable",
                detail="return-width bridge object target missing",
                pair_id=pair_id,
            )
            self._debug_print(
                f"  Pair {pair_id} return-width bridge proof skipped: object target missing"
            )
            return None
        if not self._return_width_bridge_target_is_specific(target):
            self._set_return_width_bridge_pending_evidence(
                object_target_key=target,
                subreason="object_target_not_specific",
                detail="return-width bridge object target is weak",
                pair_id=pair_id,
            )
            self._debug_print(
                f"  Pair {pair_id} return-width bridge proof skipped: weak object target"
            )
            return None
        narrow_width = self._return_width_bridge_target_narrow_width(target)
        if narrow_width is None:
            self._set_return_width_bridge_pending_evidence(
                object_target_key=target,
                subreason="target_member_profile_unavailable",
                detail="narrow return width unavailable",
                pair_id=pair_id,
            )
            self._debug_print(
                f"  Pair {pair_id} return-width bridge proof skipped: narrow width unavailable"
            )
            return None

        reason_record = make_unknown_reason(
            UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING,
            stage="S_PAIRWISE",
            pair_or_case=pair_id,
            evidence_refs=("return-width-mismatch", blocking_detail),
            object_target_key=target,
            object_evidence=self._set_return_width_bridge_pending_evidence(
                object_target_key=target,
                subreason="proof_not_attempted",
                detail=blocking_detail,
                pair_id=pair_id,
                narrow_width=narrow_width,
            ),
            detail=blocking_detail,
        )
        self._last_return_width_bridge_pending_evidence = None
        narrow_query = build_return_width_bridge_narrow_query(
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            pair_id,
            target_bits=narrow_width,
        )
        proof_result = self._solve_query_internal(
            narrow_query,
            pair_id,
            stage="return-width-bridge-narrow-ineq",
            use_hard_timeout=True,
        )
        if proof_result.is_equivalent is not True:
            self._set_return_width_bridge_pending_evidence(
                object_target_key=target,
                subreason="narrow_query_not_unsat",
                detail="return-width bridge narrow query was not UNSAT",
                pair_id=pair_id,
                narrow_width=narrow_width,
                query_stage="return-width-bridge-narrow-ineq",
            )
            self._debug_print(
                "  Pair "
                f"{pair_id} return-width bridge proof skipped: narrow query was not UNSAT"
            )
            return None
        high_bit_query = build_return_width_bridge_high_bit_query(
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            pair_id,
            narrow_bits=narrow_width,
            return_size1=base_ctx.get("return_size1", narrow_width),
            return_size2=base_ctx.get("return_size2", narrow_width),
        )
        if high_bit_query is None:
            if not self._return_width_bridge_has_summary_parameter_extension_evidence(target):
                widths = self._return_width_bridge_target_widths(target)
                wide_param_replace_fn = (
                    param_replace_fn1
                    if widths is not None and widths[0] > widths[1]
                    else param_replace_fn2
                )
                if self._record_completed_return_width_bridge_semantic_narrowing_proofs(
                    reason_record,
                    analysis1,
                    analysis2,
                    narrow_width=narrow_width,
                    base_ctx=base_ctx,
                    wide_param_replace_fn=wide_param_replace_fn,
                ) and self._return_width_bridge_proof_is_complete(
                    reason_record,
                    analysis1,
                    analysis2,
                    base_ctx=base_ctx,
                    wide_param_replace_fn=wide_param_replace_fn,
                ):
                    proof_result.last_query = narrow_query
                    proof_result.pair_stage = "return-width-bridge-narrow-ineq"
                    self._debug_print(
                        "  Pair "
                        f"{pair_id}: return-width bridge completed by semantic return-width narrowing proof"
                    )
                    return proof_result
                if self._record_completed_return_width_bridge_member_narrow_producer_proofs(
                    reason_record,
                    analysis1,
                    analysis2,
                    narrow_width=narrow_width,
                ) and self._return_width_bridge_proof_is_complete(
                    reason_record,
                    analysis1,
                    analysis2,
                ):
                    proof_result.last_query = narrow_query
                    proof_result.pair_stage = "return-width-bridge-narrow-ineq"
                    self._debug_print(
                        "  Pair "
                        f"{pair_id}: return-width bridge completed by target member narrow producer proof"
                    )
                    return proof_result
                if getattr(self, "_last_return_width_bridge_pending_evidence", None) is None:
                    self._set_return_width_bridge_pending_evidence(
                        object_target_key=target,
                        subreason="high_bit_query_unavailable",
                        detail="high-bit query unavailable and no semantic/member producer proof completed",
                        pair_id=pair_id,
                        narrow_width=narrow_width,
                        query_stage="return-width-bridge-high-bit-extension",
                    )
                self._debug_print(
                    f"  Pair {pair_id} return-width bridge proof skipped: high-bit query unavailable"
                )
                return None
            if not self._record_completed_return_width_bridge_proofs(
                reason_record,
                analysis1,
                analysis2,
                query_stage="summary-parameter-extension-object-evidence",
                narrow_width=narrow_width,
                proof_source=(
                    "return_width_bridge_narrow_query_unsat_and_summary_parameter_extension"
                ),
            ):
                self._set_return_width_bridge_pending_evidence(
                    object_target_key=target,
                    subreason="summary_parameter_proof_not_recorded",
                    detail="summary parameter return-width bridge proof was not recorded",
                    pair_id=pair_id,
                    narrow_width=narrow_width,
                    query_stage="summary-parameter-extension-object-evidence",
                )
                self._debug_print(
                    "  Pair "
                    f"{pair_id} return-width bridge proof skipped: summary parameter proof not recorded"
                )
                return None
            if not self._return_width_bridge_proof_is_complete(
                reason_record,
                analysis1,
                analysis2,
            ):
                self._set_return_width_bridge_pending_evidence(
                    object_target_key=target,
                    subreason="summary_parameter_proof_not_accepted",
                    detail="summary parameter return-width bridge proof was not accepted",
                    pair_id=pair_id,
                    narrow_width=narrow_width,
                    query_stage="summary-parameter-extension-object-evidence",
                )
                self._debug_print(
                    "  Pair "
                    f"{pair_id} return-width bridge proof skipped: summary parameter proof not accepted"
                )
                return None
            proof_result.last_query = narrow_query
            proof_result.pair_stage = "return-width-bridge-narrow-ineq"
            self._debug_print(
                "  Pair "
                f"{pair_id}: return-width bridge completed by narrow-width and summary parameter extension proofs"
            )
            return proof_result
        high_bit_result = self._solve_query_internal(
            high_bit_query,
            pair_id,
            stage="return-width-bridge-high-bit-extension",
            use_hard_timeout=True,
        )
        if high_bit_result.is_equivalent is not True:
            widths = self._return_width_bridge_target_widths(target)
            wide_param_replace_fn = (
                param_replace_fn1
                if widths is not None and widths[0] > widths[1]
                else param_replace_fn2
            )
            if self._record_completed_return_width_bridge_semantic_narrowing_proofs(
                reason_record,
                analysis1,
                analysis2,
                narrow_width=narrow_width,
                base_ctx=base_ctx,
                wide_param_replace_fn=wide_param_replace_fn,
            ) and self._return_width_bridge_proof_is_complete(
                reason_record,
                analysis1,
                analysis2,
                base_ctx=base_ctx,
                wide_param_replace_fn=wide_param_replace_fn,
            ):
                proof_result.last_query = narrow_query
                proof_result.pair_stage = "return-width-bridge-narrow-ineq"
                self._debug_print(
                    "  Pair "
                    f"{pair_id}: return-width bridge completed by semantic return-width narrowing proof"
                )
                return proof_result
            if self._record_completed_return_width_bridge_member_narrow_producer_proofs(
                reason_record,
                analysis1,
                analysis2,
                narrow_width=narrow_width,
            ) and self._return_width_bridge_proof_is_complete(
                reason_record,
                analysis1,
                analysis2,
            ):
                proof_result.last_query = narrow_query
                proof_result.pair_stage = "return-width-bridge-narrow-ineq"
                self._debug_print(
                    "  Pair "
                    f"{pair_id}: return-width bridge completed by target member narrow producer proof"
                )
                return proof_result
            if getattr(self, "_last_return_width_bridge_pending_evidence", None) is None:
                self._set_return_width_bridge_pending_evidence(
                    object_target_key=target,
                    subreason="high_bit_query_not_unsat",
                    detail="return-width bridge high-bit query was not UNSAT",
                    pair_id=pair_id,
                    narrow_width=narrow_width,
                    query_stage="return-width-bridge-high-bit-extension",
                )
            self._debug_print(
                "  Pair "
                f"{pair_id} return-width bridge proof skipped: high-bit query was not UNSAT"
            )
            return None

        if not self._record_completed_return_width_bridge_proofs(
            reason_record,
            analysis1,
            analysis2,
            query_stage="return-width-bridge-high-bit-extension",
            narrow_width=narrow_width,
        ):
            self._set_return_width_bridge_pending_evidence(
                object_target_key=target,
                subreason="completed_proof_not_recorded",
                detail="return-width bridge completed proof was not recorded",
                pair_id=pair_id,
                narrow_width=narrow_width,
                query_stage="return-width-bridge-high-bit-extension",
            )
            self._debug_print(
                f"  Pair {pair_id} return-width bridge proof skipped: completed proof not recorded"
            )
            return None
        if not self._return_width_bridge_proof_is_complete(
            reason_record,
            analysis1,
            analysis2,
        ):
            self._set_return_width_bridge_pending_evidence(
                object_target_key=target,
                subreason="completed_proof_not_accepted",
                detail="return-width bridge completed proof was not accepted",
                pair_id=pair_id,
                narrow_width=narrow_width,
                query_stage="return-width-bridge-high-bit-extension",
            )
            self._debug_print(
                f"  Pair {pair_id} return-width bridge proof skipped: completed proof not accepted"
            )
            return None

        proof_result.last_query = narrow_query
        proof_result.pair_stage = "return-width-bridge-narrow-ineq"
        self._debug_print(
            f"  Pair {pair_id}: return-width bridge completed by narrow-width and high-bit proofs"
        )
        return proof_result

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
        contains_unresolved = self._get_expression_safety_checker(base_ctx).value_contains_unresolved(
            case,
            own_render_fn=own_render_fn,
            extra_conditions=extra_conditions,
            extra_render_fn=extra_render_fn,
            query_label=query_label,
        )
        if not contains_unresolved:
            return False
        if self._case_value_unresolved_is_pairwise_lowered(
            case,
            base_ctx=base_ctx,
            query_label=query_label,
        ):
            return False
        return True

    def _case_value_unresolved_is_pairwise_lowered(
        self,
        case: ReturnCase,
        *,
        base_ctx: Optional[Dict[str, Any]],
        query_label: str,
    ) -> bool:
        if base_ctx is None:
            return False
        pair_id, side = self._pair_id_and_side_from_value_query_label(query_label)
        if pair_id is None or side is None:
            return False
        lowered_by_pair = base_ctx.get("pairwise_unresolved_deferred_call_lowered_unknown_keys_by_pair") or {}
        lowered = lowered_by_pair.get(pair_id) or {}
        lowered_keys = set(lowered.get(side) or ())
        if not lowered_keys:
            return False
        value_expr = getattr(case, "value_expr", None)
        if self._expression_has_unsupported_smt_op_excluding_unknowns(value_expr):
            return False
        unknown_keys = tuple(
            self._expression_runtime_object_key(expr)
            for expr in self._collect_unknown_expression_nodes(value_expr)
        )
        if not unknown_keys:
            return False
        return all(key in lowered_keys for key in unknown_keys)

    @staticmethod
    def _pair_id_and_side_from_value_query_label(
        query_label: str,
    ) -> Tuple[Optional[str], Optional[str]]:
        if not isinstance(query_label, str) or ":" not in query_label:
            return None, None
        pair_id, suffix = query_label.rsplit(":", 1)
        if suffix == "value1":
            return pair_id, "left"
        if suffix == "value2":
            return pair_id, "right"
        return None, None

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
