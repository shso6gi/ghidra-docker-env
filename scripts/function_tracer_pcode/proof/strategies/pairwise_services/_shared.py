"""Shared dependencies for PairwiseStrategy services."""

from dataclasses import dataclass
from typing import Any, List, Optional, Tuple
from scripts.function_tracer_pcode.core import ReadonlyReductionTermRef
from scripts.function_tracer_pcode.core.runtime_refs import _loop_summary_term_at_index
from scripts.function_tracer_pcode.analysis.effects.summary import canonicalize_location
from scripts.function_tracer_pcode.analysis.condition.simplifier import ConditionSimplifier
from scripts.function_tracer_pcode.analysis.condition.normalizer import ConditionNormalizer
from scripts.function_tracer_pcode.analysis.condition.smt_oracle import ConditionSMTOracle
from scripts.function_tracer_pcode.proof.strategies.base import CheckStrategy, StrategyResult
from scripts.function_tracer_pcode.proof.strategies.pairwise_models import QueryResult, ReturnCase
from scripts.function_tracer_pcode.proof.strategies.pairwise_normalization import (
    try_normalization_equivalence,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_solver_proven_rewrite import (
    try_solver_proven_rewrite_equivalence,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import (
    build_canonical_return_observation_query,
    build_condition_only_query,
    build_single_case_condition_query,
    build_normalized_inequality_query,
    build_pair_query,
    extract_return_cases,
    save_unknown_query,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
    solve_query_internal,
    solve_query_twostage,
    validate_counterexample_across_cases,
)
from scripts.function_tracer_pcode.proof.strategies.expression_safety import ExpressionSafetyChecker
from scripts.function_tracer_pcode.proof.formula.input_correspondence import extension_premise_lines
from scripts.function_tracer_pcode.proof.formula.input_correspondence.binding import (
    comparison_evidence,
    merge_new_evidence,
    store_comparison_evidence,
)
from scripts.function_tracer_pcode.proof.formula.symbol_replace import build_symbol_replacer
from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo
from scripts.function_tracer_pcode.semantics.normalize import (
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
from scripts.function_tracer_pcode.semantics.param_semantics import (
    infer_parameter_semantics,
    parameter_identity_key_from_descriptor,
    parameter_identity_key_from_expression,
)
from scripts.function_tracer_pcode.semantics.semantic_width import (
    align_return_value_extension_surfaces,
    normalize_analysis_semantic_width,
)
from scripts.function_tracer_pcode.checker.debug_trace import NormalizationRuleApplication
from scripts.function_tracer_pcode.checker.unknown_reason import (
    build_unknown_recovery_actions,
    make_internal_v2_reason_diagnostic,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.proof.unknown_reason import (
    UnknownReasonId,
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    UnknownRecoveryProofObligation,
)

@dataclass(frozen=True)
class _RuntimeShortcutDecision:
    equivalent: bool
    requires_guard_equivalence: bool
    reason: str = 'unknown'

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
        return self._int_constant(getattr(self.loop_summary, 'start_expr', None), default=0)

    @property
    def index_step(self) -> int:
        return max(1, self._int_constant(getattr(self.loop_summary, 'step_expr', None), default=1))

    @property
    def seed_terms(self) -> Tuple[ReadonlyReductionTermRef, ...]:
        return tuple(getattr(self.loop_summary, 'seed_terms', ()) or ())

    @property
    def seed_term_count(self) -> Optional[int]:
        value = getattr(self.loop_summary, 'seed_term_count', None)
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
        if getattr(getattr(value, 'expr_type', None), 'name', None) == 'CONSTANT':
            try:
                return int(getattr(value, 'value'))
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
        if any((not isinstance(term, ReadonlyReductionTermRef) for term in terms)):
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

__all__ = ('CheckStrategy', 'ConditionNormalizer', 'ConditionSMTOracle', 'ConditionSimplifier', 'ExpressionSafetyChecker', 'NormalizationContext', 'NormalizationRuleApplication', 'NormalizationSettings', 'ParameterInfo', 'QueryResult', 'ReturnCase', 'SignFacts', 'StrategyResult', 'UnknownReasonId', 'UnknownRecoveryActionStatus', 'UnknownRecoveryProofKind', 'UnknownRecoveryProofObligation', '_ExactReadonlyReductionProof', '_MethodBCoveringCaseProof', '_PendingLoopSummaryPair', '_ReadonlyLoopSummaryProofAdapter', '_RuntimeShortcutDecision', '_UnresolvedDeferredCallLowering', 'align_return_value_extension_surfaces', 'are_structurally_equivalent', 'build_canonical_return_observation_query', 'build_condition_only_query', 'build_normalized_inequality_query', 'build_pair_query', 'build_single_case_condition_query', 'build_symbol_replacer', 'build_unknown_recovery_actions', 'canonicalize_location', 'comparison_evidence', 'contains_udiv', 'extension_premise_lines', 'extract_min_excluded_params', 'extract_return_cases', 'extract_sign_facts', 'extract_upper_bound_facts', 'get_structural_summary', 'infer_parameter_semantics', 'make_internal_v2_reason_diagnostic', 'make_unknown_reason', 'merge_new_evidence', 'normalize_analysis_semantic_width', 'normalize_expression', 'normalize_udiv_with_guard', 'parameter_identity_key_from_descriptor', 'parameter_identity_key_from_expression', 'save_unknown_query', 'store_comparison_evidence', 'solve_query_internal', 'solve_query_twostage', 'try_normalization_equivalence', 'try_solver_proven_rewrite_equivalence', 'validate_counterexample_across_cases')
