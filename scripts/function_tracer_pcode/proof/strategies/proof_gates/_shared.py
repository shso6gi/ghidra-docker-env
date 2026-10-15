"""Shared dependencies for CheckStrategy services."""

from typing import Optional, Dict, Any, List, Set, Tuple
from dataclasses import dataclass, field
from scripts.function_tracer_pcode.analysis.condition.smt_oracle import ConditionSMTOracle
from scripts.function_tracer_pcode.core import ReadonlyReductionRef
from scripts.function_tracer_pcode.smt import ParallelResult
from scripts.function_tracer_pcode.proof.formula.returns import coerce_value_to_bitvec_width
from scripts.function_tracer_pcode.checker.unknown_reason import (
    UnknownReasonRecord,
    build_unknown_recovery_actions,
    coerce_unknown_reason_records,
    make_internal_v2_reason_diagnostic,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.proof.formula.input_correspondence.gate import (
    CrossSideIdentification,
    certify_owner_free_identity,
    owner_free_identity_gate,
)
from scripts.function_tracer_pcode.proof.formula.input_correspondence.binding import (
    comparison_evidence,
    current_relation,
    relation_digest_is_current,
    store_comparison_evidence,
)
from scripts.function_tracer_pcode.proof.unknown_reason import (
    UnknownReasonId,
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    UnknownRecoveryProofObligation,
    build_proof_obligation_id,
)

@dataclass
class StrategyResult:
    """戦略実行結果"""
    is_equivalent: Optional[bool]
    solver_results: ParallelResult
    smt_formula: Optional[str] = None
    counterexample_raw: Optional[Dict] = None
    return_var1: Optional[str] = None
    return_var2: Optional[str] = None
    constrained_fragments: List[str] = field(default_factory=list)
    total_pairs: int = 0
    unsat_pairs: int = 0
    sat_pairs: int = 0
    unknown_pairs: int = 0
    error_pairs: int = 0
    sat_pair_info: Optional[Dict[str, Any]] = None
    normalization_rules: List[Any] = field(default_factory=list)
    pairwise_debug_stats: Optional[Dict[str, int]] = None
    unknown_reasons: List[UnknownReasonRecord] = field(default_factory=list)
    error_kind: Optional[str] = None
    error_message: Optional[str] = None

    def __post_init__(self) -> None:
        self.unknown_reasons = list(coerce_unknown_reason_records(self.unknown_reasons))

@dataclass(frozen=True)
class ReturnCoverageCheckResult:
    status: str
    reason_id: Optional[UnknownReasonId] = None
    detail: Optional[str] = None
    can_record_completion_proof: bool = False
    inconclusive_cause: Optional[str] = None
    coverage_proof_method: Optional[str] = None
    solver_status: Optional[str] = None

__all__ = ('Any', 'ConditionSMTOracle', 'CrossSideIdentification', 'Dict', 'List', 'Optional', 'ParallelResult', 'ReadonlyReductionRef', 'ReturnCoverageCheckResult', 'Set', 'StrategyResult', 'Tuple', 'UnknownReasonId', 'UnknownReasonRecord', 'UnknownRecoveryActionStatus', 'UnknownRecoveryProofKind', 'UnknownRecoveryProofObligation', 'build_proof_obligation_id', 'build_unknown_recovery_actions', 'certify_owner_free_identity', 'coerce_unknown_reason_records', 'coerce_value_to_bitvec_width', 'comparison_evidence', 'current_relation', 'dataclass', 'field', 'make_internal_v2_reason_diagnostic', 'make_unknown_reason', 'owner_free_identity_gate', 'relation_digest_is_current', 'store_comparison_evidence')
