"""Shared dependencies for CheckStrategy services."""

from abc import ABC, abstractmethod
import hashlib
import json
import re
from types import SimpleNamespace
from typing import Optional, Dict, Any, List, Mapping, Sequence, Set, Tuple
from dataclasses import dataclass, field
from ....analysis.condition.smt_oracle import ConditionSMTOracle
from ....model import Condition, Expression, FunctionReturnAnalysis, ReadonlyReductionRef, expression_provenance_key
from ....model import ExpressionType
from ....model.render_smt import expression_contains_unsupported_smt_ops, expression_smt_bit_width
from ....smt import ParallelResult
from ...formula.returns import coerce_value_to_bitvec_width
from ...unknown_reason import UnknownRecoveryActionStatus, UnknownRecoveryProofKind, UnknownRecoveryProofObligation, UnknownReasonId, UnknownReasonRecord, build_proof_obligation_id, build_unknown_recovery_actions, coerce_unknown_reason_records, make_unknown_reason

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

__all__ = ('ABC', 'Any', 'Condition', 'ConditionSMTOracle', 'Dict', 'Expression', 'ExpressionType', 'FunctionReturnAnalysis', 'List', 'Mapping', 'Optional', 'ParallelResult', 'ReadonlyReductionRef', 'ReturnCoverageCheckResult', 'Sequence', 'Set', 'SimpleNamespace', 'StrategyResult', 'Tuple', 'UnknownReasonId', 'UnknownReasonRecord', 'UnknownRecoveryActionStatus', 'UnknownRecoveryProofKind', 'UnknownRecoveryProofObligation', 'abstractmethod', 'build_proof_obligation_id', 'build_unknown_recovery_actions', 'coerce_unknown_reason_records', 'coerce_value_to_bitvec_width', 'dataclass', 'expression_contains_unsupported_smt_ops', 'expression_provenance_key', 'expression_smt_bit_width', 'field', 'hashlib', 'json', 'make_unknown_reason', 're')
