# -*- coding: utf-8 -*-
"""Typed UNKNOWN reason schema and registry."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence, Tuple


UNKNOWN_TUPLE_MISSING = "<missing>"


class UnknownCountKind(str, Enum):
    FINAL_RESULT = "final_result"
    VALIDATION_UNKNOWN_UNIT = "validation_unknown_unit"
    REASON_RECORD = "reason_record"
    PROOF_ACTION = "proof_action"


class UnknownReasonId(str, Enum):
    RETURN_WIDTH_BRIDGE_MISSING = "return_width_bridge_missing"
    RECOVERABLE_PARTIAL = "recoverable_partial"
    READONLY_IDENTITY_MISSING = "readonly_identity_missing"
    METHOD_B_CLOSURE_BLOCKED = "method_b_closure_blocked"
    LOOP_SUMMARY_PROOF_MISSING = "loop_summary_proof_missing"
    RETURN_COVERAGE_GAP = "return_coverage_gap"
    RETURN_COVERAGE_INCONCLUSIVE = "return_coverage_inconclusive"
    OUTCOME_PARTITION_UNKNOWN = "outcome_partition_unknown"
    SUMMARY_RETURN_CANDIDATE_INVALID = "summary_return_candidate_invalid"
    SUMMARY_RETURN_OVERLAP_UNPROVEN = "summary_return_overlap_unproven"
    SUMMARY_EFFECT_UNMODELED = "summary_effect_unmodeled"
    SUMMARY_PRECONDITION_INCOMPLETE = "summary_precondition_incomplete"
    SUMMARY_PARTITION_NOT_TOTAL = "summary_partition_not_total"
    PHI_CIRCULAR_REPLACEMENT_UNPROVEN = "phi_circular_replacement_unproven"
    EQUIVALENCE_BLOCKING_UNSAFETY = "equivalence_blocking_unsafety"
    SAT_UNSAFETY = "sat_unsafety"
    SAT_COUNTEREXAMPLE_AMBIGUOUS = "sat_counterexample_ambiguous"
    UNRESOLVED_EXPRESSION = "unresolved_expression"
    UNRESOLVED_VALUE_EXPRESSION = "unresolved_value_expression"
    NORMALIZATION_NO_CHANGE = "normalization_no_change"
    SOLVER_PROVEN_REWRITE_NO_CHANGE = "solver_proven_rewrite_no_change"
    SOLVER_PROVEN_REWRITE_PROOF_FAILED = "solver_proven_rewrite_proof_failed"
    SOLVER_UNKNOWN_TIMEOUT = "solver_unknown_timeout"
    DECOMPILATION_FAILED = "decompilation_failed"
    HIGH_FUNCTION_MISSING = "high_function_missing"
    EMPTY_RETURN_CASES = "empty_return_cases"
    UNEXPECTED_PAIRWISE_STATE = "unexpected_pairwise_state"
    STRATEGY_EXCEPTION = "strategy_exception"
    UNKNOWN = "unknown"


class UnknownReasonClass(str, Enum):
    PROOF_OBLIGATION = "proof_obligation"
    COVERAGE_GAP = "coverage_gap"
    UNSAFE_ANALYSIS = "unsafe_analysis"
    OPERATIONAL_GAP = "operational_gap"
    SOLVER_LIMITATION = "solver_limitation"
    INTERNAL_ERROR = "internal_error"
    DIAGNOSTIC = "diagnostic"


class UnknownDecisionEffect(str, Enum):
    BLOCKS_EQUIVALENCE = "blocks_equivalence"
    BLOCKS_DISEQUIVALENCE = "blocks_disequivalence"
    BLOCKS_DECISION = "blocks_decision"
    RETRYABLE = "retryable"
    DIAGNOSTIC_ONLY = "diagnostic_only"


class UnknownReasonScope(str, Enum):
    PAIR = "pair"
    CASE = "case"
    FUNCTION = "function"
    STAGE = "stage"
    QUERY = "query"
    EXPRESSION = "expression"
    GLOBAL = "global"


class UnknownAggregationUnit(str, Enum):
    PAIR = "pair"
    CASE = "case"
    FUNCTION = "function"
    STAGE = "stage"
    QUERY = "query"
    RESULT = "result"


class UnknownRecoveryProofKind(str, Enum):
    NONE = "none"
    ABI_RELATION_HIGH_BIT_PROOF = "abi_relation_high_bit_proof"
    ABI_RELATION_PROOF = "abi_relation_proof"
    HIGH_BIT_PROOF = "high_bit_proof"
    CALL_EFFECT_SUMMARY_PROOF = "call_effect_summary_proof"
    PATH_SENSITIVE_ARGUMENT_MERGE = "path_sensitive_argument_merge"
    STORAGE_BACKED_IDENTITY_PROPAGATION = "storage_backed_identity_propagation"
    PROOF_BACKED_COVERING_CASE = "proof_backed_covering_case"
    GUARD_PARTITION_COMPLETION = "guard_partition_completion"
    LOOP_SUMMARY_COMPLETION = "loop_summary_completion"
    RETURN_PARTITION_OVERLAP_PROOF = "return_partition_overlap_proof"
    EFFECT_SUMMARY_COMPLETION = "effect_summary_completion"
    PRECONDITION_COMPLETION = "precondition_completion"
    LOOP_RECURRENCE_PROOF = "loop_recurrence_proof"
    SAT_UNSAFETY_RESOLUTION = "sat_unsafety_resolution"
    SOLVER_RETRY_OR_NORMALIZATION = "solver_retry_or_normalization"
    RETURN_COVERAGE_COMPLETION = "return_coverage_completion"


def _enum_value(value: Any) -> Optional[str]:
    if value is None:
        return None
    if isinstance(value, Enum):
        return str(value.value)
    return str(value)


def _coerce_evidence_refs(evidence_refs: Optional[Sequence[Any]]) -> Tuple[str, ...]:
    refs = []
    for ref in evidence_refs or ():
        if ref is None:
            continue
        refs.append(str(ref))
    return tuple(refs)


def _coerce_optional_tuple(value: Any) -> Optional[Tuple[Any, ...]]:
    if value is None:
        return None
    if isinstance(value, tuple):
        return tuple(_coerce_optional_tuple(item) if isinstance(item, list) else item for item in value)
    if isinstance(value, list):
        return tuple(_coerce_optional_tuple(item) if isinstance(item, list) else item for item in value)
    return (value,)


def _registered_recovery_proof_kind_values() -> Tuple[str, ...]:
    return tuple(kind.value for kind in UnknownRecoveryProofKind)


def normalize_recovery_proof_kind(value: Any) -> Optional[str]:
    raw = _enum_value(value)
    if raw is None:
        return None
    if raw in _registered_recovery_proof_kind_values():
        return raw
    return UnknownRecoveryProofKind.NONE.value


@dataclass(frozen=True)
class UnknownRecoveryProofObligation:
    proof_kind: str
    proof_stage: str
    required_evidence: Tuple[str, ...] = ()
    description: Optional[str] = None

    @classmethod
    def create(
        cls,
        proof_kind: Any,
        proof_stage: str,
        *,
        required_evidence: Optional[Sequence[Any]] = None,
        description: Optional[str] = None,
    ) -> "UnknownRecoveryProofObligation":
        return cls(
            proof_kind=normalize_recovery_proof_kind(proof_kind) or UnknownRecoveryProofKind.NONE.value,
            proof_stage=str(proof_stage),
            required_evidence=_coerce_evidence_refs(required_evidence),
            description=description,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "proof_kind": self.proof_kind,
            "proof_stage": self.proof_stage,
            "required_evidence": list(self.required_evidence),
            "description": self.description,
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "UnknownRecoveryProofObligation":
        return cls.create(
            payload.get("proof_kind"),
            str(payload.get("proof_stage") or "unspecified"),
            required_evidence=payload.get("required_evidence") or (),
            description=payload.get("description"),
        )


@dataclass(frozen=True)
class UnknownRecoveryPlan:
    reason_id: str
    proof_obligations: Tuple[UnknownRecoveryProofObligation, ...] = ()
    target_regression: Optional[str] = None
    description: Optional[str] = None

    @classmethod
    def create(
        cls,
        reason_id: Any,
        proof_obligations: Sequence[Any],
        *,
        target_regression: Optional[str] = None,
        description: Optional[str] = None,
    ) -> "UnknownRecoveryPlan":
        return cls(
            reason_id=normalize_unknown_reason_id(reason_id),
            proof_obligations=coerce_unknown_recovery_proof_obligations(proof_obligations),
            target_regression=target_regression,
            description=description,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "reason_id": self.reason_id,
            "proof_obligations": [obligation.to_dict() for obligation in self.proof_obligations],
            "target_regression": self.target_regression,
            "description": self.description,
        }


class UnknownRecoveryActionStatus(str, Enum):
    PLANNED = "planned"
    PENDING_PROOF = "pending_proof"
    PROOF_COMPLETE = "proof_complete"
    NO_REGISTERED_PLAN = "no_registered_plan"


@dataclass(frozen=True)
class UnknownRecoveryAction:
    count_kind: str
    reason_id: str
    decision_effect: str
    reason_scope: str
    proof_kind: str
    proof_stage: str
    status: str
    aggregation_unit: str
    stage: Optional[str] = None
    pair_or_case: Optional[str] = None
    required_evidence: Tuple[str, ...] = ()
    evidence_refs: Tuple[str, ...] = ()
    evidence_kind: Optional[str] = None
    object_target_key: Optional[Tuple[Any, ...]] = None
    object_evidence: Optional[Any] = None
    proof_obligation_id: Optional[Tuple[Any, ...]] = None
    recovery_action: Optional[str] = None
    target_regression: Optional[str] = None
    detail: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        payload = {
            "count_kind": self.count_kind,
            "reason_id": self.reason_id,
            "decision_effect": self.decision_effect,
            "reason_scope": self.reason_scope,
            "proof_kind": self.proof_kind,
            "proof_stage": self.proof_stage,
            "status": self.status,
            "aggregation_unit": self.aggregation_unit,
            "stage": self.stage,
            "pair_or_case": self.pair_or_case,
            "required_evidence": list(self.required_evidence),
            "evidence_refs": list(self.evidence_refs),
            "evidence_kind": self.evidence_kind,
            "object_target_key": self.object_target_key,
            "proof_obligation_id": self.proof_obligation_id,
            "recovery_action": self.recovery_action,
            "target_regression": self.target_regression,
            "detail": self.detail,
        }
        if self.object_evidence is not None:
            payload["object_evidence"] = self.object_evidence
        return payload

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "UnknownRecoveryAction":
        reason_id = normalize_unknown_reason_id(payload.get("reason_id"))
        definition = get_unknown_reason_definition(reason_id)
        use_definition_defaults = reason_id != UnknownReasonId.UNKNOWN.value
        return cls(
            count_kind=_enum_value(payload.get("count_kind")) or UnknownCountKind.PROOF_ACTION.value,
            reason_id=reason_id,
            decision_effect=str(
                payload.get("decision_effect")
                or (
                    definition.decision_effect
                    if use_definition_defaults
                    else UnknownDecisionEffect.DIAGNOSTIC_ONLY.value
                )
            ),
            reason_scope=str(
                payload.get("reason_scope")
                or (
                    definition.reason_scope
                    if use_definition_defaults
                    else UnknownReasonScope.GLOBAL.value
                )
            ),
            proof_kind=normalize_recovery_proof_kind(payload.get("proof_kind")) or UnknownRecoveryProofKind.NONE.value,
            proof_stage=str(payload.get("proof_stage") or "unspecified"),
            status=str(payload.get("status") or UnknownRecoveryActionStatus.PLANNED.value),
            aggregation_unit=str(
                payload.get("aggregation_unit")
                or (
                    definition.aggregation_unit
                    if use_definition_defaults
                    else UnknownAggregationUnit.RESULT.value
                )
            ),
            stage=payload.get("stage"),
            pair_or_case=payload.get("pair_or_case"),
            required_evidence=_coerce_evidence_refs(payload.get("required_evidence") or ()),
            evidence_refs=_coerce_evidence_refs(payload.get("evidence_refs") or ()),
            evidence_kind=payload.get("evidence_kind"),
            object_target_key=_coerce_optional_tuple(payload.get("object_target_key")),
            object_evidence=payload.get("object_evidence"),
            proof_obligation_id=_coerce_optional_tuple(payload.get("proof_obligation_id")),
            recovery_action=payload.get("recovery_action"),
            target_regression=(
                payload.get("target_regression")
                if payload.get("target_regression") is not None
                else definition.target_regression if use_definition_defaults else None
            ),
            detail=payload.get("detail"),
        )


@dataclass(frozen=True)
class UnknownReasonDefinition:
    reason_id: str
    reason_class: str
    decision_effect: str
    reason_scope: str
    aggregation_unit: str
    recovery_proof_kind: str = UnknownRecoveryProofKind.NONE.value
    target_regression: Optional[str] = None

    @classmethod
    def create(
        cls,
        reason_id: Any,
        reason_class: Any,
        decision_effect: Any,
        reason_scope: Any,
        aggregation_unit: Any,
        *,
        recovery_proof_kind: Any = UnknownRecoveryProofKind.NONE,
        target_regression: Optional[str] = None,
    ) -> "UnknownReasonDefinition":
        return cls(
            reason_id=_enum_value(reason_id) or UnknownReasonId.UNKNOWN.value,
            reason_class=_enum_value(reason_class) or UnknownReasonClass.DIAGNOSTIC.value,
            decision_effect=_enum_value(decision_effect) or UnknownDecisionEffect.DIAGNOSTIC_ONLY.value,
            reason_scope=_enum_value(reason_scope) or UnknownReasonScope.GLOBAL.value,
            aggregation_unit=_enum_value(aggregation_unit) or UnknownAggregationUnit.RESULT.value,
            recovery_proof_kind=_enum_value(recovery_proof_kind) or UnknownRecoveryProofKind.NONE.value,
            target_regression=target_regression,
        )


_UNKNOWN_REASON_REGISTRY: Dict[str, UnknownReasonDefinition] = {}
_UNKNOWN_RECOVERY_PLAN_REGISTRY: Dict[str, UnknownRecoveryPlan] = {}


def register_unknown_reason(definition: UnknownReasonDefinition) -> UnknownReasonDefinition:
    _UNKNOWN_REASON_REGISTRY[definition.reason_id] = definition
    return definition


def register_unknown_recovery_plan(plan: UnknownRecoveryPlan) -> UnknownRecoveryPlan:
    _UNKNOWN_RECOVERY_PLAN_REGISTRY[plan.reason_id] = plan
    return plan


def _register_defaults() -> None:
    for definition in (
        UnknownReasonDefinition.create(
            UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING,
            UnknownReasonClass.PROOF_OBLIGATION,
            UnknownDecisionEffect.BLOCKS_EQUIVALENCE,
            UnknownReasonScope.QUERY,
            UnknownAggregationUnit.PAIR,
            recovery_proof_kind=UnknownRecoveryProofKind.ABI_RELATION_HIGH_BIT_PROOF,
            target_regression="return_width_bridge_missing",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.RECOVERABLE_PARTIAL,
            UnknownReasonClass.OPERATIONAL_GAP,
            UnknownDecisionEffect.RETRYABLE,
            UnknownReasonScope.FUNCTION,
            UnknownAggregationUnit.FUNCTION,
            recovery_proof_kind=UnknownRecoveryProofKind.PATH_SENSITIVE_ARGUMENT_MERGE,
            target_regression="recoverable_partial",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.READONLY_IDENTITY_MISSING,
            UnknownReasonClass.PROOF_OBLIGATION,
            UnknownDecisionEffect.BLOCKS_EQUIVALENCE,
            UnknownReasonScope.EXPRESSION,
            UnknownAggregationUnit.PAIR,
            recovery_proof_kind=UnknownRecoveryProofKind.STORAGE_BACKED_IDENTITY_PROPAGATION,
            target_regression="readonly_identity_missing",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.METHOD_B_CLOSURE_BLOCKED,
            UnknownReasonClass.PROOF_OBLIGATION,
            UnknownDecisionEffect.BLOCKS_EQUIVALENCE,
            UnknownReasonScope.STAGE,
            UnknownAggregationUnit.PAIR,
            recovery_proof_kind=UnknownRecoveryProofKind.PROOF_BACKED_COVERING_CASE,
            target_regression="method_b_closure_blocked",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.LOOP_SUMMARY_PROOF_MISSING,
            UnknownReasonClass.PROOF_OBLIGATION,
            UnknownDecisionEffect.BLOCKS_EQUIVALENCE,
            UnknownReasonScope.PAIR,
            UnknownAggregationUnit.PAIR,
            recovery_proof_kind=UnknownRecoveryProofKind.GUARD_PARTITION_COMPLETION,
            target_regression="loop_summary_proof_missing",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.RETURN_COVERAGE_GAP,
            UnknownReasonClass.COVERAGE_GAP,
            UnknownDecisionEffect.BLOCKS_EQUIVALENCE,
            UnknownReasonScope.FUNCTION,
            UnknownAggregationUnit.FUNCTION,
            recovery_proof_kind=UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION,
            target_regression="return_coverage_gap",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
            UnknownReasonClass.COVERAGE_GAP,
            UnknownDecisionEffect.BLOCKS_DECISION,
            UnknownReasonScope.FUNCTION,
            UnknownAggregationUnit.FUNCTION,
            recovery_proof_kind=UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION,
            target_regression="return_coverage_inconclusive",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.OUTCOME_PARTITION_UNKNOWN,
            UnknownReasonClass.PROOF_OBLIGATION,
            UnknownDecisionEffect.BLOCKS_EQUIVALENCE,
            UnknownReasonScope.FUNCTION,
            UnknownAggregationUnit.FUNCTION,
            recovery_proof_kind=UnknownRecoveryProofKind.GUARD_PARTITION_COMPLETION,
            target_regression="outcome_partition_unknown",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.SUMMARY_RETURN_CANDIDATE_INVALID,
            UnknownReasonClass.PROOF_OBLIGATION,
            UnknownDecisionEffect.BLOCKS_EQUIVALENCE,
            UnknownReasonScope.FUNCTION,
            UnknownAggregationUnit.FUNCTION,
            recovery_proof_kind=UnknownRecoveryProofKind.LOOP_SUMMARY_COMPLETION,
            target_regression="summary_return_candidate_invalid",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.SUMMARY_RETURN_OVERLAP_UNPROVEN,
            UnknownReasonClass.PROOF_OBLIGATION,
            UnknownDecisionEffect.BLOCKS_EQUIVALENCE,
            UnknownReasonScope.FUNCTION,
            UnknownAggregationUnit.FUNCTION,
            recovery_proof_kind=UnknownRecoveryProofKind.RETURN_PARTITION_OVERLAP_PROOF,
            target_regression="summary_return_overlap_unproven",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.SUMMARY_EFFECT_UNMODELED,
            UnknownReasonClass.PROOF_OBLIGATION,
            UnknownDecisionEffect.BLOCKS_EQUIVALENCE,
            UnknownReasonScope.FUNCTION,
            UnknownAggregationUnit.FUNCTION,
            recovery_proof_kind=UnknownRecoveryProofKind.EFFECT_SUMMARY_COMPLETION,
            target_regression="summary_effect_unmodeled",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.SUMMARY_PRECONDITION_INCOMPLETE,
            UnknownReasonClass.PROOF_OBLIGATION,
            UnknownDecisionEffect.BLOCKS_EQUIVALENCE,
            UnknownReasonScope.FUNCTION,
            UnknownAggregationUnit.FUNCTION,
            recovery_proof_kind=UnknownRecoveryProofKind.PRECONDITION_COMPLETION,
            target_regression="summary_precondition_incomplete",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.SUMMARY_PARTITION_NOT_TOTAL,
            UnknownReasonClass.COVERAGE_GAP,
            UnknownDecisionEffect.BLOCKS_EQUIVALENCE,
            UnknownReasonScope.FUNCTION,
            UnknownAggregationUnit.FUNCTION,
            recovery_proof_kind=UnknownRecoveryProofKind.PRECONDITION_COMPLETION,
            target_regression="summary_partition_not_total",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.PHI_CIRCULAR_REPLACEMENT_UNPROVEN,
            UnknownReasonClass.PROOF_OBLIGATION,
            UnknownDecisionEffect.BLOCKS_EQUIVALENCE,
            UnknownReasonScope.FUNCTION,
            UnknownAggregationUnit.FUNCTION,
            recovery_proof_kind=UnknownRecoveryProofKind.LOOP_RECURRENCE_PROOF,
            target_regression="phi_circular_replacement_unproven",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY,
            UnknownReasonClass.UNSAFE_ANALYSIS,
            UnknownDecisionEffect.BLOCKS_EQUIVALENCE,
            UnknownReasonScope.FUNCTION,
            UnknownAggregationUnit.FUNCTION,
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.SAT_UNSAFETY,
            UnknownReasonClass.UNSAFE_ANALYSIS,
            UnknownDecisionEffect.BLOCKS_DISEQUIVALENCE,
            UnknownReasonScope.PAIR,
            UnknownAggregationUnit.PAIR,
            recovery_proof_kind=UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION,
            target_regression="sat_unsafety",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS,
            UnknownReasonClass.UNSAFE_ANALYSIS,
            UnknownDecisionEffect.BLOCKS_DISEQUIVALENCE,
            UnknownReasonScope.PAIR,
            UnknownAggregationUnit.PAIR,
            recovery_proof_kind=UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION,
            target_regression="sat_counterexample_ambiguous",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.UNRESOLVED_EXPRESSION,
            UnknownReasonClass.OPERATIONAL_GAP,
            UnknownDecisionEffect.BLOCKS_DECISION,
            UnknownReasonScope.EXPRESSION,
            UnknownAggregationUnit.PAIR,
            target_regression="unresolved_expression",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.UNRESOLVED_VALUE_EXPRESSION,
            UnknownReasonClass.OPERATIONAL_GAP,
            UnknownDecisionEffect.BLOCKS_DECISION,
            UnknownReasonScope.EXPRESSION,
            UnknownAggregationUnit.PAIR,
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT,
            UnknownReasonClass.SOLVER_LIMITATION,
            UnknownDecisionEffect.RETRYABLE,
            UnknownReasonScope.QUERY,
            UnknownAggregationUnit.PAIR,
            recovery_proof_kind=UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
            target_regression="solver_unknown_timeout",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.DECOMPILATION_FAILED,
            UnknownReasonClass.OPERATIONAL_GAP,
            UnknownDecisionEffect.BLOCKS_DECISION,
            UnknownReasonScope.FUNCTION,
            UnknownAggregationUnit.FUNCTION,
            target_regression="decompilation_failed",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.HIGH_FUNCTION_MISSING,
            UnknownReasonClass.OPERATIONAL_GAP,
            UnknownDecisionEffect.BLOCKS_DECISION,
            UnknownReasonScope.FUNCTION,
            UnknownAggregationUnit.FUNCTION,
            target_regression="high_function_missing",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.NORMALIZATION_NO_CHANGE,
            UnknownReasonClass.OPERATIONAL_GAP,
            UnknownDecisionEffect.RETRYABLE,
            UnknownReasonScope.PAIR,
            UnknownAggregationUnit.PAIR,
            recovery_proof_kind=UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
            target_regression="normalization_no_change",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.SOLVER_PROVEN_REWRITE_NO_CHANGE,
            UnknownReasonClass.PROOF_OBLIGATION,
            UnknownDecisionEffect.RETRYABLE,
            UnknownReasonScope.PAIR,
            UnknownAggregationUnit.PAIR,
            recovery_proof_kind=UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
            target_regression="solver_proven_rewrite_no_change",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.SOLVER_PROVEN_REWRITE_PROOF_FAILED,
            UnknownReasonClass.PROOF_OBLIGATION,
            UnknownDecisionEffect.RETRYABLE,
            UnknownReasonScope.PAIR,
            UnknownAggregationUnit.PAIR,
            recovery_proof_kind=UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
            target_regression="solver_proven_rewrite_proof_failed",
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.EMPTY_RETURN_CASES,
            UnknownReasonClass.COVERAGE_GAP,
            UnknownDecisionEffect.BLOCKS_DECISION,
            UnknownReasonScope.FUNCTION,
            UnknownAggregationUnit.RESULT,
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.UNEXPECTED_PAIRWISE_STATE,
            UnknownReasonClass.INTERNAL_ERROR,
            UnknownDecisionEffect.BLOCKS_DECISION,
            UnknownReasonScope.STAGE,
            UnknownAggregationUnit.RESULT,
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.STRATEGY_EXCEPTION,
            UnknownReasonClass.INTERNAL_ERROR,
            UnknownDecisionEffect.BLOCKS_DECISION,
            UnknownReasonScope.STAGE,
            UnknownAggregationUnit.RESULT,
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.UNKNOWN,
            UnknownReasonClass.DIAGNOSTIC,
            UnknownDecisionEffect.BLOCKS_DECISION,
            UnknownReasonScope.GLOBAL,
            UnknownAggregationUnit.RESULT,
        ),
    ):
        register_unknown_reason(definition)


_register_defaults()


def _register_default_recovery_plans() -> None:
    for plan in (
        UnknownRecoveryPlan.create(
            UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.ABI_RELATION_PROOF,
                    "abi_relation",
                    required_evidence=(
                        "calling_convention",
                        "return_storage",
                        "narrow_return_width",
                    ),
                    description="Prove the compared return storages are related by the active ABI.",
                ),
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.HIGH_BIT_PROOF,
                    "high_bit_relation",
                    required_evidence=(
                        "producer_width",
                        "extension_semantics",
                        "high_bits_irrelevant_or_equal",
                    ),
                    description="Prove the wider return high bits cannot change the semantic result.",
                ),
            ),
            target_regression="return_width_bridge_missing",
            description="Recover width-mismatched returns only with ABI relation plus high-bit proof.",
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.RECOVERABLE_PARTIAL,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.PATH_SENSITIVE_ARGUMENT_MERGE,
                    "call_argument_recovery",
                    required_evidence=(
                        "callsite_guard_partition",
                        "argument_value_by_path",
                        "callee_parameter_storage",
                    ),
                    description="Merge partial call-argument evidence under path-sensitive guards.",
                ),
            ),
            target_regression="recoverable_partial",
            description="Recover partial call argument evidence by completing a path-sensitive merge.",
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.READONLY_IDENTITY_MISSING,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.STORAGE_BACKED_IDENTITY_PROPAGATION,
                    "readonly_operand_identity",
                    required_evidence=(
                        "object_storage_identity",
                        "count_identity",
                        "guard_implication",
                        "finite_witness",
                    ),
                    description="Propagate readonly identity from storage-backed object/count evidence.",
                ),
            ),
            target_regression="readonly_identity_missing",
            description="Recover readonly equality only from object-centric storage/count identity.",
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.METHOD_B_CLOSURE_BLOCKED,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.PROOF_BACKED_COVERING_CASE,
                    "method_b_covering_case",
                    required_evidence=(
                        "seed_compensation",
                        "term_sequence",
                        "pure_side_effect_profile",
                    ),
                    description="Prove a Method-B covering case from seed compensation and terms.",
                ),
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.GUARD_PARTITION_COMPLETION,
                    "method_b_guard_partition",
                    required_evidence=(
                        "guard_partition",
                        "partition_coverage_proof",
                    ),
                    description="Complete the guard partition that justifies the covering case.",
                ),
            ),
            target_regression="method_b_closure_blocked",
            description="Recover Method-B closure only when covering case and guard partition proofs exist.",
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.LOOP_SUMMARY_PROOF_MISSING,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.GUARD_PARTITION_COMPLETION,
                    "loop_summary_guard_partition",
                    required_evidence=(
                        "loop_summary_seed",
                        "term_sequence",
                        "case_guard_disjunction",
                        "pure_side_effect_profile",
                    ),
                    description="Complete the loop-summary guard partition before using it as proof.",
                ),
            ),
            target_regression="loop_summary_proof_missing",
            description="Recover generic loop-summary proof gaps by completing the guard partition.",
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.RETURN_COVERAGE_GAP,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION,
                    "return_partition_extraction",
                    required_evidence=(
                        "missing_return_guard",
                        "tail_or_default_return_value",
                        "return_storage",
                    ),
                    description="Extract the missing return partition and value under its guard.",
                ),
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION,
                    "return_guard_coverage",
                    required_evidence=(
                        "case_guard_disjunction",
                        "path_feasibility",
                        "function_precondition",
                    ),
                    description="Prove the completed return cases cover the function precondition.",
                ),
            ),
            target_regression="return_coverage_gap",
            description="Recover return coverage gaps by adding the missing partition and coverage proof.",
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION,
                    "return_coverage_smt_disambiguation",
                    required_evidence=(
                        "case_guard_disjunction",
                        "normalized_guard_formula",
                        "solver_model_or_timeout",
                    ),
                    description="Disambiguate inconclusive return coverage with normalized SMT guards.",
                ),
            ),
            target_regression="return_coverage_inconclusive",
            description="Recover inconclusive coverage by proving or refuting the uncovered guard.",
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.OUTCOME_PARTITION_UNKNOWN,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.GUARD_PARTITION_COMPLETION,
                    "outcome_partition_resolution",
                    required_evidence=(
                        "unknown_outcome_guard",
                        "unknown_outcome_reason",
                        "must_diverge_or_return_proof",
                    ),
                    description="Resolve UnknownOutcome members into proved return/divergence outcomes.",
                ),
            ),
            target_regression="outcome_partition_unknown",
            description="Recover unknown outcome partitions by proving the unknown member semantics.",
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.SUMMARY_RETURN_CANDIDATE_INVALID,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.LOOP_SUMMARY_COMPLETION,
                    "summary_return_candidate_validation",
                    required_evidence=(
                        "summary_guard",
                        "summary_value_provenance",
                        "loop_summary_identity",
                    ),
                    description="Validate a loop-summary return candidate before exposing it as ReturnInfo.",
                ),
            ),
            target_regression="summary_return_candidate_invalid",
            description="Recover summary-derived returns only after candidate validity is complete.",
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.SUMMARY_RETURN_OVERLAP_UNPROVEN,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.RETURN_PARTITION_OVERLAP_PROOF,
                    "summary_return_overlap_value_equality",
                    required_evidence=(
                        "overlap_guard",
                        "return_storage",
                        "value_inequality_unsat",
                    ),
                    description="Prove overlapping exact/summary returns have equal values under the overlap guard.",
                ),
            ),
            target_regression="summary_return_overlap_unproven",
            description="Keep overlapping summary returns out of the accepted partition until value equality is proved.",
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.SUMMARY_EFFECT_UNMODELED,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.EFFECT_SUMMARY_COMPLETION,
                    "summary_return_effect_region",
                    required_evidence=(
                        "effect_region",
                        "memory_write_set",
                        "call_effect_summary",
                    ),
                    description="Bind summary-derived returns to modeled side effects or object-derived no-effect evidence.",
                ),
            ),
            target_regression="summary_effect_unmodeled",
            description="Reject value-only summary returns when effects, memory, or calls are not modeled.",
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.SUMMARY_PRECONDITION_INCOMPLETE,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.PRECONDITION_COMPLETION,
                    "summary_return_active_precondition",
                    required_evidence=(
                        "active_function_precondition",
                        "summary_applicability_guard",
                    ),
                    description="Define the active precondition covered by the proposed return partition.",
                ),
            ),
            target_regression="summary_precondition_incomplete",
            description="Do not accept summary returns without the applicability/precondition context.",
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.SUMMARY_PARTITION_NOT_TOTAL,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.PRECONDITION_COMPLETION,
                    "summary_return_partition_totality",
                    required_evidence=(
                        "active_function_precondition",
                        "summary_guard_disjunction",
                        "miss_region_unsat",
                    ),
                    description="Prove the accepted exact/summary return partition covers the active precondition.",
                ),
            ),
            target_regression="summary_partition_not_total",
            description="Keep summary returns out of the accepted partition until total coverage is proved.",
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.PHI_CIRCULAR_REPLACEMENT_UNPROVEN,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.LOOP_RECURRENCE_PROOF,
                    "phi_circular_structural_replacement",
                    required_evidence=(
                        "origin_pcode_ref",
                        "induction_binding",
                        "exit_guard_binding",
                        "replacement_expression",
                    ),
                    description="Replace phi_circular only through a structural loop recurrence proof.",
                ),
            ),
            target_regression="phi_circular_replacement_unproven",
            description="Keep phi_circular unresolved until a structural recurrence replacement is proved.",
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.SAT_UNSAFETY,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION,
                    "sat_counterexample_safety",
                    required_evidence=(
                        "counterexample_replay",
                        "active_unsafety_discharge",
                        "coverage_effect_safety",
                    ),
                    description=(
                        "Accept a SAT counterexample only after replay and all active "
                        "coverage/effect unsafety blockers are discharged."
                    ),
                ),
            ),
            target_regression="sat_unsafety",
            description="Recover SAT unsafety only with replay plus coverage/effect safety proof.",
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION,
                    "sat_counterexample_safety",
                    required_evidence=(
                        "counterexample_replay",
                        "case_partition_disambiguation",
                        "coverage_effect_safety",
                    ),
                    description=(
                        "Accept an ambiguous SAT counterexample only after replay proves "
                        "a unique disequivalence witness under the active case partition."
                    ),
                ),
            ),
            target_regression="sat_counterexample_ambiguous",
            description="Recover ambiguous SAT counterexamples only with replay plus partition proof.",
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                    "solver_timeout_retry",
                    required_evidence=(
                        "query_hash",
                        "timeout_budget",
                        "solver_options",
                        "normalized_query",
                    ),
                    description="Retry the timed-out query with traceable options and normalized terms.",
                ),
            ),
            target_regression="solver_unknown_timeout",
            description="Recover solver timeouts by retrying a normalized query with explicit solver settings.",
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.UNRESOLVED_EXPRESSION,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                    "typed_expression_lowering",
                    required_evidence=(
                        "object_target_key",
                        "typed_expression_key",
                        "lowering_rule",
                    ),
                    description=(
                        "Lower the object-derived unresolved expression into a typed SMT term "
                        "without erasing provenance."
                    ),
                ),
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                    "type_normalization",
                    required_evidence=(
                        "operand_widths",
                        "signedness_policy",
                        "normalized_expression",
                    ),
                    description=(
                        "Normalize operand widths and signedness before retrying the affected query."
                    ),
                ),
            ),
            target_regression="unresolved_expression",
            description=(
                "Recover unresolved expressions by typed lowering and type normalization before "
                "any solver retry can affect equivalence decisions."
            ),
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.NORMALIZATION_NO_CHANGE,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                    "normalization_strategy_selection",
                    required_evidence=(
                        "query_hash",
                        "typed_expression_key",
                        "candidate_rewrite_rules",
                    ),
                    description="Select a typed normalization strategy when the previous pass made no change.",
                ),
            ),
            target_regression="normalization_no_change",
            description="Recover no-op normalization by choosing a typed rewrite strategy.",
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.SOLVER_PROVEN_REWRITE_NO_CHANGE,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                    "rewrite_candidate_generation",
                    required_evidence=(
                        "pre_normalized_query",
                        "rewrite_candidate",
                        "typed_expression_key",
                    ),
                    description="Generate a semantically typed rewrite candidate before retrying the solver.",
                ),
            ),
            target_regression="solver_proven_rewrite_no_change",
            description="Recover no-op solver rewrites by producing a typed rewrite candidate.",
        ),
        UnknownRecoveryPlan.create(
            UnknownReasonId.SOLVER_PROVEN_REWRITE_PROOF_FAILED,
            (
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                    "rewrite_proof_recheck",
                    required_evidence=(
                        "rewrite_before_expr",
                        "rewrite_after_expr",
                        "proof_counterexample_or_solver_trace",
                    ),
                    description="Recheck the failed rewrite proof with typed expressions and counterexample evidence.",
                ),
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                    "solver_retry",
                    required_evidence=(
                        "normalized_query",
                        "solver_options",
                        "query_hash",
                    ),
                    description="Retry the normalized query with explicit solver settings and traceable query identity.",
                ),
            ),
            target_regression="solver_proven_rewrite_proof_failed",
            description="Recover failed solver-proven rewrites by rechecking the proof and retrying the normalized query.",
        ),
    ):
        register_unknown_recovery_plan(plan)


def normalize_unknown_reason_id(reason_id: Any) -> str:
    raw = _enum_value(reason_id) or UnknownReasonId.UNKNOWN.value
    if raw in _UNKNOWN_REASON_REGISTRY:
        return raw
    suffix = raw.rsplit(":", 1)[-1]
    if suffix in _UNKNOWN_REASON_REGISTRY:
        return suffix
    return UnknownReasonId.UNKNOWN.value


def get_unknown_reason_definition(reason_id: Any) -> UnknownReasonDefinition:
    normalized = normalize_unknown_reason_id(reason_id)
    definition = _UNKNOWN_REASON_REGISTRY.get(normalized)
    if definition is not None:
        return definition
    return _UNKNOWN_REASON_REGISTRY[UnknownReasonId.UNKNOWN.value]


def unknown_reason_registry_snapshot() -> Dict[str, UnknownReasonDefinition]:
    return dict(_UNKNOWN_REASON_REGISTRY)


def get_unknown_recovery_plan(reason_id: Any) -> UnknownRecoveryPlan:
    normalized = normalize_unknown_reason_id(reason_id)
    plan = _UNKNOWN_RECOVERY_PLAN_REGISTRY.get(normalized)
    if plan is not None:
        return plan
    return UnknownRecoveryPlan(
        reason_id=normalized,
        proof_obligations=(),
        target_regression=get_unknown_reason_definition(normalized).target_regression,
    )


def unknown_recovery_plan_registry_snapshot() -> Dict[str, UnknownRecoveryPlan]:
    return dict(_UNKNOWN_RECOVERY_PLAN_REGISTRY)


def build_proof_obligation_id(
    reason_id: Any,
    proof_stage: Any,
    recovery_proof_kind: Any,
    evidence_kind: Any,
    object_target_key: Any,
) -> Tuple[Any, ...]:
    return (
        normalize_unknown_reason_id(reason_id),
        str(proof_stage or UNKNOWN_TUPLE_MISSING),
        normalize_recovery_proof_kind(recovery_proof_kind) or UnknownRecoveryProofKind.NONE.value,
        str(evidence_kind or UNKNOWN_TUPLE_MISSING),
        _coerce_optional_tuple(object_target_key) or (UNKNOWN_TUPLE_MISSING,),
    )


def coerce_unknown_recovery_proof_obligation(value: Any) -> UnknownRecoveryProofObligation:
    if isinstance(value, UnknownRecoveryProofObligation):
        return value
    if isinstance(value, Mapping):
        return UnknownRecoveryProofObligation.from_dict(value)
    return UnknownRecoveryProofObligation.create(value, "unspecified")


def coerce_unknown_recovery_proof_obligations(
    values: Optional[Iterable[Any]],
) -> Tuple[UnknownRecoveryProofObligation, ...]:
    return tuple(coerce_unknown_recovery_proof_obligation(value) for value in (values or ()))


_register_default_recovery_plans()


@dataclass(frozen=True)
class UnknownReasonRecord:
    count_kind: str
    reason_id: str
    reason_class: str
    decision_effect: str
    reason_scope: str
    aggregation_unit: str
    stage: Optional[str] = None
    pair_or_case: Optional[str] = None
    evidence_refs: Tuple[str, ...] = ()
    recovery_proof_kind: str = UnknownRecoveryProofKind.NONE.value
    recovery_proof_obligations: Tuple[UnknownRecoveryProofObligation, ...] = ()
    proof_stage: Optional[str] = None
    evidence_kind: Optional[str] = None
    object_target_key: Optional[Tuple[Any, ...]] = None
    object_evidence: Optional[Any] = None
    proof_obligation_id: Optional[Tuple[Any, ...]] = None
    typed_cause_key: Optional[Mapping[str, Any]] = None
    proof_requirement_ids: Tuple[Mapping[str, Any], ...] = ()
    recovery_action: Optional[str] = None
    action_status: Optional[str] = None
    target_regression: Optional[str] = None
    detail: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        payload = {
            "count_kind": self.count_kind,
            "reason_id": self.reason_id,
            "reason_class": self.reason_class,
            "decision_effect": self.decision_effect,
            "reason_scope": self.reason_scope,
            "aggregation_unit": self.aggregation_unit,
            "stage": self.stage,
            "pair_or_case": self.pair_or_case,
            "evidence_refs": list(self.evidence_refs),
            "recovery_proof_kind": self.recovery_proof_kind,
            "recovery_proof_obligations": [
                obligation.to_dict() for obligation in self.recovery_proof_obligations
            ],
            "proof_stage": self.proof_stage,
            "evidence_kind": self.evidence_kind,
            "object_target_key": self.object_target_key,
            "proof_obligation_id": self.proof_obligation_id,
            "typed_cause_key": dict(self.typed_cause_key) if self.typed_cause_key else None,
            "proof_requirement_ids": [dict(item) for item in self.proof_requirement_ids],
            "recovery_action": self.recovery_action,
            "action_status": self.action_status,
            "target_regression": self.target_regression,
            "detail": self.detail,
        }
        if self.object_evidence is not None:
            payload["object_evidence"] = self.object_evidence
        return payload

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "UnknownReasonRecord":
        return make_unknown_reason(
            payload.get("reason_id"),
            count_kind=payload.get("count_kind"),
            reason_class=payload.get("reason_class"),
            decision_effect=payload.get("decision_effect"),
            reason_scope=payload.get("reason_scope"),
            aggregation_unit=payload.get("aggregation_unit"),
            stage=payload.get("stage"),
            pair_or_case=payload.get("pair_or_case"),
            evidence_refs=payload.get("evidence_refs") or (),
            recovery_proof_kind=payload.get("recovery_proof_kind"),
            recovery_proof_obligations=payload.get("recovery_proof_obligations"),
            proof_stage=payload.get("proof_stage"),
            evidence_kind=payload.get("evidence_kind"),
            object_target_key=payload.get("object_target_key"),
            object_evidence=payload.get("object_evidence"),
            proof_obligation_id=payload.get("proof_obligation_id"),
            typed_cause_key=payload.get("typed_cause_key"),
            proof_requirement_ids=payload.get("proof_requirement_ids") or (),
            recovery_action=payload.get("recovery_action"),
            action_status=payload.get("action_status"),
            target_regression=payload.get("target_regression"),
            detail=payload.get("detail"),
        )


def make_unknown_reason(
    reason_id: Any,
    *,
    count_kind: Any = None,
    reason_class: Any = None,
    decision_effect: Any = None,
    reason_scope: Any = None,
    aggregation_unit: Any = None,
    stage: Optional[str] = None,
    pair_or_case: Optional[str] = None,
    evidence_refs: Optional[Sequence[Any]] = None,
    recovery_proof_kind: Any = None,
    recovery_proof_obligations: Optional[Sequence[Any]] = None,
    proof_stage: Optional[str] = None,
    evidence_kind: Optional[str] = None,
    object_target_key: Any = None,
    object_evidence: Any = None,
    proof_obligation_id: Any = None,
    typed_cause_key: Optional[Mapping[str, Any]] = None,
    proof_requirement_ids: Optional[Sequence[Mapping[str, Any]]] = None,
    recovery_action: Optional[str] = None,
    action_status: Any = None,
    target_regression: Optional[str] = None,
    detail: Optional[str] = None,
) -> UnknownReasonRecord:
    original_reason_id = _enum_value(reason_id)
    original_recovery_proof_kind = _enum_value(recovery_proof_kind)
    definition = get_unknown_reason_definition(reason_id)
    coerced_evidence_refs = _coerce_evidence_refs(evidence_refs)
    if (
        definition.reason_id == UnknownReasonId.UNKNOWN.value
        and original_reason_id
        and original_reason_id != UnknownReasonId.UNKNOWN.value
    ):
        coerced_evidence_refs = (original_reason_id,) + coerced_evidence_refs
        if detail is None:
            detail = original_reason_id
    normalized_recovery_proof_kind = normalize_recovery_proof_kind(recovery_proof_kind)
    if (
        original_recovery_proof_kind is not None
        and normalized_recovery_proof_kind == UnknownRecoveryProofKind.NONE.value
        and original_recovery_proof_kind not in _registered_recovery_proof_kind_values()
    ):
        coerced_evidence_refs = (f"invalid_recovery_proof_kind:{original_recovery_proof_kind}",) + coerced_evidence_refs
        if detail is None:
            detail = f"invalid recovery_proof_kind: {original_recovery_proof_kind}"
    if recovery_proof_obligations is None:
        coerced_recovery_obligations = get_unknown_recovery_plan(definition.reason_id).proof_obligations
    else:
        coerced_recovery_obligations = coerce_unknown_recovery_proof_obligations(
            recovery_proof_obligations
        )
    normalized_proof_kind = normalized_recovery_proof_kind or definition.recovery_proof_kind
    coerced_object_target_key = _coerce_optional_tuple(object_target_key)
    normalized_action_status = _enum_value(action_status)
    if normalized_action_status is not None:
        normalized_action_status = str(normalized_action_status)
    resolved_proof_stage = proof_stage
    if resolved_proof_stage is None and len(coerced_recovery_obligations) == 1:
        resolved_proof_stage = coerced_recovery_obligations[0].proof_stage
    resolved_evidence_kind = str(evidence_kind) if evidence_kind is not None else None
    coerced_proof_obligation_id = _coerce_optional_tuple(proof_obligation_id)
    if (
        coerced_proof_obligation_id is None
        and resolved_proof_stage is not None
        and resolved_evidence_kind is not None
        and coerced_object_target_key is not None
        and normalized_proof_kind != UnknownRecoveryProofKind.NONE.value
    ):
        coerced_proof_obligation_id = build_proof_obligation_id(
            definition.reason_id,
            resolved_proof_stage,
            normalized_proof_kind,
            resolved_evidence_kind,
            coerced_object_target_key,
        )
    return UnknownReasonRecord(
        count_kind=_enum_value(count_kind) or UnknownCountKind.REASON_RECORD.value,
        reason_id=definition.reason_id,
        reason_class=_enum_value(reason_class) or definition.reason_class,
        decision_effect=_enum_value(decision_effect) or definition.decision_effect,
        reason_scope=_enum_value(reason_scope) or definition.reason_scope,
        aggregation_unit=_enum_value(aggregation_unit) or definition.aggregation_unit,
        stage=stage,
        pair_or_case=pair_or_case,
        evidence_refs=coerced_evidence_refs,
        recovery_proof_kind=normalized_proof_kind,
        recovery_proof_obligations=coerced_recovery_obligations,
        proof_stage=resolved_proof_stage,
        evidence_kind=resolved_evidence_kind,
        object_target_key=coerced_object_target_key,
        object_evidence=object_evidence,
        proof_obligation_id=coerced_proof_obligation_id,
        typed_cause_key=dict(typed_cause_key) if typed_cause_key else None,
        proof_requirement_ids=tuple(dict(item) for item in (proof_requirement_ids or ())),
        recovery_action=recovery_action,
        action_status=normalized_action_status,
        target_regression=target_regression if target_regression is not None else definition.target_regression,
        detail=detail,
    )


def coerce_unknown_reason_record(value: Any) -> UnknownReasonRecord:
    if isinstance(value, UnknownReasonRecord):
        return value
    if isinstance(value, Mapping):
        return UnknownReasonRecord.from_dict(value)
    return make_unknown_reason(value)


def coerce_unknown_reason_records(values: Optional[Iterable[Any]]) -> Tuple[UnknownReasonRecord, ...]:
    return tuple(coerce_unknown_reason_record(value) for value in (values or ()))


def coerce_unknown_recovery_action(value: Any) -> UnknownRecoveryAction:
    if isinstance(value, UnknownRecoveryAction):
        return value
    if isinstance(value, Mapping):
        return UnknownRecoveryAction.from_dict(value)
    return UnknownRecoveryAction(
        count_kind=UnknownCountKind.PROOF_ACTION.value,
        reason_id=UnknownReasonId.UNKNOWN.value,
        decision_effect=UnknownDecisionEffect.DIAGNOSTIC_ONLY.value,
        reason_scope=UnknownReasonScope.GLOBAL.value,
        proof_kind=UnknownRecoveryProofKind.NONE.value,
        proof_stage="unspecified",
        status=UnknownRecoveryActionStatus.NO_REGISTERED_PLAN.value,
        aggregation_unit=UnknownAggregationUnit.RESULT.value,
        detail=str(value),
    )


def coerce_unknown_recovery_actions(values: Optional[Iterable[Any]]) -> Tuple[UnknownRecoveryAction, ...]:
    return tuple(coerce_unknown_recovery_action(value) for value in (values or ()))


def build_unknown_recovery_actions(
    values: Optional[Iterable[Any]],
    *,
    primary_by_aggregation_unit: bool = False,
) -> Tuple[UnknownRecoveryAction, ...]:
    records = coerce_unknown_reason_records(values)
    if primary_by_aggregation_unit:
        records = _select_primary_records_by_aggregation_unit(records)
    actions = []
    for record in records:
        obligations = record.recovery_proof_obligations
        if not obligations:
            plan = get_unknown_recovery_plan(record.reason_id)
            obligations = plan.proof_obligations
        if not obligations:
            if record.recovery_proof_kind == UnknownRecoveryProofKind.NONE.value:
                continue
            actions.append(
                UnknownRecoveryAction(
                    count_kind=UnknownCountKind.PROOF_ACTION.value,
                    reason_id=record.reason_id,
                    decision_effect=record.decision_effect,
                    reason_scope=record.reason_scope,
                    proof_kind=record.recovery_proof_kind,
                    proof_stage=record.proof_stage or "unspecified",
                    status=record.action_status or UnknownRecoveryActionStatus.NO_REGISTERED_PLAN.value,
                    aggregation_unit=record.aggregation_unit,
                    stage=record.stage,
                    pair_or_case=record.pair_or_case,
                    evidence_refs=record.evidence_refs,
                    evidence_kind=record.evidence_kind,
                    object_target_key=record.object_target_key,
                    object_evidence=record.object_evidence,
                    proof_obligation_id=record.proof_obligation_id,
                    recovery_action=record.recovery_action,
                    target_regression=record.target_regression,
                    detail=record.detail,
                )
            )
            continue
        for obligation in obligations:
            proof_stage = record.proof_stage or obligation.proof_stage
            if (
                record.proof_stage is not None
                or record.evidence_kind is not None
                or record.recovery_action is not None
            ):
                proof_kind = record.recovery_proof_kind
                if proof_kind == UnknownRecoveryProofKind.NONE.value:
                    proof_kind = obligation.proof_kind
            else:
                proof_kind = obligation.proof_kind
            evidence_kind = record.evidence_kind
            if evidence_kind is None and obligation.required_evidence:
                evidence_kind = obligation.required_evidence[0]
            proof_obligation_id = record.proof_obligation_id
            if (
                proof_obligation_id is None
                and evidence_kind is not None
                and record.object_target_key is not None
            ):
                proof_obligation_id = build_proof_obligation_id(
                    record.reason_id,
                    proof_stage,
                    proof_kind,
                    evidence_kind,
                    record.object_target_key,
                )
            actions.append(
                UnknownRecoveryAction(
                    count_kind=UnknownCountKind.PROOF_ACTION.value,
                    reason_id=record.reason_id,
                    decision_effect=record.decision_effect,
                    reason_scope=record.reason_scope,
                    proof_kind=proof_kind,
                    proof_stage=proof_stage,
                    status=record.action_status or UnknownRecoveryActionStatus.PLANNED.value,
                    aggregation_unit=record.aggregation_unit,
                    stage=record.stage,
                    pair_or_case=record.pair_or_case,
                    required_evidence=obligation.required_evidence,
                    evidence_refs=record.evidence_refs,
                    evidence_kind=evidence_kind,
                    object_target_key=record.object_target_key,
                    object_evidence=record.object_evidence,
                    proof_obligation_id=proof_obligation_id,
                    recovery_action=record.recovery_action,
                    target_regression=record.target_regression,
                    detail=obligation.description or record.detail,
                )
            )
    return tuple(actions)


def summarize_unknown_reason_counts(
    values: Optional[Iterable[Any]],
    *,
    primary_by_aggregation_unit: bool = False,
) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    records = coerce_unknown_reason_records(values)
    if primary_by_aggregation_unit:
        records = _select_primary_records_by_aggregation_unit(records)
    for record in records:
        counts[record.reason_id] = int(counts.get(record.reason_id, 0) or 0) + 1
    return counts


def _select_primary_records_by_aggregation_unit(
    records: Iterable[UnknownReasonRecord],
) -> Tuple[UnknownReasonRecord, ...]:
    primary_records: Dict[Tuple[str, str], UnknownReasonRecord] = {}
    fallback_index = 0
    for record in records:
        aggregation_key = str(record.aggregation_unit or UnknownAggregationUnit.RESULT.value)
        unit_key = record.pair_or_case or record.stage
        if unit_key is None:
            unit_key = f"record:{fallback_index}"
            fallback_index += 1
        primary_records.setdefault((aggregation_key, unit_key), record)
    return tuple(primary_records.values())


def summarize_unknown_recovery_backlog(
    values: Optional[Iterable[Any]],
    *,
    primary_by_aggregation_unit: bool = False,
) -> Dict[str, Dict[str, Any]]:
    records = coerce_unknown_reason_records(values)
    if primary_by_aggregation_unit:
        records = _select_primary_records_by_aggregation_unit(records)
    summary: Dict[str, Dict[str, Any]] = {}
    for record in records:
        entry = summary.setdefault(
            record.reason_id,
            {
                "count": 0,
                "target_regression": record.target_regression,
                "recovery_proof_kind": record.recovery_proof_kind,
                "proof_obligation_counts": {},
                "proof_obligations": [],
            },
        )
        entry["count"] = int(entry["count"]) + 1
        if entry.get("target_regression") is None:
            entry["target_regression"] = record.target_regression
        if (
            entry.get("recovery_proof_kind") == UnknownRecoveryProofKind.NONE.value
            and record.recovery_proof_kind != UnknownRecoveryProofKind.NONE.value
        ):
            entry["recovery_proof_kind"] = record.recovery_proof_kind
        seen_obligations = {
            (obligation["proof_kind"], obligation["proof_stage"])
            for obligation in entry["proof_obligations"]
        }
        proof_counts = entry["proof_obligation_counts"]
        for obligation in record.recovery_proof_obligations:
            proof_counts[obligation.proof_kind] = int(proof_counts.get(obligation.proof_kind, 0) or 0) + 1
            obligation_key = (obligation.proof_kind, obligation.proof_stage)
            if obligation_key not in seen_obligations:
                entry["proof_obligations"].append(obligation.to_dict())
                seen_obligations.add(obligation_key)
    return summary
