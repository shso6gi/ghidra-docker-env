# -*- coding: utf-8 -*-
"""Typed UNKNOWN reason schema and registry."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence, Tuple


class UnknownReasonId(str, Enum):
    RETURN_WIDTH_BRIDGE_MISSING = "return_width_bridge_missing"
    RECOVERABLE_PARTIAL = "recoverable_partial"
    READONLY_IDENTITY_MISSING = "readonly_identity_missing"
    METHOD_B_CLOSURE_BLOCKED = "method_b_closure_blocked"
    LOOP_SUMMARY_PROOF_MISSING = "loop_summary_proof_missing"
    RETURN_COVERAGE_GAP = "return_coverage_gap"
    RETURN_COVERAGE_INCONCLUSIVE = "return_coverage_inconclusive"
    EQUIVALENCE_BLOCKING_UNSAFETY = "equivalence_blocking_unsafety"
    SAT_UNSAFETY = "sat_unsafety"
    SAT_COUNTEREXAMPLE_AMBIGUOUS = "sat_counterexample_ambiguous"
    UNRESOLVED_EXPRESSION = "unresolved_expression"
    UNRESOLVED_VALUE_EXPRESSION = "unresolved_value_expression"
    NORMALIZATION_NO_CHANGE = "normalization_no_change"
    SOLVER_PROVEN_REWRITE_NO_CHANGE = "solver_proven_rewrite_no_change"
    SOLVER_PROVEN_REWRITE_PROOF_FAILED = "solver_proven_rewrite_proof_failed"
    SOLVER_UNKNOWN_TIMEOUT = "solver_unknown_timeout"
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
    PATH_SENSITIVE_ARGUMENT_MERGE = "path_sensitive_argument_merge"
    STORAGE_BACKED_IDENTITY_PROPAGATION = "storage_backed_identity_propagation"
    PROOF_BACKED_COVERING_CASE = "proof_backed_covering_case"
    GUARD_PARTITION_COMPLETION = "guard_partition_completion"
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
    NO_REGISTERED_PLAN = "no_registered_plan"


@dataclass(frozen=True)
class UnknownRecoveryAction:
    reason_id: str
    proof_kind: str
    proof_stage: str
    status: str
    aggregation_unit: str
    stage: Optional[str] = None
    pair_or_case: Optional[str] = None
    required_evidence: Tuple[str, ...] = ()
    evidence_refs: Tuple[str, ...] = ()
    target_regression: Optional[str] = None
    detail: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "reason_id": self.reason_id,
            "proof_kind": self.proof_kind,
            "proof_stage": self.proof_stage,
            "status": self.status,
            "aggregation_unit": self.aggregation_unit,
            "stage": self.stage,
            "pair_or_case": self.pair_or_case,
            "required_evidence": list(self.required_evidence),
            "evidence_refs": list(self.evidence_refs),
            "target_regression": self.target_regression,
            "detail": self.detail,
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "UnknownRecoveryAction":
        return cls(
            reason_id=normalize_unknown_reason_id(payload.get("reason_id")),
            proof_kind=normalize_recovery_proof_kind(payload.get("proof_kind")) or UnknownRecoveryProofKind.NONE.value,
            proof_stage=str(payload.get("proof_stage") or "unspecified"),
            status=str(payload.get("status") or UnknownRecoveryActionStatus.PLANNED.value),
            aggregation_unit=str(payload.get("aggregation_unit") or UnknownAggregationUnit.RESULT.value),
            stage=payload.get("stage"),
            pair_or_case=payload.get("pair_or_case"),
            required_evidence=_coerce_evidence_refs(payload.get("required_evidence") or ()),
            evidence_refs=_coerce_evidence_refs(payload.get("evidence_refs") or ()),
            target_regression=payload.get("target_regression"),
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
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.RETURN_COVERAGE_GAP,
            UnknownReasonClass.COVERAGE_GAP,
            UnknownDecisionEffect.BLOCKS_EQUIVALENCE,
            UnknownReasonScope.FUNCTION,
            UnknownAggregationUnit.FUNCTION,
            recovery_proof_kind=UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION,
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
            UnknownReasonClass.COVERAGE_GAP,
            UnknownDecisionEffect.BLOCKS_DECISION,
            UnknownReasonScope.FUNCTION,
            UnknownAggregationUnit.FUNCTION,
            recovery_proof_kind=UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION,
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
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS,
            UnknownReasonClass.UNSAFE_ANALYSIS,
            UnknownDecisionEffect.BLOCKS_DISEQUIVALENCE,
            UnknownReasonScope.PAIR,
            UnknownAggregationUnit.PAIR,
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.UNRESOLVED_EXPRESSION,
            UnknownReasonClass.OPERATIONAL_GAP,
            UnknownDecisionEffect.BLOCKS_DECISION,
            UnknownReasonScope.EXPRESSION,
            UnknownAggregationUnit.PAIR,
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
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.NORMALIZATION_NO_CHANGE,
            UnknownReasonClass.OPERATIONAL_GAP,
            UnknownDecisionEffect.RETRYABLE,
            UnknownReasonScope.PAIR,
            UnknownAggregationUnit.PAIR,
            recovery_proof_kind=UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.SOLVER_PROVEN_REWRITE_NO_CHANGE,
            UnknownReasonClass.PROOF_OBLIGATION,
            UnknownDecisionEffect.RETRYABLE,
            UnknownReasonScope.PAIR,
            UnknownAggregationUnit.PAIR,
            recovery_proof_kind=UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
        ),
        UnknownReasonDefinition.create(
            UnknownReasonId.SOLVER_PROVEN_REWRITE_PROOF_FAILED,
            UnknownReasonClass.PROOF_OBLIGATION,
            UnknownDecisionEffect.RETRYABLE,
            UnknownReasonScope.PAIR,
            UnknownAggregationUnit.PAIR,
            recovery_proof_kind=UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
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
    target_regression: Optional[str] = None
    detail: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
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
            "target_regression": self.target_regression,
            "detail": self.detail,
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "UnknownReasonRecord":
        return make_unknown_reason(
            payload.get("reason_id"),
            reason_class=payload.get("reason_class"),
            decision_effect=payload.get("decision_effect"),
            reason_scope=payload.get("reason_scope"),
            aggregation_unit=payload.get("aggregation_unit"),
            stage=payload.get("stage"),
            pair_or_case=payload.get("pair_or_case"),
            evidence_refs=payload.get("evidence_refs") or (),
            recovery_proof_kind=payload.get("recovery_proof_kind"),
            recovery_proof_obligations=payload.get("recovery_proof_obligations"),
            target_regression=payload.get("target_regression"),
            detail=payload.get("detail"),
        )


def make_unknown_reason(
    reason_id: Any,
    *,
    reason_class: Any = None,
    decision_effect: Any = None,
    reason_scope: Any = None,
    aggregation_unit: Any = None,
    stage: Optional[str] = None,
    pair_or_case: Optional[str] = None,
    evidence_refs: Optional[Sequence[Any]] = None,
    recovery_proof_kind: Any = None,
    recovery_proof_obligations: Optional[Sequence[Any]] = None,
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
    return UnknownReasonRecord(
        reason_id=definition.reason_id,
        reason_class=_enum_value(reason_class) or definition.reason_class,
        decision_effect=_enum_value(decision_effect) or definition.decision_effect,
        reason_scope=_enum_value(reason_scope) or definition.reason_scope,
        aggregation_unit=_enum_value(aggregation_unit) or definition.aggregation_unit,
        stage=stage,
        pair_or_case=pair_or_case,
        evidence_refs=coerced_evidence_refs,
        recovery_proof_kind=normalized_recovery_proof_kind or definition.recovery_proof_kind,
        recovery_proof_obligations=coerced_recovery_obligations,
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
        reason_id=UnknownReasonId.UNKNOWN.value,
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
                    reason_id=record.reason_id,
                    proof_kind=record.recovery_proof_kind,
                    proof_stage="unspecified",
                    status=UnknownRecoveryActionStatus.NO_REGISTERED_PLAN.value,
                    aggregation_unit=record.aggregation_unit,
                    stage=record.stage,
                    pair_or_case=record.pair_or_case,
                    evidence_refs=record.evidence_refs,
                    target_regression=record.target_regression,
                    detail=record.detail,
                )
            )
            continue
        for obligation in obligations:
            actions.append(
                UnknownRecoveryAction(
                    reason_id=record.reason_id,
                    proof_kind=obligation.proof_kind,
                    proof_stage=obligation.proof_stage,
                    status=UnknownRecoveryActionStatus.PLANNED.value,
                    aggregation_unit=record.aggregation_unit,
                    stage=record.stage,
                    pair_or_case=record.pair_or_case,
                    required_evidence=obligation.required_evidence,
                    evidence_refs=record.evidence_refs,
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
