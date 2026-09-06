# -*- coding: utf-8 -*-
"""Typed UNKNOWN reason schema and registry."""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence, Tuple

# Phase 7-1b-1 (#97): pure な定義層は proof.unknown_reason へ移動した。以下は (a) 本 module の実装が使う名前と
# (b) 旧 path `checker.unknown_reason` からの互換 import のための再輸出（同一 object。再定義しない）。
from scripts.function_tracer_pcode.proof.unknown_reason import (  # noqa: F401
    UNKNOWN_TUPLE_MISSING,
    UnknownAggregationUnit,
    UnknownCountKind,
    UnknownDecisionEffect,
    UnknownReasonClass,
    UnknownReasonDefinition,
    UnknownReasonId,
    UnknownReasonScope,
    UnknownRecoveryActionStatus,
    UnknownRecoveryPlan,
    UnknownRecoveryProofKind,
    UnknownRecoveryProofObligation,
    _UNKNOWN_REASON_REGISTRY,
    _UNKNOWN_RECOVERY_PLAN_REGISTRY,
    _coerce_evidence_refs,
    _coerce_optional_tuple,
    _enum_value,
    _registered_recovery_proof_kind_values,
    build_proof_obligation_id,
    coerce_unknown_recovery_proof_obligation,
    coerce_unknown_recovery_proof_obligations,
    format_projection_detail,
    get_unknown_reason_definition,
    get_unknown_recovery_plan,
    normalize_recovery_proof_kind,
    normalize_unknown_reason_id,
    register_unknown_reason,
    register_unknown_recovery_plan,
)


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
        raw_reason_id = _enum_value(payload.get("reason_id"))
        reason_id = normalize_unknown_reason_id(raw_reason_id)
        if reason_id == UnknownReasonId.UNKNOWN.value and raw_reason_id:
            try:
                from scripts.function_tracer_pcode.authority.process.supervisor import (
                    PROCESS_DURABLE_REASON_REGISTRY,
                )

                PROCESS_DURABLE_REASON_REGISTRY.get(raw_reason_id)
            except KeyError:
                pass
            else:
                # Exact v2 compatibility diagnostics are reader-supported
                # without registering them as legacy decision reasons.  Keep
                # their identity and the already serialized typed fields.
                reason_id = raw_reason_id
        definition = get_unknown_reason_definition(reason_id)
        use_definition_defaults = (
            reason_id != UnknownReasonId.UNKNOWN.value
            and reason_id in _UNKNOWN_REASON_REGISTRY
        )
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
        constructor = make_unknown_reason
        raw_reason_id = _enum_value(payload.get("reason_id"))
        if raw_reason_id not in _UNKNOWN_REASON_REGISTRY:
            try:
                from scripts.function_tracer_pcode.authority.process.supervisor import (
                    PROCESS_DURABLE_REASON_REGISTRY,
                )

                PROCESS_DURABLE_REASON_REGISTRY.get(raw_reason_id)
            except KeyError:
                pass
            else:
                constructor = make_internal_v2_reason_diagnostic
        return constructor(
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


def make_internal_v2_reason_diagnostic(
    reason_id: Any,
    **kwargs: Any,
) -> UnknownReasonRecord:
    """Build an internal legacy diagnostic from one exact sealed v2 reason.

    This value may support the pre-Phase-8 legacy decision path, but it is not a
    typed result projection and must never be serialized as canonical v2
    compatibility authority.
    """
    from scripts.function_tracer_pcode.authority.sites.activation import RETIRED_UMBRELLA_REASON_IDS
    from scripts.function_tracer_pcode.authority.process.supervisor import (
        PROCESS_DURABLE_REASON_REGISTRY,
    )

    exact_reason_id = _enum_value(reason_id)
    if exact_reason_id in RETIRED_UMBRELLA_REASON_IDS:
        raise ValueError("retired UNKNOWN umbrella is reader-only")
    definition = PROCESS_DURABLE_REASON_REGISTRY.get(exact_reason_id)
    class_map = {
        "proof_obligation": UnknownReasonClass.PROOF_OBLIGATION.value,
        "unsupported_semantics": UnknownReasonClass.OPERATIONAL_GAP.value,
        "semantic_safety_gate": UnknownReasonClass.UNSAFE_ANALYSIS.value,
        "semantic_partition_blocker": UnknownReasonClass.PROOF_OBLIGATION.value,
    }
    projected_reason_class = class_map.get(
        definition.reason_class, UnknownReasonClass.PROOF_OBLIGATION.value
    )
    provided_reason_class = _enum_value(kwargs.pop("reason_class", None))
    provided_decision_effect = _enum_value(kwargs.pop("decision_effect", None))
    provided_target_regression = kwargs.pop("target_regression", None)
    if provided_reason_class not in {None, projected_reason_class}:
        raise ValueError("typed compatibility reason class differs from v2 registry")
    if provided_decision_effect not in {None, definition.decision_effect}:
        raise ValueError("typed compatibility decision effect differs from v2 registry")
    if provided_target_regression not in {None, definition.reason_id}:
        raise ValueError("typed compatibility target differs from exact v2 reason")
    provided_proof_obligation_id = _coerce_optional_tuple(
        kwargs.get("proof_obligation_id")
    )
    projected = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_VALUE_EXPRESSION,
        reason_class=projected_reason_class,
        decision_effect=definition.decision_effect,
        reason_scope=kwargs.pop("reason_scope", UnknownReasonScope.QUERY.value),
        aggregation_unit=kwargs.pop(
            "aggregation_unit", UnknownAggregationUnit.PAIR.value
        ),
        **kwargs,
    )
    exact_proof_obligation_id = projected.proof_obligation_id
    if (
        projected.proof_stage is not None
        and projected.evidence_kind is not None
        and projected.object_target_key is not None
        and projected.recovery_proof_kind != UnknownRecoveryProofKind.NONE.value
    ):
        exact_proof_obligation_id = build_proof_obligation_id(
            definition.reason_id,
            projected.proof_stage,
            projected.recovery_proof_kind,
            projected.evidence_kind,
            projected.object_target_key,
        )
        if (
            provided_proof_obligation_id is not None
            and provided_proof_obligation_id != exact_proof_obligation_id
        ):
            raise ValueError("typed compatibility proof ID differs from exact v2 reason")
    diagnostic_cause_key = dict(projected.typed_cause_key or {})
    diagnostic_cause_key["authority_class"] = "LEGACY_DIAGNOSTIC"
    return replace(
        projected,
        reason_id=definition.reason_id,
        reason_class=projected_reason_class,
        decision_effect=definition.decision_effect,
        proof_obligation_id=exact_proof_obligation_id,
        typed_cause_key=diagnostic_cause_key,
        target_regression=definition.reason_id,
    )


def build_projection_diagnostic(
    receipt: Any,
    *,
    cause_occurrence: Any = None,
    legacy_reasons: Sequence[Any] = (),
    function_names: Mapping[str, Any] = None,
    binary_names: Mapping[str, Any] = None,
    projected_reason_counts: Mapping[str, int] = None,
) -> Dict[str, Any]:
    """Human-readable, machine-aggregatable facts for one projected v2 cause.

    The projected record only carried digests (Issue #17).  This collects, in
    priority order, the typed cause occurrence (what semantic fact is missing,
    on which target kind and scope, from which producer site), the matching
    legacy strategy reason (site / case pair / free-text detail), and the
    function/binary names of the compared pair.  It is diagnostic data, not
    authority: no digest or receipt is derived from it.
    """
    from scripts.function_tracer_pcode.authority.contracts import canonical_value

    diagnostic: Dict[str, Any] = {
        "schema": "unknown-reason-diagnostic-v1",
        "reason_id": getattr(receipt, "reason_id", None),
        "functions": {
            "function1": (function_names or {}).get("function1"),
            "function2": (function_names or {}).get("function2"),
        },
        "binaries": {
            "binary1": (binary_names or {}).get("binary1"),
            "binary2": (binary_names or {}).get("binary2"),
        },
    }
    if cause_occurrence is not None:
        cause_id = getattr(cause_occurrence, "cause_id", None)
        scope = getattr(cause_occurrence, "identity_scope", None)
        diagnostic["cause"] = {
            "occurrence_id": getattr(cause_occurrence, "occurrence_id", None),
            "target_kind": getattr(cause_occurrence, "target_kind", None),
            "identity_scope": getattr(scope, "value", scope),
            "producer_id": getattr(cause_occurrence, "producer_id", None),
            "evidence_kind": getattr(cause_occurrence, "evidence_kind", None),
            "evidence_refs": list(getattr(cause_occurrence, "evidence_refs", ()) or ()),
            "canonical_target_key": canonical_value(
                getattr(cause_id, "canonical_target_key", None)
            ),
            "missing_semantic_fact": canonical_value(
                getattr(cause_id, "missing_semantic_fact", None)
            ),
        }
    matched, match_kind = _match_legacy_reasons(
        diagnostic["reason_id"],
        cause_occurrence,
        legacy_reasons,
        projected_reason_counts or {},
    )
    if matched:
        diagnostic["legacy_match"] = match_kind
        diagnostic["legacy"] = [
            {
                "stage": getattr(record, "stage", None),
                "pair_or_case": getattr(record, "pair_or_case", None),
                "detail": getattr(record, "detail", None),
                "evidence_refs": list(getattr(record, "evidence_refs", ()) or ()),
                "object_target_key": canonical_value(getattr(record, "object_target_key", None)),
            }
            for record in matched
        ]
    return diagnostic


def _match_legacy_reasons(
    reason_id: Any,
    cause_occurrence: Any,
    legacy_reasons: Sequence[Any],
    projected_reason_counts: Mapping[str, int],
) -> Tuple[Tuple[Any, ...], Optional[str]]:
    """Pick the legacy records that describe *this* cause, never a sibling site.

    1. exact: the legacy ``object_target_key`` equals the cause's canonical
       target key (SAT-safety and other producers emit the record's key as the
       cause target), or the legacy proof obligation / evidence refs equal the
       cause's proof requirement ids / evidence refs.
    2. unique: no exact key is available, but the reason id has exactly one
       legacy record and exactly one projected cause, so the correspondence is
       1:1 by construction.
    Otherwise nothing is attached; the typed cause occurrence alone is used.
    """
    from scripts.function_tracer_pcode.authority.contracts import canonical_value

    candidates = tuple(
        record for record in (legacy_reasons or ())
        if getattr(record, "reason_id", None) == reason_id
    )
    if not candidates:
        return (), None
    cause_id = getattr(cause_occurrence, "cause_id", None)
    cause_target = canonical_value(getattr(cause_id, "canonical_target_key", None)) if cause_id is not None else None
    cause_requirements = set(getattr(cause_occurrence, "proof_requirement_ids", ()) or ()) if cause_occurrence is not None else set()
    exact = []
    for record in candidates:
        record_target = canonical_value(getattr(record, "object_target_key", None))
        if cause_target is not None and record_target is not None and record_target == cause_target:
            exact.append(record)
            continue
        record_obligation = getattr(record, "proof_obligation_id", None)
        if record_obligation is not None and cause_requirements and str(
            canonical_value(record_obligation)
        ) in {str(item) for item in cause_requirements}:
            exact.append(record)
            continue
    if exact:
        return tuple(exact), "exact"
    if len(candidates) == 1 and int(projected_reason_counts.get(reason_id, 0) or 0) == 1:
        return candidates, "unique"
    return (), None


def make_production_unknown_reason(
    projection_receipt: Any,
    *,
    projection_factory: Any,
    detail: Optional[str] = None,
    diagnostic: Optional[Mapping[str, Any]] = None,
) -> UnknownReasonRecord:
    """Project one factory-owned active v2 cause to compatibility data."""

    from scripts.function_tracer_pcode.authority.sites.activation import (
        TypedResultProjectionFactory,
        TypedResultProjectionReceipt,
    )

    if type(projection_factory) is not TypedResultProjectionFactory:
        raise TypeError("production compatibility projection requires exact issuer")
    if type(projection_receipt) is not TypedResultProjectionReceipt:
        raise TypeError("production compatibility projection requires exact receipt")
    if not projection_factory.owns(projection_receipt):
        raise ValueError("production compatibility projection is not issuer-owned")
    receipt = projection_receipt
    definition = projection_factory.reason_definition_for(receipt)
    class_map = {
        "proof_obligation": UnknownReasonClass.PROOF_OBLIGATION.value,
        "unsupported_semantics": UnknownReasonClass.OPERATIONAL_GAP.value,
        "semantic_safety_gate": UnknownReasonClass.UNSAFE_ANALYSIS.value,
        "semantic_partition_blocker": UnknownReasonClass.PROOF_OBLIGATION.value,
        "semantic": UnknownReasonClass.PROOF_OBLIGATION.value,
    }
    return UnknownReasonRecord(
        count_kind=UnknownCountKind.REASON_RECORD.value,
        reason_id=receipt.reason_id,
        reason_class=class_map.get(
            definition.reason_class, UnknownReasonClass.PROOF_OBLIGATION.value
        ),
        decision_effect=definition.decision_effect,
        reason_scope=UnknownReasonScope.QUERY.value,
        aggregation_unit=UnknownAggregationUnit.RESULT.value,
        stage="V2_TYPED_RESULT_PROJECTION",
        evidence_refs=(receipt.event_digest, receipt.receipt_digest),
        typed_cause_key={
            "authority_class": "V2_FACTORY_PROJECTION",
            "projection_schema": receipt.projection_schema,
            "activation_id": receipt.activation_id,
            "expected_cause_slot_id": receipt.expected_cause_slot_id,
            "result_occurrence_id": receipt.result_occurrence_id,
            "occurrence_id": receipt.occurrence_id,
            "cause_id": receipt.cause_id,
            "reason_id": receipt.reason_id,
            "source_snapshot_fingerprint": receipt.source_snapshot_fingerprint,
            "event_digest": receipt.event_digest,
            "event_stream_digest": receipt.event_stream_digest,
            "semantic_projection_digest": receipt.semantic_projection_digest,
            "lifecycle_projection_digest": receipt.lifecycle_projection_digest,
            "reason_registry_digest": receipt.reason_registry_digest,
            "recovery_registry_digest": receipt.recovery_registry_digest,
            "receipt_digest": receipt.receipt_digest,
        },
        target_regression=receipt.reason_id,
        detail=detail if detail is not None else (
            format_projection_detail(diagnostic) if diagnostic else None
        ),
        pair_or_case=_first_legacy_field(diagnostic, "pair_or_case"),
        object_target_key=(
            (diagnostic.get("cause") or {}).get("canonical_target_key")
            if diagnostic else None
        ),
        object_evidence=dict(diagnostic) if diagnostic else None,
    )


def _first_legacy_field(diagnostic: Optional[Mapping[str, Any]], field_name: str) -> Any:
    for item in (diagnostic or {}).get("legacy") or ():
        value = item.get(field_name)
        if value is not None:
            return value
    return None


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
