"""Strict, digest-checked JSON codecs for v2 authority objects."""

from __future__ import annotations

import json
import math
from dataclasses import fields, is_dataclass
from enum import Enum
from types import MappingProxyType
from typing import Any, Mapping

from scripts.function_tracer_pcode.authority.census_contract import CensusEntry, CensusManifest
from scripts.function_tracer_pcode.authority.contracts import (
    BlockerEligibilityBaseRow,
    CActiveBaseRow,
    CensusMode,
    CauseIdV2,
    CauseOccurrence,
    CauseOccurrenceAuthority,
    CauseTransformationEvent,
    CauseTransformationProofReceipt,
    IdentityScope,
    Outcome,
    ProofRequirement,
    QOpenBaseRow,
    RecoveryAddressability,
    ReasonDefinition,
    RequirementCompletionReceipt,
    ResultKind,
    TransformationKind,
    VerifiedLifecycleProjection,
    authority_digest,
    canonical_value,
    _CAUSE_ID_CODEC_TOKEN,
)
from scripts.function_tracer_pcode.authority.decision.conditional import (
    ConditionalDecisionReceipt,
    ConditionalDecisiveProofKind,
    ConditionalDecisiveProofReceipt,
    _CONDITIONAL_DECISION_CODEC_TOKEN,
)
from scripts.function_tracer_pcode.authority.decision.decision import (
    DecisiveProofKind,
    DecisiveProofReceipt,
    DecisionReceipt,
    ErrorReceipt,
    TerminalTimeoutReceipt,
    _DECISION_RECEIPT_CODEC_TOKEN,
)
from scripts.function_tracer_pcode.authority.lifecycle.stream import (
    CauseObservedEventAuthority,
    CauseTransformedEventAuthority,
    DecisiveProofEventAuthority,
    ErrorEventAuthority,
    EventHeader,
    EventStreamEnvelope,
    EventType,
    GenericReceiptBoundSolverExecutionEventAuthority,
    OutcomeProducerAttemptEventAuthority,
    RecordedEvent,
    ProcessCompletionEventAuthority,
    ProcessExecutionEventAuthority,
    RequirementCompletedEventAuthority,
    ReceiptBoundSolverExecutionEventAuthority,
    SealedEventStream,
    SolverExecutionEventAuthority,
    StageObservationEventAuthority,
)
from scripts.function_tracer_pcode.authority.registry import (
    SatisfactionBindingFactory,
    SealedReasonRegistry,
    SealedRecoveryRegistry,
)
from scripts.function_tracer_pcode.proof.assumptions import (
    AssumptionKind,
    AssumptionPremise,
)
from scripts.function_tracer_pcode.proof.cause_identity import ProofRequirementId


def _json_value(value: Any) -> Any:
    if isinstance(value, Enum):
        return value.value
    if is_dataclass(value):
        return {field.name: _json_value(getattr(value, field.name)) for field in fields(value)}
    if isinstance(value, Mapping):
        if any(type(key) is not str for key in value):
            raise TypeError("strict v2 JSON authority mappings require exact string keys")
        return {key: _json_value(child) for key, child in value.items()}
    if isinstance(value, (tuple, list)):
        return [_json_value(child) for child in value]
    if isinstance(value, (set, frozenset)):
        return sorted((_json_value(child) for child in value), key=authority_digest)
    if isinstance(value, float) and not math.isfinite(value):
        raise TypeError("strict v2 JSON forbids non-finite numbers")
    if value is None or isinstance(value, (str, int, float, bool)):
        return value
    raise TypeError(f"unsupported strict-v2 JSON value: {type(value).__name__}")


def _require_keys(payload: Mapping[str, Any], expected: set[str]) -> None:
    if set(payload) != expected:
        raise ValueError(
            f"strict v2 payload fields differ: missing={sorted(expected - set(payload))}, "
            f"extra={sorted(set(payload) - expected)}"
        )


def _require_exact_string_fields(payload: Mapping[str, Any], names: set[str]) -> None:
    for name in names:
        if type(payload[name]) is not str or not payload[name]:
            raise TypeError(f"strict v2 field {name} must be a non-empty exact string")


def _row_c(payload: Mapping[str, Any]) -> CActiveBaseRow:
    _require_keys(payload, {field.name for field in fields(CActiveBaseRow)})
    return CActiveBaseRow(**payload)


def _row_q(payload: Mapping[str, Any]) -> QOpenBaseRow:
    _require_keys(payload, {field.name for field in fields(QOpenBaseRow)})
    return QOpenBaseRow(**payload)


def _row_eligibility(payload: Mapping[str, Any]) -> BlockerEligibilityBaseRow:
    _require_keys(payload, {field.name for field in fields(BlockerEligibilityBaseRow)})
    return BlockerEligibilityBaseRow(**payload)


def _decode_projection(payload: Mapping[str, Any]) -> VerifiedLifecycleProjection:
    _require_keys(payload, {field.name for field in fields(VerifiedLifecycleProjection)})
    rebuilt = VerifiedLifecycleProjection.seal(
        result_occurrence_id=payload["result_occurrence_id"],
        snapshot_digest=payload["snapshot_digest"],
        c_active_base=tuple(_row_c(row) for row in payload["c_active_base"]),
        q_open_base=tuple(_row_q(row) for row in payload["q_open_base"]),
        blocker_eligibility_base=tuple(
            _row_eligibility(row) for row in payload["blocker_eligibility_base"]
        ),
        satisfaction_projection=payload["satisfaction_projection"],
    )
    if _json_value(rebuilt) != dict(payload):
        raise ValueError("persisted lifecycle projection digest/fields mismatch")
    return rebuilt


def _decode_bound_contract(payload: Mapping[str, Any], codec: "StrictV2JsonCodec"):
    from scripts.function_tracer_pcode.authority.contracts import BoundSatisfactionContract

    _require_keys(payload, {field.name for field in fields(BoundSatisfactionContract)})
    bindings = {}
    for item in payload["slot_bindings"]:
        if type(item) is not list or len(item) != 2 or type(item[0]) is not str:
            raise TypeError("strict v2 slot binding must be [exact-string, requirement]")
        bindings[item[0]] = _decode_requirement(item[1])
    bound = SatisfactionBindingFactory(codec._recovery_registry).bind(
        contract_definition_id=payload["contract_definition_id"],
        contract_version=payload["contract_version"],
        bindings=bindings,
    )
    if _json_value(bound) != dict(payload):
        raise ValueError("persisted bound satisfaction contract differs from registry binding")
    return bound


def _decode_occurrence_authority(
    payload: Mapping[str, Any], codec: "StrictV2JsonCodec"
) -> CauseOccurrenceAuthority:
    _require_keys(payload, {"occurrence", "bound_contract"})
    occurrence = _decode_occurrence(payload["occurrence"])
    bound_payload = payload["bound_contract"]
    bound = None if bound_payload is None else _decode_bound_contract(bound_payload, codec)
    authority = CauseOccurrenceAuthority(occurrence, bound)
    codec._validate_registry_ownership(authority)
    return authority


def _decode_event_payload(
    event_type: EventType, payload: Mapping[str, Any], codec: "StrictV2JsonCodec"
) -> Any:
    if event_type == EventType.CAUSE_OBSERVED:
        _require_keys(payload, {"occurrence_authority"})
        return CauseObservedEventAuthority(
            _decode_occurrence_authority(payload["occurrence_authority"], codec)
        )
    if event_type == EventType.REQUIREMENT_COMPLETED:
        _require_keys(payload, {"completion_receipt"})
        return RequirementCompletedEventAuthority(
            _decode_completion(payload["completion_receipt"])
        )
    if event_type == EventType.CAUSE_TRANSFORMED:
        _require_keys(payload, {"transformation_event", "proof_receipt"})
        return CauseTransformedEventAuthority(
            _decode_transformation(payload["transformation_event"]),
            _decode_transformation_receipt(payload["proof_receipt"]),
        )
    if event_type == EventType.OUTCOME_PRODUCER_ATTEMPT:
        _require_keys(payload, {
            "proof_requirement_id", "stage", "producer_status",
            "producer_attempt_identity", "producer_attempt_ordinal",
            "execution_identity_digest",
        })
        return OutcomeProducerAttemptEventAuthority(**payload)
    if event_type in {EventType.SOLVER_UNKNOWN, EventType.SOLVER_TIMEOUT, EventType.SOLVER_ERROR}:
        legacy_fields = {
            "proof_requirement_id", "solver_invocation_id", "observed_status",
            "configured_timeout_ms",
        }
        receipt_fields = {
            "proof_requirement_id", "execution_receipt_authority",
            "terminal_candidate",
        }
        if set(payload) == legacy_fields:
            return SolverExecutionEventAuthority(**payload)
        _require_keys(payload, receipt_fields)
        receipt = dict(payload["execution_receipt_authority"])
        if "runner_issuer_id" in receipt:
            return GenericReceiptBoundSolverExecutionEventAuthority(
                proof_requirement_id=payload["proof_requirement_id"],
                execution_receipt_authority=receipt,
                terminal_candidate=payload["terminal_candidate"],
            )
        receipt["proof_requirement_identity"] = ProofRequirementId.from_dict(
            receipt["proof_requirement_identity"]
        ).to_dict()
        receipt["function_identity"] = tuple(receipt["function_identity"])
        receipt["input_domain_contract"] = tuple(receipt["input_domain_contract"])
        return ReceiptBoundSolverExecutionEventAuthority(
            proof_requirement_id=payload["proof_requirement_id"],
            execution_receipt_authority=receipt,
            terminal_candidate=payload["terminal_candidate"],
        )
    if event_type == EventType.PROCESS_COMPLETED:
        _require_keys(payload, {
            "proof_requirement_id", "process_invocation_id",
            "execution_receipt_digest",
        })
        return ProcessCompletionEventAuthority(**payload)
    if event_type in {EventType.PROCESS_TIMEOUT, EventType.CANCELLED}:
        _require_keys(payload, {"proof_requirement_id", "process_invocation_id"})
        return ProcessExecutionEventAuthority(**payload)
    if event_type in {EventType.NORMALIZATION_NO_CHANGE, EventType.REWRITE_NO_CHANGE}:
        _require_keys(payload, {"stage_id", "observation_artifact_digest"})
        return StageObservationEventAuthority(**payload)
    if event_type in {EventType.EQ_CLOSURE, EventType.COUNTEREXAMPLE}:
        _require_keys(payload, {"proof_artifact_digest"})
        return DecisiveProofEventAuthority(**payload)
    if event_type == EventType.ERROR:
        _require_keys(payload, {"error_kind", "error_artifact_digest"})
        return ErrorEventAuthority(**payload)
    raise ValueError(f"unsupported event type: {event_type}")


def _decode_stream(
    payload: Mapping[str, Any], codec: "StrictV2JsonCodec"
) -> SealedEventStream:
    _require_keys(payload, {"envelope", "events"})
    envelope_payload = payload["envelope"]
    _require_keys(envelope_payload, {field.name for field in fields(EventStreamEnvelope)})
    if type(envelope_payload["schema_version"]) is not int or envelope_payload["schema_version"] != 2:
        raise TypeError("event envelope schema_version must be exact integer 2")
    envelope = EventStreamEnvelope(**envelope_payload)
    events = []
    for item in payload["events"]:
        _require_keys(item, {"header", "authority_payload", "diagnostic_payload", "authority_digest"})
        header_payload = item["header"]
        _require_keys(header_payload, {field.name for field in fields(EventHeader)})
        if type(header_payload["schema_version"]) is not int or header_payload["schema_version"] != 2:
            raise TypeError("event header schema_version must be exact integer 2")
        header = EventHeader(
            **{
                **header_payload,
                "event_type": EventType(header_payload["event_type"]),
            }
        )
        authority_payload = _decode_event_payload(
            header.event_type, item["authority_payload"], codec
        )
        events.append(RecordedEvent(
            header=header,
            authority_payload=authority_payload,
            diagnostic_payload=canonical_value(item["diagnostic_payload"]),
            authority_digest=item["authority_digest"],
        ))
    stream = SealedEventStream(envelope, tuple(events))
    stream.validate()
    return stream


def _decode_decisive(payload: Mapping[str, Any]) -> DecisiveProofReceipt:
    _require_keys(payload, {field.name for field in fields(DecisiveProofReceipt)})
    _require_exact_string_fields(payload, {
        "result_occurrence_id", "lifecycle_projection_digest",
        "proof_artifact_digest", "receipt_digest",
    })
    receipt = DecisiveProofReceipt(**{**payload, "proof_kind": DecisiveProofKind(payload["proof_kind"])})
    receipt.validate()
    return receipt


def _decode_timeout(payload: Mapping[str, Any]) -> TerminalTimeoutReceipt:
    _require_keys(payload, {field.name for field in fields(TerminalTimeoutReceipt)})
    _require_exact_string_fields(payload, set(payload))
    receipt = TerminalTimeoutReceipt(**payload)
    receipt.validate()
    return receipt


def _decode_error(payload: Mapping[str, Any]) -> ErrorReceipt:
    _require_keys(payload, {field.name for field in fields(ErrorReceipt)})
    _require_exact_string_fields(payload, set(payload))
    receipt = ErrorReceipt(**payload)
    receipt.validate()
    return receipt


def _decode_assumption_premise(payload: Mapping[str, Any]) -> AssumptionPremise:
    _require_keys(payload, {field.name for field in fields(AssumptionPremise)})
    _require_exact_string_fields(payload, {"kind", "subject"})
    if type(payload["schema_version"]) is not int:
        raise TypeError("strict v2 field schema_version must be an exact int")
    if not isinstance(payload["payload"], list):
        raise TypeError("strict v2 assumption payload must be a JSON array of pairs")
    # AssumptionPremise re-normalizes the decoded lists back into its canonical
    # tuple form and rejects any leaf the proof layer does not allow, so a
    # tampered payload cannot round-trip into a premise.
    return AssumptionPremise(
        kind=AssumptionKind(payload["kind"]),
        subject=payload["subject"],
        payload=payload["payload"],
        schema_version=payload["schema_version"],
    )


def _decode_conditional_decisive(
    payload: Mapping[str, Any],
) -> ConditionalDecisiveProofReceipt:
    _require_keys(payload, {field.name for field in fields(ConditionalDecisiveProofReceipt)})
    _require_exact_string_fields(payload, {
        "result_occurrence_id", "lifecycle_projection_digest",
        "proof_artifact_digest", "assumption_set_digest", "receipt_digest",
    })
    if not isinstance(payload["assumption_dependencies"], list):
        raise TypeError("strict v2 assumption dependencies must be a JSON array")
    receipt = ConditionalDecisiveProofReceipt.create(
        result_occurrence_id=payload["result_occurrence_id"],
        lifecycle_projection_digest=payload["lifecycle_projection_digest"],
        proof_kind=ConditionalDecisiveProofKind(payload["proof_kind"]),
        proof_artifact_digest=payload["proof_artifact_digest"],
        assumption_dependencies=tuple(
            _decode_assumption_premise(item)
            for item in payload["assumption_dependencies"]
        ),
    )
    if (
        receipt.assumption_set_digest != payload["assumption_set_digest"]
        or receipt.receipt_digest != payload["receipt_digest"]
    ):
        raise ValueError("persisted conditional proof receipt digest mismatch")
    receipt.validate()
    return receipt


def _decode_conditional_decision(payload: Mapping[str, Any]) -> ConditionalDecisionReceipt:
    _require_keys(payload, {field.name for field in fields(ConditionalDecisionReceipt)})
    _require_exact_string_fields(payload, {
        "result_occurrence_id", "unconditional_receipt_digest",
        "lifecycle_projection_digest", "assumption_set_digest",
        "authority_input_digest", "receipt_digest",
    })
    return ConditionalDecisionReceipt.from_persisted(
        **{
            **payload,
            "conditional_outcome": Outcome(payload["conditional_outcome"]),
            "unconditional_outcome": Outcome(payload["unconditional_outcome"]),
        },
        _codec_token=_CONDITIONAL_DECISION_CODEC_TOKEN,
    )


def _decode_decision(payload: Mapping[str, Any]) -> DecisionReceipt:
    _require_keys(payload, {field.name for field in fields(DecisionReceipt)})
    _require_exact_string_fields(payload, {
        "result_occurrence_id", "lifecycle_projection_digest",
        "authority_input_digest", "receipt_digest",
    })
    return DecisionReceipt.from_persisted(
        **{**payload, "outcome": Outcome(payload["outcome"])},
        _codec_token=_DECISION_RECEIPT_CODEC_TOKEN,
    )


def _decode_census_entry(payload: Mapping[str, Any]) -> CensusEntry:
    _require_keys(payload, {field.name for field in fields(CensusEntry)})
    _require_exact_string_fields(payload, {"result_occurrence_id", "result_artifact_digest"})
    for name in (
        "event_stream_authority_digest", "lifecycle_projection_digest",
        "decision_receipt_digest", "migration_pair_id",
    ):
        if payload[name] is not None and (type(payload[name]) is not str or not payload[name]):
            raise TypeError(f"census entry field {name} must be an optional exact string")
    return CensusEntry(**{**payload, "result_kind": ResultKind(payload["result_kind"])})


def _decode_manifest(payload: Mapping[str, Any]) -> CensusManifest:
    _require_keys(payload, {field.name for field in fields(CensusManifest)})
    if type(payload["schema_version"]) is not int or payload["schema_version"] != 2:
        raise TypeError("census manifest schema_version must be exact integer 2")
    _require_exact_string_fields(payload, {
        "manifest_id", "repository_commit", "analysis_config_digest",
        "manifest_authority_digest",
    })
    observed_digest = payload["manifest_authority_digest"]
    manifest = CensusManifest(
        manifest_id=payload["manifest_id"],
        census_mode=CensusMode(payload["census_mode"]),
        repository_commit=payload["repository_commit"],
        analysis_config_digest=payload["analysis_config_digest"],
        entries=tuple(_decode_census_entry(item) for item in payload["entries"]),
        generated_at=payload["generated_at"],
        schema_version=payload["schema_version"],
    )
    if manifest.manifest_authority_digest != observed_digest:
        raise ValueError("persisted census manifest digest mismatch")
    return manifest


def _decode_cause(payload: Mapping[str, Any]) -> CauseIdV2:
    _require_keys(payload, {field.name for field in fields(CauseIdV2)})
    if type(payload["schema_version"]) is not int or payload["schema_version"] != 2:
        raise TypeError("cause schema_version must be exact integer 2")
    _require_exact_string_fields(payload, {
        "reason_id", "semantic_proposition_digest", "value",
    })
    return CauseIdV2.from_persisted(
        **{**payload, "identity_scope": IdentityScope(payload["identity_scope"])},
        _codec_token=_CAUSE_ID_CODEC_TOKEN,
    )


def _decode_reason(payload: Mapping[str, Any]) -> ReasonDefinition:
    _require_keys(payload, {field.name for field in fields(ReasonDefinition)})
    if type(payload["schema_version"]) is not int or payload["schema_version"] != 2:
        raise TypeError("reason schema_version must be exact integer 2")
    _require_exact_string_fields(payload, {
        "reason_id", "domain", "reason_class", "decision_effect",
        "canonicalization_policy_id",
    })
    for name in ("allowed_target_kinds", "required_evidence_contract", "allowed_proof_kinds"):
        if type(payload[name]) is not list or any(
            type(value) is not str or not value for value in payload[name]
        ):
            raise TypeError(f"reason field {name} must contain exact strings")
    if type(payload["terminal_eligibility"]) is not bool:
        raise TypeError("reason terminal_eligibility must be an exact boolean")
    return ReasonDefinition(**{
        **payload,
        "allowed_target_kinds": frozenset(payload["allowed_target_kinds"]),
        "required_evidence_contract": tuple(payload["required_evidence_contract"]),
        "allowed_proof_kinds": frozenset(payload["allowed_proof_kinds"]),
        "recovery_addressability": RecoveryAddressability(payload["recovery_addressability"]),
    })


def _decode_requirement(payload: Mapping[str, Any]) -> ProofRequirement:
    _require_keys(payload, {field.name for field in fields(ProofRequirement)})
    _require_exact_string_fields(payload, {"requirement_id", "proof_kind"})
    return ProofRequirement(**payload)


def _decode_occurrence(payload: Mapping[str, Any]) -> CauseOccurrence:
    _require_keys(payload, {field.name for field in fields(CauseOccurrence)})
    _require_exact_string_fields(payload, {
        "occurrence_id", "reason_id", "target_id", "target_kind", "evidence_kind",
        "source_snapshot_fingerprint", "producer_id", "attempt_id",
    })
    if type(payload["proof_requirement_ids"]) is not list or any(
        type(value) is not str or not value for value in payload["proof_requirement_ids"]
    ):
        raise TypeError("occurrence proof requirement IDs must be exact strings")
    if type(payload["evidence_refs"]) is not list or any(
        type(value) is not str or not value for value in payload["evidence_refs"]
    ):
        raise TypeError("occurrence evidence refs must be exact strings")
    for name in (
        "bound_satisfaction_contract_id", "normalized_expression_digest",
        "bound_expression_digest",
    ):
        if payload[name] is not None and (type(payload[name]) is not str or not payload[name]):
            raise TypeError(f"occurrence field {name} must be an optional exact string")
    version = payload["bound_satisfaction_contract_version"]
    if version is not None and type(version) is not int:
        raise TypeError("occurrence contract version must be an optional exact integer")
    return CauseOccurrence(**{
        **payload,
        "cause_id": _decode_cause(payload["cause_id"]),
        "identity_scope": IdentityScope(payload["identity_scope"]),
        "proof_requirement_ids": tuple(payload["proof_requirement_ids"]),
        "evidence_refs": tuple(payload["evidence_refs"]),
    })


def _decode_completion(payload: Mapping[str, Any]) -> RequirementCompletionReceipt:
    _require_keys(payload, {field.name for field in fields(RequirementCompletionReceipt)})
    _require_exact_string_fields(payload, {
        "cause_id", "occurrence_id", "proof_requirement_id",
        "bound_satisfaction_contract_id", "bound_expression_digest",
        "proof_artifact_digest", "applicability_receipt",
    })
    if type(payload["bound_satisfaction_contract_version"]) is not int:
        raise TypeError("completion contract version must be an exact integer")
    return RequirementCompletionReceipt(**payload)


def _decode_transformation(payload: Mapping[str, Any]) -> CauseTransformationEvent:
    _require_keys(payload, {field.name for field in fields(CauseTransformationEvent)})
    _require_exact_string_fields(payload, {
        "transformation_proof_receipt_id", "recognizing_stage",
        "source_snapshot_fingerprint",
    })
    for name in ("replaced_occurrence_ids", "replacement_occurrence_ids"):
        if type(payload[name]) is not list or any(
            type(value) is not str or not value for value in payload[name]
        ):
            raise TypeError(f"transformation field {name} must contain exact strings")
    return CauseTransformationEvent(**{
        **payload,
        "transformation_kind": TransformationKind(payload["transformation_kind"]),
        "replaced_occurrence_ids": tuple(payload["replaced_occurrence_ids"]),
        "replacement_occurrence_ids": tuple(payload["replacement_occurrence_ids"]),
    })


def _decode_transformation_receipt(payload: Mapping[str, Any]) -> CauseTransformationProofReceipt:
    _require_keys(payload, {field.name for field in fields(CauseTransformationProofReceipt)})
    _require_exact_string_fields(payload, {"receipt_id", "source_snapshot_fingerprint"})
    if type(payload["exact_completion_transfer"]) is not bool:
        raise TypeError("transformation completion transfer flag must be exact boolean")
    return CauseTransformationProofReceipt(**{
        **payload,
        "replaced_occurrence_bindings": tuple(tuple(item) for item in payload["replaced_occurrence_bindings"]),
        "replacement_occurrence_bindings": tuple(tuple(item) for item in payload["replacement_occurrence_bindings"]),
        "requirement_mapping": tuple(tuple(item) for item in payload["requirement_mapping"]),
    })


_DECODERS = MappingProxyType({
    "ReasonDefinition": _decode_reason,
    "CauseIdV2": _decode_cause,
    "ProofRequirement": _decode_requirement,
    "SealedEventStream": lambda payload: payload,
    "VerifiedLifecycleProjection": _decode_projection,
    "CActiveBaseRow": _row_c,
    "QOpenBaseRow": _row_q,
    "BlockerEligibilityBaseRow": _row_eligibility,
    "DecisiveProofReceipt": _decode_decisive,
    "TerminalTimeoutReceipt": _decode_timeout,
    "ErrorReceipt": _decode_error,
    "DecisionReceipt": _decode_decision,
    "AssumptionPremise": _decode_assumption_premise,
    "ConditionalDecisiveProofReceipt": _decode_conditional_decisive,
    "ConditionalDecisionReceipt": _decode_conditional_decision,
    "CauseOccurrenceAuthority": lambda payload: payload,
    "RequirementCompletionReceipt": _decode_completion,
    "CauseTransformationEvent": _decode_transformation,
    "CauseTransformationProofReceipt": _decode_transformation_receipt,
    "CensusEntry": _decode_census_entry,
    "CensusManifest": _decode_manifest,
})


def _strict_object_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate strict v2 JSON key: {key}")
        result[key] = value
    return result


def _reject_json_constant(value):
    raise ValueError(f"non-finite strict v2 JSON constant: {value}")


class StrictV2JsonCodec:
    """No aliases, suffix normalization, unknown fields, or legacy fallback."""

    def __init__(
        self,
        *,
        reason_registry: SealedReasonRegistry,
        recovery_registry: SealedRecoveryRegistry,
    ) -> None:
        if not isinstance(reason_registry, SealedReasonRegistry):
            raise TypeError("strict v2 codec requires a sealed reason registry")
        if not isinstance(recovery_registry, SealedRecoveryRegistry):
            raise TypeError("strict v2 codec requires a sealed recovery registry")
        self._reason_registry = reason_registry
        self._recovery_registry = recovery_registry

    def _validate_registry_ownership(self, value: Any) -> None:
        if isinstance(value, SealedEventStream):
            for event in value.events:
                if isinstance(event.authority_payload, CauseObservedEventAuthority):
                    self._validate_registry_ownership(
                        event.authority_payload.occurrence_authority
                    )
        elif isinstance(value, ReasonDefinition):
            if self._reason_registry.get(value.reason_id) != value:
                raise ValueError("reason definition differs from sealed registry")
        elif isinstance(value, CauseIdV2):
            self._reason_registry.get(value.reason_id)
        elif isinstance(value, CauseOccurrence):
            definition = self._reason_registry.get(value.reason_id)
            if value.target_kind not in definition.allowed_target_kinds:
                raise ValueError("occurrence target differs from sealed reason registry")
            if value.bound_satisfaction_contract_id is not None:
                contract = self._recovery_registry.get(
                    value.bound_satisfaction_contract_id,
                    int(value.bound_satisfaction_contract_version),
                )
                if contract.normalized_expression_digest != value.normalized_expression_digest:
                    raise ValueError("occurrence satisfaction definition differs from registry")
        elif isinstance(value, CauseOccurrenceAuthority):
            occurrence = value.occurrence
            definition = self._reason_registry.get(occurrence.reason_id)
            bound = value.bound_contract
            if bound is None:
                occurrence.validate_against(definition, None)
            else:
                contract = self._recovery_registry.get(
                    bound.contract_definition_id, bound.contract_version
                )
                bound.validate_against(contract)
                occurrence.validate_against(definition, bound)
        elif isinstance(value, CActiveBaseRow):
            definition = self._reason_registry.get(value.reason_id)
            if (
                value.domain != definition.domain
                or value.decision_effect != definition.decision_effect
                or value.target_kind not in definition.allowed_target_kinds
            ):
                raise ValueError("active cause metadata differs from sealed reason registry")
        elif isinstance(value, VerifiedLifecycleProjection):
            value.validate()
            definitions_by_cause = {}
            for row in value.c_active_base:
                self._validate_registry_ownership(row)
                definitions_by_cause[
                    (row.result_occurrence_id, row.occurrence_id, row.cause_id)
                ] = self._reason_registry.get(row.reason_id)
            for row in value.q_open_base:
                definition = definitions_by_cause[
                    (row.result_occurrence_id, row.occurrence_id, row.cause_id)
                ]
                if row.proof_kind not in definition.allowed_proof_kinds:
                    raise ValueError("open requirement proof kind differs from reason registry")

    @staticmethod
    def _validate_structural_authority(value: Any) -> None:
        if isinstance(value, SealedEventStream):
            value.validate()
        elif isinstance(value, VerifiedLifecycleProjection):
            value.validate()
        elif isinstance(value, (DecisiveProofReceipt, TerminalTimeoutReceipt, ErrorReceipt, DecisionReceipt)):
            value.validate()
        elif isinstance(value, (ConditionalDecisiveProofReceipt, ConditionalDecisionReceipt)):
            value.validate()
        elif isinstance(value, AssumptionPremise):
            # Re-running the proof-layer normalization proves the premise is
            # already canonical; a non-canonical one would not compare equal.
            rebuilt = AssumptionPremise(
                kind=value.kind, subject=value.subject,
                payload=value.payload, schema_version=value.schema_version,
            )
            if rebuilt != value:
                raise ValueError("assumption premise is not in canonical form")
        elif isinstance(value, CensusManifest):
            rebuilt = CensusManifest(
                value.manifest_id, value.census_mode, value.repository_commit,
                value.analysis_config_digest, value.entries, generated_at=value.generated_at,
                schema_version=value.schema_version,
            )
            if rebuilt != value:
                raise ValueError("census manifest is not a valid sealed authority object")
        elif isinstance(value, CensusEntry):
            rebuilt = CensusEntry(**{
                field.name: getattr(value, field.name) for field in fields(CensusEntry)
            })
            if rebuilt != value:
                raise ValueError("census entry is not a valid authority object")

    def dumps(self, value: Any) -> str:
        object_type = type(value).__name__
        if object_type not in _DECODERS:
            raise TypeError(f"unregistered strict v2 object type: {object_type}")
        self._validate_structural_authority(value)
        self._validate_registry_ownership(value)
        payload = _json_value(value)
        envelope = {
            "schema_version": 2,
            "object_type": object_type,
            "payload": payload,
            "payload_digest": authority_digest(payload),
        }
        return json.dumps(envelope, sort_keys=True, separators=(",", ":"), ensure_ascii=False)

    def loads(self, raw_json_text: str) -> Any:
        envelope = json.loads(
            raw_json_text,
            object_pairs_hook=_strict_object_pairs,
            parse_constant=_reject_json_constant,
        )
        if not isinstance(envelope, Mapping):
            raise ValueError("strict v2 envelope must be an object")
        _require_keys(envelope, {"schema_version", "object_type", "payload", "payload_digest"})
        if type(envelope["schema_version"]) is not int or envelope["schema_version"] != 2:
            raise ValueError("unsupported strict v2 codec schema")
        object_type = envelope["object_type"]
        if object_type not in _DECODERS:
            raise ValueError(f"unknown strict v2 object type: {object_type!r}")
        payload = envelope["payload"]
        if not isinstance(payload, Mapping):
            raise ValueError("strict v2 payload must be an object")
        if authority_digest(payload) != envelope["payload_digest"]:
            raise ValueError("strict v2 payload digest mismatch")
        if object_type == "SealedEventStream":
            value = _decode_stream(payload, self)
        elif object_type == "CauseOccurrenceAuthority":
            value = _decode_occurrence_authority(payload, self)
        else:
            value = _DECODERS[object_type](payload)
        self._validate_structural_authority(value)
        self._validate_registry_ownership(value)
        return value
