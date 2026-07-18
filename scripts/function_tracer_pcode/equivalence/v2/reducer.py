"""Outcome-independent replay of one sealed v2 lifecycle event stream."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping, Optional, Sequence, Tuple

from .contracts import (
    BlockerEligibilityBaseRow,
    CActiveBaseRow,
    CauseOccurrenceAuthority,
    QOpenBaseRow,
    RecoveryAddressability,
    RequirementCompletionReceipt,
    VerifiedLifecycleProjection,
    VerifiedLifecyclePrefixProjection,
    _PREFIX_PROJECTION_FACTORY_TOKEN,
    authority_digest,
    canonical_value,
)
from .frontier import (
    FrontierBudgetExceeded,
    FrontierEvaluationBudget,
    evaluate_live_frontier,
)
from .registry import SealedReasonRegistry, SealedRecoveryRegistry
from .stream import (
    CauseObservedEventAuthority,
    CauseTransformedEventAuthority,
    EventType,
    EventStreamEnvelope,
    EventStreamPrefixView,
    GenericReceiptBoundSolverExecutionEventAuthority,
    OutcomeProducerAttemptEventAuthority,
    ProcessCompletionEventAuthority,
    ProcessExecutionEventAuthority,
    ReceiptBoundSolverExecutionEventAuthority,
    RequirementCompletedEventAuthority,
    SealedEventStream,
    SolverExecutionEventAuthority,
)


class ShadowEvidenceIncomplete(ValueError):
    """No canonical lifecycle artifact may be emitted for this stream."""


@dataclass(frozen=True)
class CauseLifecycleSnapshot:
    result_occurrence_id: str
    source_snapshot_fingerprint: str
    event_stream_authority_digest: str
    occurrence_authorities: Tuple[CauseOccurrenceAuthority, ...]
    active_occurrence_ids: Tuple[str, ...]
    completion_receipts: Tuple[RequirementCompletionReceipt, ...]
    transformation_receipt_ids: Tuple[str, ...]
    execution_event_digests: Tuple[str, ...]
    terminal_timeout_event_digests: Tuple[str, ...]
    terminal_timeout_event_bindings: Tuple[Tuple[str, str], ...]
    decisive_proof_artifact_digests: Tuple[str, ...]
    decisive_proof_event_bindings: Tuple[Tuple[str, str], ...]
    error_artifact_digests: Tuple[str, ...]
    error_event_bindings: Tuple[Tuple[str, str], ...]
    snapshot_digest: str

    @classmethod
    def seal(
        cls,
        *,
        result_occurrence_id: str,
        source_snapshot_fingerprint: str,
        event_stream_authority_digest: str,
        occurrence_authorities: Sequence[CauseOccurrenceAuthority],
        active_occurrence_ids: Sequence[str],
        completion_receipts: Sequence[RequirementCompletionReceipt],
        transformation_receipt_ids: Sequence[str],
        execution_event_digests: Sequence[str],
        terminal_timeout_event_digests: Sequence[str],
        terminal_timeout_event_bindings: Sequence[Tuple[str, str]],
        decisive_proof_artifact_digests: Sequence[str],
        decisive_proof_event_bindings: Sequence[Tuple[str, str]],
        error_artifact_digests: Sequence[str],
        error_event_bindings: Sequence[Tuple[str, str]],
    ) -> "CauseLifecycleSnapshot":
        occurrences = tuple(sorted(
            occurrence_authorities, key=lambda item: item.occurrence.occurrence_id
        ))
        active = tuple(sorted(active_occurrence_ids))
        completions = tuple(sorted(
            completion_receipts,
            key=lambda item: (item.occurrence_id, item.proof_requirement_id),
        ))
        transformations = tuple(transformation_receipt_ids)
        executions = tuple(execution_event_digests)
        terminal_timeouts = tuple(terminal_timeout_event_digests)
        terminal_timeout_bindings = tuple(terminal_timeout_event_bindings)
        decisive_proofs = tuple(decisive_proof_artifact_digests)
        decisive_bindings = tuple(decisive_proof_event_bindings)
        errors = tuple(error_artifact_digests)
        error_bindings = tuple(error_event_bindings)
        if len({item.occurrence.occurrence_id for item in occurrences}) != len(occurrences):
            raise ValueError("duplicate lifecycle occurrence identity")
        if not set(active).issubset({item.occurrence.occurrence_id for item in occurrences}):
            raise ValueError("active lifecycle occurrence is undeclared")
        payload = {
            "result_occurrence_id": result_occurrence_id,
            "source_snapshot_fingerprint": source_snapshot_fingerprint,
            "event_stream_authority_digest": event_stream_authority_digest,
            "occurrence_authorities": occurrences,
            "active_occurrence_ids": active,
            "completion_receipts": completions,
            "transformation_receipt_ids": transformations,
            "execution_event_digests": executions,
            "terminal_timeout_event_digests": terminal_timeouts,
            "terminal_timeout_event_bindings": terminal_timeout_bindings,
            "decisive_proof_artifact_digests": decisive_proofs,
            "decisive_proof_event_bindings": decisive_bindings,
            "error_artifact_digests": errors,
            "error_event_bindings": error_bindings,
        }
        return cls(
            result_occurrence_id,
            source_snapshot_fingerprint,
            event_stream_authority_digest,
            occurrences,
            active,
            completions,
            transformations,
            executions,
            terminal_timeouts,
            terminal_timeout_bindings,
            decisive_proofs,
            decisive_bindings,
            errors,
            error_bindings,
            authority_digest(payload),
        )

    def validate(self) -> None:
        rebuilt = CauseLifecycleSnapshot.seal(
            result_occurrence_id=self.result_occurrence_id,
            source_snapshot_fingerprint=self.source_snapshot_fingerprint,
            event_stream_authority_digest=self.event_stream_authority_digest,
            occurrence_authorities=self.occurrence_authorities,
            active_occurrence_ids=self.active_occurrence_ids,
            completion_receipts=self.completion_receipts,
            transformation_receipt_ids=self.transformation_receipt_ids,
            execution_event_digests=self.execution_event_digests,
            terminal_timeout_event_digests=self.terminal_timeout_event_digests,
            terminal_timeout_event_bindings=self.terminal_timeout_event_bindings,
            decisive_proof_artifact_digests=self.decisive_proof_artifact_digests,
            decisive_proof_event_bindings=self.decisive_proof_event_bindings,
            error_artifact_digests=self.error_artifact_digests,
            error_event_bindings=self.error_event_bindings,
        )
        if rebuilt != self:
            raise ValueError("lifecycle snapshot digest/fields mismatch")


@dataclass(frozen=True)
class ShadowReductionResult:
    snapshot: CauseLifecycleSnapshot
    projection: VerifiedLifecycleProjection


class ShadowLifecycleReducer:
    def __init__(
        self,
        *,
        reason_registry: SealedReasonRegistry,
        recovery_registry: SealedRecoveryRegistry,
        frontier_budget: FrontierEvaluationBudget = FrontierEvaluationBudget(),
    ) -> None:
        self._reason_registry = reason_registry
        self._recovery_registry = recovery_registry
        self._frontier_budget = frontier_budget

    def _validate_occurrence_authority(self, authority: CauseOccurrenceAuthority) -> None:
        occurrence = authority.occurrence
        definition = self._reason_registry.get(occurrence.reason_id)
        bound = authority.bound_contract
        if bound is None:
            occurrence.validate_against(definition, None)
            return
        contract = self._recovery_registry.get(
            bound.contract_definition_id, bound.contract_version
        )
        bound.validate_against(contract)
        occurrence.validate_against(definition, bound)

    def _frontier(
        self,
        authority: CauseOccurrenceAuthority,
        completed: set[str],
    ):
        bound = authority.bound_contract
        if bound is None:
            return None
        definition = self._recovery_registry.get(
            bound.contract_definition_id, bound.contract_version
        )
        try:
            return evaluate_live_frontier(
                definition, bound, completed, self._frontier_budget
            )
        except FrontierBudgetExceeded as exc:
            raise ShadowEvidenceIncomplete("frontier evaluation budget exhausted") from exc

    def replay(self, stream: SealedEventStream) -> ShadowReductionResult:
        ordered_stream = SealedEventStream(
            stream.envelope,
            tuple(sorted(stream.events, key=lambda item: item.header.sequence_number)),
        )
        try:
            ordered_stream.validate()
        except (TypeError, ValueError) as exc:
            raise ShadowEvidenceIncomplete("invalid sealed event stream") from exc

        occurrences: dict[str, CauseOccurrenceAuthority] = {}
        active: set[str] = set()
        completed: dict[str, set[str]] = {}
        completion_receipts: list[RequirementCompletionReceipt] = []
        transformation_receipt_ids: list[str] = []
        execution_event_digests: list[str] = []
        terminal_timeout_event_digests: list[str] = []
        terminal_timeout_event_bindings: list[tuple[str, str]] = []
        decisive_proof_artifact_digests: list[str] = []
        decisive_proof_event_bindings: list[tuple[str, str]] = []
        error_artifact_digests: list[str] = []
        error_event_bindings: list[tuple[str, str]] = []

        def live_matches(requirement_id: str) -> list[str]:
            matches = []
            for occurrence_id in sorted(active):
                frontier = self._frontier(
                    occurrences[occurrence_id], completed[occurrence_id]
                )
                if frontier is not None and requirement_id in frontier.live_open_requirements:
                    matches.append(occurrence_id)
            return matches

        for recorded in ordered_stream.events:
            event_type = recorded.header.event_type
            payload = recorded.authority_payload
            if event_type == EventType.CAUSE_OBSERVED:
                assert isinstance(payload, CauseObservedEventAuthority)
                authority = payload.occurrence_authority
                try:
                    self._validate_occurrence_authority(authority)
                except (KeyError, TypeError, ValueError) as exc:
                    raise ShadowEvidenceIncomplete(
                        "cause observation is not registry/binding valid"
                    ) from exc
                occurrence = authority.occurrence
                if occurrence.source_snapshot_fingerprint != stream.envelope.source_snapshot_fingerprint:
                    raise ShadowEvidenceIncomplete("occurrence source snapshot differs from stream")
                if occurrence.occurrence_id in occurrences:
                    raise ShadowEvidenceIncomplete("duplicate occurrence observation")
                occurrences[occurrence.occurrence_id] = authority
                active.add(occurrence.occurrence_id)
                completed[occurrence.occurrence_id] = set()
            elif event_type == EventType.REQUIREMENT_COMPLETED:
                assert isinstance(payload, RequirementCompletedEventAuthority)
                receipt = payload.completion_receipt
                if receipt.occurrence_id not in active:
                    raise ShadowEvidenceIncomplete("completion targets inactive/unknown occurrence")
                authority = occurrences[receipt.occurrence_id]
                frontier = self._frontier(authority, completed[receipt.occurrence_id])
                if authority.bound_contract is None or frontier is None:
                    raise ShadowEvidenceIncomplete("completion targets unbound occurrence")
                try:
                    receipt.validate_against(
                        authority.occurrence,
                        authority.bound_contract,
                        frontier.live_open_requirements,
                    )
                except (TypeError, ValueError) as exc:
                    raise ShadowEvidenceIncomplete("invalid completion receipt") from exc
                completed[receipt.occurrence_id].add(receipt.proof_requirement_id)
                completion_receipts.append(receipt)
                after = self._frontier(authority, completed[receipt.occurrence_id])
                if after is not None and after.satisfied:
                    active.remove(receipt.occurrence_id)
            elif event_type == EventType.CAUSE_TRANSFORMED:
                assert isinstance(payload, CauseTransformedEventAuthority)
                event = payload.transformation_event
                receipt = payload.proof_receipt
                old_ids = set(event.replaced_occurrence_ids)
                new_ids = set(event.replacement_occurrence_ids)
                if not old_ids.issubset(active):
                    raise ShadowEvidenceIncomplete("transformation replaces inactive/unknown occurrence")
                if not new_ids.issubset(occurrences):
                    raise ShadowEvidenceIncomplete("replacement occurrence was not observed first")
                if event.source_snapshot_fingerprint != stream.envelope.source_snapshot_fingerprint:
                    raise ShadowEvidenceIncomplete("transformation source snapshot differs")
                try:
                    receipt.validate_event(event)
                except (TypeError, ValueError) as exc:
                    raise ShadowEvidenceIncomplete("invalid atomic transformation receipt") from exc
                expected_old_bindings = {
                    (
                        occurrence_id,
                        occurrences[occurrence_id].occurrence.cause_id.value,
                    )
                    for occurrence_id in old_ids
                }
                expected_new_bindings = {
                    (
                        occurrence_id,
                        occurrences[occurrence_id].occurrence.cause_id.value,
                    )
                    for occurrence_id in new_ids
                }
                if set(receipt.replaced_occurrence_bindings) != expected_old_bindings:
                    raise ShadowEvidenceIncomplete(
                        "transformation old occurrence/cause binding differs from state"
                    )
                if set(receipt.replacement_occurrence_bindings) != expected_new_bindings:
                    raise ShadowEvidenceIncomplete(
                        "transformation new occurrence/cause binding differs from state"
                    )
                transfers: list[tuple[str, str]] = []
                if receipt.exact_completion_transfer:
                    mapping = dict(receipt.requirement_mapping)
                    mapping_owners: dict[str, tuple[str, str]] = {}
                    for old_requirement, new_requirement in receipt.requirement_mapping:
                        old_owners = [
                            occurrence_id for occurrence_id in old_ids
                            if old_requirement
                            in occurrences[occurrence_id].occurrence.proof_requirement_ids
                        ]
                        new_owners = [
                            occurrence_id for occurrence_id in new_ids
                            if new_requirement
                            in occurrences[occurrence_id].occurrence.proof_requirement_ids
                        ]
                        if len(old_owners) != 1 or len(new_owners) != 1:
                            raise ShadowEvidenceIncomplete(
                                "completion mapping requirement owner is not unique/declared"
                            )
                        mapping_owners[old_requirement] = (
                            new_owners[0], new_requirement
                        )
                    completed_old = {
                        requirement
                        for occurrence_id in old_ids
                        for requirement in completed[occurrence_id]
                    }
                    for old_requirement in completed_old:
                        if old_requirement not in mapping:
                            raise ShadowEvidenceIncomplete("exact completion transfer is incomplete")
                        transfers.append(mapping_owners[old_requirement])
                active.difference_update(old_ids)
                for occurrence_id, requirement_id in transfers:
                    completed[occurrence_id].add(requirement_id)
                for occurrence_id in new_ids.intersection(active):
                    frontier = self._frontier(
                        occurrences[occurrence_id], completed[occurrence_id]
                    )
                    if frontier is not None and frontier.satisfied:
                        active.remove(occurrence_id)
                transformation_receipt_ids.append(receipt.receipt_id)
            elif type(payload) is OutcomeProducerAttemptEventAuthority:
                matches = live_matches(payload.proof_requirement_id)
                if len(matches) != 1:
                    raise ShadowEvidenceIncomplete(
                        "outcome producer attempt requirement is not uniquely live"
                    )
            elif isinstance(
                payload, (
                    SolverExecutionEventAuthority,
                    ReceiptBoundSolverExecutionEventAuthority,
                    GenericReceiptBoundSolverExecutionEventAuthority,
                    ProcessCompletionEventAuthority,
                    ProcessExecutionEventAuthority,
                )
            ):
                matches = live_matches(payload.proof_requirement_id)
                if len(matches) != 1:
                    raise ShadowEvidenceIncomplete(
                        "execution event requirement is not uniquely live"
                    )
                execution_event_digests.append(recorded.authority_digest)
                if event_type in {EventType.SOLVER_TIMEOUT, EventType.PROCESS_TIMEOUT}:
                    terminal_timeout_event_digests.append(recorded.authority_digest)
                    terminal_timeout_event_bindings.append((
                        recorded.authority_digest, payload.proof_requirement_id
                    ))
            elif event_type in {EventType.EQ_CLOSURE, EventType.COUNTEREXAMPLE}:
                decisive_proof_artifact_digests.append(payload.proof_artifact_digest)
                decisive_proof_event_bindings.append((
                    event_type.value, payload.proof_artifact_digest
                ))
            elif event_type == EventType.ERROR:
                error_artifact_digests.append(payload.error_artifact_digest)
                error_event_bindings.append((
                    payload.error_kind, payload.error_artifact_digest
                ))

        c_active = []
        q_open = []
        satisfaction_rows = []
        for occurrence_id, authority in sorted(occurrences.items()):
            occurrence = authority.occurrence
            definition = self._reason_registry.get(occurrence.reason_id)
            is_active = occurrence_id in active
            frontier = self._frontier(authority, completed[occurrence_id])
            live = () if frontier is None else tuple(sorted(frontier.live_open_requirements))
            satisfied = False if frontier is None else frontier.satisfied
            if is_active:
                c_active.append(CActiveBaseRow(
                    stream.envelope.result_occurrence_id,
                    occurrence_id,
                    occurrence.cause_id.value,
                    occurrence.reason_id,
                    definition.domain,
                    definition.decision_effect,
                    occurrence.target_kind,
                ))
                if (
                    definition.recovery_addressability
                    == RecoveryAddressability.REQUIREMENT_REQUIRED
                    and not live
                ):
                    raise ShadowEvidenceIncomplete(
                        "required active occurrence has empty live frontier"
                    )
                if authority.bound_contract is not None:
                    by_id = {
                        requirement.requirement_id: requirement
                        for _, requirement in authority.bound_contract.slot_bindings
                    }
                    for requirement_id in live:
                        q_open.append(QOpenBaseRow(
                            stream.envelope.result_occurrence_id,
                            occurrence_id,
                            occurrence.cause_id.value,
                            requirement_id,
                            by_id[requirement_id].proof_kind,
                            authority_digest({
                                "semantic_target": canonical_value(
                                    by_id[requirement_id].semantic_target_key
                                )
                            }),
                        ))
            satisfaction_rows.append({
                "occurrence_id": occurrence_id,
                "cause_id": occurrence.cause_id.value,
                "contract_definition_id": occurrence.bound_satisfaction_contract_id,
                "contract_version": occurrence.bound_satisfaction_contract_version,
                "bound_expression_digest": occurrence.bound_expression_digest,
                "completed_requirement_ids": tuple(sorted(completed[occurrence_id])),
                "live_requirement_ids": live,
                "satisfied": satisfied,
                "active": is_active,
            })

        snapshot = CauseLifecycleSnapshot.seal(
            result_occurrence_id=stream.envelope.result_occurrence_id,
            source_snapshot_fingerprint=stream.envelope.source_snapshot_fingerprint,
            event_stream_authority_digest=stream.envelope.authority_chain_digest,
            occurrence_authorities=tuple(occurrences.values()),
            active_occurrence_ids=active,
            completion_receipts=completion_receipts,
            transformation_receipt_ids=transformation_receipt_ids,
            execution_event_digests=execution_event_digests,
            terminal_timeout_event_digests=terminal_timeout_event_digests,
            terminal_timeout_event_bindings=terminal_timeout_event_bindings,
            decisive_proof_artifact_digests=decisive_proof_artifact_digests,
            decisive_proof_event_bindings=decisive_proof_event_bindings,
            error_artifact_digests=error_artifact_digests,
            error_event_bindings=error_event_bindings,
        )
        projection = VerifiedLifecycleProjection.seal(
            result_occurrence_id=stream.envelope.result_occurrence_id,
            snapshot_digest=snapshot.snapshot_digest,
            c_active_base=c_active,
            q_open_base=q_open,
            blocker_eligibility_base=tuple(
                BlockerEligibilityBaseRow(
                    stream.envelope.result_occurrence_id,
                    authority.occurrence.occurrence_id,
                    authority.occurrence.cause_id.value,
                )
                for authority in occurrences.values()
            ),
            satisfaction_projection={
                "occurrences": tuple(satisfaction_rows),
                "execution_event_digests": tuple(execution_event_digests),
                "transformation_receipt_ids": tuple(transformation_receipt_ids),
            },
        )
        snapshot.validate()
        projection.validate()
        return ShadowReductionResult(snapshot, projection)

    def replay_prefix(
        self, prefix: EventStreamPrefixView
    ) -> VerifiedLifecyclePrefixProjection:
        if type(prefix) is not EventStreamPrefixView:
            raise TypeError("prefix replay requires exact recorder prefix authority")
        prefix.validate()
        internal_stream = SealedEventStream(
            EventStreamEnvelope(
                prefix.stream_id,
                prefix.result_occurrence_id,
                prefix.source_snapshot_fingerprint,
                1,
                len(prefix.events),
                len(prefix.events),
                prefix.prefix_chain_digest,
                True,
            ),
            prefix.events,
        )
        reduction = self.replay(internal_stream)
        return VerifiedLifecyclePrefixProjection._issue(
            reduction.projection,
            prefix.prefix_chain_digest,
            _factory_token=_PREFIX_PROJECTION_FACTORY_TOKEN,
        )
