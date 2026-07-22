"""Typed Phase 6.1 SAT-safety cause and decisive-counterexample encoder."""

from __future__ import annotations

from typing import Any

from .contracts import (
    CauseOccurrence,
    CauseOccurrenceAuthority,
    IdentityScope,
    ProofRequirement,
    ReasonDefinition,
    RecoveryAddressability,
    RequirementCompletionReceipt,
    RequirementSlotDefinition,
    SatisfactionContractDefinition,
    authority_digest,
    requirement_slot,
)
from .production_signals import (
    SAT_SAFETY_TYPED_REASON_IDS,
    SafeCounterexampleProductionSignal,
    SatSafetyBlockerProductionSignal,
)
from .registry import (
    SatisfactionBindingFactory,
    SealedReasonRegistry,
    SealedRecoveryRegistry,
    SemanticCauseIdentityFactory,
)
from .stream import (
    CauseObservedEventAuthority,
    DecisiveProofEventAuthority,
    EventIntent,
    EventType,
    RequirementCompletedEventAuthority,
)


SAT_SAFETY_CONTRACT = SatisfactionContractDefinition(
    "counterexample-safety-recovery",
    1,
    (RequirementSlotDefinition("safety", frozenset(("counterexample_safety",))),),
    requirement_slot("safety"),
)


def _reason(reason_id: str) -> ReasonDefinition:
    return ReasonDefinition(
        reason_id,
        "sat_safety",
        "semantic_safety_gate",
        "blocks_disequivalence",
        frozenset(("counterexample_safety_gate",)),
        ("safety_gate_target", "counterexample_evidence"),
        frozenset(("counterexample_safety",)),
        True,
        "sat-safety-v2",
        RecoveryAddressability.REQUIREMENT_REQUIRED,
    )


SAT_SAFETY_REASON_REGISTRY = SealedReasonRegistry.build(
    _reason(reason_id) for reason_id in sorted(SAT_SAFETY_TYPED_REASON_IDS)
)
SAT_SAFETY_RECOVERY_REGISTRY = SealedRecoveryRegistry.build((SAT_SAFETY_CONTRACT,))


class SatSafetyPilotEncoder:
    def __init__(self) -> None:
        self._cause_factory = SemanticCauseIdentityFactory(SAT_SAFETY_REASON_REGISTRY)
        self._binding_factory = SatisfactionBindingFactory(SAT_SAFETY_RECOVERY_REGISTRY)

    @staticmethod
    def _state(session: Any) -> tuple[set[str], set[str]]:
        observed = session.domain_signal_state.setdefault("sat_safety_observed", set())
        completed = session.domain_signal_state.setdefault("sat_safety_completed", set())
        return observed, completed

    def _authority(self, session: Any, signal: SatSafetyBlockerProductionSignal):
        cause = self._cause_factory.create(
            reason_id=signal.reason_id,
            identity_scope=IdentityScope.RELATIONAL,
            target_kind="counterexample_safety_gate",
            canonical_target_key=signal.canonical_target_key,
            missing_semantic_fact=signal.missing_semantic_fact,
            semantic_proposition=("counterexample_is_safe_and_decisive", signal.reason_id),
            observation_surface=("analysis_safety", "case_replay", "same_function_replay"),
            active_semantic_precondition=("sat_candidate_observed", True),
            correspondence_contract=("ordered_function_pair",),
        )
        requirement_id = "sat-safety-" + authority_digest({
            "cause_id": cause.value,
            "proof_kind": "counterexample_safety",
        })[:32]
        requirement = ProofRequirement(
            requirement_id,
            "counterexample_safety",
            ("cause", cause.value),
        )
        bound = self._binding_factory.bind(
            contract_definition_id=SAT_SAFETY_CONTRACT.contract_definition_id,
            contract_version=SAT_SAFETY_CONTRACT.contract_version,
            bindings={"safety": requirement},
        )
        occurrence_id = "sat-safety-occ-" + authority_digest({
            "cause_id": cause.value,
            "session": session.identity.result_occurrence_id,
        })[:32]
        occurrence = CauseOccurrence(
            occurrence_id,
            cause,
            signal.reason_id,
            authority_digest(signal.canonical_target_key),
            "counterexample_safety_gate",
            IdentityScope.RELATIONAL,
            bound.contract_definition_id,
            bound.contract_version,
            bound.normalized_expression_digest,
            bound.bound_expression_digest,
            (requirement_id,),
            signal.evidence_refs,
            "sat_safety_producer_signal",
            session.identity.source_snapshot_fingerprint,
            signal.producer_id,
            session.identity.execution_identity_digest,
        )
        return CauseOccurrenceAuthority(occurrence, bound), requirement_id

    def authority_for_signal(
        self, session: Any, signal: SatSafetyBlockerProductionSignal,
    ) -> CauseOccurrenceAuthority:
        if type(signal) is not SatSafetyBlockerProductionSignal:
            raise TypeError("SAT safety authority requires an exact blocker signal")
        return self._authority(session, signal)[0]

    def register_transformed_observation(
        self, session: Any, signal: SatSafetyBlockerProductionSignal,
    ) -> None:
        authority, _ = self._authority(session, signal)
        observed, _completed = self._state(session)
        occurrence_id = authority.occurrence.occurrence_id
        if occurrence_id in observed:
            raise ValueError("SAT safety transformed observation is duplicated")
        observed.add(occurrence_id)

    def __call__(self, session: Any, signal: Any) -> tuple[EventIntent, ...]:
        if type(signal) is SafeCounterexampleProductionSignal:
            return (EventIntent(
                EventType.COUNTEREXAMPLE,
                DecisiveProofEventAuthority(signal.proof_artifact_digest),
            ),)
        if type(signal) is not SatSafetyBlockerProductionSignal:
            return ()
        authority, requirement_id = self._authority(session, signal)
        occurrence_key = authority.occurrence.occurrence_id
        observed_occurrences, completed_occurrences = self._state(session)
        if signal.action == "OBSERVED":
            if occurrence_key in observed_occurrences:
                return ()
            observed_occurrences.add(occurrence_key)
            return (EventIntent(
                EventType.CAUSE_OBSERVED,
                CauseObservedEventAuthority(authority),
            ),)
        if occurrence_key not in observed_occurrences:
            raise ValueError("SAT safety completion has no observed active occurrence")
        if occurrence_key in completed_occurrences:
            return ()
        completed_occurrences.add(occurrence_key)
        receipt = RequirementCompletionReceipt(
            authority.occurrence.cause_id.value,
            authority.occurrence.occurrence_id,
            requirement_id,
            authority.bound_contract.contract_definition_id,
            authority.bound_contract.contract_version,
            authority.bound_contract.bound_expression_digest,
            str(signal.proof_artifact_digest),
            authority_digest({
                "proof_artifact_digest": signal.proof_artifact_digest,
                "cause_id": authority.occurrence.cause_id.value,
            }),
        )
        return (EventIntent(
            EventType.REQUIREMENT_COMPLETED,
            RequirementCompletedEventAuthority(receipt),
        ),)

    def has_observed(self, session: Any, signal: Any) -> bool:
        if type(signal) is not SatSafetyBlockerProductionSignal:
            return False
        authority, _ = self._authority(session, signal)
        observed_occurrences, _ = self._state(session)
        return authority.occurrence.occurrence_id in observed_occurrences
