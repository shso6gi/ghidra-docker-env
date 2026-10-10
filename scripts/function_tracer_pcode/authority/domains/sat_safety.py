"""Typed Phase 6.1 SAT-safety cause and decisive-counterexample encoder."""

from __future__ import annotations

from typing import Any

from scripts.function_tracer_pcode.authority.contracts import (
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
from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
    SafeCounterexampleProductionSignal,
    SatSafetyBlockerProductionSignal,
)
from scripts.function_tracer_pcode.proof.sat_safety_resolution import (
    SAT_SAFETY_TYPED_REASON_IDS,
)
from scripts.function_tracer_pcode.authority.registry import (
    SatisfactionBindingFactory,
    SealedReasonRegistry,
    SealedRecoveryRegistry,
    SemanticCauseIdentityFactory,
)
from scripts.function_tracer_pcode.authority.lifecycle.stream import (
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
    def _committed_ledger(session: Any, key: str) -> set[str]:
        ledger = session.domain_signal_state.get(key)
        if ledger is None:
            return set()
        if type(ledger) is not set:
            raise TypeError(f"SAT safety committed ledger is not an exact set: {key}")
        return ledger

    def _authority(self, session: Any, signal: SatSafetyBlockerProductionSignal):
        # identity は検証済みの blocker からしか作らない。重複判定・deferred の登録・
        # 完了の照合はすべてこの identity を使うので、不整合な対（構築の迂回を含む）は
        # どの経路でも identity より前に止まる（plan v4 I5）。
        signal.blocker
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

    def commit_transformed_observation(
        self, session: Any, signal: SatSafetyBlockerProductionSignal,
    ) -> None:
        """Commit a transformed cause through the same canonical ledger callback."""

        intents = tuple(self(session, signal))
        if (
            len(intents) != 1
            or intents[0].event_type is not EventType.CAUSE_OBSERVED
        ):
            raise ValueError("SAT safety transformed observation is duplicated")
        self.commit_emitted_signal(session, signal, intents)

    def __call__(self, session: Any, signal: Any) -> tuple[EventIntent, ...]:
        if type(signal) is SafeCounterexampleProductionSignal:
            if not signal.validates():
                raise ValueError(
                    "safe counterexample signal lacks validated receipt authority"
                )
            if session.domain_signal_state.get(
                "sat_safety_safe_counterexample_committed"
            ):
                return ()
            return (EventIntent(
                EventType.COUNTEREXAMPLE,
                DecisiveProofEventAuthority(signal.proof_artifact_digest),
            ),)
        if type(signal) is not SatSafetyBlockerProductionSignal:
            return ()
        authority, requirement_id = self._authority(session, signal)
        occurrence_key = authority.occurrence.occurrence_id
        observed_occurrences = self._committed_ledger(
            session, "sat_safety_observed"
        )
        completed_occurrences = self._committed_ledger(
            session, "sat_safety_completed"
        )
        if signal.action == "OBSERVED":
            if occurrence_key in observed_occurrences:
                # 同じ identity の再観測は、記録した観測の言い直しのときだけ重複。
                # 別の根拠は衝突として拒否する（generic な route でも黙って捨てない）。
                signal.require_restates(self._recorded_observation(session, occurrence_key))
                return ()
            intents = (EventIntent(
                EventType.CAUSE_OBSERVED,
                CauseObservedEventAuthority(authority),
            ),)
            action = "OBSERVED"
        elif occurrence_key not in observed_occurrences:
            raise ValueError("SAT safety completion has no observed active occurrence")
        elif occurrence_key in completed_occurrences:
            return ()
        else:
            # 許可は記録した観測の blocker で決める（完了の signal の主張を信じない）。
            # 拒否は例外として session が domain signal の失敗に記録する（plan v4 I5）。
            signal.require_completes(self._recorded_observation(session, occurrence_key))
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
            intents = (EventIntent(
                EventType.REQUIREMENT_COMPLETED,
                RequirementCompletedEventAuthority(receipt),
            ),)
            action = "COMPLETED"
        pending_key = "sat_safety_pending_emission_transactions"
        pending = session.domain_signal_state.setdefault(pending_key, {})
        if type(pending) is not dict:
            raise TypeError("SAT safety pending transaction ledger is not exact")
        if id(signal) in pending:
            raise ValueError("SAT safety signal already owns an emission transaction")
        pending[id(signal)] = (intents, action, occurrence_key)
        return intents

    def commit_emitted_signal(
        self, session: Any, signal: Any, intents: tuple[EventIntent, ...],
    ) -> None:
        if type(signal) is SafeCounterexampleProductionSignal:
            if len(intents) != 1 or intents[0].event_type is not EventType.COUNTEREXAMPLE:
                raise ValueError("safe counterexample emission transaction is invalid")
            if session.domain_signal_state.get(
                "sat_safety_safe_counterexample_committed"
            ):
                raise ValueError("safe counterexample was already committed")
            session.domain_signal_state[
                "sat_safety_safe_counterexample_committed"
            ] = signal.proof_artifact_digest
            return
        if type(signal) is not SatSafetyBlockerProductionSignal:
            return
        pending_key = "sat_safety_pending_emission_transactions"
        pending = session.domain_signal_state.get(pending_key)
        if pending is None:
            return
        if type(pending) is not dict:
            raise TypeError("SAT safety pending transaction ledger is not exact")
        try:
            expected_intents, action, occurrence_key = pending[id(signal)]
        except KeyError as exc:
            raise ValueError("SAT safety emission transaction is missing") from exc
        if tuple(intents) != expected_intents:
            raise ValueError("SAT safety emission transaction intents changed")
        ledger_key = (
            "sat_safety_observed"
            if action == "OBSERVED"
            else "sat_safety_completed"
        )
        ledger = session.domain_signal_state.setdefault(ledger_key, set())
        if type(ledger) is not set:
            raise TypeError("SAT safety committed ledger is not an exact set")
        if occurrence_key in ledger:
            raise ValueError("SAT safety transaction duplicates committed state")
        ledger.add(occurrence_key)
        if action == "OBSERVED":
            observed = session.domain_signal_state.setdefault(
                "sat_safety_observed_signals", {}
            )
            if type(observed) is not dict:
                raise TypeError("SAT safety observed signal ledger is not exact")
            prior = observed.setdefault(occurrence_key, signal)
            if prior != signal:
                raise ValueError("SAT safety observed signal authority collided")
        pending.pop(id(signal))
        if not pending:
            session.domain_signal_state.pop(pending_key, None)

    def rollback_emitted_signal(self, session: Any, signal: Any) -> None:
        if type(signal) is not SatSafetyBlockerProductionSignal:
            return
        pending_key = "sat_safety_pending_emission_transactions"
        pending = session.domain_signal_state.get(pending_key)
        if pending is None:
            return
        if type(pending) is not dict:
            raise TypeError("SAT safety pending transaction ledger is not exact")
        pending.pop(id(signal), None)
        if not pending:
            session.domain_signal_state.pop(pending_key, None)

    @staticmethod
    def _recorded_observation(session: Any, occurrence_key: str) -> SatSafetyBlockerProductionSignal:
        observed = session.domain_signal_state.get("sat_safety_observed_signals", {})
        if type(observed) is not dict:
            raise TypeError("SAT safety observed signal ledger is not exact")
        try:
            return observed[occurrence_key]
        except KeyError as exc:
            raise ValueError("SAT safety completion has no recorded observation") from exc

    def has_observed(self, session: Any, signal: Any) -> bool:
        if type(signal) is not SatSafetyBlockerProductionSignal:
            return False
        authority, _ = self._authority(session, signal)
        observed_occurrences = self._committed_ledger(
            session, "sat_safety_observed"
        )
        occurrence_key = authority.occurrence.occurrence_id
        if occurrence_key not in observed_occurrences:
            return False
        if signal.action == "OBSERVED":
            # 重複と答えてよいのは、記録した観測の言い直しだけ。別の根拠は衝突
            # （``ValueError``）で、呼び手は黙って捨てずに失敗として記録する。
            signal.require_restates(self._recorded_observation(session, occurrence_key))
        return True
