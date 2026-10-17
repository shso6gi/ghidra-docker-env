# -*- coding: utf-8 -*-
"""Cross-side identity domain: the sealed reason for an EQ that identified left and right
values by an owner-free key the final input correspondence does not justify (plan v4 PR-P).

owner を含まない key（parameter の index・名前、Method-B key など）で左右を同一視した closure は、
最終 ``InputCorrespondence`` が位置どおり・同じ名前・全幅の等式のときだけ EQ の根拠になる
（規則の owner は ``proof/formula/input_correspondence/gate.py``）。最終の EQ gate（``orchestration.
veto_unproven_cross_side_identity``。``checker/preflight_gate``・frame の無い互換・legacy の経路・
pairwise の後の昇格が呼ぶ）がその条件を満たさない EQ を止めたとき、この domain の cause を 1 つ観測する。

* reason は 1 つ（``cross_side_identity_unproven``）。site の gate の拒否（closure を作らない・等式を
  足さない）は cause を作らない: 拒否された pair は、本当に欠けている証明（loop の関係など）の reason
  で UNKNOWN になる。この cause は「EQ の直前まで来た owner を含まない同一視を、最終 gate が止めた」
  ことだけを表す。
* ``decision_effect`` は ``blocks_equivalence``。止めたのは EQ の根拠だけで、反例（NOT_EQ）の側の
  証明には関与しない。
* 回復は relation を通した翻訳（PR-H の ``CorrespondenceScope``）で、ここでは requirement の枠だけを作る。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from scripts.function_tracer_pcode.authority.contracts import (
    CauseOccurrence,
    CauseOccurrenceAuthority,
    IdentityScope,
    ProofRequirement,
    ReasonDefinition,
    RecoveryAddressability,
    RequirementSlotDefinition,
    SatisfactionContractDefinition,
    authority_digest,
    canonical_value,
    requirement_slot,
)
from scripts.function_tracer_pcode.authority.registry import (
    SatisfactionBindingFactory,
    SealedReasonRegistry,
    SealedRecoveryRegistry,
    SemanticCauseIdentityFactory,
)
from scripts.function_tracer_pcode.authority.lifecycle.stream import (
    CauseObservedEventAuthority,
    EventIntent,
    EventType,
)


CROSS_SIDE_IDENTITY_DOMAIN = "cross_side_identity"
CROSS_SIDE_IDENTITY_REASON_ID = "cross_side_identity_unproven"
CROSS_SIDE_IDENTITY_PROOF_KIND = "cross_side_identity_correspondence"
CROSS_SIDE_IDENTITY_CONTRACT_ID = "cross-side-identity-recovery"
CROSS_SIDE_IDENTITY_TARGET_KIND = "pair_comparison_identification"
CROSS_SIDE_IDENTITY_PRODUCER_ID = "cross-side-identity-final-gate-v1"
#: producer site（Phase 7 manifest の site id。``emit_cross_side_identity_signal`` の呼び手は 1 つ）。
CROSS_SIDE_IDENTITY_SITE_ID = "pairwise-cross-side-identity-veto"
CROSS_SIDE_IDENTITY_IDENTITY_SCOPE = IdentityScope.RELATIONAL
#: session ごとに「どの比較の拒否を **これまでに一度でも** 観測したか」の履歴（reducer の重複
#: occurrence 拒否を避けるためだけの key。cause が active かは lifecycle projection が正本）。
CROSS_SIDE_IDENTITY_LEDGER_KEY = "cross_side_identity_ever_observed"

CROSS_SIDE_IDENTITY_REASON_REGISTRY = SealedReasonRegistry.build((
    ReasonDefinition(
        CROSS_SIDE_IDENTITY_REASON_ID, CROSS_SIDE_IDENTITY_DOMAIN, "proof_obligation",
        "blocks_equivalence", frozenset((CROSS_SIDE_IDENTITY_TARGET_KIND,)),
        ("owner_free_closures", "input_correspondence"),
        frozenset((CROSS_SIDE_IDENTITY_PROOF_KIND,)), True,
        "cross_side_identity_v1", RecoveryAddressability.REQUIREMENT_REQUIRED,
    ),
))
CROSS_SIDE_IDENTITY_RECOVERY_REGISTRY = SealedRecoveryRegistry.build((
    SatisfactionContractDefinition(
        CROSS_SIDE_IDENTITY_CONTRACT_ID, 1,
        (RequirementSlotDefinition(
            "correspondence", frozenset((CROSS_SIDE_IDENTITY_PROOF_KIND,))
        ),),
        requirement_slot("correspondence"),
    ),
))


@dataclass(frozen=True)
class CrossSideIdentityBlockerSignal:
    """最終の EQ gate が止めた 1 つの比較（branch・generation）の owner を含まない同一視。"""

    comparison_session_id: str
    branch_id: str
    generation: int
    input_correspondence_digest: str
    owner_free_sources: tuple[str, ...]
    evidence_refs: tuple[str, ...] = ()
    producer_id: str = CROSS_SIDE_IDENTITY_PRODUCER_ID

    def __post_init__(self) -> None:
        for value in (
            self.comparison_session_id, self.branch_id,
            self.input_correspondence_digest, self.producer_id,
        ):
            if type(value) is not str or not value:
                raise TypeError("cross-side identity signal authority is incomplete")
        if isinstance(self.generation, bool) or not isinstance(self.generation, int):
            raise TypeError("cross-side identity signal generation is not exact")
        object.__setattr__(self, "generation", int(self.generation))
        for name in ("owner_free_sources", "evidence_refs"):
            values = tuple(getattr(self, name))
            if any(type(item) is not str or not item for item in values):
                raise TypeError("cross-side identity signal evidence is incomplete")
            object.__setattr__(self, name, values)
        if not self.owner_free_sources:
            raise ValueError("cross-side identity signal requires an owner-free source")

    def _phase7_signal_authority(self) -> Mapping[str, Any]:
        return {
            "reason_id": CROSS_SIDE_IDENTITY_REASON_ID,
            "target": self.cause_target(),
            "evidence_refs": self.evidence_refs,
            "producer_id": self.producer_id,
        }

    def cause_target(self) -> tuple:
        return canonical_value((
            "cross_side_identity_v1",
            self.comparison_session_id,
            self.branch_id,
            self.generation,
            self.input_correspondence_digest,
            self.owner_free_sources,
        ))


class CrossSideIdentityPilotEncoder:
    """1 つの拒否を CAUSE_OBSERVED 1 つにする（同じ比較の拒否の繰り返しは 1 つの cause）。"""

    def __init__(self) -> None:
        self._cause_factory = SemanticCauseIdentityFactory(CROSS_SIDE_IDENTITY_REASON_REGISTRY)
        self._binding_factory = SatisfactionBindingFactory(CROSS_SIDE_IDENTITY_RECOVERY_REGISTRY)

    @staticmethod
    def _observed_ledger(session: Any) -> set:
        ledger = session.domain_signal_state.get(CROSS_SIDE_IDENTITY_LEDGER_KEY)
        if ledger is None:
            return set()
        if type(ledger) is not set:
            raise TypeError("cross-side identity observed ledger is not an exact set")
        return ledger

    def has_observed(self, session: Any, signal: Any) -> bool:
        if type(signal) is not CrossSideIdentityBlockerSignal:
            return False
        return self._authority(session, signal).occurrence.occurrence_id in self._observed_ledger(session)

    def commit_emitted_signal(
        self, session: Any, signal: Any, intents: tuple[EventIntent, ...],
    ) -> None:
        if type(signal) is not CrossSideIdentityBlockerSignal or not intents:
            return
        session.domain_signal_state.setdefault(CROSS_SIDE_IDENTITY_LEDGER_KEY, set()).add(
            self._authority(session, signal).occurrence.occurrence_id
        )

    def authority_for_signal(self, session: Any, signal: CrossSideIdentityBlockerSignal) -> CauseOccurrenceAuthority:
        return self._authority(session, signal)

    def __call__(self, session: Any, signal: CrossSideIdentityBlockerSignal) -> tuple[EventIntent, ...]:
        if type(signal) is not CrossSideIdentityBlockerSignal:
            raise TypeError("cross-side identity encoder requires an exact signal")
        authority = self._authority(session, signal)
        if authority.occurrence.occurrence_id in self._observed_ledger(session):
            return ()
        return (EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),)

    def _authority(self, session: Any, signal: CrossSideIdentityBlockerSignal) -> CauseOccurrenceAuthority:
        target = signal.cause_target()
        cause = self._cause_factory.create(
            reason_id=CROSS_SIDE_IDENTITY_REASON_ID,
            identity_scope=CROSS_SIDE_IDENTITY_IDENTITY_SCOPE,
            target_kind=CROSS_SIDE_IDENTITY_TARGET_KIND,
            canonical_target_key=target,
            missing_semantic_fact=("owner_free_identification_justified", signal.owner_free_sources),
            semantic_proposition=("left_right_identified_under_input_correspondence", signal.branch_id),
            observation_surface=(signal.input_correspondence_digest, signal.evidence_refs),
            active_semantic_precondition=("final_equivalence_gate_refused", signal.generation),
            correspondence_contract=None,
        )
        requirement = ProofRequirement(
            "cross-side-identity-q-" + authority_digest(target)[:32],
            CROSS_SIDE_IDENTITY_PROOF_KIND, target,
        )
        bound = self._binding_factory.bind(
            contract_definition_id=CROSS_SIDE_IDENTITY_CONTRACT_ID,
            contract_version=1, bindings={"correspondence": requirement},
        )
        occurrence = CauseOccurrence(
            "cross-side-identity-occ-" + authority_digest({
                "result_occurrence_id": session.identity.result_occurrence_id,
                "target": target,
            })[:32],
            cause, CROSS_SIDE_IDENTITY_REASON_ID, authority_digest(target),
            CROSS_SIDE_IDENTITY_TARGET_KIND, CROSS_SIDE_IDENTITY_IDENTITY_SCOPE,
            bound.contract_definition_id, bound.contract_version,
            bound.normalized_expression_digest, bound.bound_expression_digest,
            (requirement.requirement_id,),
            (*signal.owner_free_sources, *signal.evidence_refs),
            "cross_side_identity_producer_signal",
            session.identity.source_snapshot_fingerprint, signal.producer_id,
            session.identity.execution_identity_digest,
        )
        return CauseOccurrenceAuthority(occurrence, bound)


__all__ = (
    "CROSS_SIDE_IDENTITY_DOMAIN",
    "CROSS_SIDE_IDENTITY_IDENTITY_SCOPE",
    "CROSS_SIDE_IDENTITY_PRODUCER_ID",
    "CROSS_SIDE_IDENTITY_REASON_ID",
    "CROSS_SIDE_IDENTITY_REASON_REGISTRY",
    "CROSS_SIDE_IDENTITY_RECOVERY_REGISTRY",
    "CROSS_SIDE_IDENTITY_SITE_ID",
    "CrossSideIdentityBlockerSignal",
    "CrossSideIdentityPilotEncoder",
)
