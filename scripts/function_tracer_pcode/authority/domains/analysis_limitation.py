# -*- coding: utf-8 -*-
"""Analysis-limitation domain: one sealed reason for an exhausted analysis budget.

Issue #125 PR-125-A。`core/errors.py` の `AnalysisLimitation` を判定 authority
へ載せるための **最小の** producer 経路（domain 1 / sealed reason 1 /
producer site 1）。

`decision_effect` を `blocks_decision` にするのは、予算切れで解析を打ち切った
場合 EQ 側・NOT_EQ 側のどちらの証明も完了していないため。片方向だけを塞ぐ
根拠が無い。これは「新規に観測した限界そのもの」に対する effect であって、
**既存 cause へ帰属した限界には適用しない**（既存 cause の
`decision_effect` をそのまま尊重する。
`authority/decision/limitation_attribution.py`）。

未解消のまま残れば cause は active のままなので、`finalize_decision` は
EQ / NOT_EQ のどちらにも進まない（fail-closed）。予算内で再解析できたことの
証明（discharge）は #106 の責務で、ここでは requirement の枠だけを作る。
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


ANALYSIS_LIMITATION_DOMAIN = "analysis_limitation"
ANALYSIS_BUDGET_REASON_ID = "analysis_budget_exceeded"
ANALYSIS_BUDGET_PROOF_KIND = "analysis_budget_proof"
ANALYSIS_BUDGET_CONTRACT_ID = "analysis-budget-recovery"
ANALYSIS_LIMITATION_TARGET_KIND = "analysis_limitation"
ANALYSIS_LIMITATION_PRODUCER_ID = "analysis-limitation-producer-v1"
#: cause identity の名前空間。限界ごとに別 cause にする（1 つに丸めない）。
ANALYSIS_LIMITATION_TARGET_NAMESPACE = "analysis_limitation_v1"
#: この domain が発行できる identity scope（manifest の slot と一致させる）。
ANALYSIS_LIMITATION_IDENTITY_SCOPE = IdentityScope.RELATIONAL
#: session ごとに「どの限界を既に観測したか」を持つ ledger の key。
ANALYSIS_LIMITATION_LEDGER_KEY = "analysis_limitation_observed"

ANALYSIS_LIMITATION_REASON_REGISTRY = SealedReasonRegistry.build((
    ReasonDefinition(
        ANALYSIS_BUDGET_REASON_ID, ANALYSIS_LIMITATION_DOMAIN, "proof_obligation",
        "blocks_decision", frozenset((ANALYSIS_LIMITATION_TARGET_KIND,)),
        ("limitation_site", "analysis_budget"),
        frozenset((ANALYSIS_BUDGET_PROOF_KIND,)), True,
        "analysis_limitation_v1", RecoveryAddressability.REQUIREMENT_REQUIRED,
    ),
))
ANALYSIS_LIMITATION_RECOVERY_REGISTRY = SealedRecoveryRegistry.build((
    SatisfactionContractDefinition(
        ANALYSIS_BUDGET_CONTRACT_ID, 1,
        (RequirementSlotDefinition(
            "budget", frozenset((ANALYSIS_BUDGET_PROOF_KIND,))
        ),),
        requirement_slot("budget"),
    ),
))


@dataclass(frozen=True)
class AnalysisLimitationBlockerSignal:
    """One observed analysis limitation that owns a sealed limitation reason."""

    declared_reason_id: str
    limitation_site: str
    canonical_target_key: Any
    missing_semantic_fact: Any
    evidence_refs: tuple[str, ...] = ()
    producer_id: str = ANALYSIS_LIMITATION_PRODUCER_ID

    def __post_init__(self) -> None:
        for value in (
            self.declared_reason_id, self.limitation_site, self.producer_id,
        ):
            if type(value) is not str or not value:
                raise TypeError("analysis limitation signal authority is incomplete")
        object.__setattr__(
            self, "canonical_target_key", canonical_value(self.canonical_target_key)
        )
        object.__setattr__(
            self, "missing_semantic_fact", canonical_value(self.missing_semantic_fact)
        )
        object.__setattr__(self, "evidence_refs", tuple(self.evidence_refs))
        if any(type(item) is not str or not item for item in self.evidence_refs):
            raise TypeError("analysis limitation evidence authority is incomplete")
        if self.declared_reason_id not in {
            item.reason_id
            for item in ANALYSIS_LIMITATION_REASON_REGISTRY.snapshot()
        }:
            raise ValueError("analysis limitation signal reason is not domain-owned")

    def _phase7_signal_authority(self) -> Mapping[str, Any]:
        """Project only semantic signal data into Phase 7 authority."""
        return {
            "declared_reason_id": self.declared_reason_id,
            "limitation_site": self.limitation_site,
            "canonical_target_key": self.canonical_target_key,
            "missing_semantic_fact": self.missing_semantic_fact,
            "evidence_refs": self.evidence_refs,
            "producer_id": self.producer_id,
        }

    def cause_target(self) -> tuple:
        """限界ごとに別 cause になる canonical target key。"""
        return (
            ANALYSIS_LIMITATION_TARGET_NAMESPACE,
            self.declared_reason_id,
            self.limitation_site,
            self.canonical_target_key,
        )


class AnalysisLimitationPilotEncoder:
    """Encode one limitation observation into a single CAUSE_OBSERVED intent.

    Observing the *same* limitation twice in one session (a retry phase hits the
    same budget at the same site) is one cause, not two. The reducer rejects a
    repeated occurrence id outright, so the repeat is dropped here and the
    producer site reports the cause as already materialized.
    """

    def __init__(self) -> None:
        self._cause_factory = SemanticCauseIdentityFactory(
            ANALYSIS_LIMITATION_REASON_REGISTRY
        )
        self._binding_factory = SatisfactionBindingFactory(
            ANALYSIS_LIMITATION_RECOVERY_REGISTRY
        )

    @staticmethod
    def _observed_ledger(session: Any) -> set:
        ledger = session.domain_signal_state.get(ANALYSIS_LIMITATION_LEDGER_KEY)
        if ledger is None:
            return set()
        if type(ledger) is not set:
            raise TypeError("analysis limitation observed ledger is not an exact set")
        return ledger

    def has_observed(self, session: Any, signal: Any) -> bool:
        """Report whether this exact limitation already has a committed cause."""
        if type(signal) is not AnalysisLimitationBlockerSignal:
            return False
        occurrence_id = self.authority_for_signal(
            session, signal,
        ).occurrence.occurrence_id
        return occurrence_id in self._observed_ledger(session)

    def commit_emitted_signal(
        self, session: Any, signal: Any, intents: tuple[EventIntent, ...],
    ) -> None:
        if type(signal) is not AnalysisLimitationBlockerSignal or not intents:
            return
        occurrence_id = self.authority_for_signal(
            session, signal,
        ).occurrence.occurrence_id
        session.domain_signal_state.setdefault(
            ANALYSIS_LIMITATION_LEDGER_KEY, set()
        ).add(occurrence_id)

    def authority_for_signal(
        self, session: Any, signal: AnalysisLimitationBlockerSignal,
    ) -> CauseOccurrenceAuthority:
        """Resolve the occurrence authority without emitting an event."""
        return self._authority(session, signal)

    def __call__(
        self, session: Any, signal: AnalysisLimitationBlockerSignal,
    ) -> tuple[EventIntent, ...]:
        if type(signal) is not AnalysisLimitationBlockerSignal:
            raise TypeError("analysis limitation encoder requires an exact signal")
        authority = self._authority(session, signal)
        if authority.occurrence.occurrence_id in self._observed_ledger(session):
            return ()
        return (EventIntent(
            EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority),
        ),)

    def _authority(
        self, session: Any, signal: AnalysisLimitationBlockerSignal,
    ) -> CauseOccurrenceAuthority:
        target = signal.cause_target()
        cause = self._cause_factory.create(
            reason_id=signal.declared_reason_id,
            identity_scope=ANALYSIS_LIMITATION_IDENTITY_SCOPE,
            target_kind=ANALYSIS_LIMITATION_TARGET_KIND,
            canonical_target_key=target,
            missing_semantic_fact=signal.missing_semantic_fact,
            semantic_proposition=(
                "analysis_completed_within_budget",
                signal.declared_reason_id,
                signal.limitation_site,
            ),
            observation_surface=(signal.limitation_site, signal.evidence_refs),
            active_semantic_precondition=(
                "analysis_limitation_observed", signal.declared_reason_id,
            ),
            correspondence_contract=None,
        )
        requirement = ProofRequirement(
            "analysis-limitation-q-" + authority_digest(target)[:32],
            ANALYSIS_BUDGET_PROOF_KIND, target,
        )
        bound = self._binding_factory.bind(
            contract_definition_id=ANALYSIS_BUDGET_CONTRACT_ID,
            contract_version=1, bindings={"budget": requirement},
        )
        occurrence = CauseOccurrence(
            "analysis-limitation-occ-" + authority_digest({
                "result_occurrence_id": session.identity.result_occurrence_id,
                "target": target,
            })[:32],
            cause, signal.declared_reason_id, authority_digest(target),
            ANALYSIS_LIMITATION_TARGET_KIND, ANALYSIS_LIMITATION_IDENTITY_SCOPE,
            bound.contract_definition_id, bound.contract_version,
            bound.normalized_expression_digest, bound.bound_expression_digest,
            (requirement.requirement_id,),
            (signal.limitation_site, *signal.evidence_refs),
            "analysis_limitation_producer_signal",
            session.identity.source_snapshot_fingerprint, signal.producer_id,
            session.identity.execution_identity_digest,
        )
        return CauseOccurrenceAuthority(occurrence, bound)


@dataclass(frozen=True)
class AnalysisLimitationProducerSiteSpec:
    """Sealed Phase 7 producer-site contract for the limitation lifecycle."""

    site_id: str
    producer_id: str
    disposition: str
    reason_ids: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if (
            type(self.site_id) is not str
            or not self.site_id
            or type(self.producer_id) is not str
            or not self.producer_id
            or self.disposition != "ELIGIBLE"
            or type(self.reason_ids) is not tuple
            or not self.reason_ids
            or any(type(item) is not str or not item for item in self.reason_ids)
        ):
            raise ValueError("analysis-limitation producer-site contract is invalid")


ANALYSIS_LIMITATION_OBSERVED_SITE = AnalysisLimitationProducerSiteSpec(
    "analysis-limitation-observed",
    ANALYSIS_LIMITATION_PRODUCER_ID,
    "ELIGIBLE",
    (ANALYSIS_BUDGET_REASON_ID,),
)

ANALYSIS_LIMITATION_PRODUCER_SITE_SPECS = (ANALYSIS_LIMITATION_OBSERVED_SITE,)


def observe_analysis_limitation(
    *,
    reason_id: str,
    limitation_site: str,
    target_key: Any = (),
    missing_semantic_fact: Any = (),
    evidence_refs: tuple[str, ...] = (),
) -> int:
    """この domain が所有する限界を 1 件観測する（唯一の emit 呼び出し）。

    戻り値は **その限界の cause が session に materialize されている数**（0 か 1）で、
    追加された event 数ではない。同じ限界を同じ session で 2 度観測した場合、
    新しい event は作られないが cause は既に active なので 1 を返す。pilot session
    が無ければ 0（strict no-op）。呼び出し側は 1 でないときに **帰属できなかった**
    とみなし、fail-closed で ERROR に落とす。
    """
    # Deferred import: `production_signals` はこの module の signal 型を
    # import するので、module top で読むと循環する。
    from scripts.function_tracer_pcode.authority.lifecycle.production_context import (
        active_production_pilot_session,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        emit_analysis_limitation_signal,
    )

    signal = AnalysisLimitationBlockerSignal(
        declared_reason_id=reason_id,
        limitation_site=limitation_site,
        canonical_target_key=target_key,
        missing_semantic_fact=missing_semantic_fact,
        evidence_refs=tuple(evidence_refs),
    )
    emitted = int(emit_analysis_limitation_signal(
        signal,
        producer_site_manifest_id=ANALYSIS_LIMITATION_OBSERVED_SITE.site_id,
    ))
    if emitted:
        return emitted
    session = active_production_pilot_session()
    if session is None:
        return 0
    observed = getattr(session.domain_signal_encoder, "has_observed", None)
    return 1 if callable(observed) and observed(session, signal) else 0
