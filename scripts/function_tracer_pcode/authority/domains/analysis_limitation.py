# -*- coding: utf-8 -*-
"""Analysis-limitation domain: sealed reasons for an exhausted analysis budget.

Issue #125 PR-125-A。`core/errors.py` の `AnalysisLimitation` を判定 authority
へ載せるための **最小の** producer 経路（domain 1 / producer site 1）。sealed
reason は 2 つ: 時間・段数の予算（`analysis_budget_exceeded`、#125）と式の
大きさの予算（`expression_size_budget_exceeded`、#22 PR-22-D）。どちらも同じ
site・同じ encoder・同じ回復契約を通る（reason が違うだけ）。

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
from typing import Any, Mapping, Optional

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
#: Issue #22 PR-22-D: 式の大きさの予算（展開・solver 向け描画・直列化）を超えて
#: 打ち切った限界。`core/errors.ExpressionSizeBudgetExceeded.REASON_ID` と同じ値。
EXPRESSION_SIZE_BUDGET_REASON_ID = "expression_size_budget_exceeded"
ANALYSIS_BUDGET_PROOF_KIND = "analysis_budget_proof"
ANALYSIS_BUDGET_CONTRACT_ID = "analysis-budget-recovery"
ANALYSIS_LIMITATION_TARGET_KIND = "analysis_limitation"
ANALYSIS_LIMITATION_PRODUCER_ID = "analysis-limitation-producer-v1"
#: cause identity の名前空間。限界ごとに別 cause にする（1 つに丸めない）。
ANALYSIS_LIMITATION_TARGET_NAMESPACE = "analysis_limitation_v1"
#: この domain が発行できる identity scope（manifest の slot と一致させる）。
ANALYSIS_LIMITATION_IDENTITY_SCOPE = IdentityScope.RELATIONAL
#: session ごとに「どの限界を **これまでに一度でも** 観測したか」を持つ ledger の key。
#: これは reducer の重複 occurrence 拒否を避けるためだけの履歴で、
#: **その cause が今も active かどうかは一切表さない**（discharge 済みの cause も
#: 載ったまま）。active かどうかは常に現在の lifecycle projection の
#: `c_active_base` が正本（`authority/decision/limitation_attribution.py`）。
ANALYSIS_LIMITATION_LEDGER_KEY = "analysis_limitation_ever_observed"

ANALYSIS_LIMITATION_REASON_REGISTRY = SealedReasonRegistry.build((
    ReasonDefinition(
        ANALYSIS_BUDGET_REASON_ID, ANALYSIS_LIMITATION_DOMAIN, "proof_obligation",
        "blocks_decision", frozenset((ANALYSIS_LIMITATION_TARGET_KIND,)),
        ("limitation_site", "analysis_budget"),
        frozenset((ANALYSIS_BUDGET_PROOF_KIND,)), True,
        "analysis_limitation_v1", RecoveryAddressability.REQUIREMENT_REQUIRED,
    ),
    # 予算超過も時間切れと同じく EQ 側・NOT_EQ 側どちらの証明も完了していない
    # ので `blocks_decision`。回復の契約（予算内で解析し直せたことの証明）も
    # 同じ `analysis-budget-recovery` を共有する。
    ReasonDefinition(
        EXPRESSION_SIZE_BUDGET_REASON_ID, ANALYSIS_LIMITATION_DOMAIN,
        "proof_obligation", "blocks_decision",
        frozenset((ANALYSIS_LIMITATION_TARGET_KIND,)),
        ("limitation_site", "expression_size_budget"),
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
    same budget at the same site) is one cause, not two: the reducer rejects a
    repeated occurrence id outright, so the repeat is dropped here.

    Dropping the repeat says nothing about whether that cause is still active.
    The producer site reports the occurrence id and the decision layer confirms
    it against `c_active_base`; a limitation whose cause was discharged is not
    re-materialized by this ledger.
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
        """Report whether this exact limitation was **ever** observed in this session.

        This is the reducer's duplicate-occurrence guard, not an activeness
        answer: an occurrence whose requirement has been discharged stays in the
        ledger while its cause is no longer in `c_active_base`. Callers that need
        "is there an unresolved cause for this limitation" must read the current
        lifecycle projection instead.
        """
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
    (ANALYSIS_BUDGET_REASON_ID, EXPRESSION_SIZE_BUDGET_REASON_ID),
)

ANALYSIS_LIMITATION_PRODUCER_SITE_SPECS = (ANALYSIS_LIMITATION_OBSERVED_SITE,)


def analysis_limitation_signal(
    *,
    reason_id: str,
    limitation_site: str,
    target_key: Any = (),
    missing_semantic_fact: Any = (),
    evidence_refs: tuple[str, ...] = (),
) -> AnalysisLimitationBlockerSignal:
    """この domain の限界 1 件の signal（観測する側と、その occurrence を先に知りたい側が同じ形を作る）。"""

    return AnalysisLimitationBlockerSignal(
        declared_reason_id=reason_id,
        limitation_site=limitation_site,
        canonical_target_key=target_key,
        missing_semantic_fact=missing_semantic_fact,
        evidence_refs=tuple(evidence_refs),
    )


def observe_analysis_limitation(
    *,
    reason_id: str,
    limitation_site: str,
    target_key: Any = (),
    missing_semantic_fact: Any = (),
    evidence_refs: tuple[str, ...] = (),
) -> Optional[str]:
    """この domain が所有する限界を 1 件観測する（唯一の emit 呼び出し）。

    戻り値は **この限界に対応する occurrence id**（pilot session や encoder が無ければ
    `None`）。「その cause が今も active か」はここでは答えない: 同じ限界を再観測した
    場合、新しい event は作られず同じ occurrence id が返るだけで、その cause が
    discharge 済みであることもある。active かどうかは呼び出し側が現在の
    `c_active_base` で確認する（`authority/decision/limitation_attribution.py`）。
    """
    # Deferred import: `production_signals` はこの module の signal 型を
    # import するので、module top で読むと循環する。
    from scripts.function_tracer_pcode.authority.lifecycle.production_context import (
        active_production_pilot_session,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        emit_analysis_limitation_signal,
    )

    session = active_production_pilot_session()
    if session is None:
        # pilot が無ければ何もしない（記述も作らない）
        return None
    # Issue #110: 記述（live な値でもよい）は、signal を作る前に限界の event の上限まで数えながら plain
    # な値へ写す（上限の外は契約の超過。作ってから測らない）
    describe = getattr(session, "plain_limitation_description", None)
    if not callable(describe):
        raise TypeError("the production pilot session cannot bound a limitation description")
    target_key, missing_semantic_fact, evidence_refs = describe(
        (target_key, missing_semantic_fact, evidence_refs),
    )
    signal = analysis_limitation_signal(
        reason_id=reason_id,
        limitation_site=limitation_site,
        target_key=target_key,
        missing_semantic_fact=missing_semantic_fact,
        evidence_refs=evidence_refs,
    )
    emit_analysis_limitation_signal(
        signal,
        producer_site_manifest_id=ANALYSIS_LIMITATION_OBSERVED_SITE.site_id,
    )
    resolver = getattr(session.domain_signal_encoder, "authority_for_signal", None)
    if not callable(resolver):
        return None
    return resolver(session, signal).occurrence.occurrence_id
