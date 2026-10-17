# -*- coding: utf-8 -*-
"""Return-coverage domain: sealed reasons for a return partition whose coverage no outcome seed certifies
(plan v4 PR-C).

比較の前に、各側の return の条件が入力の全域を覆うか（被覆）を return-coverage gate
（``proof/strategies/proof_gates/return_coverage.py``）が決める。outcome seed のある解析（本番の解析器の
出力）では、被覆は outcome partition の段が決め、決められなければその段の cause（``outcome_*``）が
authority へ出る。seed の無い解析（``semantic_successor`` の view: 再帰の抽象化・conditional lane・
recurrence promotion、pre-return counted loop の要約）では outcome partition の段が走らず、gate は
条件の SMT による全域性の検査（``_check_return_case_coverage_gap``）で決める。その「覆わない（gap）」・
「決められない（inconclusive）」は、この domain より前には authority の cause を持たなかった。被覆の印は
monolithic fallback も止めるので、比較は cause も inconclusive の terminal も無いまま終わり、終了処理が
ERROR にしていた。

* reason は 2 つ: ``return_coverage_gap``（全域でない入力の領域がある）と ``return_coverage_inconclusive``
  （全域かどうか決められない: 条件を SMT へ訳せない、solver が答えない ...）。どちらも legacy の
  ``UnknownReasonId`` と同じ id で、``PILOT_TYPED_CAUSE_KINDS`` が以前から名前だけ宣言していた。
* ``decision_effect`` は ``blocks_equivalence``。被覆の欠けは「全域で同じ値を返す」証明を塞ぐ。反例
  （NOT_EQ）の側は、被覆の欠けを SAT の安全性の理由として既に扱っている（``sat_safety``）。
* identity scope は ``UNARY``（1 つの関数の被覆）。cause は関数の identity と reason で 1 つ。
* 回復は被覆の証明で、ここでは requirement の枠だけを作る（seed を作り直して outcome partition に
  任せるのが本来の回復）。
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


RETURN_COVERAGE_DOMAIN = "return_coverage"
RETURN_COVERAGE_GAP_REASON_ID = "return_coverage_gap"
RETURN_COVERAGE_INCONCLUSIVE_REASON_ID = "return_coverage_inconclusive"
RETURN_COVERAGE_PROOF_KIND = "return_coverage_completion"
RETURN_COVERAGE_CONTRACT_ID = "return-coverage-recovery"
RETURN_COVERAGE_TARGET_KIND = "function_return_coverage"
RETURN_COVERAGE_PRODUCER_ID = "return-coverage-seedless-gate-v1"
#: producer site（Phase 7 manifest の site id。``emit_return_coverage_signal`` の呼び手は 1 つ）。
RETURN_COVERAGE_SITE_ID = "return-coverage-seedless-blocker"
RETURN_COVERAGE_IDENTITY_SCOPE = IdentityScope.UNARY
#: session ごとに「どの cause を **これまでに一度でも** 観測したか」（reducer の重複 occurrence 拒否を
#: 避けるためだけの履歴。cause が active かは lifecycle projection が正本）。
RETURN_COVERAGE_LEDGER_KEY = "return_coverage_ever_observed"

RETURN_COVERAGE_REASON_IDS = (RETURN_COVERAGE_GAP_REASON_ID, RETURN_COVERAGE_INCONCLUSIVE_REASON_ID)

RETURN_COVERAGE_REASON_REGISTRY = SealedReasonRegistry.build(tuple(
    ReasonDefinition(
        reason_id, RETURN_COVERAGE_DOMAIN, "semantic_partition_blocker",
        "blocks_equivalence", frozenset((RETURN_COVERAGE_TARGET_KIND,)),
        ("return_cases", "coverage_check"),
        frozenset((RETURN_COVERAGE_PROOF_KIND,)), True,
        "return_coverage_v1", RecoveryAddressability.REQUIREMENT_REQUIRED,
    )
    for reason_id in RETURN_COVERAGE_REASON_IDS
))
RETURN_COVERAGE_RECOVERY_REGISTRY = SealedRecoveryRegistry.build((
    SatisfactionContractDefinition(
        RETURN_COVERAGE_CONTRACT_ID, 1,
        (RequirementSlotDefinition("coverage", frozenset((RETURN_COVERAGE_PROOF_KIND,))),),
        requirement_slot("coverage"),
    ),
))


@dataclass(frozen=True)
class ReturnCoverageBlockerSignal:
    """seed の無い解析の 1 つの関数について、gate が決めた被覆の gap / inconclusive。"""

    declared_reason_id: str
    function_identity: Any
    coverage_check: str
    evidence_refs: tuple[str, ...] = ()
    producer_id: str = RETURN_COVERAGE_PRODUCER_ID

    def __post_init__(self) -> None:
        if self.declared_reason_id not in RETURN_COVERAGE_REASON_IDS:
            raise ValueError("return-coverage signal reason is not domain-owned")
        for value in (self.coverage_check, self.producer_id):
            if type(value) is not str or not value:
                raise TypeError("return-coverage signal authority is incomplete")
        object.__setattr__(self, "function_identity", canonical_value(self.function_identity))
        evidence = tuple(self.evidence_refs)
        if any(type(item) is not str or not item for item in evidence):
            raise TypeError("return-coverage signal evidence is incomplete")
        object.__setattr__(self, "evidence_refs", evidence)

    def _phase7_signal_authority(self) -> Mapping[str, Any]:
        return {
            "declared_reason_id": self.declared_reason_id,
            "target": self.cause_target(),
            "coverage_check": self.coverage_check,
            "evidence_refs": self.evidence_refs,
            "producer_id": self.producer_id,
        }

    def cause_target(self) -> tuple:
        return canonical_value(("return_coverage_v1", self.declared_reason_id, self.function_identity))


class ReturnCoveragePilotEncoder:
    """1 つの関数・reason の被覆の欠けを CAUSE_OBSERVED 1 つにする（再観測は同じ cause）。"""

    def __init__(self) -> None:
        self._cause_factory = SemanticCauseIdentityFactory(RETURN_COVERAGE_REASON_REGISTRY)
        self._binding_factory = SatisfactionBindingFactory(RETURN_COVERAGE_RECOVERY_REGISTRY)

    @staticmethod
    def _observed_ledger(session: Any) -> set:
        ledger = session.domain_signal_state.get(RETURN_COVERAGE_LEDGER_KEY)
        if ledger is None:
            return set()
        if type(ledger) is not set:
            raise TypeError("return-coverage observed ledger is not an exact set")
        return ledger

    def has_observed(self, session: Any, signal: Any) -> bool:
        if type(signal) is not ReturnCoverageBlockerSignal:
            return False
        return self._authority(session, signal).occurrence.occurrence_id in self._observed_ledger(session)

    def commit_emitted_signal(
        self, session: Any, signal: Any, intents: tuple[EventIntent, ...],
    ) -> None:
        if type(signal) is not ReturnCoverageBlockerSignal or not intents:
            return
        session.domain_signal_state.setdefault(RETURN_COVERAGE_LEDGER_KEY, set()).add(
            self._authority(session, signal).occurrence.occurrence_id
        )

    def authority_for_signal(self, session: Any, signal: ReturnCoverageBlockerSignal) -> CauseOccurrenceAuthority:
        return self._authority(session, signal)

    def __call__(self, session: Any, signal: ReturnCoverageBlockerSignal) -> tuple[EventIntent, ...]:
        if type(signal) is not ReturnCoverageBlockerSignal:
            raise TypeError("return-coverage encoder requires an exact signal")
        authority = self._authority(session, signal)
        if authority.occurrence.occurrence_id in self._observed_ledger(session):
            return ()
        return (EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),)

    def _authority(self, session: Any, signal: ReturnCoverageBlockerSignal) -> CauseOccurrenceAuthority:
        target = signal.cause_target()
        cause = self._cause_factory.create(
            reason_id=signal.declared_reason_id,
            identity_scope=RETURN_COVERAGE_IDENTITY_SCOPE,
            target_kind=RETURN_COVERAGE_TARGET_KIND,
            canonical_target_key=target,
            missing_semantic_fact=("return_partition_covers_input_domain", signal.declared_reason_id),
            semantic_proposition=("function_returns_on_every_input", signal.function_identity),
            observation_surface=(signal.coverage_check, signal.evidence_refs),
            active_semantic_precondition=("outcome_seed_absent", signal.declared_reason_id),
            correspondence_contract=None,
        )
        requirement = ProofRequirement(
            "return-coverage-q-" + authority_digest(target)[:32],
            RETURN_COVERAGE_PROOF_KIND, target,
        )
        bound = self._binding_factory.bind(
            contract_definition_id=RETURN_COVERAGE_CONTRACT_ID,
            contract_version=1, bindings={"coverage": requirement},
        )
        occurrence = CauseOccurrence(
            "return-coverage-occ-" + authority_digest({
                "result_occurrence_id": session.identity.result_occurrence_id,
                "target": target,
            })[:32],
            cause, signal.declared_reason_id, authority_digest(target),
            RETURN_COVERAGE_TARGET_KIND, RETURN_COVERAGE_IDENTITY_SCOPE,
            bound.contract_definition_id, bound.contract_version,
            bound.normalized_expression_digest, bound.bound_expression_digest,
            (requirement.requirement_id,),
            (signal.coverage_check, *signal.evidence_refs),
            "return_coverage_producer_signal",
            session.identity.source_snapshot_fingerprint, signal.producer_id,
            session.identity.execution_identity_digest,
        )
        return CauseOccurrenceAuthority(occurrence, bound)


__all__ = (
    "RETURN_COVERAGE_DOMAIN",
    "RETURN_COVERAGE_GAP_REASON_ID",
    "RETURN_COVERAGE_IDENTITY_SCOPE",
    "RETURN_COVERAGE_INCONCLUSIVE_REASON_ID",
    "RETURN_COVERAGE_PRODUCER_ID",
    "RETURN_COVERAGE_REASON_IDS",
    "RETURN_COVERAGE_REASON_REGISTRY",
    "RETURN_COVERAGE_RECOVERY_REGISTRY",
    "RETURN_COVERAGE_SITE_ID",
    "ReturnCoverageBlockerSignal",
    "ReturnCoveragePilotEncoder",
)
