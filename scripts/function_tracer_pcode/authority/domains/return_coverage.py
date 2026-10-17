# -*- coding: utf-8 -*-
"""Return-coverage domain: sealed reasons for a final comparison that ended on a return-coverage verdict no
outcome seed certifies (plan v4 PR-C).

比較の前に、各側の return の条件が入力の全域を覆うか（被覆）を return-coverage gate
（``proof/strategies/proof_gates/return_coverage.py``）が決める。outcome seed のある解析（本番の解析器の
出力）では、被覆は outcome partition の段が決め、決められなければその段の cause（``outcome_*``）が
authority へ出る。seed の無い解析（pre-return counted loop の要約・合成の解析）では gate は条件の SMT による
全域性の検査で決め、その「覆わない（gap）」・「決められない（inconclusive）」を raw analysis の被覆の印
（``return_case_coverage_*``）に残す。印は monolithic fallback を止めるので、比較は cause も inconclusive の
terminal も無いまま終わり、終了処理が ERROR にしていた。

責務は 3 つに分ける。

1. 被覆を判定する: return-coverage gate（この domain は判定しない）。
2. 不足がどの比較に適用されるかを記録する: runner が monolithic fallback を止めたとき、その runner が raw pair
   について行った比較自身の判定（``PreparedDispatchFrame.coverage_verdict_notes``。analysis に追記される印では
   ない）から不足を取り、runner の結果に ``UnsealedCoverageTerminal`` を付ける（``stage_runner``）。記録はその
   結果の比較（dispatch frame）に束縛され、cause はまだ作らない。
3. 採用する: どの結果が最終かを決めた後の authority の終了処理（``pilot.finish``）が、**最終の結果**に付いた
   記録だけを、最終の比較の frame と照合して cause にする（``observe_final_unsealed_coverage``）。

型の再試行の段（P1 / P2 ...）や recurrence promotion の結果が最終になれば、前の比較の記録はその結果と一緒に
捨てられ、cause にならない。後の段の解析が被覆を回復して示した EQ を、前の段の不足が塞がない。逆に最終の
比較の被覆が欠けていれば、その比較の cause が判定を UNKNOWN にする。再試行の開始時の一律の削除・EQ という
結果による解消・段の名前による例外は無い。view（抽象化・promotion）の被覆の印は view に付き、runner の raw
pair の記録にならない。

* reason は 2 つ: ``return_coverage_gap``（全域でない入力の領域がある）と ``return_coverage_inconclusive``
  （全域かどうか決められない: 条件を SMT へ訳せない、solver が答えない ...）。どちらも legacy の
  ``UnknownReasonId`` と同じ id。
* ``decision_effect`` は ``blocks_equivalence``。被覆の欠けは「全域で同じ値を返す」証明を塞ぐ。反例
  （NOT_EQ）の側は、被覆の欠けを SAT の安全性の理由として既に扱っている（``sat_safety``）。
* identity scope は ``RELATIONAL``: cause は「この比較（raw pair・branch・generation）のこの側の被覆」で、
  関数だけの性質ではない。
* 回復の requirement は枠だけを作る（この cause は最終の比較にだけ作られるので、それを解消する別の証明は
  その比較の中には無い）。
"""

from __future__ import annotations

from dataclasses import dataclass, field
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
#: 被覆の証明（legacy の ``UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION`` とは別の名前: legacy の回復の
#: 証明がこの requirement を満たしたことにならない）。
RETURN_COVERAGE_PROOF_KIND = "seedless_return_coverage_proof"
RETURN_COVERAGE_CONTRACT_ID = "return-coverage-recovery"
RETURN_COVERAGE_TARGET_KIND = "function_return_coverage"
RETURN_COVERAGE_PRODUCER_ID = "return-coverage-final-terminal-v1"
#: producer site（Phase 7 manifest の site id。``emit_return_coverage_signal`` の呼び手は 1 つ:
#: ``observe_final_unsealed_coverage``）。
RETURN_COVERAGE_SITE_ID = "return-coverage-final-terminal"
RETURN_COVERAGE_IDENTITY_SCOPE = IdentityScope.RELATIONAL
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
    """最終の比較の 1 つの側について、seed の無い解析の被覆の gap / inconclusive。

    ``comparison_identity`` はその比較（raw pair の digest・branch・generation）で、cause の identity に入る:
    別の比較（別の段の再解析・別の branch）で観測した同じ関数の不足は別の cause。
    """

    declared_reason_id: str
    function_identity: Any
    coverage_check: str
    comparison_identity: tuple[str, ...]
    evidence_refs: tuple[str, ...] = ()
    producer_id: str = RETURN_COVERAGE_PRODUCER_ID

    def __post_init__(self) -> None:
        if self.declared_reason_id not in RETURN_COVERAGE_REASON_IDS:
            raise ValueError("return-coverage signal reason is not domain-owned")
        comparison = tuple(self.comparison_identity)
        if not comparison or any(type(item) is not str or not item for item in comparison):
            raise TypeError("return-coverage signal is not bound to a comparison")
        object.__setattr__(self, "comparison_identity", comparison)
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
            "comparison_identity": self.comparison_identity,
            "evidence_refs": self.evidence_refs,
            "producer_id": self.producer_id,
        }

    def cause_target(self) -> tuple:
        return canonical_value((
            "return_coverage_v2", self.declared_reason_id, self.comparison_identity, self.function_identity,
        ))


class ReturnCoveragePilotEncoder:
    """1 つの比較・側・reason の被覆の欠けを CAUSE_OBSERVED 1 つにする（再観測は同じ cause）。"""

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
            active_semantic_precondition=("final_comparison_unsealed", signal.comparison_identity),
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


#: runner の raw analysis の被覆の印 → reason（``proof/obligations/snapshot.COMPARISON_ANNOTATION_NOTES`` と一致）。
COVERAGE_NOTE_REASONS = (
    ("return_case_coverage_gap", RETURN_COVERAGE_GAP_REASON_ID),
    ("return_case_coverage_inconclusive", RETURN_COVERAGE_INCONCLUSIVE_REASON_ID),
)


@dataclass(frozen=True)
class UnsealedCoverageObservation:
    """fallback を止めた被覆の印 1 つ（側・reason・関数）。"""

    label: str
    reason_id: str
    coverage_note: str
    function_identity: Any

    def __post_init__(self) -> None:
        if (self.coverage_note, self.reason_id) not in COVERAGE_NOTE_REASONS:
            raise ValueError("unsealed coverage observation is not a registered coverage note")
        if type(self.label) is not str or not self.label:
            raise TypeError("unsealed coverage observation has no side label")
        object.__setattr__(self, "function_identity", canonical_value(self.function_identity))


def unsealed_coverage_observations(
    analysis1: Any, analysis2: Any, verdict_notes: tuple,
) -> tuple[UnsealedCoverageObservation, ...]:
    """runner の raw pair の比較が観測した被覆の不足のうち、seed の無い側のもの。

    ``verdict_notes`` はその比較の判定（``PreparedDispatchFrame.coverage_verdict_notes``: (側, 被覆の印)）。
    raw analysis の ``analysis_notes`` は読まない: analysis は比較をまたいで使い回され（再解析しなかった側）、
    印は追記だけなので、前の比較の不足を今の比較の不足と取り違える。seed のある側の被覆は outcome partition の
    段が cause を持つので含めない。
    """

    verdicts = set(tuple(item) for item in verdict_notes or ())
    observations = []
    for label, analysis in (("function1", analysis1), ("function2", analysis2)):
        if getattr(analysis, "outcome_seed", None) is not None:
            continue
        for note, reason_id in COVERAGE_NOTE_REASONS:
            if (label, note) in verdicts:
                observations.append(UnsealedCoverageObservation(
                    label, reason_id, note, tuple(analysis.outcome_function_identity()),
                ))
    return tuple(observations)


@dataclass(frozen=True)
class UnsealedCoverageTerminal:
    """runner の比較が被覆の欠けで inconclusive の terminal 無しに終わったことの記録（まだ cause ではない）。

    その runner の結果の dispatch frame（比較）に束縛する。comparison receipt は要らない（SMT の意味の拒否で
    pairwise が pair ledger を作る前に止まった比較にも receipt は無い）。終了処理は、最終の結果の frame と同じ
    比較の記録だけを cause にする（``observe_final_unsealed_coverage``）。
    """

    observations: tuple[UnsealedCoverageObservation, ...]
    comparison_identity: tuple[str, ...]
    _frame: Any = field(default=None, repr=False, compare=False)

    @staticmethod
    def _comparison_identity(frame: Any) -> tuple:
        binding = getattr(frame, "comparison_binding", None)
        identity = (
            getattr(binding, "raw_pair_digest", None),
            getattr(frame, "branch_id", None),
            getattr(frame, "generation", None),
        )
        if (
            type(identity[0]) is not str or not identity[0]
            or type(identity[1]) is not str or not identity[1]
            or type(identity[2]) is not int
        ):
            return ()
        return (identity[0], identity[1], str(identity[2]))

    @classmethod
    def issue(cls, frame: Any, observations: tuple) -> "UnsealedCoverageTerminal":
        observations = tuple(observations)
        if not observations or any(type(item) is not UnsealedCoverageObservation for item in observations):
            raise ValueError("unsealed coverage terminal needs exact observations")
        identity = cls._comparison_identity(frame)
        if not identity:
            raise ValueError("unsealed coverage terminal is not bound to a comparison")
        return cls(observations, identity, frame)

    def binds(self, frame: Any) -> bool:
        """``frame`` がこの記録を作った比較そのもの（同じ frame で、raw pair・branch・generation も同じ）か。"""

        return frame is not None and frame is self._frame and self._comparison_identity(frame) == self.comparison_identity

    def signals(self) -> tuple[ReturnCoverageBlockerSignal, ...]:
        comparison = self.comparison_identity
        return tuple(
            ReturnCoverageBlockerSignal(
                declared_reason_id=item.reason_id,
                function_identity=item.function_identity,
                coverage_check=item.coverage_note,
                comparison_identity=comparison,
                evidence_refs=(f"coverage_label:{item.label}", "monolithic_fallback_skipped"),
            )
            for item in self.observations
        )


def observe_final_unsealed_coverage(terminal: Any, final_frame: Any) -> int:
    """最終の結果の記録を cause にする（唯一の emit 呼び出し。``adopt_final_unsealed_coverage`` が呼ぶ）。

    記録が最終の結果の比較に束縛されていなければ、終了処理を止める（別の比較の記録を最終の判定に使わない）。
    戻り値は発行した event の数。
    """

    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        emit_return_coverage_signal,
    )

    if type(terminal) is not UnsealedCoverageTerminal or not terminal.binds(final_frame):
        raise ValueError("unsealed coverage terminal is not bound to the final comparison")
    emitted = 0
    for signal in terminal.signals():
        emitted += emit_return_coverage_signal(
            signal, producer_site_manifest_id="return-coverage-final-terminal",
        )
    return emitted


def adopt_final_unsealed_coverage(result: Any, final_legacy_outcome: Any) -> int:
    """採用の規則（唯一の入口。``pilot.finish`` が、どの結果が最終かが決まった後に最終の結果について呼ぶ）。

    最終の結果が判定を持たない（UNKNOWN / TIMEOUT）ときだけ、その結果の記録を最終の比較の frame と照合して
    cause にする。EQ / NOT_EQ の結果には記録は付かない（runner は判定がまだ無いときだけ fallback を止める）。
    ERROR の結果は ERROR のまま（legacy の被覆の理由は結果の legacy の理由に残る）。
    """

    from scripts.function_tracer_pcode.authority.contracts import Outcome

    terminal = getattr(result, "_unsealed_coverage_terminal", None)
    if terminal is None or final_legacy_outcome not in {Outcome.UNKNOWN, Outcome.TIMEOUT}:
        return 0
    return observe_final_unsealed_coverage(terminal, getattr(result, "_prepared_dispatch_frame", None))


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
    "COVERAGE_NOTE_REASONS",
    "ReturnCoverageBlockerSignal",
    "ReturnCoveragePilotEncoder",
    "UnsealedCoverageObservation",
    "UnsealedCoverageTerminal",
    "adopt_final_unsealed_coverage",
    "observe_final_unsealed_coverage",
    "unsealed_coverage_observations",
)
