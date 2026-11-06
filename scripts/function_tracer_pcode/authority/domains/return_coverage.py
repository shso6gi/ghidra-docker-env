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
2. 不足がどの比較に適用されるかを記録する: pairwise の比較は自分の判定を自分の obligation runtime に記録する
   （``ObligationRuntimeSession.coverage_verdict``。analysis に追記される印ではない）。runner が monolithic fallback
   を止めたとき、runner の runtime の判定から不足を取る（抽象化・promotion の比較は別の runtime に書くので、ここに
   書くのは runner の raw pair の比較。runner の runtime は自分の raw pair に予約されている。コード読解からの帰結:
   仮に raw pair の比較が別の runtime を得ると、その判定は runner に届かず記録は作られず、main と同じく終了処理が
   ERROR にする。この経路は test で通していない）。そして runner の結果に ``UnsealedCoverageTerminal`` を
   付ける（``stage_runner``）。記録は、不足を観測した比較の identity と、付けた結果の比較（dispatch frame）への
   束縛を分けて持ち、cause はまだ作らない。
3. 採用する: どの結果が最終かを決めた後の authority の終了処理（``pilot.finish``）が、**最終の結果**に付いた
   記録だけを、最終の比較の frame と照合して cause にする（``observe_final_unsealed_coverage``）。

型の再試行の段（P1 / P2 ...）の結果が最終になれば、前の段の runner の記録はその結果と一緒に捨てられ、cause に
ならない。後の段の解析が被覆を回復して示した EQ を、前の段の不足が塞がない。逆に最終の比較の被覆が欠けていれば、
その runner の記録の cause が判定を UNKNOWN にする。再試行の開始時の一律の削除・EQ という結果による解消・段の
名前による例外は無い。

同じ runner の中で recurrence promotion・再帰の抽象化の比較が最後の結果になったとき（その比較は自分の runtime で
動く）は、runner が fallback を止めた理由である raw pair の比較の不足を、その最後の結果に束縛して記録する。cause は
不足を観測した raw pair の比較を名指しする。promotion・抽象化の比較が被覆を回復しても別の理由で UNKNOWN なら、
fallback を止めたのは raw pair の不足なので、その cause が残る（判定は UNKNOWN のまま変わらない）。view の比較の
判定は view の runtime に書かれ、runner の記録にならない。

* reason は 3 つ: ``return_coverage_gap``（全域でない入力の領域がある）と ``return_coverage_inconclusive``
  （全域かどうか決められない: 条件を SMT へ訳せない、solver が答えない ...）。どちらも legacy の
  ``UnknownReasonId`` と同じ id。``return_partition_control_flow_incomplete``（Issue #257）は、制御フローが
  不完全で戻り値が未解決（または条件なしの return が重なる）側があり、runner が monolithic fallback を止めた比較:
  return の分割そのものが関数の全経路を表していない。gate の判定ではなく、fallback を止めた理由から記録する。
* fallback を止める理由（``core.analysis.MONOLITHIC_FALLBACK_SKIP_REASONS``）と、その比較の UNKNOWN を説明する
  cause の owner の対応は ``MONOLITHIC_FALLBACK_SKIP_CAUSE_OWNERS`` の 1 つの表に置く。
* ``decision_effect`` は ``blocks_equivalence``。被覆の欠けは「全域で同じ値を返す」証明を塞ぐ。反例
  （NOT_EQ）の側は、被覆の欠けを SAT の安全性の理由として既に扱っている（``sat_safety``）。
* identity scope は ``RELATIONAL``: cause は「この比較（raw pair・branch・generation）のこの側の被覆」で、
  関数だけの性質ではない。
* 回復の requirement は枠だけを作る（この cause は最終の比較にだけ作られるので、それを解消する別の証明は
  その比較の中には無い）。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from types import MappingProxyType
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

#: return-coverage gate が判定する被覆の不足（比較の ``coverage_verdict`` に記録される reason）
RETURN_COVERAGE_REASON_IDS = (RETURN_COVERAGE_GAP_REASON_ID, RETURN_COVERAGE_INCONCLUSIVE_REASON_ID)
#: runner が「制御フローが不完全」で monolithic fallback を止めた比較の側（Issue #257）
RETURN_PARTITION_CONTROL_FLOW_REASON_ID = "return_partition_control_flow_incomplete"
#: この domain が所有する reason の全部
RETURN_COVERAGE_DOMAIN_REASON_IDS = RETURN_COVERAGE_REASON_IDS + (RETURN_PARTITION_CONTROL_FLOW_REASON_ID,)

#: cause を outcome partition の段が持つ理由の owner（seed のある解析の unknown outcome）
OUTCOME_PARTITION_STAGE_OWNER = "outcome_partition_stage"
#: monolithic fallback を止める理由 → その比較を UNKNOWN にする cause の owner（Issue #257: 表は 1 つ）。
#: 理由を足すときはここに owner を足す（``core.analysis.MONOLITHIC_FALLBACK_SKIP_REASONS`` と一致することを test が見る）。
MONOLITHIC_FALLBACK_SKIP_CAUSE_OWNERS = MappingProxyType({
    "unknown_outcome_partition": OUTCOME_PARTITION_STAGE_OWNER,
    "return_case_coverage_gap": RETURN_COVERAGE_GAP_REASON_ID,
    "return_case_coverage_inconclusive": RETURN_COVERAGE_INCONCLUSIVE_REASON_ID,
    "incomplete_control_flow": RETURN_PARTITION_CONTROL_FLOW_REASON_ID,
})

#: 制御フローの不完全さの回復の証明（seed の有無に依らないので被覆の証明とは別の名前）
RETURN_PARTITION_CONTROL_FLOW_PROOF_KIND = "return_partition_control_flow_proof"
RETURN_PARTITION_CONTROL_FLOW_CONTRACT_ID = "return-partition-control-flow-recovery"
#: reason → (回復の proof kind, 契約)
_RECOVERY_BY_REASON = MappingProxyType({
    RETURN_COVERAGE_GAP_REASON_ID: (RETURN_COVERAGE_PROOF_KIND, RETURN_COVERAGE_CONTRACT_ID),
    RETURN_COVERAGE_INCONCLUSIVE_REASON_ID: (RETURN_COVERAGE_PROOF_KIND, RETURN_COVERAGE_CONTRACT_ID),
    RETURN_PARTITION_CONTROL_FLOW_REASON_ID: (
        RETURN_PARTITION_CONTROL_FLOW_PROOF_KIND, RETURN_PARTITION_CONTROL_FLOW_CONTRACT_ID,
    ),
})

RETURN_COVERAGE_REASON_REGISTRY = SealedReasonRegistry.build(tuple(
    ReasonDefinition(
        reason_id, RETURN_COVERAGE_DOMAIN, "semantic_partition_blocker",
        "blocks_equivalence", frozenset((RETURN_COVERAGE_TARGET_KIND,)),
        ("return_cases", "coverage_check"),
        frozenset((_RECOVERY_BY_REASON[reason_id][0],)), True,
        "return_coverage_v1", RecoveryAddressability.REQUIREMENT_REQUIRED,
    )
    for reason_id in RETURN_COVERAGE_DOMAIN_REASON_IDS
))
RETURN_COVERAGE_RECOVERY_REGISTRY = SealedRecoveryRegistry.build(tuple(
    SatisfactionContractDefinition(
        contract_id, 1,
        (RequirementSlotDefinition("coverage", frozenset((proof_kind,))),),
        requirement_slot("coverage"),
    )
    for proof_kind, contract_id in sorted(set(_RECOVERY_BY_REASON.values()))
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
        if self.declared_reason_id not in RETURN_COVERAGE_DOMAIN_REASON_IDS:
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
        proof_kind, contract_id = _RECOVERY_BY_REASON[signal.declared_reason_id]
        requirement = ProofRequirement(
            "return-coverage-q-" + authority_digest(target)[:32],
            proof_kind, target,
        )
        bound = self._binding_factory.bind(
            contract_definition_id=contract_id,
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


def comparison_identity_of(frame: Any) -> tuple:
    """比較（dispatch frame）の決定的な identity: (raw pair の digest, branch, generation)。取れなければ ``()``。"""

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


@dataclass(frozen=True)
class UnsealedCoverageObservation:
    """runner の raw pair の比較が観測した被覆の不足 1 つ（側・reason・関数）。"""

    label: str
    reason_id: str
    function_identity: Any

    def __post_init__(self) -> None:
        if self.reason_id not in RETURN_COVERAGE_DOMAIN_REASON_IDS:
            raise ValueError("unsealed coverage observation reason is not domain-owned")
        if type(self.label) is not str or not self.label:
            raise TypeError("unsealed coverage observation has no side label")
        object.__setattr__(self, "function_identity", canonical_value(self.function_identity))


def unsealed_coverage_observations(
    analysis1: Any, analysis2: Any, verdict: tuple,
) -> tuple[UnsealedCoverageObservation, ...]:
    """runner の raw pair の比較の判定（``ObligationRuntimeSession.coverage_verdict`` の (側, reason id)）のうち、
    seed の無い側の不足。

    raw analysis の被覆の印（``analysis_notes``）は読まない: analysis は比較をまたいで使い回され（再解析しな
    かった側）、印は追記だけなので、前の比較の不足を今の比較の不足と取り違える。seed のある側の被覆は outcome
    partition の段が cause を持つので含めない。
    """

    observed = set(tuple(item) for item in verdict or ())
    observations = []
    for label, analysis in (("function1", analysis1), ("function2", analysis2)):
        if getattr(analysis, "outcome_seed", None) is not None:
            continue
        for reason_id in RETURN_COVERAGE_REASON_IDS:
            if (label, reason_id) in observed:
                observations.append(UnsealedCoverageObservation(
                    label, reason_id, tuple(analysis.outcome_function_identity()),
                ))
    return tuple(observations)


def control_flow_skip_observations(analysis1: Any, analysis2: Any) -> tuple[UnsealedCoverageObservation, ...]:
    """runner が monolithic fallback を止めた理由のうち、制御フローの不完全さ（``incomplete_control_flow``）の側。

    gate の判定でなく、runner がこの比較の analysis から fallback を止めた理由そのもの
    （``FunctionReturnAnalysis.monolithic_fallback_skip_reasons``）を読む。制御フローの不完全さと未解決の戻り値は
    analysis の解析結果そのもので、比較をまたいで追記される印ではない。seed の有無で除外しない（seed のある
    解析で outcome partition の段の cause が既にあっても、足すのは EQ を止める側の cause だけ）。
    """

    from scripts.function_tracer_pcode.core.analysis import FALLBACK_SKIP_INCOMPLETE_CONTROL_FLOW

    observations = []
    for label, analysis in (("function1", analysis1), ("function2", analysis2)):
        reasons = getattr(analysis, "monolithic_fallback_skip_reasons", None)
        if callable(reasons) and FALLBACK_SKIP_INCOMPLETE_CONTROL_FLOW in reasons():
            observations.append(UnsealedCoverageObservation(
                label, RETURN_PARTITION_CONTROL_FLOW_REASON_ID, tuple(analysis.outcome_function_identity()),
            ))
    return tuple(observations)


@dataclass(frozen=True)
class UnsealedCoverageTerminal:
    """runner の比較が被覆の欠けで inconclusive の terminal 無しに終わったことの記録（まだ cause ではない）。

    2 つの比較を分けて持つ。

    * ``observed_comparison``: 不足を観測した比較（runner の raw pair の比較）。cause の identity に入る。
    * 束縛: runner の結果（最終の候補）の dispatch frame。runner の最後の結果が抽象化・promotion の比較でも、
      記録はその結果に付き、その結果が最終のときだけ使える。

    comparison receipt は要らない（SMT の意味の拒否で pairwise が pair ledger を作る前に止まった比較にも receipt
    は無い）。終了処理は、最終の結果の frame と同じ比較に束縛された記録だけを cause にする
    （``observe_final_unsealed_coverage``）。
    """

    observations: tuple[UnsealedCoverageObservation, ...]
    observed_comparison: tuple[str, ...]
    bound_comparison: tuple[str, ...]
    _frame: Any = field(default=None, repr=False, compare=False)

    @classmethod
    def issue(cls, frame: Any, observed_comparison: tuple, observations: tuple) -> "UnsealedCoverageTerminal":
        observations = tuple(observations)
        if not observations or any(type(item) is not UnsealedCoverageObservation for item in observations):
            raise ValueError("unsealed coverage terminal needs exact observations")
        observed = tuple(observed_comparison or ())
        if len(observed) != 3 or any(type(item) is not str or not item for item in observed):
            raise ValueError("unsealed coverage terminal needs the observing comparison")
        bound = comparison_identity_of(frame)
        if not bound:
            raise ValueError("unsealed coverage terminal is not bound to a comparison")
        return cls(observations, observed, bound, frame)

    def binds(self, frame: Any) -> bool:
        """``frame`` がこの記録を付けた結果の比較そのもの（同じ frame で、identity も同じ）か。"""

        return frame is not None and frame is self._frame and comparison_identity_of(frame) == self.bound_comparison

    def signals(self) -> tuple[ReturnCoverageBlockerSignal, ...]:
        return tuple(
            ReturnCoverageBlockerSignal(
                declared_reason_id=item.reason_id,
                function_identity=item.function_identity,
                coverage_check=(
                    "monolithic_fallback_skip_reason"
                    if item.reason_id == RETURN_PARTITION_CONTROL_FLOW_REASON_ID
                    else "return_coverage_gate_verdict"
                ),
                comparison_identity=self.observed_comparison,
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
    "MONOLITHIC_FALLBACK_SKIP_CAUSE_OWNERS",
    "OUTCOME_PARTITION_STAGE_OWNER",
    "RETURN_COVERAGE_DOMAIN",
    "RETURN_COVERAGE_DOMAIN_REASON_IDS",
    "RETURN_COVERAGE_GAP_REASON_ID",
    "RETURN_COVERAGE_IDENTITY_SCOPE",
    "RETURN_COVERAGE_INCONCLUSIVE_REASON_ID",
    "RETURN_COVERAGE_PRODUCER_ID",
    "RETURN_COVERAGE_REASON_IDS",
    "RETURN_COVERAGE_REASON_REGISTRY",
    "RETURN_COVERAGE_RECOVERY_REGISTRY",
    "RETURN_COVERAGE_SITE_ID",
    "RETURN_PARTITION_CONTROL_FLOW_REASON_ID",
    "ReturnCoverageBlockerSignal",
    "ReturnCoveragePilotEncoder",
    "UnsealedCoverageObservation",
    "UnsealedCoverageTerminal",
    "adopt_final_unsealed_coverage",
    "comparison_identity_of",
    "control_flow_skip_observations",
    "observe_final_unsealed_coverage",
    "unsealed_coverage_observations",
)
