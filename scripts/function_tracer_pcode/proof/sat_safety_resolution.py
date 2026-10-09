"""SAT-safety の reason が何によって解消されてよいか（解消の型）の唯一の owner。

counterexample の replay は、SAT の model が宣言した記号へ与えた値を固定して、
同じ抽象式について「到達可能な case の組がすべて違う値になる」ことを確かめる
だけである。固定した値が実際の実行で同時に起こり得ること、解析が捨てた経路・
効果・入力の上位 bit が無いことは示さない。したがって replay が解消してよいのは
**replay 型**の理由（その witness の replay が済んでいないこと）だけで、解析の
不安全（解析の不完全・被覆の欠け・入力対応の不足）は replay では解消しない。

契約は 1 つ: **SAT-safety の blocker は (reason id, evidence ref の組) の対で、
その対が整合しているときだけ存在し、型はその対から決まる**（``SatSafetyBlocker``）。
呼び手が付けた reason id だけを信じる述語は置かない。

* 分類: ``classify_sat_safety_blocker``（不整合・未知の id・空の replay は
  ``SatSafetyBlockerInconsistent``）。producer が ref から id を選ぶときは
  ``sat_safety_reason_id_for_refs``。ref の部分文字列で型を推測しない。
* 解消の許可: ``SatSafetyBlocker.replay_resolvable``（replay の証明が解消してよい）と
  ``SatSafetyBlocker.completable``（authority の cause を COMPLETED にしてよい。
  replay 型と partition の曖昧さだけ）。整合しない対はどちらも偽。
* 回復の要求: ``SAT_SAFETY_RECOVERY_REQUIREMENTS``（型ごとの required evidence と説明）。

pairwise と monolithic、stage runner の gate、authority の観測・完了・deferred の
破棄はすべてここを読む。authority は完了の signal 自身の主張ではなく、観測済み
（または deferred）として記録した blocker をここで分類して許可を決める。

この module は他の module を import しない（proof の leaf）。proof の gate と
conditional lane は同じ層から、authority（``production_signals`` の
``SAT_SAFETY_TYPED_REASON_IDS``・SAT-safety の encoder と producer site）と
checker は下向きにこれを読む。
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from types import MappingProxyType
from typing import Iterable, Mapping


class SatSafetyResolution(str, Enum):
    """SAT-safety の reason を解消してよい証明の型。"""

    #: その witness の replay（model を固定した同じ抽象式の再確認）で解消する。
    REPLAY = "replay"
    #: 解析の安全性の証明が要る。replay では解消しない（入力対応の不足・被覆の欠けを含む）。
    ANALYSIS_UNSAFETY = "analysis_unsafety"
    #: case partition の曖昧さの解消（別の完了経路。replay の証明記録では解消しない）。
    PARTITION_AMBIGUITY = "partition_ambiguity"


COUNTEREXAMPLE_REPLAY_UNPROVEN = "counterexample_replay_unproven"
COUNTEREXAMPLE_ANALYSIS_SAFETY_UNPROVEN = "counterexample_analysis_safety_unproven"
COUNTEREXAMPLE_PARTITION_REPLAY_AMBIGUOUS = "counterexample_partition_replay_ambiguous"

#: SAT-safety の typed reason id → 解消の型。
SAT_SAFETY_REASON_RESOLUTION: Mapping[str, SatSafetyResolution] = MappingProxyType({
    COUNTEREXAMPLE_ANALYSIS_SAFETY_UNPROVEN: SatSafetyResolution.ANALYSIS_UNSAFETY,
    COUNTEREXAMPLE_PARTITION_REPLAY_AMBIGUOUS: SatSafetyResolution.PARTITION_AMBIGUITY,
    COUNTEREXAMPLE_REPLAY_UNPROVEN: SatSafetyResolution.REPLAY,
})

#: SAT-safety の typed reason id の集合（語彙の公開元。authority は同じ object を再輸出する）。
SAT_SAFETY_TYPED_REASON_IDS = frozenset(SAT_SAFETY_REASON_RESOLUTION)

#: replay 型の blocker を表す唯一の evidence ref。replay の要求を出す producer はこれを使う。
COUNTEREXAMPLE_REPLAY_MISSING_REF = "counterexample_replay_missing"

#: 型ごとの回復の要求（required evidence と説明）。SAT-safety の obligation を作る全ての
#: 場所（typed reason と旧来の ``sat_unsafety`` の回復計画）がここを読む。
SAT_SAFETY_RECOVERY_REQUIREMENTS: Mapping[SatSafetyResolution, tuple[tuple[str, ...], str]] = MappingProxyType({
    SatSafetyResolution.REPLAY: (
        ("counterexample_replay", "active_unsafety_discharge", "coverage_effect_safety"),
        "Replay the SAT counterexample under its bound query, model, premise "
        "and pair before accepting disequivalence.",
    ),
    SatSafetyResolution.ANALYSIS_UNSAFETY: (
        ("analysis_safety_proof", "coverage_effect_safety"),
        "Prove that the analysis is safe for this counterexample (no dropped "
        "path, effect or input bits); a counterexample replay does not "
        "discharge it.",
    ),
})


class SatSafetyBlockerInconsistent(ValueError):
    """(reason id, evidence ref の組) が owner の分類と整合しない。"""


def sat_safety_ref_resolution(ref: object) -> SatSafetyResolution:
    """1 つの evidence ref の解消の型。replay の ref と完全一致するものだけが REPLAY。

    知らない ref は解析の不安全として扱う（fail-closed）。
    """
    if type(ref) is str and ref == COUNTEREXAMPLE_REPLAY_MISSING_REF:
        return SatSafetyResolution.REPLAY
    return SatSafetyResolution.ANALYSIS_UNSAFETY


def sat_safety_reason_id_for_refs(refs: Iterable[object]) -> str:
    """SAT unsafety の evidence ref の組から、その blocker の reason id を選ぶ（producer 用）。

    全ての ref が replay 型のときだけ ``counterexample_replay_unproven``。1 つでも
    解析の不安全の ref が混ざれば（空の組も）``counterexample_analysis_safety_unproven``。
    """
    refs = tuple(refs)
    if refs and all(
        sat_safety_ref_resolution(ref) is SatSafetyResolution.REPLAY for ref in refs
    ):
        return COUNTEREXAMPLE_REPLAY_UNPROVEN
    return COUNTEREXAMPLE_ANALYSIS_SAFETY_UNPROVEN


_BLOCKER_TOKEN = object()


@dataclass(frozen=True, init=False)
class SatSafetyBlocker:
    """整合を確かめた SAT-safety の blocker。``classify_sat_safety_blocker`` だけが作る。"""

    reason_id: str
    evidence_refs: tuple[str, ...]
    resolution: SatSafetyResolution

    def __init__(self, reason_id, evidence_refs, resolution, *, _token=None) -> None:
        if _token is not _BLOCKER_TOKEN:
            raise TypeError("SAT-safety blockers are issued by classify_sat_safety_blocker")
        object.__setattr__(self, "reason_id", reason_id)
        object.__setattr__(self, "evidence_refs", evidence_refs)
        object.__setattr__(self, "resolution", resolution)

    @property
    def replay_resolvable(self) -> bool:
        """counterexample の replay の証明がこの blocker を解消してよいか。"""
        return self.resolution is SatSafetyResolution.REPLAY

    @property
    def completable(self) -> bool:
        """authority の cause を COMPLETED にしてよいか（解析の不安全は決して完了しない）。"""
        return self.resolution in {
            SatSafetyResolution.REPLAY,
            SatSafetyResolution.PARTITION_AMBIGUITY,
        }


def classify_sat_safety_blocker(reason_id: object, evidence_refs: Iterable[object]) -> SatSafetyBlocker:
    """(reason id, evidence ref の組) を分類する。整合しなければ ``SatSafetyBlockerInconsistent``。

    * reason id は表にある exact な str。ref は空でない exact な str。
    * replay 型: ref が 1 つ以上で、全てが replay の ref。
    * 解析の不安全: ref から選ぶ id が解析の不安全であること（空・混在・未知の ref を含む）。
    * partition の曖昧さ: ref が 1 つ以上で、replay の ref を含まない（id は ref から導けない
      独立の経路なので、replay の型と取り違えない条件だけを課す）。
    """
    if type(reason_id) is not str or reason_id not in SAT_SAFETY_REASON_RESOLUTION:
        raise SatSafetyBlockerInconsistent(f"unknown SAT-safety reason id: {reason_id!r}")
    refs = tuple(evidence_refs)
    if any(type(ref) is not str or not ref for ref in refs):
        raise SatSafetyBlockerInconsistent("SAT-safety evidence refs must be non-empty exact strings")
    resolution = SAT_SAFETY_REASON_RESOLUTION[reason_id]
    if resolution is SatSafetyResolution.PARTITION_AMBIGUITY:
        consistent = bool(refs) and COUNTEREXAMPLE_REPLAY_MISSING_REF not in refs
    else:
        consistent = sat_safety_reason_id_for_refs(refs) == reason_id
    if not consistent:
        raise SatSafetyBlockerInconsistent(
            f"SAT-safety reason id {reason_id!r} does not match its evidence refs {refs!r}"
        )
    return SatSafetyBlocker(reason_id, refs, resolution, _token=_BLOCKER_TOKEN)


def replay_may_resolve_sat_safety_reason(reason_id: object, evidence_refs: Iterable[object]) -> bool:
    """counterexample の replay の証明が、この (reason id, ref の組) を解消してよいか。

    整合しない対は偽（例外にしない。legacy の reason record の gate 用）。
    """
    try:
        return classify_sat_safety_blocker(reason_id, evidence_refs).replay_resolvable
    except SatSafetyBlockerInconsistent:
        return False
