"""SAT-safety の reason が何によって解消されてよいか（解消の型）の唯一の owner。

counterexample の replay は、SAT の model が宣言した記号へ与えた値を固定して、
同じ抽象式について「到達可能な case の組がすべて違う値になる」ことを確かめる
だけである。固定した値が実際の実行で同時に起こり得ること、解析が捨てた経路・
効果・入力の上位 bit が無いことは示さない。したがって replay が解消してよいのは
**replay 型**の理由（その witness の replay が済んでいないこと）だけで、解析の
不安全（解析の不完全・被覆の欠け・入力対応の不足）は replay では解消しない。

pairwise と monolithic、stage runner の gate はすべて、この module の
``replay_may_resolve_sat_safety_reason`` を通して同じ規則を読む。reason の
evidence ref から reason id を選ぶ規則（``sat_safety_reason_id_for_refs``）も
ここに置き、ref の部分文字列で型を推測しない。

この module は他の module を import しない（authority の leaf）。
"""

from __future__ import annotations

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

#: SAT-safety の typed reason id → 解消の型。``SAT_SAFETY_TYPED_REASON_IDS`` はこの表の key。
SAT_SAFETY_REASON_RESOLUTION: Mapping[str, SatSafetyResolution] = MappingProxyType({
    COUNTEREXAMPLE_ANALYSIS_SAFETY_UNPROVEN: SatSafetyResolution.ANALYSIS_UNSAFETY,
    COUNTEREXAMPLE_PARTITION_REPLAY_AMBIGUOUS: SatSafetyResolution.PARTITION_AMBIGUITY,
    COUNTEREXAMPLE_REPLAY_UNPROVEN: SatSafetyResolution.REPLAY,
})

#: replay 型の blocker を表す唯一の evidence ref。replay の要求を出す producer はこれを使う。
COUNTEREXAMPLE_REPLAY_MISSING_REF = "counterexample_replay_missing"


def sat_safety_ref_resolution(ref: object) -> SatSafetyResolution:
    """1 つの evidence ref の解消の型。replay の ref と完全一致するものだけが REPLAY。

    知らない ref は解析の不安全として扱う（fail-closed）。
    """
    if type(ref) is str and ref == COUNTEREXAMPLE_REPLAY_MISSING_REF:
        return SatSafetyResolution.REPLAY
    return SatSafetyResolution.ANALYSIS_UNSAFETY


def sat_safety_reason_id_for_refs(refs: Iterable[object]) -> str:
    """SAT unsafety の evidence ref の組から、その blocker の reason id を選ぶ。

    全ての ref が replay 型のときだけ ``counterexample_replay_unproven``。1 つでも
    解析の不安全の ref が混ざれば（空の組も）``counterexample_analysis_safety_unproven``。
    """
    refs = tuple(refs)
    if refs and all(
        sat_safety_ref_resolution(ref) is SatSafetyResolution.REPLAY for ref in refs
    ):
        return COUNTEREXAMPLE_REPLAY_UNPROVEN
    return COUNTEREXAMPLE_ANALYSIS_SAFETY_UNPROVEN


def replay_may_resolve_sat_safety_reason(reason_id: object, evidence_refs: Iterable[object]) -> bool:
    """counterexample の replay の証明が、この reason を解消してよいか。

    reason id の型が REPLAY で、しかも evidence ref の全てが replay 型のときだけ真。
    reason id と ref が食い違う record（手で組んだ・別の経路で作った）は解消しない。
    """
    if type(reason_id) is not str:
        return False
    if SAT_SAFETY_REASON_RESOLUTION.get(reason_id) is not SatSafetyResolution.REPLAY:
        return False
    return sat_safety_reason_id_for_refs(evidence_refs) == reason_id
