# -*- coding: utf-8 -*-
"""Attribute one analysis limitation to exactly one authority cause (Issue #125).

原則: 「同じ種類の cause」ではなく、**その cause が解消されたなら今回の限界も
解消されたと言える対応関係**だけを帰属とみなす。cause が active から外れるのは
その occurrence の satisfaction 式が完了 requirement で満たされたときだけなので
(`authority/lifecycle/reducer.py`)、対応関係は欠落事実・対象・scope・
requirement 集合の一致を全部要求する。

判定順:

===================== ==========================================================
UNREGISTERED          `reason_id` が sealed registry に無い / retired umbrella
OWNED_PRODUCER        analysis_limitation domain の reason → cause を観測し、
                      **その occurrence が現在 active か** を projection で確認
EXISTING_CAUSE        帰属キーに **ちょうど 1 つ** 対応する active occurrence
TRUNCATED_STREAM      上記で帰属できず、authority event の契約が stream を切った（Issue #110）→
                      契約の超過の限界の cause（専用の枠で必ず publish できる）へ帰属
UNATTRIBUTED          上記以外（fail-closed。呼び出し側が ERROR に落とす）
===================== ==========================================================

切られた stream では、限界の cause そのものが拒まれて publish できないことがある（予約の共有の枠を
他の限界が使い切ったとき）。その pair は契約の超過の限界の cause（`blocks_decision`、discharge する
producer が無い）が判定を止めているので、限界をそれへ帰属させる。帰属先の cause は解消されないので、
「cause が解消されたなら限界も解消された」の対応は空に成り立ち、EQ / NOT_EQ は通らない。

**「観測したことがある」と「今 active」は別**。producer の重複排除 ledger は
reducer の重複 occurrence 拒否を避けるための履歴で、requirement を discharge した
cause もそこに残る。履歴だけを根拠に帰属を成功させると、active な blocker が 1 つも
無いのに limitation が「帰属できた」ことになり、EQ / NOT_EQ の decisive proof が
そのまま通ってしまう。よって **両方の経路とも** active 判定は現在の
`c_active_base` を唯一の authority とし、discharge 済みの限界を再観測した場合は
（PR-125-A の範囲で健全な再 activation authority を定義できないので）
`limitation_unattributed` で fail-closed にする。

帰属は cause を**追加も強化もしない**（既存 active cause の存在を確認するだけ）。
したがって EQ / NOT_EQ の証明条件は変わらず、`blocks_equivalence` の cause に
帰属した限界が NOT_EQ を塞ぐこともない（塞いでいるのはその cause 自身で、
`finalize_decision` の既存規則がそのまま効く）。一致する cause が無い＝限界を
表現する authority が無いので ERROR にする。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Optional, Tuple

from scripts.function_tracer_pcode.core.errors import (
    AnalysisLimitation,
    CauseAttributionKey,
)
from scripts.function_tracer_pcode.authority.contracts import IdentityScope
from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
    ANALYSIS_LIMITATION_DOMAIN,
    observe_analysis_limitation,
)


#: `attribute_analysis_limitation` が返す判定。
UNREGISTERED = "UNREGISTERED"
ATTRIBUTED_NEW_CAUSE = "ATTRIBUTED_NEW_CAUSE"
ATTRIBUTED_EXISTING_CAUSE = "ATTRIBUTED_EXISTING_CAUSE"
ATTRIBUTED_TRUNCATED_STREAM = "ATTRIBUTED_TRUNCATED_STREAM"
UNATTRIBUTED = "UNATTRIBUTED"

#: 帰属できなかったときに結果へ載せる `failure_status`。
UNREGISTERED_REASON_STATUS = "unregistered_reason"
LIMITATION_UNATTRIBUTED_STATUS = "limitation_unattributed"

_ATTRIBUTED = frozenset({
    ATTRIBUTED_NEW_CAUSE, ATTRIBUTED_EXISTING_CAUSE, ATTRIBUTED_TRUNCATED_STREAM,
})


@dataclass(frozen=True)
class LimitationAttribution:
    """1 件の限界をどの cause へ帰属させたか（判定には直接効かない記述）。"""

    disposition: str
    reason_id: str
    detail: str
    cause_id: Optional[str] = None
    occurrence_id: Optional[str] = None
    decision_effect: Optional[str] = None

    @property
    def is_attributed(self) -> bool:
        return self.disposition in _ATTRIBUTED

    @property
    def failure_status(self) -> Optional[str]:
        if self.disposition == UNREGISTERED:
            return UNREGISTERED_REASON_STATUS
        if self.disposition == UNATTRIBUTED:
            return LIMITATION_UNATTRIBUTED_STATUS
        return None

    def to_diagnostic(self) -> Dict[str, Any]:
        return {
            "disposition": self.disposition,
            "reason_id": self.reason_id,
            "cause_id": self.cause_id,
            "occurrence_id": self.occurrence_id,
            "decision_effect": self.decision_effect,
            "detail": self.detail,
        }


def _active_pilot_session() -> Optional[Any]:
    from scripts.function_tracer_pcode.authority.lifecycle.production_context import (
        active_production_pilot_session,
    )

    return active_production_pilot_session()


def _reason_definition(reason_id: str) -> Optional[Any]:
    from scripts.function_tracer_pcode.authority.sites.activation import (
        RETIRED_UMBRELLA_REASON_IDS,
    )
    from scripts.function_tracer_pcode.authority.process.supervisor import (
        PROCESS_DURABLE_REASON_REGISTRY,
    )

    if reason_id in RETIRED_UMBRELLA_REASON_IDS:
        return None
    try:
        return PROCESS_DURABLE_REASON_REGISTRY.get(reason_id)
    except (KeyError, ValueError):
        return None


def _recomputed_cause_identity(key: CauseAttributionKey) -> Optional[Any]:
    """帰属キーから `CauseIdV2` を再計算する（digest の内訳は再実装しない）。

    再計算が一致すれば identity_scope / reason_id / canonical_target_key /
    missing_semantic_fact / semantic_proposition_digest の 5 要素が一致したこと
    になる。`target_kind` は digest に含まれないので呼び出し側が独立に照合する。
    """
    from scripts.function_tracer_pcode.authority.registry import (
        SemanticCauseIdentityFactory,
    )
    from scripts.function_tracer_pcode.authority.process.supervisor import (
        PROCESS_DURABLE_REASON_REGISTRY,
    )

    try:
        return SemanticCauseIdentityFactory(PROCESS_DURABLE_REASON_REGISTRY).create(
            reason_id=key.reason_id,
            identity_scope=IdentityScope(key.identity_scope),
            target_kind=key.target_kind,
            canonical_target_key=key.canonical_target_key,
            missing_semantic_fact=key.missing_semantic_fact,
            semantic_proposition=key.semantic_proposition,
            observation_surface=key.observation_surface,
            active_semantic_precondition=key.active_semantic_precondition,
            correspondence_contract=key.correspondence_contract,
        )
    except (KeyError, TypeError, ValueError):
        return None


def _observed_occurrences(prefix: Any) -> Dict[str, Any]:
    """event prefix に記録された occurrence を `occurrence_id` で引けるようにする。

    reducer は同じ `occurrence_id` の再観測を拒否するので、この写像は reducer の
    内部状態と一致する。active かどうかはここでは決めない（`c_active_base` が正）。
    projection を作ったのと **同じ prefix** を受け取る（別々に prefix を取ると、
    間に event が積まれたときに projection と occurrence 写像が食い違う）。
    """
    from scripts.function_tracer_pcode.authority.lifecycle.stream import (
        CauseObservedEventAuthority,
        EventType,
    )

    occurrences: Dict[str, Any] = {}
    for recorded in prefix.events:
        if recorded.header.event_type is not EventType.CAUSE_OBSERVED:
            continue
        payload = recorded.authority_payload
        if type(payload) is not CauseObservedEventAuthority:
            continue
        occurrence = payload.occurrence_authority.occurrence
        occurrences[occurrence.occurrence_id] = occurrence
    return occurrences


def _current_projection(session: Any) -> Tuple[Any, Any]:
    """現在の event prefix と、それを reduce した lifecycle projection。

    `worker_runtime.prepare` と同じ読み方。prefix は 1 度だけ取り、projection と
    occurrence 写像の両方に同じものを使う。event が 1 件も無い prefix は封印
    できないので `(None, None)` を返す（event が無い = active な cause も無い）。
    """
    if not getattr(session.recorder, "event_count", 0):
        return None, None
    prefix = session.recorder.prefix_view()
    return prefix, session.reducer.replay_prefix(prefix)


def _active_row_for_occurrence(session: Any, occurrence_id: str) -> Optional[Any]:
    """`occurrence_id` が現在 active なら、その `c_active_base` 行を返す。

    履歴（観測したことがあるか）ではなく **現在の projection** を見る。
    """
    _prefix, projection = _current_projection(session)
    if projection is None:
        return None
    for row in projection.c_active_base:
        if row.occurrence_id == occurrence_id:
            return row
    return None


def _matching_active_rows(
    session: Any, key: CauseAttributionKey,
) -> Tuple[Tuple[Any, Any], ...]:
    """帰属キーに一意対応する active occurrence 候補を集める。"""
    expected = _recomputed_cause_identity(key)
    if expected is None:
        return ()
    prefix, projection = _current_projection(session)
    if projection is None:
        return ()
    occurrences = _observed_occurrences(prefix)
    requirement_ids = frozenset(key.proof_requirement_ids)
    matches = []
    for row in projection.c_active_base:
        if (
            row.reason_id != key.reason_id
            or row.target_kind != key.target_kind
            or row.cause_id != expected.value
        ):
            continue
        occurrence = occurrences.get(row.occurrence_id)
        if occurrence is None:
            continue
        cause_id = occurrence.cause_id
        if (
            occurrence.reason_id != key.reason_id
            or occurrence.target_kind != key.target_kind
            or occurrence.identity_scope.value != key.identity_scope
            or cause_id.value != expected.value
            or cause_id.canonical_target_key != expected.canonical_target_key
            or cause_id.missing_semantic_fact != expected.missing_semantic_fact
            or cause_id.semantic_proposition_digest
            != expected.semantic_proposition_digest
            or frozenset(occurrence.proof_requirement_ids) != requirement_ids
            or len(occurrence.proof_requirement_ids) != len(requirement_ids)
        ):
            continue
        matches.append((row, occurrence))
    return tuple(matches)


def _unattributed(
    pilot: Any, limitation: AnalysisLimitation, detail: str,
) -> LimitationAttribution:
    """帰属できなかった: stream が切られていれば契約の超過の限界の cause（active）へ帰属させる。"""

    unattributed = LimitationAttribution(UNATTRIBUTED, limitation.reason_id, detail)
    if pilot is None or getattr(pilot, "stream_truncated", False) is not True:
        return unattributed
    try:
        occurrence_id = pilot.ensure_event_contract_limitation()
        row = (
            None if occurrence_id is None
            else _active_row_for_occurrence(pilot, occurrence_id)
        )
    except (TypeError, ValueError) as exc:
        return LimitationAttribution(
            UNATTRIBUTED, limitation.reason_id,
            f"{detail}; the truncated stream's contract cause is not active: "
            f"{type(exc).__name__}",
        )
    if row is None:
        return unattributed
    return LimitationAttribution(
        ATTRIBUTED_TRUNCATED_STREAM, limitation.reason_id,
        "the authority event contract truncated the stream before this limitation "
        f"could be attributed ({detail}); the contract limitation cause blocks the decision",
        cause_id=row.cause_id,
        occurrence_id=row.occurrence_id,
        decision_effect=row.decision_effect,
    )


def attribute_analysis_limitation(
    session: Any, limitation: AnalysisLimitation,
) -> LimitationAttribution:
    """1 件の限界を、判定 authority の cause へ帰属させる（できなければ fail-closed）。"""

    if not isinstance(limitation, AnalysisLimitation):
        raise TypeError("limitation attribution requires an exact analysis limitation")
    reason_id = limitation.reason_id
    key = limitation.attribution

    definition = _reason_definition(reason_id)
    if definition is None:
        return LimitationAttribution(
            UNREGISTERED, reason_id,
            "limitation reason is not a sealed v2 reason",
        )
    if key is not None and key.reason_id != reason_id:
        # 例外と帰属キーの reason が食い違う。どちらを信じるかを決める根拠が無い。
        return LimitationAttribution(
            UNATTRIBUTED, reason_id,
            "attribution key reason differs from the limitation reason",
        )

    # emit が届く session（contextvar）と checker が持つ view は production では
    # 同じ object。明示引数を優先し、無ければ emit と同じ session を読む。
    pilot = session if session is not None else _active_pilot_session()

    if definition.domain == ANALYSIS_LIMITATION_DOMAIN:
        if pilot is None:
            return _unattributed(
                pilot, limitation,
                "no production pilot session is available to confirm an active cause",
            )
        try:
            occurrence_id = observe_analysis_limitation(
                reason_id=reason_id,
                limitation_site=limitation.site,
                target_key=limitation.target_key,
                missing_semantic_fact=limitation.missing_semantic_fact,
                evidence_refs=limitation.evidence_refs,
            )
            row = (
                None if occurrence_id is None
                else _active_row_for_occurrence(pilot, occurrence_id)
            )
        except Exception as exc:  # 観測も確認もできないなら帰属できない
            return _unattributed(
                pilot, limitation,
                f"analysis limitation producer failed: {type(exc).__name__}",
            )
        if occurrence_id is None:
            return _unattributed(
                pilot, limitation,
                "analysis limitation producer did not observe a cause",
            )
        if row is None:
            # 過去に観測済みでも、その cause が discharge 済みなら未解消の
            # blocker は存在しない。履歴だけを根拠に成功扱いしない。
            return _unattributed(
                pilot, limitation,
                "the limitation cause is not active in the current lifecycle "
                "projection (a discharged observation is not re-activated here)",
            )
        return LimitationAttribution(
            ATTRIBUTED_NEW_CAUSE, reason_id,
            "analysis limitation producer materialized one active cause",
            cause_id=row.cause_id,
            occurrence_id=row.occurrence_id,
            # active 行の effect をそのまま使う（registry と同値。強化しない）。
            decision_effect=row.decision_effect,
        )

    if key is None:
        return _unattributed(
            pilot, limitation,
            "limitation carries no cause attribution key",
        )
    if pilot is None:
        return _unattributed(
            pilot, limitation,
            "no production pilot session is available to read active causes",
        )
    try:
        matches = _matching_active_rows(pilot, key)
    except Exception as exc:  # 読めないなら帰属できない（fail-closed）
        return _unattributed(
            pilot, limitation,
            f"active cause prefix is unreadable: {type(exc).__name__}",
        )
    if len(matches) != 1:
        return _unattributed(
            pilot, limitation,
            f"attribution key matches {len(matches)} active causes, not exactly one",
        )
    row, occurrence = matches[0]
    return LimitationAttribution(
        ATTRIBUTED_EXISTING_CAUSE, reason_id,
        "limitation corresponds to one existing active cause",
        cause_id=row.cause_id,
        occurrence_id=occurrence.occurrence_id,
        # 既存 cause の effect をそのまま尊重する（強化も緩和もしない）。
        decision_effect=row.decision_effect,
    )
