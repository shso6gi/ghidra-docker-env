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
OWNED_PRODUCER        analysis_limitation domain の reason → 新しい cause を発行
EXISTING_CAUSE        帰属キーに **ちょうど 1 つ** 対応する active occurrence
UNATTRIBUTED          上記以外（fail-closed。呼び出し側が ERROR に落とす）
===================== ==========================================================

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
UNATTRIBUTED = "UNATTRIBUTED"

#: 帰属できなかったときに結果へ載せる `failure_status`。
UNREGISTERED_REASON_STATUS = "unregistered_reason"
LIMITATION_UNATTRIBUTED_STATUS = "limitation_unattributed"

_ATTRIBUTED = frozenset({ATTRIBUTED_NEW_CAUSE, ATTRIBUTED_EXISTING_CAUSE})


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


def _observed_occurrences(session: Any) -> Dict[str, Any]:
    """event prefix に記録された occurrence を `occurrence_id` で引けるようにする。

    reducer は同じ `occurrence_id` の再観測を拒否するので、この写像は reducer の
    内部状態と一致する。active かどうかはここでは決めない（`c_active_base` が正）。
    """
    from scripts.function_tracer_pcode.authority.lifecycle.stream import (
        CauseObservedEventAuthority,
        EventType,
    )

    occurrences: Dict[str, Any] = {}
    for recorded in session.recorder.prefix_view().events:
        if recorded.header.event_type is not EventType.CAUSE_OBSERVED:
            continue
        payload = recorded.authority_payload
        if type(payload) is not CauseObservedEventAuthority:
            continue
        occurrence = payload.occurrence_authority.occurrence
        occurrences[occurrence.occurrence_id] = occurrence
    return occurrences


def _matching_active_rows(
    session: Any, key: CauseAttributionKey,
) -> Tuple[Tuple[Any, Any], ...]:
    """帰属キーに一意対応する active occurrence 候補を集める。"""
    expected = _recomputed_cause_identity(key)
    if expected is None:
        return ()
    prefix = session.recorder.prefix_view()
    projection = session.reducer.replay_prefix(prefix)
    occurrences = _observed_occurrences(session)
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

    if definition.domain == ANALYSIS_LIMITATION_DOMAIN:
        emitted = observe_analysis_limitation(
            reason_id=reason_id,
            limitation_site=limitation.site,
            target_key=limitation.target_key,
            missing_semantic_fact=limitation.missing_semantic_fact,
            evidence_refs=limitation.evidence_refs,
        )
        if emitted != 1:
            return LimitationAttribution(
                UNATTRIBUTED, reason_id,
                "analysis limitation producer did not materialize a cause",
            )
        return LimitationAttribution(
            ATTRIBUTED_NEW_CAUSE, reason_id,
            "analysis limitation producer materialized one new cause",
            decision_effect=definition.decision_effect,
        )

    if key is None:
        return LimitationAttribution(
            UNATTRIBUTED, reason_id,
            "limitation carries no cause attribution key",
        )
    if session is None:
        return LimitationAttribution(
            UNATTRIBUTED, reason_id,
            "no production pilot session is available to read active causes",
        )
    try:
        matches = _matching_active_rows(session, key)
    except Exception as exc:  # 読めないなら帰属できない（fail-closed）
        return LimitationAttribution(
            UNATTRIBUTED, reason_id,
            f"active cause prefix is unreadable: {type(exc).__name__}",
        )
    if len(matches) != 1:
        return LimitationAttribution(
            UNATTRIBUTED, reason_id,
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
