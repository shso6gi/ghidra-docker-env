"""authority の event / cause occurrence / relation の件数と表現量の契約（Issue #110）の唯一の owner。

pair ごとの sealed event stream に入る event の数・1 event の大きさ・stream 全体の大きさと、authority が
作る cause occurrence の数（= canonical reason の行数）・relation の行数（`c_active_base` /
`q_open_base`）の上限をここで決め、**event を作る時点**（session の publication gate、digest の前）で
強制する。authority の外（出力の schema など）がこれらの上限を使うときもここを正本として読み、
ここ以外に数値を書かない。封印（`authority/seal_work`）が作業量の上限を導く派生の上限（封印した形の
大きさ・projection / receipt / execution payload の上限）もここが持つ。

超えるときは、authority の判定の **前** に pair の限界（登録済みの理由 `analysis_budget_exceeded`、
限界の場所 `authority.event_contract`）にする: 限界を pair の台帳へ記録してから（pair terminal）、
その event の transaction を拒む。stream はそれまでの prefix のまま（部分的な event を残さない）で、
限界の cause（`analysis_limitation` domain）は予約した枠で必ず記録できる。判定は限界の cause が
`blocks_decision` なので UNKNOWN（EQ / NOT_EQ にならない）。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Optional, Sequence

from scripts.function_tracer_pcode.authority.canonical_units import canonical_units_within
from scripts.function_tracer_pcode.core.errors import (
    AnalysisLimitation,
    PairStopState,
    current_pair_ledger,
)

#: 契約の超過を表す限界の場所（cause identity の一部。限界ごとに別 cause）
EVENT_CONTRACT_LIMITATION_SITE = "authority.event_contract"


@dataclass(frozen=True)
class AuthorityEventContract:
    """pair ごとの authority event の上限（固定の契約の parameter）。

    値は固定 subset（main `9f79560`、139 pair）の実測の最大（event 98 件・1 event 43 KB・stream 731 KB・
    cause 54 件・relation 34 行）に対して 4〜40 倍の余裕を持つ 2 の冪。出力の schema（PR #190 の
    reason 256 行・relation 512 行）と同じ値を、ここを正本として共有する。
    """

    #: cause occurrence の数（canonical reason の行・`c_active_base` の行の上限）
    max_cause_occurrences: int = 256
    #: relation の行（`q_open_base` の行 = occurrence が束ねる proof requirement の数の上限）
    max_relation_rows: int = 512
    #: 1 stream の event の数
    max_events: int = 4096
    #: 1 event の authority / diagnostic payload の canonical unit
    max_event_payload_units: int = 1 << 20
    #: 1 stream の payload の canonical unit の合計
    max_stream_payload_units: int = 16 << 20
    #: 限界の cause（`analysis_limitation` domain）のための予約
    limitation_reserve_occurrences: int = 4
    #: 封印した形（codec が encode した event・replay した値）の単位は、payload の canonical unit の
    #: 高々この倍 + 1 event の枠（型の名前と payload の包み・dict の key の分）。固定 subset（main
    #: `9f79560`、4,626 event）の実測は 1.8 倍以下（2,000 単位を超える payload）・枠 1,966 単位以下
    sealed_form_factor: int = 4
    #: 封印した形の 1 event の枠（header・event digest・包み）の単位
    sealed_event_frame_units: int = 4096
    #: lifecycle projection（`c_active_base` / `q_open_base` / eligibility / satisfaction の行）の単位
    max_projection_units: int = 64 << 20
    #: receipt（decisive / timeout / error / decision / occurrence / selection）と bundle の固定の field の単位
    max_receipt_units: int = 4 << 20
    #: execution payload（pair の実行の identity）の単位
    max_execution_payload_units: int = 1 << 20

    def __post_init__(self) -> None:
        for name in (
            "max_cause_occurrences", "max_relation_rows", "max_events",
            "max_event_payload_units", "max_stream_payload_units",
            "limitation_reserve_occurrences", "sealed_form_factor", "sealed_event_frame_units",
            "max_projection_units", "max_receipt_units", "max_execution_payload_units",
        ):
            value = getattr(self, name)
            if type(value) is not int or value <= 0:
                raise ValueError(f"authority event contract {name} is not a positive int")
        if self.limitation_reserve_occurrences >= self.max_cause_occurrences:
            raise ValueError("the limitation reserve must leave room for ordinary causes")

    @property
    def max_sealed_stream_units(self) -> int:
        """封印した形の stream の単位の上限（契約の内側の stream はこれを超えない）。"""

        return (
            self.sealed_form_factor * self.max_stream_payload_units
            + self.max_events * self.sealed_event_frame_units
        )

    @property
    def ordinary_cause_occurrences(self) -> int:
        """限界の cause 以外の occurrence が使える数（予約を除く）。"""

        return self.max_cause_occurrences - self.limitation_reserve_occurrences

    @property
    def ordinary_relation_rows(self) -> int:
        return self.max_relation_rows - self.limitation_reserve_occurrences

    @property
    def ordinary_events(self) -> int:
        return self.max_events - self.limitation_reserve_occurrences

    @property
    def ordinary_stream_payload_units(self) -> int:
        return self.max_stream_payload_units - (
            self.limitation_reserve_occurrences * _LIMITATION_EVENT_UNITS
        )


#: 限界の cause の event 1 つの canonical unit の上限（予約する stream の大きさ）
_LIMITATION_EVENT_UNITS = 64 * 1024

AUTHORITY_EVENT_CONTRACT = AuthorityEventContract()


class AuthorityEventContractExceeded(AnalysisLimitation):
    """authority event の契約を超えた（判定の前の pair の限界）。

    pair の台帳へ記録してから上げる（途中で握り潰されても、pair 境界が限界として読む）。
    """

    def __init__(self, bound: str, *, limit: int, observed: int) -> None:
        from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
            ANALYSIS_BUDGET_REASON_ID,
        )

        super().__init__(
            ANALYSIS_BUDGET_REASON_ID,
            f"authority event contract {bound} exceeded ({observed} > {limit})",
            site=EVENT_CONTRACT_LIMITATION_SITE,
            target_key=("authority_event_contract", bound),
            missing_semantic_fact=("authority_event_contract", bound, limit),
            evidence_refs=(f"limit={limit}",),
        )
        self.bound = bound
        self.limit = limit
        self.observed = observed


@dataclass(frozen=True)
class _Admission:
    #: 数えた時の勘定（publish の時点で勘定が進んでいれば、この admission は古い: 数え直す）
    base: tuple
    events: int
    ordinary_occurrences: int
    limitation_occurrences: int
    relation_rows: int
    payload_units: int


class EventContractLedger:
    """1 session の authority event の勘定（publication gate が transaction ごとに 1 回だけ数える）。

    数えるのは publish した event だけ（拒んだ transaction は数えない）。occurrence の数・relation の
    行は event の authority から数え、payload の大きさは digest の前に上限まで測る。
    """

    __slots__ = (
        "contract", "events", "ordinary_occurrences", "limitation_occurrences",
        "relation_rows", "payload_units", "exceeded",
    )

    def __init__(self, contract: AuthorityEventContract = AUTHORITY_EVENT_CONTRACT) -> None:
        if type(contract) is not AuthorityEventContract:
            raise TypeError("an event contract ledger needs an exact contract")
        self.contract = contract
        self.events = 0
        self.ordinary_occurrences = 0
        self.limitation_occurrences = 0
        self.relation_rows = 0
        self.payload_units = 0
        #: 最初に超えた契約（超えた後の ordinary な transaction は全部拒む: stream は prefix のまま）
        self.exceeded: Optional[AuthorityEventContractExceeded] = None

    @property
    def limitation_recorded(self) -> bool:
        """契約の超過を記録する限界の cause を publish したか（判定が必ず UNKNOWN になる）。"""

        return self.limitation_occurrences > 0

    def admit(self, intents: Sequence[Any], *, pending_occurrences: int = 0) -> _Admission:
        """transaction を publish してよいか確かめ、よければ publish 後の勘定を返す（まだ数えない）。

        超えるなら限界を pair の台帳へ記録して `AuthorityEventContractExceeded` を上げる。件数は測る前に
        （O(1) で）比べ、payload は 1 event ずつ、残りの枠（1 event の上限と stream の残りの小さい方）
        まで測る: 超える transaction を全部測ってから拒まない。`pending_occurrences` は判定の前に必ず
        publish される予定の occurrence（遅延した SAT-safety の観測など）。
        """

        contract = self.contract
        limitation_only = bool(intents) and all(_is_limitation_cause(intent) for intent in intents)
        if self.exceeded is not None and not limitation_only:
            raise self.exceeded
        if limitation_only:
            # 予約した枠（限界の cause）: 上限そのものまで
            event_limit, cause_limit = contract.max_events, contract.max_cause_occurrences
            relation_limit, unit_limit = contract.max_relation_rows, contract.max_stream_payload_units
        else:
            event_limit, cause_limit = contract.ordinary_events, contract.ordinary_cause_occurrences
            relation_limit, unit_limit = contract.ordinary_relation_rows, contract.ordinary_stream_payload_units
        events = self.events + len(intents)
        if events > event_limit:
            self._exceed("events", event_limit, events)
        ordinary = self.ordinary_occurrences
        limitation = self.limitation_occurrences
        relations = self.relation_rows
        units = self.payload_units
        for intent in intents:
            occurrence = _occurrence_of(intent)
            if occurrence is not None:
                if _is_limitation_cause(intent):
                    limitation += 1
                else:
                    ordinary += 1
                relations += len(occurrence.proof_requirement_ids)
                causes = ordinary + limitation if limitation_only else ordinary + pending_occurrences
                if causes > cause_limit:
                    self._exceed("cause_occurrences", cause_limit, causes)
                if relations > relation_limit:
                    self._exceed("relation_rows", relation_limit, relations)
            remaining = unit_limit - units
            per_event = min(contract.max_event_payload_units, remaining)
            measured = _payload_units(intent, per_event) if per_event >= 0 else None
            if measured is None:
                if per_event < contract.max_event_payload_units:
                    self._exceed("stream_payload_units", unit_limit, unit_limit + 1)
                self._exceed("event_payload_units", contract.max_event_payload_units,
                             contract.max_event_payload_units + 1)
            units += measured
        if not limitation_only and ordinary + pending_occurrences > cause_limit:
            self._exceed("cause_occurrences", cause_limit, ordinary + pending_occurrences)
        return _Admission(self._state(), events, ordinary, limitation, relations, units)

    def _state(self) -> tuple:
        return (
            self.events, self.ordinary_occurrences, self.limitation_occurrences,
            self.relation_rows, self.payload_units,
        )

    def is_current(self, admission: Any) -> bool:
        """`admission` が今の勘定の上で数えたものか（古ければ publish の前に数え直す）。"""

        return type(admission) is _Admission and admission.base == self._state()

    def commit(self, admission: _Admission) -> None:
        """`admit` が返した勘定を publish の後に 1 回だけ反映する。"""

        if type(admission) is not _Admission:
            raise TypeError("event contract commit needs an admission")
        if admission.base != self._state():
            raise ValueError("event contract admission is stale")
        self.events = admission.events
        self.ordinary_occurrences = admission.ordinary_occurrences
        self.limitation_occurrences = admission.limitation_occurrences
        self.relation_rows = admission.relation_rows
        self.payload_units = admission.payload_units

    def checkpoint(self, *, pending_occurrences: int) -> None:
        """判定の前の確認: 予定の occurrence を足しても枠が残るか（超えるなら限界を記録して上げる）。"""

        if self.exceeded is not None:
            raise self.exceeded
        observed = self.ordinary_occurrences + pending_occurrences
        if observed > self.contract.ordinary_cause_occurrences:
            self._exceed("cause_occurrences", self.contract.ordinary_cause_occurrences, observed)

    def _exceed(self, bound: str, limit: int, observed: int) -> None:
        exceeded = AuthorityEventContractExceeded(bound, limit=limit, observed=observed)
        self.exceeded = exceeded
        ledger = current_pair_ledger()
        if ledger is not None:
            ledger.record_limitation(exceeded, stop=PairStopState.PAIR_TERMINAL_LIMITATION)
        raise exceeded


def require_events_within_contract(
    count: int, *, contract: AuthorityEventContract = AUTHORITY_EVENT_CONTRACT,
) -> None:
    """記録済みの stream（durable な prefix・composite stream）の event 数が契約の中か（O(1)。外なら `ValueError`）。

    検証（hash chain・replay）の仕事は event 数に比例する: 契約の外の stream は検証を始めずに無効にする。
    """

    if type(count) is not int or count > contract.max_events:
        raise ValueError(
            f"recorded event stream has {count} events, outside the authority event contract"
        )


def _occurrence_of(intent: Any) -> Any:
    from scripts.function_tracer_pcode.authority.lifecycle.stream import (
        CauseObservedEventAuthority,
        EventType,
    )

    if getattr(intent, "event_type", None) is not EventType.CAUSE_OBSERVED:
        return None
    payload = intent.authority_payload
    if type(payload) is not CauseObservedEventAuthority:
        return None
    return payload.occurrence_authority.occurrence


def _is_limitation_cause(intent: Any) -> bool:
    """予約した枠を使える event か: `analysis_limitation` domain の cause（pair の限界の cause）。

    契約の超過そのものの限界だけでなく、それより前に台帳へ記録された別の限界（gate が帰属させる
    winner）の cause も予約した枠で publish できる（超過の後でも限界が帰属でき、ERROR にならない）。
    限界の cause は限界ごとに 1 つ（encoder が target ごとに重複を除く）なので、予約は小さい。
    """
    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        ANALYSIS_LIMITATION_TARGET_KIND,
    )

    occurrence = _occurrence_of(intent)
    return occurrence is not None and occurrence.target_kind == ANALYSIS_LIMITATION_TARGET_KIND


def _payload_units(intent: Any, limit: int) -> Optional[int]:
    """event の authority / diagnostic payload の canonical unit（`limit` を超えれば `None`）。"""

    authority = canonical_units_within(intent.authority_payload, limit)
    if authority is None:
        return None
    diagnostic = canonical_units_within(intent.diagnostic_payload, max(0, limit - authority))
    if diagnostic is None:
        return None
    return authority + diagnostic


__all__ = [
    "require_events_within_contract",
    "AUTHORITY_EVENT_CONTRACT",
    "AuthorityEventContract",
    "AuthorityEventContractExceeded",
    "EVENT_CONTRACT_LIMITATION_SITE",
    "EventContractLedger",
]
