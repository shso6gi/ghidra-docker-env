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

from dataclasses import dataclass, fields
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
    """pair ごとの authority event の上限（固定の契約の parameter）。**契約の数値はここだけに書く**。

    値は固定 subset（main `9f79560`、139 pair）の実測の最大（event 98 件・1 event 43 KB・stream 731 KB・
    cause 54 件・relation 34 行）に対して 4〜40 倍の余裕を持つ 2 の冪。出力の schema（PR #190 の
    reason 256 行・relation 512 行）と同じ値を、ここを正本として共有する。

    予約（`limitation_reserve_occurrences`）は限界の cause（`analysis_limitation` domain）のための枠で、
    そのうち 1 つは **契約の超過そのものの限界の cause** 専用（他の限界の cause が使い切れない）。
    """

    #: cause occurrence の数（canonical reason の行・`c_active_base` の行の上限）
    max_cause_occurrences: int = 256
    #: relation の行（`q_open_base` の行 = occurrence が束ねる proof requirement の数の上限）
    max_relation_rows: int = 512
    #: worker の 1 stream の event の数
    max_events: int = 4096
    #: 1 event の authority / diagnostic payload の canonical unit
    max_event_payload_units: int = 1 << 20
    #: 1 stream の payload の canonical unit の合計
    max_stream_payload_units: int = 16 << 20
    #: 限界の cause（`analysis_limitation` domain）のための予約（1 つは契約の超過の限界の cause 専用）
    limitation_reserve_occurrences: int = 4
    #: 限界の cause の event 1 つの payload の canonical unit（予約する stream の大きさ。限界の event は
    #: 1 event の上限ではなくこの上限で測る: 契約の超過の限界の cause は固定の形で、必ずこの中に入る）
    max_limitation_event_units: int = 64 << 10
    #: supervisor が worker の prefix に足す終端の event（PROCESS_TIMEOUT / ERROR）の数
    supervisor_terminal_events: int = 1
    #: supervisor の終端の event 1 つの payload の canonical unit
    max_terminal_event_units: int = 64 << 10
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
    #: 結果の payload 全体を preimage にする封印（CLI・結果の検証・reporting）の preimage の単位
    max_result_preimage_units: int = 256 << 20
    #: supervisor の終端の封印（固定の形の preimage）の preimage の単位
    max_supervisor_preimage_units: int = 64 << 10
    #: bundle の固定の包み（field の名前・digest・schema）の単位
    bundle_frame_units: int = 4096

    def __post_init__(self) -> None:
        for field_ in fields(self):
            value = getattr(self, field_.name)
            if type(value) is not int or value <= 0:
                raise ValueError(f"authority event contract {field_.name} is not a positive int")
        if self.limitation_reserve_occurrences >= min(
            self.max_cause_occurrences, self.max_relation_rows, self.max_events,
        ):
            raise ValueError("the limitation reserve must leave room for ordinary causes")
        if self.limitation_reserve_occurrences * self.max_limitation_event_units >= (
            self.max_stream_payload_units
        ):
            raise ValueError("the limitation reserve must leave stream room for ordinary events")

    @property
    def max_sealed_events(self) -> int:
        """封印・検証する stream の event の数の上限（worker の stream + supervisor の終端の event）。"""

        return self.max_events + self.supervisor_terminal_events

    @property
    def max_sealed_stream_units(self) -> int:
        """封印した形の stream の単位の上限（契約の内側の stream と supervisor の終端はこれを超えない）。"""

        return (
            self.sealed_form_factor * (
                self.max_stream_payload_units
                + self.supervisor_terminal_events * self.max_terminal_event_units
            )
            + self.max_sealed_events * self.sealed_event_frame_units
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
            self.limitation_reserve_occurrences * self.max_limitation_event_units
        )


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


#: admission の種類（transaction の全 intent が何か）
_ORDINARY = "ordinary"
#: 限界の cause（契約の超過以外の限界を含む）だけ: 予約のうち契約の超過の枠を除いた分まで
_LIMITATION = "limitation"
#: 契約の超過そのものの限界の cause だけ: 上限そのものまで（専用の 1 枠）
_CONTRACT = "contract"


@dataclass(frozen=True)
class _Admission:
    #: 数えた時の勘定（publish の時点で勘定が進んでいれば、この admission は古い: 数え直す）
    base: tuple
    events: int
    ordinary_occurrences: int
    limitation_occurrences: int
    relation_rows: int
    payload_units: int
    #: この transaction が publish する cause occurrence の id（遅延した約束を果たしたかを commit で反映する）
    occurrence_ids: tuple
    #: 契約の超過の限界の cause を publish するか（専用の枠を使い切る）
    publishes_contract_cause: bool


@dataclass(frozen=True)
class _Commit:
    """`commit` を取り消すための記録（publish が失敗したときだけ使う）。"""

    base: tuple
    after: tuple
    added_ids: tuple


class EventContractLedger:
    """1 session の authority event の勘定（publication gate が transaction ごとに 1 回だけ数える）。

    数えるのは publish した event だけ（拒んだ transaction は数えない）。occurrence の数・relation の
    行は event の authority から数え、payload の大きさは digest の前に上限まで測る。

    判定の前に publish すると約束した occurrence（遅延した SAT-safety の観測）は `defer` で約束の時点に
    数え、publish したとき（`commit`）か約束が消えたとき（`release`）に約束の勘定から外す: 同じ occurrence を
    約束と publish の 2 回数えない（exact-once）。約束の数も契約の中（約束の時点で超えれば拒む）。

    予約のうち 1 枠（1 cause・1 event・その relation の行・限界の event 1 つの単位）は、契約の超過の
    限界の cause が publish されるまで、他のどの transaction も使えない。
    """

    __slots__ = (
        "contract", "events", "ordinary_occurrences", "limitation_occurrences",
        "relation_rows", "payload_units", "exceeded", "deferred_unpublished",
        "contract_cause_published", "_deferred_ids", "_published_ids",
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
        #: 約束して、まだ publish していない occurrence の数
        self.deferred_unpublished = 0
        #: 契約の超過の限界の cause を publish したか（専用の枠を使った）
        self.contract_cause_published = False
        #: 約束した occurrence の id（契約で `ordinary + 約束` 以下に抑えるので有界）
        self._deferred_ids: set = set()
        #: publish した cause occurrence の id（契約で `max_cause_occurrences` 以下に抑えるので有界）
        self._published_ids: set = set()

    @property
    def stream_truncated(self) -> bool:
        """契約を超えた（sticky）: stream はその時点までの prefix で、判定は契約の限界の cause が決める。"""

        return self.exceeded is not None

    @property
    def limitation_recorded(self) -> bool:
        """限界の cause（`analysis_limitation` domain）を 1 つ以上 publish したか。"""

        return self.limitation_occurrences > 0

    def refuse_if_truncated(self) -> None:
        """切られた stream へ ordinary な transaction を作らせない（encode の前に O(1) で拒む）。"""

        if self.exceeded is not None:
            raise self.exceeded

    def _limits(self, kind: str) -> tuple:
        """(event, cause の合計, relation, stream の単位) の上限。専用の枠は使われるまで残す。"""

        contract = self.contract
        if kind == _CONTRACT:
            return (
                contract.max_events, contract.max_cause_occurrences,
                contract.max_relation_rows, contract.max_stream_payload_units,
            )
        slot = 0 if self.contract_cause_published else 1
        if kind == _LIMITATION:
            return (
                contract.max_events - slot, contract.max_cause_occurrences - slot,
                contract.max_relation_rows - slot,
                contract.max_stream_payload_units - slot * contract.max_limitation_event_units,
            )
        return (
            contract.ordinary_events, contract.max_cause_occurrences - slot,
            contract.ordinary_relation_rows, contract.ordinary_stream_payload_units,
        )

    def admit(self, intents: Sequence[Any]) -> _Admission:
        """transaction を publish してよいか確かめ、よければ publish 後の勘定を返す（まだ数えない）。

        超えるなら限界を pair の台帳へ記録して `AuthorityEventContractExceeded` を上げる。件数は測る前に
        （O(1) で）比べ、payload は 1 event ずつ、残りの枠（1 event の上限と stream の残りの小さい方）
        まで測る: 超える transaction を全部測ってから拒まない。cause の数は、publish 済み・この
        transaction・約束して未 publish の合計（約束をこの transaction が果たすなら 1 回だけ数える）。
        """

        contract = self.contract
        kind = _admission_kind(intents)
        if self.exceeded is not None and kind == _ORDINARY:
            raise self.exceeded
        event_limit, cause_limit, relation_limit, unit_limit = self._limits(kind)
        events = self.events + len(intents)
        if events > event_limit:
            self._exceed("events", event_limit, events)
        ordinary = self.ordinary_occurrences
        limitation = self.limitation_occurrences
        pending = self.deferred_unpublished
        relations = self.relation_rows
        units = self.payload_units
        occurrence_ids = []
        for intent in intents:
            occurrence = _occurrence_of(intent)
            is_limitation = occurrence is not None and _is_limitation_cause(intent)
            if occurrence is not None:
                occurrence_id = occurrence.occurrence_id
                if (
                    occurrence_id in self._deferred_ids
                    and occurrence_id not in self._published_ids
                    and occurrence_id not in occurrence_ids
                ):
                    # 約束を果たす occurrence: 約束の勘定から publish の勘定へ移す（2 回数えない）
                    pending -= 1
                occurrence_ids.append(occurrence_id)
                if is_limitation:
                    limitation += 1
                else:
                    ordinary += 1
                relations += len(occurrence.proof_requirement_ids)
                total = ordinary + limitation + pending
                if total > cause_limit:
                    self._exceed("cause_occurrences", cause_limit, total)
                if kind == _ORDINARY and ordinary + pending > contract.ordinary_cause_occurrences:
                    self._exceed(
                        "cause_occurrences", contract.ordinary_cause_occurrences, ordinary + pending,
                    )
                if relations > relation_limit:
                    self._exceed("relation_rows", relation_limit, relations)
            event_bound = (
                contract.max_limitation_event_units if is_limitation
                else contract.max_event_payload_units
            )
            remaining = unit_limit - units
            per_event = min(event_bound, remaining)
            measured = _payload_units(intent, per_event) if per_event >= 0 else None
            if measured is None:
                if per_event < event_bound:
                    self._exceed("stream_payload_units", unit_limit, unit_limit + 1)
                self._exceed("event_payload_units", event_bound, event_bound + 1)
            units += measured
        return _Admission(
            self._state(), events, ordinary, limitation, relations, units, tuple(occurrence_ids),
            kind == _CONTRACT,
        )

    def _state(self) -> tuple:
        return (
            self.events, self.ordinary_occurrences, self.limitation_occurrences,
            self.relation_rows, self.payload_units, self.deferred_unpublished,
            self.contract_cause_published,
        )

    def is_current(self, admission: Any) -> bool:
        """`admission` が今の勘定の上で数えたものか（古ければ publish の前に数え直す）。"""

        return type(admission) is _Admission and admission.base == self._state()

    def commit(self, admission: _Admission) -> _Commit:
        """`admit` が返した勘定を publish の **前** に 1 回だけ反映する（publish が失敗したら `undo`）。"""

        if type(admission) is not _Admission:
            raise TypeError("event contract commit needs an admission")
        if admission.base != self._state():
            raise ValueError("event contract admission is stale")
        added, fulfilled = [], []
        for occurrence_id in admission.occurrence_ids:
            if occurrence_id in self._published_ids:
                continue
            self._published_ids.add(occurrence_id)
            added.append(occurrence_id)
            if occurrence_id in self._deferred_ids:
                fulfilled.append(occurrence_id)
        self.events = admission.events
        self.ordinary_occurrences = admission.ordinary_occurrences
        self.limitation_occurrences = admission.limitation_occurrences
        self.relation_rows = admission.relation_rows
        self.payload_units = admission.payload_units
        self.deferred_unpublished -= len(fulfilled)
        self.contract_cause_published = (
            self.contract_cause_published or admission.publishes_contract_cause
        )
        return _Commit(admission.base, self._state(), tuple(added))

    def undo(self, committed: _Commit) -> None:
        """publish できなかった transaction の `commit` を取り消す（直後にだけ呼べる）。"""

        if type(committed) is not _Commit or committed.after != self._state():
            raise ValueError("event contract commit can only be undone right after it")
        (
            self.events, self.ordinary_occurrences, self.limitation_occurrences,
            self.relation_rows, self.payload_units, self.deferred_unpublished,
            self.contract_cause_published,
        ) = committed.base
        for occurrence_id in committed.added_ids:
            self._published_ids.discard(occurrence_id)

    def defer(self, occurrence_id: str) -> None:
        """判定の前に publish すると約束した occurrence を、約束の時点で数える（超えるなら拒む）。

        publish 済み・約束済みの occurrence は数えない。超えるなら限界を pair の台帳へ記録して
        `AuthorityEventContractExceeded` を上げ、約束は記録しない。
        """

        if type(occurrence_id) is not str or not occurrence_id:
            raise TypeError("a deferred occurrence id is a non-empty str")
        if occurrence_id in self._deferred_ids or occurrence_id in self._published_ids:
            return
        if self.exceeded is not None:
            raise self.exceeded
        contract = self.contract
        pending = self.deferred_unpublished + 1
        if self.ordinary_occurrences + pending > contract.ordinary_cause_occurrences:
            self._exceed(
                "cause_occurrences", contract.ordinary_cause_occurrences,
                self.ordinary_occurrences + pending,
            )
        cause_limit = self._limits(_ORDINARY)[1]
        total = self.ordinary_occurrences + self.limitation_occurrences + pending
        if total > cause_limit:
            self._exceed("cause_occurrences", cause_limit, total)
        self._deferred_ids.add(occurrence_id)
        self.deferred_unpublished = pending

    def release(self, occurrence_id: str) -> None:
        """約束が消えた（完了で退いた・finish で publish を試みた）occurrence を約束の勘定から外す。"""

        if occurrence_id not in self._deferred_ids:
            return
        self._deferred_ids.discard(occurrence_id)
        if occurrence_id not in self._published_ids:
            self.deferred_unpublished -= 1

    def _exceed(self, bound: str, limit: int, observed: int) -> None:
        exceeded = AuthorityEventContractExceeded(bound, limit=limit, observed=observed)
        if self.exceeded is None:
            # 最初の超過が stream を切った点（限界の cause はこの超過を記録する）
            self.exceeded = exceeded
            ledger = current_pair_ledger()
            if ledger is not None:
                ledger.record_limitation(exceeded, stop=PairStopState.PAIR_TERMINAL_LIMITATION)
        raise exceeded


def require_events_within_contract(
    count: int, *, contract: AuthorityEventContract = AUTHORITY_EVENT_CONTRACT,
) -> None:
    """記録済みの stream（durable な prefix・supervisor の composite stream）の event 数が封印の上限の中か。

    上限は worker の stream + supervisor の終端の event（`max_sealed_events`）。O(1)。外なら `ValueError`。

    検証（hash chain・replay）の仕事は event 数に比例する: 契約の外の stream は検証を始めずに無効にする。
    """

    if type(count) is not int or count > contract.max_sealed_events:
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


def _admission_kind(intents: Sequence[Any]) -> str:
    if not intents or not all(_is_limitation_cause(intent) for intent in intents):
        return _ORDINARY
    if all(_is_contract_cause(intent) for intent in intents):
        return _CONTRACT
    return _LIMITATION


def _is_contract_cause(intent: Any) -> bool:
    """契約の超過そのものの限界の cause か（専用の枠を使える唯一の event）。"""

    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        occurrence_limitation_site,
    )

    occurrence = _occurrence_of(intent)
    return occurrence is not None and (
        occurrence_limitation_site(occurrence) == EVENT_CONTRACT_LIMITATION_SITE
    )


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
