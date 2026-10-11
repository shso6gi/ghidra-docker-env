"""SAT-safety の blocker の occurrence ごとの状態と遷移の唯一の owner（plan v4 PR-A）。

状態（occurrence ごとに 1 つ。記録の正本は常に 1 つ）:

* ABSENT    — 記録が無い。
* PROMISED  — deferred の約束（予約を持つ）。記録は約束した観測。
* PUBLISHED — 公開済みの観測。記録は公開した観測。
* COMPLETED — 公開済みで完了済み。

PROMISED と PUBLISHED は共存しない（公開は約束を退ける）。共存を見つけたら台帳の
破損として止める（片方を優先して他方を隠さない）。

判定（``decide``）は状態を変えない純粋な関数で、受付・generic な route（encoder）・
handoff・finalize のすべてが同じものを使う。整合しない対・記録と別の根拠や束縛の
再観測（衝突）・記録を言い直さない完了は ``ValueError`` で、呼び手は状態を変えずに
失敗として記録する。

遷移は次の 4 つだけで、台帳と予約を変えるのはこの class だけ:

* ``record_promise``     — ABSENT → PROMISED（予約は呼び手が ``defer_occurrence`` で取った後）
* ``retire_promise``     — PROMISED → ABSENT（未公開の約束の完了、または予算による打切り）
* ``record_publication`` — ABSENT/PROMISED → PUBLISHED（event の commit の後。約束は退ける）
* ``record_completion``  — PUBLISHED → COMPLETED（event の commit の後）

保存の形は既存の session の state の key のまま（Issue #110 の test と互換）。
"""

from __future__ import annotations

from enum import Enum
from typing import Any, Iterator, Optional


DEFERRED_KEY = "sat_safety_deferred_observations"   # occurrence -> (signal, site)
PUBLISHED_KEY = "sat_safety_observed"               # set of occurrence
PUBLISHED_SIGNALS_KEY = "sat_safety_observed_signals"  # occurrence -> signal
COMPLETED_KEY = "sat_safety_completed"              # set of occurrence

#: 台帳が持つ session の state の key の全て（他の domain の取引が巻き戻しの対象にする）。
SAT_SAFETY_LEDGER_KEYS = (DEFERRED_KEY, PUBLISHED_KEY, PUBLISHED_SIGNALS_KEY, COMPLETED_KEY)


class BlockerState(str, Enum):
    ABSENT = "absent"
    PROMISED = "promised"
    PUBLISHED = "published"
    COMPLETED = "completed"


class Disposition(str, Enum):
    """``decide`` の結論。event を出すものと出さないものを区別する。"""

    PROMISE = "promise"                  # 新しい約束（event 無し、予約を取る）
    PUBLISH = "publish"                  # 新しい観測の公開（event）
    PUBLISH_PROMISE = "publish_promise"  # 約束の公開（event。commit で約束を退ける）
    DUPLICATE = "duplicate"              # 同じ blocker の言い直し（何もしない）
    RETIRE_PROMISE = "retire_promise"    # 未公開の約束の完了（event 無し、予約を返す）
    COMPLETE = "complete"                # 公開済みの cause の完了（event）
    NOTHING = "nothing"                  # 観測の無い完了（何もしない）

    @property
    def emits_event(self) -> bool:
        return self in {Disposition.PUBLISH, Disposition.PUBLISH_PROMISE, Disposition.COMPLETE}


class SatSafetyBlockerLedger:
    """session の SAT-safety blocker の台帳への唯一の窓口。"""

    def __init__(self, session: Any) -> None:
        self._session = session
        self._state = session.domain_signal_state

    # ---- 読み取り ---------------------------------------------------------

    def _table(self, key: str, kind: type):
        value = self._state.get(key)
        if value is None:
            return kind()
        if type(value) is not kind:
            raise TypeError(f"SAT safety ledger {key} is not an exact {kind.__name__}")
        return value

    def state_of(self, occurrence_id: str) -> tuple[BlockerState, Any, Optional[str]]:
        """(状態, 記録した観測, 約束の site)。記録が無ければ (ABSENT, None, None)。"""
        promised = self._table(DEFERRED_KEY, dict).get(occurrence_id)
        published = occurrence_id in self._table(PUBLISHED_KEY, set)
        if promised is not None and published:
            raise ValueError("SAT safety ledger holds both a promise and a publication")
        if promised is not None:
            return BlockerState.PROMISED, promised[0], promised[1]
        if published:
            try:
                record = self._table(PUBLISHED_SIGNALS_KEY, dict)[occurrence_id]
            except KeyError as exc:
                raise ValueError("SAT safety publication has no recorded observation") from exc
            if occurrence_id in self._table(COMPLETED_KEY, set):
                return BlockerState.COMPLETED, record, None
            return BlockerState.PUBLISHED, record, None
        return BlockerState.ABSENT, None, None

    def records(self) -> Iterator[tuple[str, BlockerState, Any]]:
        """約束と公開済みの全ての記録（状態を変える前に list にして使う）。"""
        for occurrence_id in sorted(self._table(DEFERRED_KEY, dict)):
            yield (occurrence_id, *self.state_of(occurrence_id)[:2])
        for occurrence_id in sorted(self._table(PUBLISHED_KEY, set)):
            yield (occurrence_id, *self.state_of(occurrence_id)[:2])

    def promises(self) -> list[tuple[str, Any, Optional[str]]]:
        return [
            (occurrence_id, signal, site)
            for occurrence_id, (signal, site) in sorted(self._table(DEFERRED_KEY, dict).items())
        ]

    # ---- 判定（状態を変えない） ---------------------------------------------

    def decide(self, signal: Any, occurrence_id: str, site: Optional[str] = None) -> Disposition:
        """``signal`` を記録の正本に照らした結論。違反は ``ValueError``（状態は不変）。"""
        signal.blocker  # owner の分類（不整合な対は SatSafetyBlockerInconsistent）
        state, record, promised_site = self.state_of(occurrence_id)
        if signal.action == "OBSERVED":
            if state is BlockerState.ABSENT:
                return Disposition.PROMISE if signal.defer_until_terminal else Disposition.PUBLISH
            # 言い直しの規則は状態によらず 1 つ（同じ blocker・同じ束縛）。
            signal.require_restates(record)
            if state is BlockerState.PROMISED:
                if not signal.defer_until_terminal:
                    return Disposition.PUBLISH_PROMISE
                if site is not None and site != promised_site:
                    # 約束の持ち主（site）を黙って差し替えない。site を持つのは入口だけ。
                    raise ValueError("deferred SAT safety authority collided")
            return Disposition.DUPLICATE
        if state is BlockerState.ABSENT:
            return Disposition.NOTHING
        signal.require_completes(record)
        if state is BlockerState.PROMISED:
            return Disposition.RETIRE_PROMISE
        if state is BlockerState.PUBLISHED:
            return Disposition.COMPLETE
        return Disposition.DUPLICATE

    # ---- 遷移（台帳と予約を変える唯一の場所） ---------------------------------

    def record_promise(self, occurrence_id: str, signal: Any, site: Optional[str]) -> None:
        if self.state_of(occurrence_id)[0] is not BlockerState.ABSENT:
            raise ValueError("SAT safety promise needs an absent occurrence")
        self._state.setdefault(DEFERRED_KEY, {})[occurrence_id] = (signal, site)

    def retire_promise(self, occurrence_id: str) -> None:
        """event の無い退役（未公開の約束の完了・予算による打切り）。予約を返す。"""
        self._drop_promise(occurrence_id)
        self._session.event_contract.release(occurrence_id)

    def _drop_promise(self, occurrence_id: str) -> None:
        if self.state_of(occurrence_id)[0] is not BlockerState.PROMISED:
            raise ValueError("SAT safety promise retirement needs a promise")
        promises = self._state[DEFERRED_KEY]
        promises.pop(occurrence_id)
        if not promises:
            self._state.pop(DEFERRED_KEY, None)

    def settle_unpublished_promise(self, occurrence_id: str) -> None:
        """終端の公開を試みた後、まだ約束のままの occurrence を決着させる。

        予算による打切り（Issue #110: stream が切られた）なら約束は枠を持たないので退ける。
        検証の拒否なら失敗は記録済みで、状態を変えない。
        """
        if self.state_of(occurrence_id)[0] is not BlockerState.PROMISED:
            return
        if self._session.stream_truncated:
            self.retire_promise(occurrence_id)

    def snapshot(self) -> dict:
        """台帳の key の写し（event を伴う遷移の巻き戻し用）。"""
        copied = {}
        for key in SAT_SAFETY_LEDGER_KEYS:
            if key in self._state:
                value = self._state[key]
                copied[key] = dict(value) if type(value) is dict else set(value)
        return copied

    def restore(self, snapshot: dict) -> None:
        for key in SAT_SAFETY_LEDGER_KEYS:
            if key in snapshot:
                self._state[key] = snapshot[key]
            else:
                self._state.pop(key, None)

    def record_publication(self, occurrence_id: str, signal: Any) -> None:
        """公開の event の commit で呼ぶ。約束があれば台帳から外す。"""
        state = self.state_of(occurrence_id)[0]
        if state not in {BlockerState.ABSENT, BlockerState.PROMISED}:
            raise ValueError("SAT safety transaction duplicates committed state")
        if state is BlockerState.PROMISED:
            # 約束は果たされた。予約は event contract が公開の commit で数え済みで、
            # その undo が戻すので、ここでは release しない（台帳だけを変える）。
            self._drop_promise(occurrence_id)
        self._state.setdefault(PUBLISHED_KEY, set()).add(occurrence_id)
        self._state.setdefault(PUBLISHED_SIGNALS_KEY, {})[occurrence_id] = signal

    def record_completion(self, occurrence_id: str) -> None:
        if self.state_of(occurrence_id)[0] is not BlockerState.PUBLISHED:
            raise ValueError("SAT safety transaction duplicates committed state")
        self._state.setdefault(COMPLETED_KEY, set()).add(occurrence_id)
