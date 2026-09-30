# -*- coding: utf-8 -*-
"""pair 解析全体の協調的 deadline（Issue #106 PR-106-A）の唯一の owner。

時間に関する規則はここに 1 つずつしか無い:

=============================== ================================================
規則                             owner
=============================== ================================================
期限（absolute monotonic）        `Deadline`（`deadline_scope` を開いた時点で 1 回だけ
                                  決める。各層は相対時間を計算し直さない）
新しい仕事を始めてよいか          `Deadline.checkpoint` / `Deadline.admit`
sub-operation に渡す時間と丸め    `bounded_timeout`（純関数。worker でも同じ規則）
返ってきた答えを採ってよいか      `Deadline.settle`（query 開始時に期限内だったことは
                                  理由にならない）
時計を読む頻度                    `DeadlinePolicy.poll_interval`（`poller` が使う）
打ち切りの記録                    `Deadline._trip` → `core.errors.raise_limitation`
                                  （台帳へ記録してから raise。stop state は型で決まり
                                  `PAIR_TERMINAL_DEADLINE`）
=============================== ================================================

ここが持たないもの: UNKNOWN / ERROR の判断と receipt（authority）、失敗を結果へ変える
こと（`checker.pair_execution`）、backend ごとの時間の単位・中断の方法（`smt` の adapter）、
runner の既定値（PR-106-B）。

**thread の契約**: 期限は scope を開いた thread（owner）だけが暗黙に読める。scope は
`contextvars` に置くので solver の worker thread からは見えず、context を複製して渡され
ても owner の thread でなければ checkpoint は何もしない（台帳は同期的な入れ子実行だけを
前提にしている: `core.errors`）。worker が期限を使うときは、owner が `admit` で求めた
absolute 値（`Admission.not_after`）を **引数で** 受け取り、`bounded_timeout` で自分の
単位へ直す。worker は限界を上げない（結果の中断の種類を返すだけで、限界の確定は owner
の `settle`）。

**finalization**: `finalization()` の中（authority の確定・receipt・結果の組み立て）では
checkpoint は何もしない。期限を過ぎても確定した判定を捨てない。打ち切った後の
finalization で solver を呼ぼうとしたら `Admission.startable` が偽になる（新しい
意味の問いを始めない。呼び出し側は「実行しなかった」行を返す）。

dependency rule: 標準ライブラリと `core.errors` / `core.stage_journal` / `core.stage_clock`
以外を import しない（`core` は最下層）。
"""

from __future__ import annotations

import faulthandler
import math
import threading
import time
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Callable, Iterator, NoReturn, Optional, Tuple

from scripts.function_tracer_pcode.core.errors import DeadlineExceeded, raise_limitation
from scripts.function_tracer_pcode.core.stage_clock import active_region_path
from scripts.function_tracer_pcode.core.stage_journal import journal_note


#: 期限までに sub-operation（solver の 1 回・decompile の 1 回）を終えさせるための余裕。
#: sub-operation には「期限 − 余裕」までの時間しか渡さず、残りが余裕以下なら始めない。
#: 余裕は solver が自分の timeout を越えて返ってくる遅れと、結果を受け取って確かめる時間の
#: ため（z3 の実測: timeout 越え・interrupt 後の戻りとも最大 0.12 s、20 並列の負荷下）。
#: runner の `ANALYSIS_TIMEOUT` と process timeout の間の余裕（PR-106-B）とは別物。
DEFAULT_SUB_OPERATION_MARGIN_SECONDS = 0.5

#: hot loop（`poller`）が時計を読む間隔（呼び出し回数）。
DEFAULT_POLL_INTERVAL = 256

#: 解析の完了点（production boundary が legacy workflow の直後に置く checkpoint の stage）。
ANALYSIS_COMPLETE_STAGE = "analysis_complete"

#: `DeadlineExceeded.target_key` の先頭（deadline の限界であることを型以外でも読めるように）。
DEADLINE_TARGET = "analysis_deadline"

#: stack snapshot を書くときの失敗（診断は判定を変えない。broad except は足さない）。
_SNAPSHOT_ERRORS = (AttributeError, OSError, RuntimeError, TypeError, ValueError)


class TimeUnit(Enum):
    """backend の timeout API の単位。"""

    MILLISECONDS = "ms"
    SECONDS = "s"


def _exact_positive(name: str, value: Any) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise TypeError(f"{name} must be a number")
    value = float(value)
    if not math.isfinite(value) or value <= 0:
        raise ValueError(f"{name} must be a positive finite number of seconds")
    return value


def bounded_timeout(
    configured_seconds: float, not_after: float, unit: TimeUnit, *, now: float,
) -> Optional[int]:
    """**丸めの唯一の規則**: `not_after` までに終わる timeout を `unit` で返す。

    * 残り（`not_after - now`）が 0 以下なら ``None``（始めない）
    * 渡す時間 = min(設定値, 残り)
    * ミリ秒: 切り捨て、ただし 1 以上（0 を「timeout 無し」として渡さない）
    * 秒: 切り捨て。0 になるなら ``None``（秒単位の API に 0 を渡さない）

    worker thread でも owner と同じ規則で求められるよう、状態を持たない純関数にしてある。
    """

    remaining = float(not_after) - float(now)
    if remaining <= 0:
        return None
    granted = min(float(configured_seconds), remaining)
    if granted <= 0:
        return None
    if unit is TimeUnit.MILLISECONDS:
        return max(1, int(granted * 1000))
    whole = int(granted)
    return whole if whole >= 1 else None


def unbounded_timeout(configured_seconds: float, unit: TimeUnit) -> int:
    """期限の無い sub-operation の timeout（従来どおりの換算）。"""

    if unit is TimeUnit.MILLISECONDS:
        return int(round(float(configured_seconds) * 1000))
    return int(configured_seconds)


@dataclass(frozen=True)
class DeadlinePolicy:
    """1 回の `check_from_binaries` に与える時間予算（値だけ）。

    ``budget_seconds`` は `deadline_scope` を開いた時点からの秒数。起点で absolute に直した
    あとは、どの層もこの値から相対時間を計算し直さない。
    """

    budget_seconds: float
    sub_operation_margin_seconds: float = DEFAULT_SUB_OPERATION_MARGIN_SECONDS
    poll_interval: int = DEFAULT_POLL_INTERVAL
    #: 打ち切ったときに全 thread の Python stack を書く先（`fileno()` を持つ file）。
    #: 無くても判定は同じ（診断だけが減る）。
    snapshot_sink: Any = field(default=None, compare=False, repr=False)
    #: 時計（既定 `time.monotonic`。test が差し替える唯一の口）。worker と solver の実行予算は
    #: `time.monotonic` で残りを求めるので、差し替える時計も同じ時間軸（monotonic + 定数）にする
    clock: Callable[[], float] = field(default=time.monotonic, compare=False, repr=False)

    def __post_init__(self) -> None:
        object.__setattr__(self, "budget_seconds", _exact_positive("budget_seconds", self.budget_seconds))
        margin = self.sub_operation_margin_seconds
        if isinstance(margin, bool) or not isinstance(margin, (int, float)) or margin < 0:
            raise ValueError("sub operation margin must be a non-negative number of seconds")
        object.__setattr__(self, "sub_operation_margin_seconds", float(margin))
        interval = self.poll_interval
        if type(interval) is not int or interval < 1:
            raise ValueError("poll interval must be a positive int")


@dataclass(frozen=True)
class Admission:
    """sub-operation 1 回を始めてよいという許可と、その終わりの時刻。

    ``not_after`` は owner が `admit` で 1 回だけ求めた absolute 値（``None`` は期限なし）。
    worker へはこの値を引数で渡し、worker は `timeout` で自分の単位へ直す。
    ``startable`` が偽なのは、打ち切った後の finalization で呼ばれたときだけ（呼び出し側は
    実行せずに「実行しなかった」行を返す）。``deadline_bound`` は設定値ではなく期限が時間を
    決めている（期限で切られ得る）こと。
    """

    stage: str
    configured_seconds: float
    not_after: Optional[float] = None
    startable: bool = True
    deadline_bound: bool = False
    #: 呼び出し側が結果を待ってよい最後の時刻（= 解析の期限。``None`` は期限なし）
    wait_until: Optional[float] = None
    _deadline: Optional["Deadline"] = field(default=None, compare=False, repr=False)

    def wait_timeout(self, configured_wait_seconds: float) -> float:
        """結果を待つ時間の上限（期限があれば期限までに clamp する。0 以上）。"""

        if self.wait_until is None:
            return float(configured_wait_seconds)
        clock = self._deadline.now if self._deadline is not None else time.monotonic
        return max(0.0, min(float(configured_wait_seconds), self.wait_until - clock()))

    def timeout(self, unit: TimeUnit, *, now: Optional[float] = None) -> Optional[int]:
        """この sub-operation に渡す timeout（``None`` なら始めない）。"""

        if not self.startable:
            return None
        if self.not_after is None:
            return unbounded_timeout(self.configured_seconds, unit)
        clock = self._deadline.now if self._deadline is not None else time.monotonic
        return bounded_timeout(
            self.configured_seconds, self.not_after, unit,
            now=clock() if now is None else now,
        )

    def settle(self, *, answered: bool, evidence: Tuple[str, ...] = ()) -> None:
        """sub-operation が返った直後の確認（`Deadline.settle`）。期限の無い許可では何もしない。"""

        if self._deadline is not None:
            self._deadline.settle(self, answered=answered, evidence=evidence)


def unbounded_admission(stage: str, configured_seconds: float) -> Admission:
    return Admission(stage=stage, configured_seconds=float(configured_seconds))


class Deadline:
    """1 回の `check_from_binaries` の期限（absolute monotonic）と打ち切りの状態。"""

    def __init__(self, policy: DeadlinePolicy) -> None:
        if type(policy) is not DeadlinePolicy:
            raise TypeError("deadline needs an exact DeadlinePolicy")
        self.policy = policy
        self._clock = policy.clock
        self.clock_reads = 0
        self.started = self.now()
        self.absolute = self.started + policy.budget_seconds
        self._owner = threading.get_ident()
        self._trip: Optional[DeadlineExceeded] = None
        self._finalizing = 0
        self._hot_counters: dict = {}
        #: stage ごとに時計を読んだ回数（診断。判定に使わない）
        self.stage_reads: dict = {}

    # -- 時計 ----------------------------------------------------------------

    def now(self) -> float:
        self.clock_reads += 1
        return float(self._clock())

    def _read(self, stage: str) -> float:
        """境界で時計を読む（stage ごとの回数を数える唯一の場所）。"""
        self.stage_reads[stage] = self.stage_reads.get(stage, 0) + 1
        return self.now()

    def remaining_seconds(self) -> float:
        return self.absolute - self.now()

    @property
    def tripped(self) -> bool:
        return self._trip is not None

    @property
    def finalizing(self) -> bool:
        return self._finalizing > 0

    def owned_by_current_thread(self) -> bool:
        return threading.get_ident() == self._owner

    def _active_here(self) -> bool:
        return self._finalizing == 0 and self.owned_by_current_thread()

    # -- 境界 ----------------------------------------------------------------

    def checkpoint(self, stage: str) -> None:
        """新しい仕事を始める境界。期限を過ぎていれば（一度でも打ち切っていれば）raise。"""

        if not self._active_here():
            return
        now = self._read(stage)
        if self._trip is not None or now >= self.absolute:
            self._raise(stage, now, boundary="before")

    def admit(self, stage: str, configured_seconds: float, unit: TimeUnit) -> Admission:
        """sub-operation（solver / decompile の 1 回）を始める境界。

        解析中: 期限を過ぎている・残りが余裕以下・単位へ直すと 0 になるなら raise。始めて
        よければ「期限 − 余裕」を ``not_after`` にした許可を返す。
        finalization 中: raise しない。打ち切った後なら ``startable=False``（始めない）、
        そうでなければ期限の無い許可（確定処理の時間は PR-106-B の余裕が見る）。
        owner 以外の thread: 期限の無い許可（従来どおり）。
        """

        configured = float(configured_seconds)
        if not self.owned_by_current_thread():
            return unbounded_admission(stage, configured)
        if self._finalizing:
            if self._trip is not None:
                return Admission(stage=stage, configured_seconds=configured, startable=False)
            return unbounded_admission(stage, configured)
        now = self._read(stage)
        if self._trip is not None or now >= self.absolute:
            self._raise(stage, now, boundary="before")
        not_after = self.absolute - self.policy.sub_operation_margin_seconds
        if bounded_timeout(configured, not_after, unit, now=now) is None:
            self._raise(stage, now, boundary="before", evidence=("remaining_below_margin",))
        return Admission(
            stage=stage,
            configured_seconds=configured,
            not_after=not_after,
            deadline_bound=(not_after - now) < configured,
            wait_until=self.absolute,
            _deadline=self,
        )

    def settle(self, admission: Admission, *, answered: bool, evidence: Tuple[str, ...] = ()) -> None:
        """sub-operation が返った直後。答えを採ってよいかを決める。

        期限を過ぎていれば、答え（SAT / UNSAT を含む）があっても raise する（始めたときに
        期限内だったことは採る理由にならない）。期限がこの sub-operation の時間を決めていて
        答えが無い（timeout・中断・実行しなかった）なら、それは期限で切られたので raise。
        """

        if admission._deadline is not self or not self._active_here():
            return
        now = self._read(admission.stage)
        if self._trip is not None or now >= self.absolute:
            self._raise(admission.stage, now, boundary="after", evidence=evidence)
        if admission.deadline_bound and not answered:
            self._raise(
                admission.stage, now, boundary="after", evidence=("cut_by_deadline", *evidence),
            )

    def poll(self, stage: str, counter: "_PollCounter") -> None:
        """hot loop の checkpoint。`poll_interval` 回に 1 回だけ時計を読む。"""

        counter.calls += 1
        if self._trip is None and counter.calls % self.policy.poll_interval:
            return
        if not self._active_here():
            return
        now = self._read(stage)
        if self._trip is not None or now >= self.absolute:
            self._raise(stage, now, boundary="poll")

    def hot_checkpoint(self, stage: str) -> None:
        """`poll` の stage ごとの counter をこの期限が持つ版（再帰など loop の外で作れない所用）。"""

        counter = self._hot_counters.get(stage)
        if counter is None:
            counter = self._hot_counters[stage] = _PollCounter()
        self.poll(stage, counter)

    def diagnostic(self) -> dict:
        """結果の診断に載せる要約（有界: stage の数だけ。判定に使わない）。"""

        trip = self._trip
        return {
            "budget_seconds": self.policy.budget_seconds,
            "elapsed_seconds": round(self.now() - self.started, 6),
            "tripped": trip is not None,
            "trip_stage": None if trip is None else trip.site,
            "stage_reads": dict(sorted(self.stage_reads.items())),
        }

    @contextmanager
    def finalization(self) -> Iterator[None]:
        self._finalizing += 1
        try:
            yield
        finally:
            self._finalizing -= 1

    # -- 打ち切り ------------------------------------------------------------

    def _raise(
        self, stage: str, now: float, *, boundary: str, evidence: Tuple[str, ...] = (),
    ) -> NoReturn:
        """打ち切りを記録して raise する（最初の 1 回だけ snapshot を残す）。

        2 回目以降は最初の打ち切りと同じ site / target の限界を上げ直す（台帳は同じ 1 件に
        畳む）。途中の `except Exception` に握り潰されても、次の境界でまた止まる。
        """

        first = self._trip
        if first is None:
            elapsed = now - self.started
            path = "/".join(active_region_path())
            first = DeadlineExceeded(
                f"analysis deadline exceeded at {stage} after {elapsed:.3f}s "
                f"(budget {self.policy.budget_seconds:.3f}s)",
                site=stage,
                target_key=(DEADLINE_TARGET, stage),
                evidence_refs=(
                    f"stage={stage}",
                    f"boundary={boundary}",
                    f"region_path={path}",
                    f"elapsed_seconds={elapsed:.3f}",
                    f"budget_seconds={self.policy.budget_seconds:.3f}",
                    *evidence,
                ),
            )
            self._trip = first
            self._snapshot(first, stage, elapsed, boundary, path)
        raise_limitation(DeadlineExceeded(
            first.detail,
            site=first.site,
            target_key=first.target_key,
            evidence_refs=first.evidence_refs,
        ))

    def _snapshot(
        self, trip: DeadlineExceeded, stage: str, elapsed: float, boundary: str, path: str,
    ) -> None:
        journal_note("deadline_tripped", {
            "stage": stage,
            "boundary": boundary,
            "region_path": path,
            "elapsed_seconds": round(elapsed, 6),
            "budget_seconds": self.policy.budget_seconds,
            "snapshot": self.policy.snapshot_sink is not None,
        })
        sink = self.policy.snapshot_sink
        if sink is None:
            return
        try:
            sink.write(
                (
                    f"\n=== deadline_tripped stage={stage} boundary={boundary} "
                    f"region_path={path} elapsed={elapsed:.3f} "
                    f"budget={self.policy.budget_seconds:.3f} ===\n"
                ).encode("utf-8")
            )
            sink.flush()
            faulthandler.dump_traceback(file=sink, all_threads=True)
        except _SNAPSHOT_ERRORS:
            return


class _PollCounter:
    __slots__ = ("calls",)

    def __init__(self) -> None:
        self.calls = 0


# ---------------------------------------------------------------------------
# scope（owner thread の context だけに置く）
# ---------------------------------------------------------------------------

_ACTIVE_DEADLINE: ContextVar[Optional[Deadline]] = ContextVar("active_analysis_deadline", default=None)


def active_deadline() -> Optional[Deadline]:
    """この thread が owner の、いま有効な deadline（無ければ ``None``）。"""

    deadline = _ACTIVE_DEADLINE.get()
    if deadline is None or not deadline.owned_by_current_thread():
        return None
    return deadline


@contextmanager
def deadline_scope(policy: Optional[DeadlinePolicy]) -> Iterator[Optional[Deadline]]:
    """`policy` の期限をこの thread の context で有効にする（``None`` なら何も足さない）。

    入れ子で開いても外側の期限は延びない: 内側の期限が外側より後なら外側をそのまま使う。
    """

    outer = active_deadline()
    if policy is None:
        yield outer
        return
    deadline = Deadline(policy)
    if outer is not None and outer.absolute <= deadline.absolute:
        yield outer
        return
    token = _ACTIVE_DEADLINE.set(deadline)
    try:
        yield deadline
    finally:
        _ACTIVE_DEADLINE.reset(token)


def checkpoint(stage: str) -> None:
    """新しい意味の仕事を始める境界（期限が無ければ何もしない）。"""

    deadline = active_deadline()
    if deadline is not None:
        deadline.checkpoint(stage)


def admit(stage: str, configured_seconds: float, unit: TimeUnit) -> Admission:
    """sub-operation を始める境界（期限が無ければ従来どおりの許可）。"""

    deadline = active_deadline()
    if deadline is None:
        return unbounded_admission(stage, configured_seconds)
    return deadline.admit(stage, configured_seconds, unit)


def hot_checkpoint(stage: str) -> None:
    """頻繁に通る所の checkpoint（時計は `DeadlinePolicy.poll_interval` 回に 1 回だけ読む）。"""

    deadline = active_deadline()
    if deadline is not None:
        deadline.hot_checkpoint(stage)


def _no_poll() -> None:
    return None


def poller(stage: str) -> Callable[[], None]:
    """hot loop 用の checkpoint を 1 つ作る（loop の外で作り、loop の中で呼ぶ）。

    期限が無ければ何もしない関数を返す（時計を読まない）。読む頻度は
    `DeadlinePolicy.poll_interval` だけが決める。
    """

    deadline = active_deadline()
    if deadline is None:
        return _no_poll
    counter = _PollCounter()
    return lambda: deadline.poll(stage, counter)


@contextmanager
def finalization() -> Iterator[None]:
    """確定処理の区間（checkpoint は何もしない。期限を過ぎても確定した判定を捨てない）。"""

    deadline = active_deadline()
    if deadline is None:
        yield
        return
    with deadline.finalization():
        yield


__all__ = [
    "ANALYSIS_COMPLETE_STAGE",
    "Admission",
    "DEADLINE_TARGET",
    "DEFAULT_POLL_INTERVAL",
    "DEFAULT_SUB_OPERATION_MARGIN_SECONDS",
    "Deadline",
    "DeadlinePolicy",
    "TimeUnit",
    "active_deadline",
    "admit",
    "bounded_timeout",
    "checkpoint",
    "deadline_scope",
    "finalization",
    "hot_checkpoint",
    "poller",
    "unbounded_admission",
    "unbounded_timeout",
]
