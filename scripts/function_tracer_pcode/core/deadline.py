# -*- coding: utf-8 -*-
"""pair 解析全体の協調的 deadline（Issue #106 PR-106-A）の唯一の owner。

時間に関する規則はここに 1 つずつしか無い:

=============================== ================================================
規則                             owner
=============================== ================================================
期限（absolute monotonic）        `Deadline`（`deadline_scope` を開いた時点で 1 回だけ
                                  決める。各層は相対時間を計算し直さない）
新しい仕事を始めてよいか          `Deadline.checkpoint`、sub-operation の 1 回ごとに
                                  `DeadlineQuery.begin`（owner の thread）
sub-operation 1 回の実効の終わり  `execution_window`（純関数。**実行を始める瞬間に**
と「期限で時間が決まったか」      実行ごとに求める。worker でも同じ規則）
単位への丸め                      `bounded_timeout`（ms は 1 以上、秒は 0 なら始めない）
実行がどう終わったか（語彙）      `ExecutionEnd`（**観測された終了原因**。backend 固有の
                                  結果からこの語彙へ写すのは各 layer の写像: solver の行は
                                  `smt.interface.execution_end`、decompile は
                                  `ghidra.decompilation_broker`）
期限で切られた実行か              `ExecutionFact.cut_by_deadline`（期限が時間を決め、かつ
                                  **時間の上限で止まった**。始めなかった実行を含む）
返ってきた結果をどうするか        `settlement`（純関数。下の表）→ `DeadlineQuery.settle`
                                  （実行が返った **直後ごとに**。始めたときに期限内だった
                                  ことは答えを採る理由にならない）
時計を読む頻度                    `DeadlinePolicy.poll_interval`（`poller` が使う）
打ち切りの記録                    `Deadline._trip` → `core.errors.raise_limitation`
                                  （台帳へ記録してから raise。stop state は型で決まり
                                  `PAIR_TERMINAL_DEADLINE`）
=============================== ================================================

**論理的な問いと実行の境界**: `DeadlineQuery` は 1 つの論理的な問い（solver の問い合わせ 1 つ・
decompile 1 回）の owner 側の handle で、開始の確認（`begin`）と結果の採用（`settle`）を持つ。
その問いの中の **実行 1 回ごと**（逐次の backend の 1 つずつ、並列の worker 1 つずつ）は、始める
瞬間に `ExecutionBound.window` で自分の実効の終わりと `limited` を求める。実行は時刻をずらして
始まり得る（逐次なら先の backend が時間を使う、並列なら worker の起動が遅れる）ので、「期限で
時間が決まった」かどうかを問いの入口で固定しない。

**settle の表**（`settlement`。問い 1 つの、それまでに返った実行の事実すべてに対して）:

========================================= =============================================
事実                                      結果
========================================= =============================================
期限後でも期限で切られた実行も無い         ACCEPT（答え・通常の unknown・通常の timeout・明示
                                          の中止・失敗は、期限の無いときと同じ結果のまま）
故障を観測した（終了原因が FAILED /       KEEP_FAILURE（故障を結果に残し、期限の限界は記録
CONTRACT_VIOLATION、または                 だけして raise は次の境界）。ただし期限後で、契約
`ExecutionFact.failed`）                   違反が無く答えがある（集約でその答えが採られて
                                          しまう）なら DEADLINE
それ以外（期限後・期限で切られた実行）     DEADLINE（答えがあっても採らない）
========================================= =============================================

失敗を限界より先に置くのは、台帳の優先順位（内部バグ > 限界、`core.errors`）と同じ向き:
期限は「失敗が起きた」事実を隠す理由にならない。

ここが持たないもの: UNKNOWN / ERROR の判断と receipt（authority）、失敗を結果へ変える
こと（`checker.pair_execution`）、backend ごとの時間の単位・中断の方法（`smt` の adapter）、
runner の既定値（PR-106-B）。

**thread の契約**: 期限は scope を開いた thread（owner）だけが暗黙に読める。scope は
`contextvars` に置くので solver の worker thread からは見えず、context を複製して渡され
ても owner の thread でなければ checkpoint は何もしない（台帳は同期的な入れ子実行だけを
前提にしている: `core.errors`）。worker が期限を使うときは、owner の `DeadlineQuery.bound`
（`ExecutionBound`: absolute な `not_after` と時計だけを持つ値）を **引数で** 受け取る。
worker は限界を上げない（実行の事実を結果で返すだけで、限界の確定は owner の `settle`）。

**finalization**: `finalization()` の中（authority の確定・receipt・結果の組み立て）では
checkpoint は何もしない。期限を過ぎても確定した判定を捨てない。打ち切った後の
finalization で sub-operation を始めようとしたら `DeadlineQuery.begin` が偽を返す（新しい
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

from scripts.function_tracer_pcode.core.errors import (
    DeadlineExceeded,
    raise_limitation,
    record_limitation,
)
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
class ExecutionWindow:
    """sub-operation の実行 1 回の実効の終わり（`execution_window` が作る）。

    ``end`` は absolute monotonic（``None`` は期限なし: 設定値の timeout をそのまま使う）。
    ``limited`` は設定値の timeout ではなく **解析の期限** が終わりを決めたこと。
    """

    end: Optional[float]
    limited: bool

    def timeout(self, configured_seconds: float, unit: TimeUnit, *, now: float) -> Optional[int]:
        """この実行に渡す timeout（``None`` なら始めない）。

        期限が時間を決めていない窓は設定値をそのまま渡す（開始時刻からの丸め直しで設定値より
        短くしない: 期限なしのときと同じ値）。期限が決めた窓だけ、終わりまでを `bounded_timeout`
        で直す。
        """

        if not self.limited:
            return unbounded_timeout(configured_seconds, unit)
        return bounded_timeout(configured_seconds, self.end, unit, now=now)

    @property
    def adapter_end(self) -> Optional[float]:
        """adapter に渡す終わり（期限が時間を決めた窓だけ。そうでなければ設定値の timeout に任せる）。"""

        return self.end if self.limited else None


#: 期限の無い実行の窓
UNBOUNDED_WINDOW = ExecutionWindow(end=None, limited=False)


def execution_window(
    configured_seconds: float, not_after: Optional[float], unit: TimeUnit, *, now: float,
) -> Optional[ExecutionWindow]:
    """**実行 1 回の窓の唯一の規則**: 始める瞬間 ``now`` の、実効の終わりと ``limited``。

    * 期限なし（``not_after is None``）: 設定値のまま（`UNBOUNDED_WINDOW`）
    * ``unit`` に直すと 0 になる・残りが無い: ``None``（始めない）
    * 設定値で ``not_after`` までに終わる: 終わり = ``now + 設定値``、``limited=False``
    * それ以外: 終わり = ``not_after``、``limited=True``（解析の期限が時間を決めた）
    """

    if not_after is None:
        return UNBOUNDED_WINDOW
    if bounded_timeout(configured_seconds, not_after, unit, now=now) is None:
        return None
    configured_end = float(now) + float(configured_seconds)
    if configured_end <= float(not_after):
        return ExecutionWindow(end=configured_end, limited=False)
    return ExecutionWindow(end=float(not_after), limited=True)


class ExecutionEnd(Enum):
    """実行 1 回が **実際にどう終わったか**（観測された終了原因。backend に依らない語彙）。

    「解析の期限が上限を短くした」（`ExecutionWindow.limited`）とは別の軸: 上限を短くした
    実行でも、parse error で即座に返れば `FAILED`、上限に届く前に unknown を返せば
    `INCONCLUSIVE` で、期限で切られてはいない。
    """

    #: 期限に関係なく採れる答え（solver の SAT / UNSAT、decompile の完了）
    ANSWERED = "answered"
    #: 自分で返ったが答えが無い（時間の上限でも中止でもない unknown）
    INCONCLUSIVE = "inconclusive"
    #: 時間の上限で止まった（backend 自身の timeout・実行の予算切れ・待つのを上限でやめた）
    TIME_LIMIT = "time_limit"
    #: 呼び出し側の明示の中止（cancellation token）で止まった
    CANCELLED = "cancelled"
    #: backend の失敗（例外・parse error・始められなかった・decompiler の異常終了）
    FAILED = "failed"
    #: backend が結果の契約を破った（canonical witness の無い SAT など）
    CONTRACT_VIOLATION = "contract_violation"
    #: 期限までの時間が無いので始めなかった
    NOT_STARTED = "not_started"


#: 結果として表に出すべき失敗（期限で隠さない）
FAILURE_ENDS = frozenset({ExecutionEnd.FAILED, ExecutionEnd.CONTRACT_VIOLATION})


@dataclass(frozen=True)
class ExecutionFact:
    """実行 1 回について `settle` が読む事実（呼び出し側は自分の結果をこれに写すだけ）。"""

    #: 観測された終了原因
    end: ExecutionEnd
    #: その実行の時間の上限を解析の期限が決めた（`ExecutionWindow.limited`、または待つのを
    #: 期限でやめた）
    limited: bool
    #: 終了原因とは独立に、backend の故障を観測した（例: 明示の中止で止まった実行が、中止の
    #: 合図ではない例外を上げていた）。終了原因が FAILED / CONTRACT_VIOLATION なら常に真
    failed: bool = False

    def __post_init__(self) -> None:
        if type(self.end) is not ExecutionEnd:
            raise TypeError("execution fact needs an ExecutionEnd")
        if type(self.limited) is not bool or type(self.failed) is not bool:
            raise TypeError("execution fact needs bool limited / failed")

    @property
    def failure_observed(self) -> bool:
        """結果として表に出すべき故障を観測したか（期限で隠さない）。"""

        return self.failed or self.end in FAILURE_ENDS

    @property
    def cut_by_deadline(self) -> bool:
        """**期限で切られた実行の唯一の規則**: 期限が上限を決め、その上限で止まった
        （または期限までの時間が無くて始めなかった）。

        上限を期限が決めていても、それ以外の終わり方（答え・通常の unknown・中止・失敗）は
        期限で切られたのではない。期限が上限を決めなかった実行の timeout は通常の timeout。
        """

        if self.end is ExecutionEnd.NOT_STARTED:
            return True
        return self.limited and self.end is ExecutionEnd.TIME_LIMIT


#: 始められなかった実行（期限までの時間が無い）の事実
NOT_STARTED_FACT = ExecutionFact(end=ExecutionEnd.NOT_STARTED, limited=True)


class Settlement(Enum):
    """`settlement` の結論。"""

    #: 結果をそのまま使う（期限は関係しなかった）
    ACCEPT = "accept"
    #: 期限の限界（raise。答えがあっても採らない）
    DEADLINE = "deadline"
    #: 期限の事実（期限後・期限で切られた実行）はあるが、失敗を結果に残す。限界は記録だけして
    #: 次の境界で raise（この問いの後の実行は始めない）
    KEEP_FAILURE = "keep_failure"


def settlement(facts: Tuple[ExecutionFact, ...], *, expired: bool) -> Settlement:
    """**返ってきた結果をどうするかの唯一の規則**（module docstring の表。純関数）。

    ``facts`` は 1 つの問いのそれまでに返った実行すべて、``expired`` は今が期限以後か。
    """

    ends = {fact.end for fact in facts}
    deadline_fact = expired or any(fact.cut_by_deadline for fact in facts)
    if not deadline_fact:
        return Settlement.ACCEPT
    if any(fact.failure_observed for fact in facts):
        adoptable_answer = (
            ExecutionEnd.ANSWERED in ends and ExecutionEnd.CONTRACT_VIOLATION not in ends
        )
        if expired and adoptable_answer:
            return Settlement.DEADLINE
        return Settlement.KEEP_FAILURE
    return Settlement.DEADLINE


@dataclass(frozen=True)
class ExecutionBound:
    """worker に **引数で** 渡す、実行の窓を求めるのに要るものだけ（期限の object は渡さない）。"""

    not_after: Optional[float] = None
    clock: Callable[[], float] = field(default=time.monotonic, compare=False, repr=False)

    def window(self, configured_seconds: float, unit: TimeUnit) -> Optional[ExecutionWindow]:
        """今この thread で実行を始めるときの窓（``None`` なら始めない）。"""

        return execution_window(configured_seconds, self.not_after, unit, now=self.clock())

    def now(self) -> float:
        return float(self.clock())


#: 期限の無い実行の bound
UNBOUNDED = ExecutionBound()


class DeadlineQuery:
    """1 つの論理的な問いの owner 側の handle（`deadline_query` が作る）。

    * `begin(...)`: 実行を 1 回始める前に owner の thread で呼ぶ（逐次なら backend ごと）。
      解析中に期限を過ぎていれば限界を raise する。偽なら始めない（打ち切った後の
      finalization、またはこの問いが失敗を結果に残すと決めた後: 限界は記録済み）
    * `bound`: worker へ渡す `ExecutionBound`
    * `wait_timeout(...)`: 結果を待つ上限と、それを期限が決めたか
    * `settle(facts)`: 実行が返った直後に owner の thread で呼ぶ（逐次なら **実行ごと**。次の
      実行を始める前）。事実はこの問いの中で積み上がり、`settlement` はそれまでの全部を見る
    """

    __slots__ = ("stage", "_deadline", "_startable", "bound", "facts", "kept_failure")

    def __init__(
        self, stage: str, *, deadline: Optional["Deadline"] = None, startable: bool = True,
        bound: ExecutionBound = UNBOUNDED,
    ) -> None:
        self.stage = stage
        self._deadline = deadline
        self._startable = startable
        self.bound = bound
        #: この問いのそれまでに返った実行の事実
        self.facts: Tuple[ExecutionFact, ...] = ()
        #: 失敗を結果に残すと決めた（`Settlement.KEEP_FAILURE` で期限の限界を記録した）
        self.kept_failure = False

    @property
    def bounded(self) -> bool:
        return self._deadline is not None

    def begin(self, configured_seconds: float, unit: TimeUnit = TimeUnit.MILLISECONDS) -> bool:
        if not self._startable or self.kept_failure:
            return False
        if self._deadline is not None:
            return self._deadline.begin_execution(self, configured_seconds, unit)
        return True

    def wait_timeout(self, configured_wait_seconds: float) -> Tuple[float, bool]:
        """(待つ秒数, 期限がそれを決めたか)。期限なしなら設定値のまま。"""

        configured = float(configured_wait_seconds)
        if self.bound.not_after is None or self._deadline is None:
            return configured, False
        remaining = max(0.0, self._deadline.absolute - self.bound.now())
        if remaining < configured:
            return remaining, True
        return configured, False

    def settle(self, facts: Any, *, evidence: Tuple[str, ...] = ()) -> Settlement:
        """返った実行の事実を積み、`settlement` の結論を適用する（DEADLINE なら raise）。"""

        self.facts = self.facts + tuple(facts)
        if self._deadline is None:
            return Settlement.ACCEPT
        return self._deadline.settle(self, evidence=evidence)


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

    def query(self, stage: str) -> DeadlineQuery:
        """1 つの論理的な問いの handle。

        解析中: ``not_after`` = 期限 − 余裕 の bound を持つ（実行ごとの窓はそこから求める）。
        finalization 中: 打ち切った後なら始めない handle、そうでなければ期限の無い handle
        （確定処理の時間は PR-106-B の余裕が見る）。owner 以外の thread: 期限の無い handle。
        """

        if not self.owned_by_current_thread():
            return DeadlineQuery(stage)
        if self._finalizing:
            return DeadlineQuery(stage, startable=self._trip is None)
        return DeadlineQuery(
            stage,
            deadline=self,
            bound=ExecutionBound(
                not_after=self.absolute - self.policy.sub_operation_margin_seconds,
                clock=self._clock,
            ),
        )

    def begin_execution(self, query: DeadlineQuery, configured_seconds: float, unit: TimeUnit) -> bool:
        """実行を 1 回始める前（owner）。期限を過ぎている・残りが余裕以下・単位へ直すと 0 なら始めない。

        始めないときは限界を raise する。ただしこの問いの先の実行で故障を観測していれば
        （`ExecutionFact.failure_observed`）、その故障を結果に残すため raise せず、限界を記録
        だけして偽を返す（`Settlement.KEEP_FAILURE` と同じ扱い: 次の境界で raise）。
        """

        if not self._active_here():
            return True
        now = self._read(query.stage)
        refusal: Optional[Tuple[str, ...]] = None
        if self._trip is not None or now >= self.absolute:
            refusal = ()
        elif bounded_timeout(configured_seconds, query.bound.not_after, unit, now=now) is None:
            refusal = ("remaining_below_margin",)
        if refusal is None:
            return True
        if any(fact.failure_observed for fact in query.facts):
            query.kept_failure = True
            self._mark(query.stage, now, boundary="before", evidence=("failure_kept", *refusal))
            return False
        self._raise(query.stage, now, boundary="before", evidence=refusal)

    def settle(self, query: DeadlineQuery, *, evidence: Tuple[str, ...] = ()) -> Settlement:
        """実行が返った直後（owner）。`settlement` の結論を適用する。

        DEADLINE は限界を raise する（始めたときに期限内だったことは答えを採る理由にならない）。
        KEEP_FAILURE は結果を返す: 期限を過ぎた・期限で切られた実行があれば限界を記録だけして
        （打ち切りは sticky なので次の境界で raise）、この問いの後の実行は始めない。
        """

        if not self._active_here():
            return Settlement.ACCEPT
        now = self._read(query.stage)
        expired = self._trip is not None or now >= self.absolute
        verdict = settlement(query.facts, expired=expired)
        cut = any(fact.cut_by_deadline for fact in query.facts)
        detail = ("cut_by_deadline",) if cut else ()
        if verdict is Settlement.DEADLINE:
            self._raise(query.stage, now, boundary="after", evidence=(*detail, *evidence))
        if verdict is Settlement.KEEP_FAILURE:
            query.kept_failure = True
            self._mark(
                query.stage, now, boundary="after",
                evidence=("failure_kept", *detail, *evidence),
            )
        return verdict

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

    def _trip_now(
        self, stage: str, now: float, *, boundary: str, evidence: Tuple[str, ...] = (),
    ) -> DeadlineExceeded:
        """打ち切りの記録（最初の 1 回だけ作って snapshot を残す）。以後の限界はこれの写し。"""

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
        return DeadlineExceeded(
            first.detail,
            site=first.site,
            target_key=first.target_key,
            evidence_refs=first.evidence_refs,
        )

    def _raise(
        self, stage: str, now: float, *, boundary: str, evidence: Tuple[str, ...] = (),
    ) -> NoReturn:
        """打ち切りを記録して raise する。

        2 回目以降は最初の打ち切りと同じ site / target の限界を上げ直す（台帳は同じ 1 件に
        畳む）。途中の `except Exception` に握り潰されても、次の境界でまた止まる。
        """

        raise_limitation(self._trip_now(stage, now, boundary=boundary, evidence=evidence))

    def _mark(
        self, stage: str, now: float, *, boundary: str, evidence: Tuple[str, ...] = (),
    ) -> None:
        """打ち切りを記録するが raise しない（失敗を結果に残すとき。次の境界が raise する）。"""

        record_limitation(self._trip_now(stage, now, boundary=boundary, evidence=evidence))

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


def deadline_query(stage: str) -> DeadlineQuery:
    """1 つの論理的な問いの handle（owner の thread で作る。期限が無ければ何もしない handle）。"""

    deadline = active_deadline()
    if deadline is None:
        return DeadlineQuery(stage)
    return deadline.query(stage)


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
    "DEADLINE_TARGET",
    "DEFAULT_POLL_INTERVAL",
    "DEFAULT_SUB_OPERATION_MARGIN_SECONDS",
    "Deadline",
    "DeadlinePolicy",
    "TimeUnit",
    "DeadlineQuery",
    "ExecutionBound",
    "ExecutionEnd",
    "ExecutionFact",
    "ExecutionWindow",
    "FAILURE_ENDS",
    "NOT_STARTED_FACT",
    "Settlement",
    "UNBOUNDED",
    "UNBOUNDED_WINDOW",
    "active_deadline",
    "bounded_timeout",
    "checkpoint",
    "deadline_query",
    "deadline_scope",
    "execution_window",
    "finalization",
    "hot_checkpoint",
    "poller",
    "settlement",
    "unbounded_timeout",
]
