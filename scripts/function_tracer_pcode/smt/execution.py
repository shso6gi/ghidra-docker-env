# -*- coding: utf-8 -*-
"""1 回の solver 実行の状態（時間予算と中止）の唯一の owner（Issue #161）。

backend の実行入口は、実行を始めるときに `ExecutionBudget` を 1 つ作り、その実行の
すべての段（query の準備・初回の check・canonical witness の探索・結果の確定）へ同じ
ものを渡す。各段は自分で期限を計算したり中止を解釈したりせず、ここに問う。

**中断の規則（優先順位つき、全経路で同じ）**:

1. 明示の中止（呼び出し側の cancellation token が中止された）→ `CANCELLED`
2. 実行の期限切れ（`time.monotonic()` が期限に達した、または solver が自分の timeout で
   止まった）→ `BUDGET_EXHAUSTED`

両方が成り立つときは中止を優先する（中止は呼び出し側の意思で、期限切れより先に
確かな事実）。中断の結果の status への写し方（`CANCELLED` → UNKNOWN、`BUDGET_EXHAUSTED`
→ TIMEOUT）は `smt.interface.interrupted_result` が持つ。

**解析全体の期限との関係**（Issue #106 PR-106-A）: 解析全体の期限（pair の analysis
deadline）の owner は `core.deadline.Deadline` で、この module は 1 回の solver 実行の
残り時間だけを持つ。両者を突き合わせるのは `ExecutionBudget.starting_now(not_after=...)`
の 1 箇所だけ（解析の期限の手前で実行の期限を切る）。実行を始めてよいか・返った答えを
採ってよいかは `core.deadline`（`DeadlineQuery.begin` / `settle`）が決める。
"""

from __future__ import annotations

import time
from typing import Any, Optional

from scripts.function_tracer_pcode.core.deadline import (
    ExecutionEnd,
    TimeUnit,
    bounded_timeout,
    execution_window,
)


#: 中断の種類
CANCELLED = "cancelled"
BUDGET_EXHAUSTED = "budget_exhausted"

#: solver の unknown の理由のうち、時間の上限で止まったことを表すもの（z3: 単発の solver は
#: timeout で "timeout"、push した incremental の solver は timeout でも "canceled" と報告する。
#: 実行の予算の終わりより 1 ms 以内に早く返ることがあるので、時計だけでは見分けられない）
TIME_LIMIT_UNKNOWN_REASONS = ("timeout", "canceled")


class ExecutionBudget:
    """1 回の solver 実行の期限（`time.monotonic()` の値）と中止の入力。"""

    __slots__ = ("deadline", "_cancellation_token")

    def __init__(self, deadline: float, cancellation_token: Optional[Any] = None) -> None:
        self.deadline = float(deadline)
        self._cancellation_token = cancellation_token

    @classmethod
    def starting_now(
        cls,
        seconds: float,
        cancellation_token: Optional[Any] = None,
        *,
        not_after: Optional[float] = None,
    ) -> "ExecutionBudget":
        """今から `seconds` 秒の実行予算。

        `not_after`（Issue #106 PR-106-A）はこの実行が越えてはならない absolute monotonic の
        時刻（runner が `core.deadline.execution_window` で求めた終わり）。終わりの決め方は
        `execution_window`（解析の期限と 1 回の実行の期限を突き合わせる唯一の規則）に従い、
        残り時間の計算（`remaining_ms` / `interruption`）はこの 1 つの期限だけを見る。
        """

        now = time.monotonic()
        window = execution_window(seconds, not_after, TimeUnit.MILLISECONDS, now=now)
        if window is None:
            # 始める時間が無い: 期限切れの予算（最初の `interruption()` で止まる）
            return cls(now, cancellation_token)
        return cls(now + float(seconds) if window.end is None else window.end, cancellation_token)

    def remaining_ms(self) -> int:
        """期限までの残り（ミリ秒、切り捨て）。0 以下なら期限切れ。"""

        return int((self.deadline - time.monotonic()) * 1000)

    def timeout_ms(self) -> int:
        """solver の問い 1 回に渡すミリ秒の timeout（期限まで。0 を「timeout 無し」として渡さない）。

        丸めは `core.deadline.bounded_timeout`（解析の期限と同じ 1 つの規則）。呼ぶ前に
        `interruption()` で期限切れを確かめておくこと（ここで期限を過ぎていたら 1 ms を返し、
        solver はすぐ timeout で返る: その unknown は `interruption_after_unknown` が期限切れに数える）。
        """

        granted = bounded_timeout(
            float("inf"), self.deadline, TimeUnit.MILLISECONDS, now=time.monotonic(),
        )
        return 1 if granted is None else granted

    def interruption(self) -> Optional[str]:
        """今この実行が中断されているならその種類（中止を優先）。されていなければ None。"""

        token = self._cancellation_token
        if token is not None and token.is_cancelled():
            return CANCELLED
        if time.monotonic() >= self.deadline:
            return BUDGET_EXHAUSTED
        return None

    def interruption_after_unknown(self, reason: str) -> Optional[str]:
        """solver が unknown を返したとき、それが中断によるものならその種類。

        `interruption()` に加え、solver 自身の timeout（z3 の reason "timeout"）も期限切れに
        数える。それ以外の unknown（z3 の "canceled" を含む）は中断ではない（None）。
        """

        stop = self.interruption()
        if stop is not None:
            return stop
        if reason == "timeout":
            return BUDGET_EXHAUSTED
        return None

    def unknown_end(self, reason: str) -> ExecutionEnd:
        """`interruption_after_unknown` が中断としなかった unknown の、観測された終了原因
        （Issue #106 PR-106-A）。

        理由が時間の上限を表す（`TIME_LIMIT_UNKNOWN_REASONS`: 中止の token は中止されていない
        ので、incremental の solver の "canceled" は timeout）なら TIME_LIMIT、それ以外は
        INCONCLUSIVE。行の status（UNKNOWN）は変えない（期限なしの結果・reason の互換）。
        解析の期限はこの終了原因で「期限で切られた」かを判定する（`core.deadline`）。
        """

        if any(marker in str(reason) for marker in TIME_LIMIT_UNKNOWN_REASONS):
            return ExecutionEnd.TIME_LIMIT
        return ExecutionEnd.INCONCLUSIVE


__all__ = ["BUDGET_EXHAUSTED", "CANCELLED", "TIME_LIMIT_UNKNOWN_REASONS", "ExecutionBudget"]
