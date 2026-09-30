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
採ってよいかは `core.deadline`（`admit` / `settle`）が決める。
"""

from __future__ import annotations

import time
from typing import Any, Optional


#: 中断の種類
CANCELLED = "cancelled"
BUDGET_EXHAUSTED = "budget_exhausted"


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

        `not_after`（Issue #106 PR-106-A）は解析全体の期限から owner が求めた、この実行が
        越えてはならない absolute monotonic の時刻（`core.deadline.Admission.not_after`）。
        与えられたら実行の期限はその手前で切る。**解析の期限と 1 回の実行の期限を突き合わせる
        のはここだけ**で、残り時間の計算（`remaining_ms` / `interruption`）はこの 1 つの期限
        だけを見る。
        """

        deadline = time.monotonic() + float(seconds)
        if not_after is not None:
            deadline = min(deadline, float(not_after))
        return cls(deadline, cancellation_token)

    def remaining_ms(self) -> int:
        """期限までの残り（ミリ秒、切り捨て）。0 以下なら期限切れ。"""

        return int((self.deadline - time.monotonic()) * 1000)

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


__all__ = ["BUDGET_EXHAUSTED", "CANCELLED", "ExecutionBudget"]
