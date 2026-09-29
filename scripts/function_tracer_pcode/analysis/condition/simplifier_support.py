"""Boolean clause types and recoverable-error tuple shared by the condition simplifier and its mixins."""

from __future__ import annotations

import threading
from contextlib import contextmanager
from dataclasses import dataclass
from typing import Iterator, Tuple

from scripts.function_tracer_pcode.core.budget_policy import FallbackBudgetMeter
from scripts.function_tracer_pcode.core.condition_metrics import budget_event, note


class ConditionRecoverableSimplificationError(ValueError):
    """Raised when condition simplification cannot prove a fact soundly."""


_CONDITION_RECOVERABLE_ERRORS = (
    AttributeError,
    IndexError,
    KeyError,
    TypeError,
    ValueError,
    RecursionError,
)


BooleanAtom = Tuple[object, str, object]


BooleanLiteral = Tuple[BooleanAtom, bool]


@dataclass(frozen=True)
class BooleanClause:
    """CNF 句の object-centric 表現。"""

    literals: Tuple[BooleanLiteral, ...]
    source_indices: Tuple[int, ...]


# ---------------------------------------------------------------------------
# 打ち切り: 再入 guard（Issue #105 PR-105-A）と予算の fallback（PR-105-B）
# ---------------------------------------------------------------------------
#
# 条件簡約の再入 guard（同じ問いの途中で同じ問いが来たら打ち切る: 含意・conjunction・
# 正規化・文脈での簡約）と DPLL の決定回数予算は、打ち切った問いに弱い答え（`None` /
# `False` / 簡約しない）を返す。その弱い答えは **同じ identity の問いでも呼ばれ方で変わる**
# （再入: どこから最初に聞かれたか / DPLL: identity は条件の順に依らないが、節の順で分岐の
# 仕方と決定の数が変わる）ので、それを材料にした上位の答えを pair の cache に覚えては
# いけない（覚えると後の答えが履歴で変わり、追い出し（evict）でまた変わる）。これらの打ち切りは
# `note_reentry_guard_hit()` / `note_budget_fallback(..., history_dependent=True)` を通し、
# 答えを覚える側は `reentry_guard_scope()` の中で計算して `clean` のときだけ覚える。
#
# oracle の query 予算は違う: pair の中で一度尽きたら尽きたまま（消費は戻らない）なので、
# 尽きた後に作った答えは、後で作り直しても同じ答えになる。覚えても履歴への依存は増えない
# （覚えないと、尽きた後の pair の残りで cache が効かなくなり、重い pair ほど遅くなる）。

_GUARD_STATE = threading.local()


def _guard_hits() -> int:
    return getattr(_GUARD_STATE, "hits", 0)


def _note_truncation() -> None:
    _GUARD_STATE.hits = _guard_hits() + 1


def note_reentry_guard_hit() -> None:
    """再入 guard が問いを打ち切った（この thread の打ち切り回数を 1 つ進める）。"""

    _note_truncation()
    note("simplifier.reentry_guard_hit")


def note_budget_fallback(
    meter: FallbackBudgetMeter, *, site: str, fallback_taken: str, history_dependent: bool
) -> None:
    """fallback の予算が尽きて問いに答えなかった（診断へ 1 件残す）。

    予算の意味（上限・消費）は `meter`（`core/budget_policy`）、何を返したかは呼ぶ側が
    `fallback_taken` で示す。`history_dependent` が真（同じ identity の問いでも呼ばれ方で
    打ち切り方が変わる）なら打ち切りとしても数え、それを材料にした答えを覚えさせない。
    記録は診断だけで、判定には戻らない。
    """

    if history_dependent:
        _note_truncation()
    budget_event(
        budget_type=meter.kind.value,
        site=site,
        limit=meter.limit,
        consumed=meter.consumed,
        fallback_taken=fallback_taken,
    )


class ReentryGuardScope:
    """計算の間に打ち切り（再入 guard・予算の fallback）が起きたか（`clean` が真なら起きていない）。"""

    __slots__ = ("_start", "clean")

    def __init__(self) -> None:
        self._start = _guard_hits()
        self.clean = True

    def close(self) -> None:
        self.clean = _guard_hits() == self._start
        if not self.clean:
            note("simplifier.guard_tainted_not_stored")


@contextmanager
def reentry_guard_scope() -> Iterator[ReentryGuardScope]:
    scope = ReentryGuardScope()
    try:
        yield scope
    finally:
        scope.close()
