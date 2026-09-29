"""Boolean clause types and recoverable-error tuple shared by the condition simplifier and its mixins."""

from __future__ import annotations

import threading
from contextlib import contextmanager
from dataclasses import dataclass
from typing import Iterator, Tuple

from scripts.function_tracer_pcode.core.condition_metrics import note


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
# 再入 guard の打ち切り（Issue #105 PR-105-A）
# ---------------------------------------------------------------------------
#
# 条件簡約の再入 guard（同じ問いの途中で同じ問いが来たら打ち切る: 含意・conjunction・
# 正規化・文脈での簡約）は、打ち切った問いに弱い答え（`None` / `False` / 簡約しない）を
# 返す。その弱い答えを材料にした上位の答えは **呼ばれ方に依存する** ので、pair の
# cache に覚えてはいけない（覚えると「最初にどこから聞かれたか」で後の答えが変わり、
# 追い出し（evict）でまた変わる）。打ち切りは全部 `note_reentry_guard_hit()` を通し、
# 答えを覚える側は `reentry_guard_scope()` の中で計算して `clean` のときだけ覚える。

_GUARD_STATE = threading.local()


def _guard_hits() -> int:
    return getattr(_GUARD_STATE, "hits", 0)


def note_reentry_guard_hit() -> None:
    """再入 guard が問いを打ち切った（この thread の打ち切り回数を 1 つ進める）。"""

    _GUARD_STATE.hits = _guard_hits() + 1
    note("simplifier.reentry_guard_hit")


class ReentryGuardScope:
    """計算の間に再入 guard の打ち切りが起きたか（`clean` が真なら起きていない）。"""

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
