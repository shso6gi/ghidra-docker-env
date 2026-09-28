"""Debug state, condition identity cache keys and debug event output."""

from __future__ import annotations

from typing import Iterable, List, Optional, Tuple
from scripts.function_tracer_pcode.core import (
    Expression,
    Condition,
    condition_key,
    key_contains_placeholder,
)
from scripts.function_tracer_pcode.core.structural import unidentified_identity
from scripts.function_tracer_pcode.analysis.debug import summarize_expression, summarize_condition
from scripts.function_tracer_pcode.analysis.condition.simplifier_support import (
    _CONDITION_RECOVERABLE_ERRORS,
)


class SimplifierDebugMixin:
    """Debug state, condition identity cache keys and debug event output."""

    @classmethod
    def reset_debug_state(cls) -> None:
        cls._debug_message_count = 0
        cls._debug_suppressed = False
        cls._debug_repeat_counts.clear()

    @classmethod
    def _debug_available(cls) -> bool:
        return cls.DEBUG and cls._debug_message_count < cls._DEBUG_MESSAGE_LIMIT

    @classmethod
    def _debug_print(cls, msg: str, indent: int = 0):
        if not cls.DEBUG:
            return
        if cls._debug_message_count >= cls._DEBUG_MESSAGE_LIMIT:
            if not cls._debug_suppressed:
                prefix = "  " * indent
                print(
                    f"{prefix}[CondSimplifier] debug output suppressed after "
                    f"{cls._DEBUG_MESSAGE_LIMIT} messages"
                )
                cls._debug_suppressed = True
            return
        cls._debug_message_count += 1
        prefix = "  " * indent
        print(f"{prefix}[CondSimplifier] {msg}")

    @classmethod
    def _debug_expr_summary(cls, expr: Optional[Expression], max_depth: int = 4) -> str:
        if not cls._debug_available():
            return "<debug-suppressed>"
        return summarize_expression(expr, max_depth=max_depth)

    @classmethod
    def _debug_condition_summary(cls, condition: Optional[Condition], max_depth: int = 4) -> str:
        if not cls._debug_available():
            return "<debug-suppressed>"
        return summarize_condition(condition, max_depth=max_depth)

    @classmethod
    def _safe_condition_id(cls, condition: Optional[Condition]) -> Tuple[object, ...]:
        """条件の identity（構造 key そのもの。Issue #215）。

        `hash()` に潰すと衝突した 2 つの条件が同じ identity になる。key は
        `core/structural` の契約で「等しい ⇒ 構造が等しい」なので、そのまま使う。
        key を作れないときは識別できない token（何とも等しくならない）にする。
        """

        if condition is None:
            return ("none",)
        try:
            return ("key", condition.structural_key(budget=96))
        except _CONDITION_RECOVERABLE_ERRORS:
            return unidentified_identity("condition_key_failed")

    @classmethod
    def _safe_condition_ids(cls, conditions: Iterable[Condition]) -> Tuple[Tuple[object, ...], ...]:
        keys: List[Tuple[object, ...]] = []
        for condition in (conditions or []):
            keys.append(cls._safe_condition_id(condition))
        # key は型の混ざった tuple なので、決定的な表現（repr）で並べる
        return tuple(sorted(keys, key=repr))

    @classmethod
    def _safe_condition_cache_key(cls, conditions: Iterable[Condition], budget: int = 96) -> Tuple[object, ...]:
        keys: List[object] = []
        for condition in (conditions or []):
            try:
                key = condition_key(condition, budget=budget)
                if key_contains_placeholder(key):
                    key = ("placeholder", cls._safe_condition_id(condition))
            except _CONDITION_RECOVERABLE_ERRORS:
                key = ("unsafe", cls._safe_condition_id(condition))
            keys.append(key)
        keys.sort(key=repr)
        return tuple(keys)

    @classmethod
    def _debug_condition_event(
        cls,
        event: str,
        condition: Condition,
        indent: int = 0,
    ) -> None:
        if not cls._debug_available():
            return

        summary = cls._debug_condition_summary(condition)
        key = (event, summary)
        count = cls._debug_repeat_counts.get(key, 0) + 1
        if len(cls._debug_repeat_counts) > 4096:
            cls._debug_repeat_counts.clear()
        cls._debug_repeat_counts[key] = count

        if count <= cls._DEBUG_REPEAT_LIMIT:
            cls._debug_print(f"{event}: {summary}", indent)
        elif count == cls._DEBUG_REPEAT_LIMIT + 1:
            cls._debug_print(
                f"{event}: {summary} (further repeats suppressed)",
                indent,
            )
