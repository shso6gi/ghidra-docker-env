"""Scalar constraint extraction, bound strengthening and scalar implication."""

from __future__ import annotations

from typing import List, Dict, Optional, Tuple
from scripts.function_tracer_pcode.core import Condition
from scripts.function_tracer_pcode.analysis.condition.scalar import (
    ScalarConstraint,
    extract_scalar_constraint,
)
from scripts.function_tracer_pcode.analysis.condition.simplifier_support import (
    _CONDITION_RECOVERABLE_ERRORS,
)


class ScalarBoundsMixin:
    """Scalar constraint extraction, bound strengthening and scalar implication."""

    @classmethod
    def _extract_scalar_constraint(
        cls,
        condition: Condition,
    ) -> Optional[ScalarConstraint]:
        return extract_scalar_constraint(condition)

    @classmethod
    def extract_scalar_constraint(
        cls,
        condition: Condition,
    ) -> Optional[ScalarConstraint]:
        """条件を単一のスカラ制約として解釈する公開ラッパー"""
        return cls._extract_scalar_constraint(condition)

    @classmethod
    def _effective_lower_bound(
        cls,
        value: int,
        inclusive: bool,
        signed: bool,
        bits: int,
    ) -> int:
        minimum = -(1 << (bits - 1)) if signed else 0
        return max(minimum, value if inclusive else value + 1)

    @classmethod
    def _effective_upper_bound(
        cls,
        value: int,
        inclusive: bool,
        signed: bool,
        bits: int,
    ) -> int:
        maximum = (1 << (bits - 1)) - 1 if signed else (1 << bits) - 1
        return min(maximum, value if inclusive else value - 1)

    @classmethod
    def _bounds_contradict(
        cls,
        lower: Optional[Tuple[int, bool]],
        upper: Optional[Tuple[int, bool]],
        signed: bool,
        bits: int,
    ) -> bool:
        if lower is None or upper is None:
            return False
        lower_effective = cls._effective_lower_bound(lower[0], lower[1], signed, bits)
        upper_effective = cls._effective_upper_bound(upper[0], upper[1], signed, bits)
        return lower_effective > upper_effective

    @classmethod
    def _select_stronger_lower(
        cls,
        current: Optional[Tuple[int, bool, int]],
        candidate: Tuple[int, bool, int],
    ) -> Tuple[int, bool, int]:
        if current is None:
            return candidate

        current_effective = cls._effective_lower_bound(
            current[0],
            current[1],
            signed=False,
            bits=128,
        )
        candidate_effective = cls._effective_lower_bound(
            candidate[0],
            candidate[1],
            signed=False,
            bits=128,
        )

        if candidate_effective > current_effective:
            return candidate
        if candidate_effective < current_effective:
            return current
        return candidate if candidate[2] < current[2] else current

    @classmethod
    def _select_stronger_upper(
        cls,
        current: Optional[Tuple[int, bool, int]],
        candidate: Tuple[int, bool, int],
    ) -> Tuple[int, bool, int]:
        if current is None:
            return candidate

        current_effective = cls._effective_upper_bound(
            current[0],
            current[1],
            signed=False,
            bits=128,
        )
        candidate_effective = cls._effective_upper_bound(
            candidate[0],
            candidate[1],
            signed=False,
            bits=128,
        )

        if candidate_effective < current_effective:
            return candidate
        if candidate_effective > current_effective:
            return current
        return candidate if candidate[2] < current[2] else current

    @classmethod
    def _collect_scalar_context(
        cls,
        conditions: List[Condition],
    ) -> Dict[Tuple[object, int], Dict[str, object]]:
        context: Dict[Tuple[object, int], Dict[str, object]] = {}
        for index, cond in enumerate(conditions or []):
            if cond is None:
                continue

            try:
                fact = cls._extract_scalar_constraint(cond)
            except _CONDITION_RECOVERABLE_ERRORS:
                continue

            if fact is None:
                continue
            entry = context.setdefault(
                fact.key,
                {
                    "eq_raw_values": set(),
                    "ne_raw_values": set(),
                    "lower": {False: None, True: None},
                    "upper": {False: None, True: None},
                },
            )

            if fact.kind == "eq":
                entry["eq_raw_values"].add(fact.raw_value)
                continue
            if fact.kind == "ne":
                entry["ne_raw_values"].add(fact.raw_value)
                continue
            if fact.value is None or fact.inclusive is None:
                continue

            candidate = (fact.value, fact.inclusive, index)
            if fact.kind == "lower":
                entry["lower"][fact.signed] = cls._select_stronger_lower(
                    entry["lower"][fact.signed],
                    candidate,
                )
            else:
                entry["upper"][fact.signed] = cls._select_stronger_upper(
                    entry["upper"][fact.signed],
                    candidate,
                )
        return context

    @classmethod
    def _reduction_context_key(
        cls,
        expr,
        conditions: Optional[List[Condition]],
    ) -> Tuple[int, Tuple[int, ...]]:
        context_ids = set()
        for condition in conditions or ():
            if condition is not None:
                context_ids.add(id(condition))
        return id(expr), tuple(sorted(context_ids))

    @classmethod
    def _scalar_constraint_is_implied(
        cls,
        fact: ScalarConstraint,
        context_conditions: List[Condition],
    ) -> bool:
        context = cls._collect_scalar_context(context_conditions)
        entry = context.get(fact.key)
        if entry is None:
            return False

        bits = fact.key[1]
        eq_raw_values = entry["eq_raw_values"]
        ne_raw_values = entry["ne_raw_values"]
        lower = entry["lower"][fact.signed]
        upper = entry["upper"][fact.signed]

        if len(eq_raw_values) == 1:
            eq_raw = next(iter(eq_raw_values))
            eq_value = cls._to_signed_value(eq_raw, bits) if fact.signed else eq_raw
            if fact.kind == "eq":
                return eq_raw == fact.raw_value
            if fact.kind == "ne":
                return eq_raw != fact.raw_value
            if fact.kind == "lower":
                required = cls._effective_lower_bound(
                    fact.value,
                    bool(fact.inclusive),
                    fact.signed,
                    bits,
                )
                return eq_value >= required
            if fact.kind == "upper":
                required = cls._effective_upper_bound(
                    fact.value,
                    bool(fact.inclusive),
                    fact.signed,
                    bits,
                )
                return eq_value <= required

        if fact.kind == "eq":
            if lower is None or upper is None:
                return False
            lower_effective = cls._effective_lower_bound(lower[0], lower[1], fact.signed, bits)
            upper_effective = cls._effective_upper_bound(upper[0], upper[1], fact.signed, bits)
            if lower_effective != upper_effective:
                return False
            collapsed_raw = cls._normalize_raw_value(lower_effective, bits)
            return collapsed_raw == fact.raw_value and collapsed_raw not in ne_raw_values

        if fact.kind == "ne":
            if fact.raw_value in ne_raw_values:
                return True
            fact_value = cls._to_signed_value(fact.raw_value, bits) if fact.signed else fact.raw_value
            if lower is not None:
                lower_effective = cls._effective_lower_bound(lower[0], lower[1], fact.signed, bits)
                if fact_value < lower_effective:
                    return True
            if upper is not None:
                upper_effective = cls._effective_upper_bound(upper[0], upper[1], fact.signed, bits)
                if fact_value > upper_effective:
                    return True
            return False

        if fact.kind == "lower":
            if lower is None:
                return False
            current_effective = cls._effective_lower_bound(lower[0], lower[1], fact.signed, bits)
            required_effective = cls._effective_lower_bound(
                fact.value,
                bool(fact.inclusive),
                fact.signed,
                bits,
            )
            return current_effective >= required_effective

        if fact.kind == "upper":
            if upper is None:
                return False
            current_effective = cls._effective_upper_bound(upper[0], upper[1], fact.signed, bits)
            required_effective = cls._effective_upper_bound(
                fact.value,
                bool(fact.inclusive),
                fact.signed,
                bits,
            )
            return current_effective <= required_effective

        return False
