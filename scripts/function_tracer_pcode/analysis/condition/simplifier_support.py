"""Boolean clause types and recoverable-error tuple shared by the condition simplifier and its mixins."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Tuple


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
