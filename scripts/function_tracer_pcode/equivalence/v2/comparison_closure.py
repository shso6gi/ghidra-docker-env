"""Dependency-neutral typed input for an inconclusive base comparison."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .contracts import canonical_value


@dataclass(frozen=True)
class ComparisonClosureProductionSignal:
    """Typed proof backlog for a receipt-bound inconclusive comparison."""

    comparison_receipt_id: str
    terminal_receipt_digest: str
    branch_id: str
    runtime_premise_digest: str
    runtime_view_id: Any
    query_receipt_digests: tuple[str, ...]
    producer_id: str = "comparison-closure-producer-v1"

    def __post_init__(self) -> None:
        for value in (
            self.comparison_receipt_id, self.terminal_receipt_digest,
            self.branch_id, self.runtime_premise_digest, self.producer_id,
        ):
            if type(value) is not str or not value:
                raise TypeError("comparison closure signal authority is incomplete")
        object.__setattr__(self, "runtime_view_id", canonical_value(self.runtime_view_id))
        object.__setattr__(self, "query_receipt_digests", tuple(self.query_receipt_digests))
        if (
            not self.query_receipt_digests
            or any(type(item) is not str or not item for item in self.query_receipt_digests)
        ):
            raise TypeError("comparison closure query authority is incomplete")
