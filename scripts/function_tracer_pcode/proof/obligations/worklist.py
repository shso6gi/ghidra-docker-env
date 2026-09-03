"""Deterministic obligation worklist with supersession support."""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from typing import Any, Deque, Dict, Optional, Tuple

from scripts.function_tracer_pcode.proof.obligations.model import (
    ExecutionState,
    ObligationInstanceId,
)


@dataclass
class WorkItem:
    obligation_id: ObligationInstanceId
    kind: str
    payload: Any = None
    state: ExecutionState = ExecutionState.PLANNED


class ProofWorklist:
    def __init__(self) -> None:
        self._items: Dict[Tuple[Any, ...], WorkItem] = {}
        self._ready: Deque[Tuple[Any, ...]] = deque()

    def add(self, item: WorkItem) -> bool:
        key = item.obligation_id.to_key()
        if key in self._items:
            return False
        item.state = ExecutionState.READY
        self._items[key] = item
        self._ready.append(key)
        return True

    def pop(self) -> Optional[WorkItem]:
        while self._ready:
            key = self._ready.popleft()
            item = self._items[key]
            if item.state == ExecutionState.READY:
                item.state = ExecutionState.RUNNING
                return item
        return None

    def complete(self, item: WorkItem) -> None:
        if item.state != ExecutionState.RUNNING:
            raise ValueError("only running work can complete")
        item.state = ExecutionState.COMPLETED

    def supersede_view(self, view_id: Tuple[Any, ...]) -> int:
        count = 0
        for item in self._items.values():
            if (
                item.obligation_id.derived_view_id == view_id
                and item.state != ExecutionState.SUPERSEDED
            ):
                item.state = ExecutionState.SUPERSEDED
                count += 1
        return count

    def items(self) -> Tuple[WorkItem, ...]:
        """Return a stable diagnostic snapshot without exposing mutable storage."""
        return tuple(self._items.values())
