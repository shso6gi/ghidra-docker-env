"""Per-analysis mutable state for :class:`ReturnAnalyzer`."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple

from ..model import Condition
from ..model.analysis import DeferredCallInfo


@dataclass
class AnalysisSession:
    """State whose lifetime follows one nested analysis context.

    Long-lived caches, recursion guards, the decompiler, and diagnostic status
    intentionally remain owned by ``ReturnAnalyzer``.  This object only makes
    the previously implicit current-analysis fields explicit.
    """

    parameters: List[Dict[str, Any]] = field(default_factory=list)
    effect_summary: Optional[Any] = None
    deferred_calls: Dict[Tuple[Any, ...], DeferredCallInfo] = field(default_factory=dict)
    function_prototype: Optional[Any] = None
    function_entry_address: Optional[Any] = None
    blocked_return_path_conditions: List[List[Condition]] = field(default_factory=list)
    noreturn_terminal_observations: List[Dict[str, Any]] = field(default_factory=list)
    return_path_entry_cache: Dict[
        Tuple[Any, ...], Optional[List[Tuple[List[Any], List[Condition]]]]
    ] = field(default_factory=dict)
