"""Per-analysis mutable state for :class:`ReturnAnalyzer`."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple

from scripts.function_tracer_pcode.core import Condition
from scripts.function_tracer_pcode.core.analysis import DeferredCallInfo
from scripts.function_tracer_pcode.core.runtime_refs import ExpansionBudgetCollector


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
    # Issue #131: この scope の解析 scope key。marker の所有者を binary/関数/束縛引数
    # まで含めて識別し、別 scope の同種イベントと混同しないために持つ。
    analysis_scope_key: Optional[Tuple[Any, ...]] = None
    blocked_return_path_conditions: List[List[Condition]] = field(default_factory=list)
    noreturn_terminal_observations: List[Dict[str, Any]] = field(default_factory=list)
    return_path_entry_cache: Dict[
        Tuple[Any, ...], Optional[List[Tuple[List[Any], List[Condition]]]]
    ] = field(default_factory=dict)
    # Issue #131: この解析 scope で観測した展開/経路の切り捨て記録。子 session は
    # 自分の collector を新規に所有するので、子の記録が親へ混入しない。
    expansion_budget_collector: ExpansionBudgetCollector = field(
        default_factory=ExpansionBudgetCollector
    )
