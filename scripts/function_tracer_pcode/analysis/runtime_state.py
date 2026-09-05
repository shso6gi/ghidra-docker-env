"""Long-lived mutable runtime state of :class:`ReturnAnalyzer` (Phase 6a-2)."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set, Tuple

from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis


@dataclass
class AnalysisRuntimeState:
    """State whose lifetime is the analyzer's, not one nested analysis context.

    :class:`~scripts.function_tracer_pcode.analysis.session.AnalysisSession` holds the
    per-analysis fields that ``_analysis_context`` pushes and pops.  This object holds the
    long-lived mutable state that must survive across nested analyses: memo caches, the
    direct call graph and its completed-node set, the in-progress recursion guard, and the
    deferred-call sequence counter.  It is deliberately *not* only caches, hence the name.

    Configuration/limits (``bounded_call_*``), the decompiler resource and diagnostic status
    stay outside this object (Phase 6a-3 / #77 / Phase 6a-4).  ``ReturnAnalyzer`` exposes
    every field through a property pair so the existing ``analyzer.<name>`` seams
    (read, in-place mutation, direct assignment, ``+=``) keep working unchanged.
    """

    call_analysis_cache: Dict[Tuple[Any, ...], Optional[FunctionReturnAnalysis]] = field(default_factory=dict)
    local_target_cache: Dict[Tuple[object, ...], Optional[List[Any]]] = field(default_factory=dict)
    effect_summary_cache: Dict[Tuple[Any, ...], Any] = field(default_factory=dict)
    effect_summary_parameter_cache: Dict[Tuple[Any, ...], List[Dict]] = field(default_factory=dict)
    direct_call_graph: Dict[Tuple[Any, ...], Set[Tuple[Any, ...]]] = field(default_factory=dict)
    direct_call_graph_complete_nodes: Set[Tuple[Any, ...]] = field(default_factory=set)
    analysis_in_progress: Dict[Tuple[Any, ...], FunctionReturnAnalysis] = field(default_factory=dict)
    deferred_call_counter: int = 0
