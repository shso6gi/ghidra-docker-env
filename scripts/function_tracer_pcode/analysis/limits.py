"""Bounded-call limits of :class:`ReturnAnalyzer` (Phase 6a-3)."""

from __future__ import annotations

from dataclasses import dataclass

from scripts.function_tracer_pcode.config.settings import (
    BOUNDED_CALL_MAX_CASES,
    BOUNDED_CALL_REFINEMENT_ENABLED,
    BOUNDED_CALL_UNROLL_LIMIT,
)


@dataclass
class AnalysisLimits:
    """Configuration values that bound call refinement.

    These are settings, not mutable analysis caches, so they live apart from
    :class:`~scripts.function_tracer_pcode.analysis.runtime_state.AnalysisRuntimeState`.
    ``ReturnAnalyzer`` exposes each field through a property pair so the existing
    ``analyzer._bounded_call_*`` seams (read and direct assignment) keep working; the
    values are deliberately left mutable at this stage.  This owner is scoped to the
    three bounded-call settings only.
    """

    bounded_call_refinement_enabled: bool
    bounded_call_unroll_limit: int
    bounded_call_max_cases: int

    @classmethod
    def from_settings(cls) -> "AnalysisLimits":
        """旧 ``ReturnAnalyzer.__init__`` と同じ型変換（``bool`` / ``int``）で settings から生成する。"""
        return cls(
            bounded_call_refinement_enabled=bool(BOUNDED_CALL_REFINEMENT_ENABLED),
            bounded_call_unroll_limit=int(BOUNDED_CALL_UNROLL_LIMIT),
            bounded_call_max_cases=int(BOUNDED_CALL_MAX_CASES),
        )
