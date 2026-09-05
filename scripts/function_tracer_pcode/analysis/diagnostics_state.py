"""Diagnostic status of the last :class:`ReturnAnalyzer` entry point (Phase 6a-4)."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from scripts.function_tracer_pcode.analysis.returns._shared import AnalysisFailure


@dataclass
class AnalysisDiagnosticsState:
    """The two "last failure" fields read by ``get_last_*``.

    Only the *ownership* moves here; the update timing is unchanged and is part of the
    facade contract: ``analyze_function_by_name`` resets both fields on entry and records a
    lookup miss or an exception raised by ``analyze_function``; ``analyze_function`` itself
    records decompilation failures but does **not** reset a previous failure on entry.
    ``ReturnAnalyzer`` exposes both fields through property pairs so the existing
    ``analyzer._last_*`` seams keep working.
    """

    last_function_lookup_error: Optional[str] = None
    last_analysis_failure: Optional[AnalysisFailure] = None
