# -*- coding: utf-8 -*-
"""Structured analysis failure statuses."""

from dataclasses import dataclass
from typing import Optional


@dataclass(frozen=True)
class AnalysisFailure:
    """Structured reason for a failed analysis attempt."""

    status: str
    message: str
    function_name: Optional[str] = None


ANALYSIS_STATUS_FUNCTION_LOOKUP_MISS = "function_lookup_miss"
ANALYSIS_STATUS_DECOMPILATION_FAILED = "decompilation_failed"
ANALYSIS_STATUS_HIGH_FUNCTION_MISSING = "high_function_missing"
ANALYSIS_STATUS_ANALYSIS_EXCEPTION = "analysis_exception"
