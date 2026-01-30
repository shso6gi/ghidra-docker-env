# -*- coding: utf-8 -*-
"""Return Tracer - Ghidra High P-code Return Value Analyzer"""

from .return_analyzer import ReturnAnalyzer, FunctionReturnAnalysis, ReturnInfo
from .expression import Expression, ExpressionType, Condition
from .output_formatter import OutputFormatter
from .condition_simplifier import ConditionSimplifier

__version__ = "1.0.0"
__all__ = [
    # Main entry points
    "main",
    "ReturnAnalyzer",
    # Analysis results
    "FunctionReturnAnalysis",
    "ReturnInfo",
    # Expression handling
    "Expression",
    "ExpressionType",
    "Condition",
    # Utilities
    "ConditionSimplifier",
    "OutputFormatter",
]