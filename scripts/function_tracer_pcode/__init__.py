# -*- coding: utf-8 -*-
"""Return Tracer - Ghidra High P-code Return Value Analyzer"""

from .core import ReturnAnalyzer
from .model import FunctionReturnAnalysis, ReturnInfo, Expression, ExpressionType, Condition
from .io import OutputFormatter
from .core.condition import ConditionSimplifier
from .cli import main

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
