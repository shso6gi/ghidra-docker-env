# -*- coding: utf-8 -*-
"""Return Tracer - Ghidra High P-code Return Value Analyzer"""

from .analysis import ReturnAnalyzer
from .model import FunctionReturnAnalysis, ReturnInfo, Expression, ExpressionType, Condition
from .io import OutputFormatter
from .analysis.condition import ConditionSimplifier

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


def __getattr__(name):
    if name == "main":
        from .cli.main import main
        return main
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")