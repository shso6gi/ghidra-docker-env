# -*- coding: utf-8 -*-
"""Public package surface for the function tracer tooling.

Packaged usage should prefer ``function_tracer_pcode`` as the canonical import
path. During the refactor, repository-local tooling may continue to import the
same package via ``scripts.function_tracer_pcode`` for compatibility.
"""

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
