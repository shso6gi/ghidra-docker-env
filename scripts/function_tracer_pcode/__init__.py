# -*- coding: utf-8 -*-
"""Public package surface for the function tracer tooling.

Canonical packaged usage should prefer ``function_tracer_pcode``.
Repository-local callers may continue to use ``scripts.function_tracer_pcode``
while the compatibility layer remains.

Current layout:
- ``analysis``: tracing / decompiler-facing analysis helpers
- ``equivalence``: checker workflow, phases, strategies, SMT integration
- ``model``: AST and lightweight data models
- ``cli``: args, commands, runtime entry helpers
"""

from .analysis import ReturnAnalyzer
from .model import FunctionReturnAnalysis, ReturnInfo, Expression, ExpressionType, Condition
from .io import OutputFormatter
from .analysis.condition import ConditionSimplifier

__version__ = "0.1.0"
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
