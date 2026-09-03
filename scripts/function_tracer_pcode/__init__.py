"""Public package surface for the function tracer tooling.

Canonical packaged usage should prefer ``function_tracer_pcode``.
Repository-local callers may continue to use ``scripts.function_tracer_pcode``
while the compatibility layer remains.

Current layout:
- ``analysis``: tracing / decompiler-facing analysis helpers
- ``equivalence``: checker workflow, phases, strategies, SMT integration
- ``model``: AST and lightweight data models
- ``cli``: args, commands, runtime entry helpers

Names are resolved lazily on first access so importing a submodule never
pulls in the whole layer (and cannot create import cycles)."""

from importlib import import_module

__version__ = "0.1.0"

_LAZY = {
    "Condition": ("scripts.function_tracer_pcode.core", "Condition"),
    "ConditionSimplifier": ("scripts.function_tracer_pcode.analysis.condition", "ConditionSimplifier"),
    "Expression": ("scripts.function_tracer_pcode.core", "Expression"),
    "ExpressionType": ("scripts.function_tracer_pcode.core", "ExpressionType"),
    "FunctionReturnAnalysis": ("scripts.function_tracer_pcode.core", "FunctionReturnAnalysis"),
    "OutputFormatter": ("scripts.function_tracer_pcode.reporting", "OutputFormatter"),
    "ReturnAnalyzer": ("scripts.function_tracer_pcode.analysis", "ReturnAnalyzer"),
    "ReturnInfo": ("scripts.function_tracer_pcode.core", "ReturnInfo"),
}

__all__ = sorted(_LAZY)


def __getattr__(name):
    try:
        module_name, attribute = _LAZY[name]
    except KeyError:
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}") from None
    value = getattr(import_module(module_name), attribute)
    globals()[name] = value
    return value


def __dir__():
    return sorted(set(globals()) | set(_LAZY))
