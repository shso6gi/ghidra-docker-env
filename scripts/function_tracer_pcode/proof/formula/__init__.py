"""SMT式構築サブモジュール

Names are resolved lazily on first access so importing a submodule never
pulls in the whole layer (and cannot create import cycles)."""

from importlib import import_module

_LAZY = {
    "ExtensionType": ("scripts.function_tracer_pcode.proof.formula.variable", "ExtensionType"),
    "ExtraVariableAnalysis": ("scripts.function_tracer_pcode.proof.formula.variable", "ExtraVariableAnalysis"),
    "ExtraVariableInfo": ("scripts.function_tracer_pcode.proof.formula.types", "ExtraVariableInfo"),
    "FormulaBuilder": ("scripts.function_tracer_pcode.proof.formula.builder", "FormulaBuilder"),
    "FormulaBuilderResult": ("scripts.function_tracer_pcode.proof.formula.types", "FormulaBuilderResult"),
    "ParameterFragmentInfo": ("scripts.function_tracer_pcode.proof.formula.variable", "ParameterFragmentInfo"),
    "ParameterInfo": ("scripts.function_tracer_pcode.proof.formula.types", "ParameterInfo"),
    "ParameterPair": ("scripts.function_tracer_pcode.proof.formula.types", "ParameterPair"),
    "VariableAnalyzer": ("scripts.function_tracer_pcode.proof.formula.variable", "VariableAnalyzer"),
    "VariableClassification": ("scripts.function_tracer_pcode.proof.formula.variable", "VariableClassification"),
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
