"""解析レイヤ - P-code解析とトレースの中核機能

Names are resolved lazily on first access so importing a submodule never
pulls in the whole layer (and cannot create import cycles)."""

from importlib import import_module

_LAZY = {
    "BoundedCallRefiner": ("scripts.function_tracer_pcode.analysis.bounded_refinement", "BoundedCallRefiner"),
    "ExpandedBranch": ("scripts.function_tracer_pcode.analysis.phi_resolver", "ExpandedBranch"),
    "PcodeTracer": ("scripts.function_tracer_pcode.analysis.tracer", "PcodeTracer"),
    "PhiBranch": ("scripts.function_tracer_pcode.analysis.phi_resolver", "PhiBranch"),
    "PhiHandler": ("scripts.function_tracer_pcode.analysis.phi_resolver", "PhiHandler"),
    "ReturnAnalyzer": ("scripts.function_tracer_pcode.analysis.returns.analyzer", "ReturnAnalyzer"),
    "VarnodeKey": ("scripts.function_tracer_pcode.analysis.tracer", "VarnodeKey"),
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
