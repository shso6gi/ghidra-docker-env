"""等価性判定戦略モジュール

Names are resolved lazily on first access so importing a submodule never
pulls in the whole layer (and cannot create import cycles)."""

from importlib import import_module

_LAZY = {
    "CheckStrategy": ("scripts.function_tracer_pcode.proof.strategies.base", "CheckStrategy"),
    "MonolithicStrategy": ("scripts.function_tracer_pcode.proof.strategies.monolithic", "MonolithicStrategy"),
    "PairwiseStrategy": ("scripts.function_tracer_pcode.proof.strategies.pairwise", "PairwiseStrategy"),
    "StrategyResult": ("scripts.function_tracer_pcode.proof.strategies.base", "StrategyResult"),
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
