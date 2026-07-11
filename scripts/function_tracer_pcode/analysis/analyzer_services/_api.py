"""Late-bound analyzer facade seams used by extracted services."""

from __future__ import annotations

import importlib


def _call(name, *args, **kwargs):
    facade = importlib.import_module("..analyzer", __package__)
    return getattr(facade, name)(*args, **kwargs)


def PcodeTracer(*args, **kwargs):
    return _call("PcodeTracer", *args, **kwargs)


def ConditionTracker(*args, **kwargs):
    return _call("ConditionTracker", *args, **kwargs)


def StructuralRecurrenceSummarizer(*args, **kwargs):
    return _call("StructuralRecurrenceSummarizer", *args, **kwargs)


def accept_summary_return_candidates(*args, **kwargs):
    return _call("accept_summary_return_candidates", *args, **kwargs)


def resolve_call_targets(*args, **kwargs):
    return _call("resolve_call_targets", *args, **kwargs)
