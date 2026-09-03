"""Late-bound pairwise facade seams used by extracted services."""

from __future__ import annotations

import importlib


def _call(name, *args, **kwargs):
    facade = importlib.import_module("scripts.function_tracer_pcode.proof.strategies.pairwise")
    return getattr(facade, name)(*args, **kwargs)


def contains_udiv(*args, **kwargs):
    return _call("contains_udiv", *args, **kwargs)


def extract_sign_facts(*args, **kwargs):
    return _call("extract_sign_facts", *args, **kwargs)


def extract_min_excluded_params(*args, **kwargs):
    return _call("extract_min_excluded_params", *args, **kwargs)


def normalize_expression(*args, **kwargs):
    return _call("normalize_expression", *args, **kwargs)
