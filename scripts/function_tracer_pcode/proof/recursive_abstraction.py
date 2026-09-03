# -*- coding: utf-8 -*-
"""Compatibility wrapper for deferred call relational abstraction."""

from __future__ import annotations

from scripts.function_tracer_pcode.proof.deferred_call_abstraction import (
    AbstractedCallMatch,
    DeferredCallAbstractionResult,
    RecursiveAbstractionResult,
    abstract_deferred_calls,
    abstract_recursive_calls,
)

__all__ = [
    "AbstractedCallMatch",
    "DeferredCallAbstractionResult",
    "RecursiveAbstractionResult",
    "abstract_deferred_calls",
    "abstract_recursive_calls",
]
