# -*- coding: utf-8 -*-
"""Validation summary helpers for equivalence results.

Keep exports lazy so ``python -m scripts.function_tracer_pcode.validation.<module>``
does not preload the same submodule while package initialization is running.
"""

from importlib import import_module

__all__ = [
    "UnknownValidationDiff",
    "UnknownValidationSummary",
    "OverallValidationSummary",
    "ValidationLogRecord",
    "ValidationResultAggregate",
    "aggregate_validation_logs",
    "aggregate_validation_logs_by_function",
    "assert_aggregation_invariant",
    "compare_validation_unknowns",
    "canonical_validation_surface",
    "canonical_validation_surface_hash",
    "extract_result_payloads_from_logs",
    "extract_result_payloads_from_text",
    "format_function_results_summary",
    "format_overall_results_summary",
    "format_validation_unknown_diff",
    "format_validation_unknown_summary",
    "summarize_validation_unknowns",
]


def __getattr__(name):
    if name in {
        "UnknownValidationDiff",
        "UnknownValidationSummary",
        "compare_validation_unknowns",
        "extract_result_payloads_from_logs",
        "extract_result_payloads_from_text",
        "format_validation_unknown_diff",
        "format_validation_unknown_summary",
        "summarize_validation_unknowns",
    }:
        module = import_module(".unknown_reason_summary", __name__)
        return getattr(module, name)
    if name in {
        "OverallValidationSummary",
        "ValidationLogRecord",
        "ValidationResultAggregate",
        "aggregate_validation_logs",
        "aggregate_validation_logs_by_function",
        "assert_aggregation_invariant",
        "canonical_validation_surface",
        "canonical_validation_surface_hash",
        "format_function_results_summary",
        "format_overall_results_summary",
    }:
        module = import_module(".result_summary", __name__)
        return getattr(module, name)
    raise AttributeError(name)
