# -*- coding: utf-8 -*-
"""Issue #106 PR-106-B: ``analysis_budget_unknown`` in the run-health summary.

``analysis_budget_unknown`` is the alias of the reason count
``unknown_by_reason["analysis_budget_exceeded"]``, split by how each pair
stopped.  The reason id is shared by three limits (the runner's analysis
deadline, the fixed read bound, the authority event contract), so the split
reads the pair's stop state and never infers the deadline from the reason id.
A process ``TIMEOUT`` (the supervisor's wall clock) has no result payload; it
stays in the ``TIMEOUT`` final count and is never an ``analysis_budget_unknown``.
"""
from __future__ import annotations

import json

import pytest

from scripts.function_tracer_pcode.core.errors import PairStopState
from scripts.function_tracer_pcode.reporting.result_summary import (
    aggregate_validation_logs_by_function,
    build_run_health_summary,
    format_overall_results_summary,
    format_run_health_summary,
)
from scripts.function_tracer_pcode.reporting.run_health_summary import (
    parse_overall_summary_health,
)
from scripts.function_tracer_pcode.reporting.unknown_reason_summary import (
    ANALYSIS_BUDGET_UNKNOWN_BY_KIND_KEY,
    ANALYSIS_BUDGET_UNKNOWN_KEY,
    ANALYSIS_DEADLINE_STOPPED_KEY,
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
    summarize_analysis_budget_unknowns,
)

BUDGET = "analysis_budget_exceeded"


def _record(reason_id):
    return {
        "reason_id": reason_id,
        "decision_effect": "blocks_decision",
        "count_kind": "reason_record",
        "aggregation_unit": "result",
    }


def _payload(function, reasons, stop_state=None, **extra):
    payload = {
        "function1_name": function,
        "function2_name": function,
        "binary1_name": "B1",
        "binary2_name": "B2",
        "is_equivalent": None,
        "unknown_reasons": [_record(reason) for reason in reasons],
    }
    if stop_state is not None:
        payload["diagnostics"] = {
            "schema": "result-diagnostics-v1",
            "failures": {"pair_stop_state": stop_state},
        }
    payload.update(extra)
    return payload


def _log(tmp_path, name, payload=None, human="Result: UNKNOWN"):
    path = tmp_path / "sample" / "f" / name
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = [human]
    if payload is not None:
        lines.extend([RESULT_JSON_BEGIN, json.dumps(payload), RESULT_JSON_END])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return path


def _run(tmp_path):
    deadline = PairStopState.PAIR_TERMINAL_DEADLINE.value
    limitation = PairStopState.PAIR_TERMINAL_LIMITATION.value
    return [
        _log(tmp_path, "f_B1_B2.log", _payload("f", [BUDGET, "other_reason"], deadline)),
        _log(tmp_path, "f_B3_B4.log", _payload("f", [BUDGET], deadline)),
        # the fixed read bound shares the reason id; it is not a deadline
        _log(tmp_path, "f_B5_B6.log", _payload("f", [BUDGET], limitation)),
        # a result without a stop state is counted, not guessed into a kind
        _log(tmp_path, "f_B7_B8.log", _payload("f", [BUDGET])),
        # an UNKNOWN for another reason, and a decided pair
        _log(tmp_path, "f_B9_B10.log", _payload("f", ["other_reason"], deadline)),
        _log(tmp_path, "f_B11_B12.log", _payload("f", [], is_equivalent=True),
             human="Result: EQUIVALENT"),
        # a process TIMEOUT: no result payload at all
        _log(tmp_path, "f_B13_B14.log", None, human="Result: TIMEOUT"),
    ]


def test_the_alias_equals_the_reason_count_and_the_kinds_add_up(tmp_path):
    summary = aggregate_validation_logs_by_function(_run(tmp_path))
    health = build_run_health_summary(summary)

    assert health["unknown_by_reason"][BUDGET] == 4
    assert health[ANALYSIS_BUDGET_UNKNOWN_KEY] == 4
    assert health[ANALYSIS_BUDGET_UNKNOWN_BY_KIND_KEY] == {
        "deadline": 2, "limitation": 1, "unclassified": 1,
    }
    assert sum(health[ANALYSIS_BUDGET_UNKNOWN_BY_KIND_KEY].values()) == (
        health[ANALYSIS_BUDGET_UNKNOWN_KEY]
    )


def test_a_deadline_pair_is_counted_even_when_its_primary_reason_is_another(tmp_path):
    """One primary reason per UNKNOWN unit: a pair the deadline stopped can have
    another blocking reason as its primary one.  It is still a deadline pair."""

    deadline = PairStopState.PAIR_TERMINAL_DEADLINE.value
    logs = [
        _log(tmp_path, "f_B1_B2.log", _payload("f", [BUDGET], deadline)),
        # sorts before ``analysis_budget_exceeded``, so it is the primary reason
        _log(tmp_path, "f_B3_B4.log", _payload("f", ["aaa_other_blocking", BUDGET], deadline)),
        _log(tmp_path, "f_B5_B6.log", _payload("f", ["other_reason"], deadline)),
    ]
    health = build_run_health_summary(aggregate_validation_logs_by_function(logs))

    assert health[ANALYSIS_DEADLINE_STOPPED_KEY] == 3
    assert health[ANALYSIS_BUDGET_UNKNOWN_KEY] == health["unknown_by_reason"].get(BUDGET, 0)
    assert health[ANALYSIS_BUDGET_UNKNOWN_KEY] < 3


def test_a_process_timeout_is_not_an_analysis_budget_unknown(tmp_path):
    summary = aggregate_validation_logs_by_function(_run(tmp_path))
    health = build_run_health_summary(summary)

    assert health["final_result_counts"]["TIMEOUT"] == 1
    assert health[ANALYSIS_BUDGET_UNKNOWN_KEY] == 4  # unchanged by the TIMEOUT pair


def test_the_text_shows_the_alias_and_its_split(tmp_path):
    health = build_run_health_summary(aggregate_validation_logs_by_function(_run(tmp_path)))
    text = format_run_health_summary(health)

    assert ("  analysis_budget_unknown: 4 (deadline=2 limitation=1 unclassified=1); "
            "deadline_stopped_unknown=3 process_timeout=1") in text
    assert "TIMEOUT=1" in text


def test_a_health_without_the_key_prints_no_line():
    """An older health JSON is not shown as "0 analysis budget UNKNOWN"."""

    assert "analysis_budget_unknown" not in format_run_health_summary(
        {"total_results": 0, "final_result_counts": {}}
    )


def test_the_overall_summary_round_trip_keeps_the_alias(tmp_path):
    summary = aggregate_validation_logs_by_function(_run(tmp_path))
    path = tmp_path / "overall_summary.txt"
    path.write_text(format_overall_results_summary(summary) + "\n", encoding="utf-8")
    parsed = parse_overall_summary_health(path)

    assert parsed[ANALYSIS_BUDGET_UNKNOWN_KEY] == 4
    # the text has no per-pair stop state, so no split is invented
    assert ANALYSIS_BUDGET_UNKNOWN_BY_KIND_KEY not in parsed
    assert "  analysis_budget_unknown: 4\n" in format_run_health_summary(parsed) + "\n"


@pytest.mark.parametrize(
    "stop_state,kind",
    [
        (PairStopState.PAIR_TERMINAL_DEADLINE.value, "deadline"),
        (PairStopState.PAIR_TERMINAL_LIMITATION.value, "limitation"),
        (PairStopState.INTERNAL_BUG.value, "unclassified"),
        (None, "unclassified"),
    ],
)
def test_the_kind_comes_from_the_stop_state_only(stop_state, kind):
    counts = summarize_analysis_budget_unknowns(
        [_payload("f", [BUDGET], stop_state)]
    )[ANALYSIS_BUDGET_UNKNOWN_BY_KIND_KEY]

    assert counts[kind] == 1
    assert sum(counts.values()) == 1
