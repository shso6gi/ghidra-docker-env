"""Issue #14: per-stage timing of one pair (JVM start, project, import,
auto-analysis, check) is recorded in the unsigned diagnostics block and shown in
the result text."""
import time

import pytest

from scripts.function_tracer_pcode.checker.diagnostics import (
    StageClock,
    attach_stage_timing,
    process_age_seconds,
    result_diagnostics_payload,
)
from scripts.function_tracer_pcode.checker.result import _format_stage_seconds


@pytest.mark.wall_clock  # 壁時計の上限を module の外の時計で確かめる（Issue #239）
def test_stage_clock_accumulates_in_order_and_snapshots():
    clock = StageClock()
    with clock.timed("jvm_start"):
        time.sleep(0.01)
    clock.mark("import_binary1", 0.5)
    clock.mark("import_binary1", 0.25)      # same stage accumulates
    clock.mark("bogus", "not-a-number")     # ignored, never raises
    clock.note("project_cache", "disabled")

    snap = clock.snapshot()
    assert snap["schema"] == "pair-stage-timing-v1"
    assert list(snap["seconds"]) == ["jvm_start", "import_binary1"]
    assert snap["seconds"]["jvm_start"] >= 0.01
    assert snap["seconds"]["import_binary1"] == 0.75
    assert snap["elapsed_seconds"] >= snap["seconds"]["jvm_start"]
    assert snap["notes"] == {"project_cache": "disabled"}


def test_process_age_is_non_negative_or_unavailable():
    age = process_age_seconds()
    assert age is None or age >= 0.0


class _Result:
    def __init__(self):
        self.diagnostics = {"analysis_seconds": {"function1": 1.5}}
        self.total_time = 3.0
        self.debug_trace = None
        self.solver_results = []
        self.pairwise_stats = {}
        self.stage_path = ["P0_BASE"]


def test_stage_timing_is_attached_to_diagnostics_and_payload():
    result = _Result()
    clock = StageClock()
    clock.mark("jvm_start", 1.0)
    clock.mark("check", 3.0)
    attach_stage_timing(result, clock)

    # existing diagnostics are kept, stages added alongside
    assert result.diagnostics["analysis_seconds"] == {"function1": 1.5}
    payload = result_diagnostics_payload(result)
    assert payload["timings"]["analysis_seconds"] == {"function1": 1.5}
    assert payload["timings"]["stages"]["seconds"] == {"jvm_start": 1.0, "check": 3.0}


def test_stage_line_is_rendered_after_total_time_only_when_present():
    assert _format_stage_seconds(None) == ""
    assert _format_stage_seconds({"stages": {"seconds": {}}}) == ""
    line = _format_stage_seconds({
        "stages": {
            "seconds": {"jvm_start": 1.23456, "check": 0.5},
            "process_age_at_start_seconds": 2.0,
        }
    })
    assert line == "Stage seconds: process_startup=2.000 jvm_start=1.235 check=0.500"
