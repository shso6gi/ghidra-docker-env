# -*- coding: utf-8 -*-
"""結果表示の ERROR/TIMEOUT 分離に関する回帰テスト"""

import sys
from pathlib import Path
from typing import Optional


workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

from scripts.function_tracer_pcode.equivalence.result import EquivalenceResult
from scripts.function_tracer_pcode.equivalence.debug_trace import DebugTrace, Attempt, TransitionReason
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus


def _base_result(
    error_message: Optional[str] = None,
    solver_results: Optional[ParallelResult] = None,
) -> EquivalenceResult:
    return EquivalenceResult(
        is_equivalent=None,
        function1_name="f",
        function2_name="f",
        binary1_name="b1",
        binary2_name="b2",
        solver_results=solver_results or ParallelResult(results=[]),
        error_message=error_message,
    )


def test_to_string_reports_error_explicitly():
    result = _base_result(error_message="normalization fallback crashed")

    output = result.to_string()

    assert "Result: ERROR" in output
    assert "ERROR: normalization fallback crashed" in output
    assert "Result: TIMEOUT" not in output


def test_to_string_keeps_timeout_separate_from_error():
    result = _base_result(
        solver_results=ParallelResult(
            results=[
                SolverResult(
                    solver_name="z3",
                    status=SolverStatus.TIMEOUT,
                    elapsed_time=30.0,
                )
            ]
        )
    )

    output = result.to_string()

    assert "Result: TIMEOUT" in output
    assert "Result: ERROR" not in output


def test_to_string_can_include_phase_usage_summary():
    trace = DebugTrace(
        planned_phases=["P0_BASE", "P1_SIGNEDNESS", "P2_PATTERN_INT"],
        known_phases=["P0_BASE", "P1_SIGNEDNESS", "P2_PATTERN_INT"],
        attempts=[
            Attempt(
                attempt_id=0,
                retry_count=0,
                phase="P0_BASE",
                stage_path=["S_PAIRWISE"],
                strategy="pairwise",
                result=None,
                transition_reason=TransitionReason.UNKNOWN.value,
                elapsed_time=0.2,
            ),
            Attempt(
                attempt_id=1,
                retry_count=1,
                phase="P1_SIGNEDNESS",
                stage_path=["S_PAIRWISE"],
                strategy="pairwise",
                result=True,
                transition_reason=TransitionReason.UNSAT.value,
                elapsed_time=0.1,
            ),
        ],
        final_result=True,
        total_time=0.3,
    )

    result = EquivalenceResult(
        is_equivalent=True,
        function1_name="f",
        function2_name="f",
        binary1_name="b1",
        binary2_name="b2",
        solver_results=ParallelResult(results=[]),
        debug_trace=trace,
        total_time=0.3,
    )

    output = result.to_string(show_phase_usage=True)

    assert "Phase Usage Summary:" in output
    assert "P0_BASE: USED" in output
    assert "P1_SIGNEDNESS: USED" in output
    assert "P2_PATTERN_INT: NOT_REACHED" in output
