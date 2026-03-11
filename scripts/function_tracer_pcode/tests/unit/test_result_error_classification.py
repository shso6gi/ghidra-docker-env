# -*- coding: utf-8 -*-
"""結果表示の ERROR/TIMEOUT 分離に関する回帰テスト"""

import sys
from pathlib import Path
from typing import Optional


workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

from scripts.function_tracer_pcode.equivalence.result import EquivalenceResult
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
