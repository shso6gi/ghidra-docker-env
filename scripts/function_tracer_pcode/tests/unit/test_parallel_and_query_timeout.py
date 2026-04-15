# -*- coding: utf-8 -*-
"""Timeout 伝播の回帰テスト."""

from scripts.function_tracer_pcode.equivalence.strategies import pairwise_query_executor
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
from scripts.function_tracer_pcode.smt.parallel import ParallelSolverRunner
from scripts.function_tracer_pcode.smt.parallel import SolverResult as RunnerSolverResult


class _FakeSolver:
    name = "fake"

    def __init__(self):
        self.timeouts = []

    def set_timeout(self, timeout: int) -> None:
        self.timeouts.append(timeout)

    def check_equivalence_direct(self, query: str, cancellation_token=None) -> RunnerSolverResult:
        return RunnerSolverResult(
            solver_name=self.name,
            status=SolverStatus.UNKNOWN,
            elapsed_time=0.0,
        )

    def check_availability(self):
        return True, "ok"

    def get_model(self):
        return None


def test_parallel_runner_run_sequential_does_not_mutate_default_timeout():
    runner = ParallelSolverRunner(timeout=10, solver_classes=[], debug=False)
    solver = _FakeSolver()
    runner._solvers = [solver]

    runner.run_sequential("(check-sat)", timeout=3)

    assert solver.timeouts == [3]
    assert runner.timeout == 10


def test_parallel_runner_run_parallel_forwards_timeout_to_solver():
    runner = ParallelSolverRunner(timeout=10, solver_classes=[], debug=False)
    solver = _FakeSolver()
    runner._solvers = [solver]

    runner.run_parallel("(check-sat)", timeout=7)

    assert solver.timeouts == [7]


def test_pairwise_query_executor_supports_timeout_for_legacy_and_modern_runner():
    base_query = "(check-sat)"

    class _LegacyRunner:
        def __init__(self):
            self.called = False

        def run_sequential(self, query: str):
            self.called = query == base_query
            return _mock_parallel_result()

    class _ModernRunner:
        def __init__(self):
            self.received = None

        def run_sequential(self, query: str, timeout: int):
            self.received = timeout
            return _mock_parallel_result()

    legacy = _LegacyRunner()
    result = pairwise_query_executor._run_query_with_timeout(legacy, base_query, timeout=5)
    assert legacy.called
    assert result.is_equivalent is None

    modern = _ModernRunner()
    pairwise_query_executor._run_query_with_timeout(modern, base_query, timeout=12)
    assert modern.received == 12


def _mock_parallel_result():
    return ParallelResult(
        results=[SolverResult("fake", SolverStatus.UNKNOWN)],
        first_definitive=None,
        is_equivalent=None,
    )
