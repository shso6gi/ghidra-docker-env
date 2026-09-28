# -*- coding: utf-8 -*-
"""Issue #161: 1 つの query の判定は backend の結果の集合だけで決まる。

固定する契約（`smt.aggregation` / `smt.parallel`）:

* backend の完了順・runner が結果を受け取る順に依らない。`run_parallel` の結果
  （行・代表結果・`is_equivalent`・反例）は、完了順のすべての並べ方で同じで、
  `run_sequential` の結果とも同じ
* 行は設定された backend の順に 1 行ずつ（途中で打ち切って行が欠けない）
* SAT と UNSAT が食い違ったら判定しない（等価にも非等価にもしない、反例も無い）
* 代表の SAT は canonical witness 付きの行を優先する。witness の無い SAT しか無ければ
  非等価だが反例は無い（反例を要る consumer は受け入れない = fail closed）
* canonical witness を作れない backend の model は backend の境界で落とす
"""

from __future__ import annotations

import itertools
import threading

import pytest

from scripts.function_tracer_pcode.smt.aggregation import aggregate_backend_results
from scripts.function_tracer_pcode.smt.interface import SMTSolver, SolverResult, SolverStatus
from scripts.function_tracer_pcode.smt.parallel import ParallelResult, ParallelSolverRunner
from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver


SAT, UNSAT = SolverStatus.SAT, SolverStatus.UNSAT
TIMEOUT, UNKNOWN, ERROR = SolverStatus.TIMEOUT, SolverStatus.UNKNOWN, SolverStatus.ERROR


def _backend(name, status, *, canonical, model=None, gate=None):
    """`status` を返す fake backend。`gate` があれば (待つ event, 終わったら立てる event)。"""

    class _Backend(SMTSolver):
        PROVIDES_CANONICAL_WITNESS = canonical

        def __init__(self, timeout=10, debug=False):
            super().__init__(timeout)

        @property
        def name(self):
            return name

        def check_availability(self):
            return True, "test"

        def check_equivalence_direct(self, smt_script, cancellation_token=None):
            if gate is not None:
                assert gate[0].wait(5), f"{name} was never released"
            try:
                return SolverResult(name, status, model=None if model is None else dict(model))
            finally:
                if gate is not None:
                    gate[1].set()

    _Backend.__name__ = f"_Backend_{name}"
    return _Backend


def _run_in_completion_order(specs, completion_order, mode="parallel"):
    """`specs`（設定順）を、`completion_order` の順に終わるよう強制して解く。"""

    events = [threading.Event() for _ in specs]
    released = threading.Event()
    released.set()
    gates = {}
    previous = released
    for index in completion_order or ():
        gates[index] = (previous, events[index])
        previous = events[index]
    classes = [
        _backend(name, status, canonical=canonical, model=model,
                 gate=gates[index] if mode == "parallel" else None)
        for index, (name, status, canonical, model) in enumerate(specs)
    ]
    runner = ParallelSolverRunner(timeout=5, solver_classes=classes)
    if mode == "parallel":
        return runner.run_parallel("(check-sat)")
    return runner.run_sequential("(check-sat)")


def _observable(result: ParallelResult):
    rows = tuple((row.solver_name, row.status, row.model) for row in result.results)
    representative = result.first_definitive
    return (
        rows,
        None if representative is None else representative.solver_name,
        result.is_equivalent,
        result.get_counterexample(),
        result.backend_conflict,
    )


# (name, status, provides canonical witness, model)
SCENARIOS = {
    "canonical SAT and arbitrary SAT": (
        [("canonical", SAT, True, {"x": 0}), ("arbitrary", SAT, False, {"x": 42})],
        ("canonical", False, {"x": 0}, False),
    ),
    "arbitrary SAT configured first": (
        [("arbitrary", SAT, False, {"x": 42}), ("canonical", SAT, True, {"x": 0})],
        ("canonical", False, {"x": 0}, False),
    ),
    "canonical UNSAT and arbitrary SAT conflict": (
        [("canonical", UNSAT, True, None), ("arbitrary", SAT, False, {"x": 42})],
        (None, None, None, True),
    ),
    "canonical SAT and arbitrary UNSAT conflict": (
        [("canonical", SAT, True, {"x": 0}), ("arbitrary", UNSAT, False, None)],
        (None, None, None, True),
    ),
    "canonical TIMEOUT and arbitrary SAT": (
        [("canonical", TIMEOUT, True, None), ("arbitrary", SAT, False, {"x": 42})],
        ("arbitrary", False, None, False),
    ),
    "canonical UNKNOWN and arbitrary SAT": (
        [("canonical", UNKNOWN, True, None), ("arbitrary", SAT, False, {"x": 42})],
        ("arbitrary", False, None, False),
    ),
    "canonical UNKNOWN and arbitrary UNSAT": (
        [("canonical", UNKNOWN, True, None), ("arbitrary", UNSAT, False, None)],
        ("arbitrary", True, None, False),
    ),
    "all undecided": (
        [("canonical", TIMEOUT, True, None), ("arbitrary", ERROR, False, None)],
        (None, None, None, False),
    ),
    "two canonical SATs with different witnesses": (
        [("first", SAT, True, {"x": 1}), ("second", SAT, True, {"x": 2})],
        ("first", False, {"x": 1}, False),
    ),
    "three backends with a hidden conflict": (
        [("a", SAT, True, {"x": 0}), ("b", TIMEOUT, True, None), ("c", UNSAT, False, None)],
        (None, None, None, True),
    ),
}


@pytest.mark.parametrize("scenario", sorted(SCENARIOS))
def test_the_verdict_does_not_depend_on_which_backend_finished_first(scenario):
    specs, (representative, is_equivalent, counterexample, conflict) = SCENARIOS[scenario]
    observed = {
        order: _observable(_run_in_completion_order(specs, order))
        for order in itertools.permutations(range(len(specs)))
    }
    first = next(iter(observed.values()))
    assert all(value == first for value in observed.values()), observed
    # 逐次実行も同じ規則
    assert _observable(_run_in_completion_order(specs, None, mode="sequential")) == first

    rows, observed_representative, observed_equivalent, observed_counterexample, observed_conflict = first
    # 行は設定順に全 backend 分（打ち切りで欠けない）
    assert [row[0] for row in rows] == [spec[0] for spec in specs]
    assert observed_representative == representative
    assert observed_equivalent is is_equivalent
    assert observed_counterexample == counterexample
    assert observed_conflict is conflict


@pytest.mark.parametrize("status", [SAT, UNSAT, TIMEOUT, UNKNOWN, ERROR])
def test_a_single_backend_decides_by_its_own_status(status):
    model = {"x": 3} if status == SAT else None
    result = _run_in_completion_order([("only", status, True, model)], (0,))
    assert [row.status for row in result.results] == [status]
    assert result.is_equivalent is {SAT: False, UNSAT: True}.get(status)
    assert result.get_counterexample() == model
    assert result.backend_conflict is False


def test_a_manually_built_result_follows_the_same_rule():
    conflict = ParallelResult([
        SolverResult("a", UNSAT), SolverResult("b", SAT, model={"x": 1}),
    ])
    assert conflict.first_definitive is None
    assert conflict.is_equivalent is None
    assert conflict.get_counterexample() is None
    assert conflict.backend_conflict is True

    witnessed = ParallelResult([SolverResult("a", SAT), SolverResult("b", SAT, model={"x": 1})])
    assert witnessed.first_definitive.solver_name == "b"
    assert witnessed.get_counterexample() == {"x": 1}


def test_the_aggregation_is_a_function_of_the_ordered_rows_only():
    rows = [SolverResult("a", TIMEOUT), SolverResult("b", SAT), SolverResult("c", SAT, model={"x": 0})]
    aggregate = aggregate_backend_results(rows)
    assert aggregate.representative is rows[2]
    assert aggregate.is_equivalent is False
    assert aggregate_backend_results([]).representative is None


def test_the_backend_boundary_drops_a_model_from_a_backend_without_the_witness_contract():
    arbitrary = ParallelSolverRunner(
        timeout=1, solver_classes=[_backend("arbitrary", SAT, canonical=False, model={"x": 42})]
    )
    result = arbitrary.run_sequential("(check-sat)")
    assert result.is_equivalent is False
    assert result.get_counterexample() is None
    assert result.results[0].model is None
    assert "canonical witness unavailable" in result.results[0].error_message

    canonical = ParallelSolverRunner(
        timeout=1, solver_classes=[_backend("canonical", SAT, canonical=True, model={"x": 42})]
    )
    assert canonical.run_sequential("(check-sat)").get_counterexample() == {"x": 42}
    assert Z3Solver.PROVIDES_CANONICAL_WITNESS is True
