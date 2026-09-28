# -*- coding: utf-8 -*-
"""Issue #161: 1 つの query を複数 backend で解いた結果の集約と、`ParallelResult` の 2 つの作り方。

固定する契約（`smt.aggregation` / `smt.parallel` / `smt.interface`）:

* **1 query × backend** の結果（`ParallelResult.from_backend_results`）:
  * backend の完了順・runner が結果を受け取る順に依らない（完了順のすべての並べ方で同じで、
    `run_sequential` とも同じ）。行は設定された backend の順に 1 行ずつ
  * SAT と UNSAT が食い違ったら判定しない。canonical な witness が backend 間で食い違っても
    判定しない（canonical witness は query の意味だけで一意なので、不一致は契約違反）
  * canonical provider の witness の無い・形の違う SAT は、境界で ERROR にする（自己申告を
    信じない）。canonical でない backend の model は落とす
* **producer が合成した結果**（複数の query / region / case の証拠）: 直接構築し、backend の
  集約規則を適用しない。異なる region の SAT と UNSAT は食い違いではなく、反例は後段
  （MIPS64 Phase 4-B）まで残る
* 1 query の実行は必ず factory を通る（runner と monolithic の共有 session）
"""

from __future__ import annotations

import ast
import itertools
import pathlib
import threading
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.smt.aggregation import (
    CONTRACT_VIOLATION,
    SAT_UNSAT_CONFLICT,
    WITNESS_DISAGREEMENT,
    aggregate_backend_results,
)
from scripts.function_tracer_pcode.smt.interface import (
    SMTSolver,
    SolverResult,
    SolverStatus,
    enforce_witness_contract,
)
from scripts.function_tracer_pcode.smt.parallel import ParallelResult, ParallelSolverRunner
from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver


PACKAGE_ROOT = pathlib.Path(__file__).resolve().parents[2]
SAT, UNSAT = SolverStatus.SAT, SolverStatus.UNSAT
TIMEOUT, UNKNOWN, ERROR = SolverStatus.TIMEOUT, SolverStatus.UNKNOWN, SolverStatus.ERROR

#: fake backend が解く query（witness の成分は x だけ）
QUERY = "(declare-const x (_ BitVec 8))\n(assert (bvugt x #x00))\n(check-sat)"


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
        return runner.run_parallel(QUERY)
    return runner.run_sequential(QUERY)


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


# (name, status, provides canonical witness, model) → (代表, is_equivalent, 反例, 食い違い)
SCENARIOS = {
    "canonical SAT and arbitrary SAT": (
        [("canonical", SAT, True, {"x": 1}), ("arbitrary", SAT, False, {"x": 42})],
        ("canonical", False, {"x": 1}, None),
    ),
    "arbitrary SAT configured first": (
        [("arbitrary", SAT, False, {"x": 42}), ("canonical", SAT, True, {"x": 1})],
        ("canonical", False, {"x": 1}, None),
    ),
    "canonical UNSAT and arbitrary SAT conflict": (
        [("canonical", UNSAT, True, None), ("arbitrary", SAT, False, {"x": 42})],
        (None, None, None, SAT_UNSAT_CONFLICT),
    ),
    "canonical SAT and arbitrary UNSAT conflict": (
        [("canonical", SAT, True, {"x": 1}), ("arbitrary", UNSAT, False, None)],
        (None, None, None, SAT_UNSAT_CONFLICT),
    ),
    "canonical TIMEOUT and arbitrary SAT": (
        [("canonical", TIMEOUT, True, None), ("arbitrary", SAT, False, {"x": 42})],
        ("arbitrary", False, None, None),
    ),
    "canonical UNKNOWN and arbitrary SAT": (
        [("canonical", UNKNOWN, True, None), ("arbitrary", SAT, False, {"x": 42})],
        ("arbitrary", False, None, None),
    ),
    "canonical UNKNOWN and arbitrary UNSAT": (
        [("canonical", UNKNOWN, True, None), ("arbitrary", UNSAT, False, None)],
        ("arbitrary", True, None, None),
    ),
    "all undecided": (
        [("canonical", TIMEOUT, True, None), ("arbitrary", ERROR, False, None)],
        (None, None, None, None),
    ),
    "two canonical SATs with the same witness": (
        [("first", SAT, True, {"x": 1}), ("second", SAT, True, {"x": 1})],
        ("first", False, {"x": 1}, None),
    ),
    "two canonical SATs with different witnesses": (
        [("first", SAT, True, {"x": 1}), ("second", SAT, True, {"x": 2})],
        (None, None, None, WITNESS_DISAGREEMENT),
    ),
    "three backends with a hidden conflict": (
        [("a", SAT, True, {"x": 1}), ("b", TIMEOUT, True, None), ("c", UNSAT, False, None)],
        (None, None, None, SAT_UNSAT_CONFLICT),
    ),
    # 契約を破った backend は SAT を主張した: 他の UNSAT で等価にしない
    "a canonical provider breaks its contract next to an honest UNSAT": (
        [("liar", SAT, True, None), ("honest", UNSAT, True, None)],
        (None, None, None, CONTRACT_VIOLATION),
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
    assert observed_conflict == conflict


@pytest.mark.parametrize("status", [SAT, UNSAT, TIMEOUT, UNKNOWN, ERROR])
def test_a_single_backend_decides_by_its_own_status(status):
    model = {"x": 3} if status == SAT else None
    result = _run_in_completion_order([("only", status, True, model)], (0,))
    assert [row.status for row in result.results] == [status]
    assert result.is_equivalent is {SAT: False, UNSAT: True}.get(status)
    assert result.get_counterexample() == model
    assert result.backend_conflict is None


# ---------------------------------------------------------------------------
# canonical provider の契約は境界で検査する（自己申告を信じない）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "model, reason",
    [
        (None, "carries no witness"),
        ({}, "does not bind exactly"),
        ({"x": 1, "y": 2}, "does not bind exactly"),
        ({"x": True}, "needs an int"),
        ({"x": 256}, "out of range"),
        ({"x": -1}, "out of range"),
    ],
)
def test_a_canonical_provider_that_breaks_the_witness_contract_is_not_believed(model, reason):
    result = _run_in_completion_order([("liar", SAT, True, model)], (0,))
    row = result.results[0]
    assert row.status == ERROR
    assert "canonical witness contract violated" in row.error_message and reason in row.error_message
    assert row.witness_contract_violation is not None
    assert result.is_equivalent is None
    assert result.get_counterexample() is None
    assert result.backend_conflict == CONTRACT_VIOLATION


def test_the_witness_contract_checks_bool_and_int_sorts():
    script = "(declare-const f Bool)\n(declare-const n Int)\n(check-sat)"
    good = SolverResult("z", SAT, model={"f": False, "n": -3})
    assert enforce_witness_contract(good, script, canonical=True) is good
    for bad in ({"f": 0, "n": -3}, {"f": False, "n": False}, {"f": False, "n": "3"}):
        checked = enforce_witness_contract(SolverResult("z", SAT, model=bad), script, canonical=True)
        assert checked.status == ERROR, bad


def test_the_backend_boundary_drops_a_model_from_a_backend_without_the_witness_contract():
    arbitrary = ParallelSolverRunner(
        timeout=1, solver_classes=[_backend("arbitrary", SAT, canonical=False, model={"x": 42})]
    )
    result = arbitrary.run_sequential(QUERY)
    assert result.is_equivalent is False
    assert result.get_counterexample() is None
    assert result.results[0].model is None
    assert "canonical witness unavailable" in result.results[0].error_message

    canonical = ParallelSolverRunner(
        timeout=1, solver_classes=[_backend("canonical", SAT, canonical=True, model={"x": 42})]
    )
    assert canonical.run_sequential(QUERY).get_counterexample() == {"x": 42}
    assert Z3Solver.PROVIDES_CANONICAL_WITNESS is True


def test_the_aggregation_is_a_function_of_the_ordered_rows_only():
    rows = [SolverResult("a", TIMEOUT), SolverResult("b", SAT), SolverResult("c", SAT, model={"x": 0})]
    aggregate = aggregate_backend_results(rows)
    assert aggregate.representative is rows[2]
    assert aggregate.is_equivalent is False
    assert aggregate.counterexample == {"x": 0}
    assert aggregate_backend_results([]).representative is None


def test_a_backend_aggregate_that_decided_nothing_is_not_filled_in_later():
    conflict = ParallelResult.from_backend_results([
        SolverResult("a", UNSAT), SolverResult("b", SAT, model={"x": 1}),
    ])
    assert conflict.first_definitive is None
    assert conflict.is_equivalent is None
    assert conflict.get_counterexample() is None
    assert conflict.backend_conflict == SAT_UNSAT_CONFLICT


# ---------------------------------------------------------------------------
# producer が合成した結果（複数の region / query の証拠）には backend の規則を適用しない
# ---------------------------------------------------------------------------


def _monolithic_style_aggregate():
    """`proof/strategies/monolithic_regions.py` の集約と同じ作り方（閉じた region の UNSAT と、
    別 region の replay の SAT を 1 つの結果にまとめ、判定は producer が明示する）。"""

    terminal_results = [
        SolverResult("Z3", UNSAT),                               # region 1 の guard
        SolverResult("Z3", UNSAT),                               # region 2 の value
        SolverResult("Z3", SAT, model={"param_1_1": 7}),         # region 3 の replay
    ]
    return ParallelResult(results=list(terminal_results), is_equivalent=False)


def test_a_composite_result_with_sat_and_unsat_regions_is_not_a_backend_conflict():
    aggregate = _monolithic_style_aggregate()
    assert aggregate.backend_aggregate is None
    assert aggregate.backend_conflict is None
    assert aggregate.is_equivalent is False
    assert aggregate.get_counterexample() == {"param_1_1": 7}


def test_the_mips64_phase4b_gate_still_sees_the_counterexample_of_a_composite_not_eq():
    from scripts.function_tracer_pcode.checker.phases.handler import PhaseHandler

    handler = PhaseHandler.__new__(PhaseHandler)
    handler.arch_detector = SimpleNamespace(is_mips64=lambda _program: True)
    previous = SimpleNamespace(is_equivalent=False, solver_results=_monolithic_style_aggregate())
    ctx = SimpleNamespace(program1=object(), program2=object(), analysis1=object(), analysis2=object())
    assert handler.should_run_phase4_retry(previous, ctx) is True


def test_the_monolithic_region_aggregate_is_built_as_a_composite():
    """monolithic の region 集約は producer が判定を明示する合成の結果（factory を使わない）。"""

    source = (PACKAGE_ROOT / "proof" / "strategies" / "monolithic_regions.py").read_text(encoding="utf-8")
    tree = ast.parse(source)
    factory_calls = [
        node for node in ast.walk(tree)
        if isinstance(node, ast.Attribute) and node.attr == "from_backend_results"
    ]
    assert factory_calls == []
    assert "aggregate = ParallelResult(\n            results=list(terminal_results),\n            is_equivalent=final," in source


# ---------------------------------------------------------------------------
# 1 query の実行は必ず backend 集約の factory を通る
# ---------------------------------------------------------------------------


def _direct_parallel_result_calls(tree, scope_name):
    calls = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.ClassDef)) and node.name == scope_name:
            for inner in ast.walk(node):
                if (
                    isinstance(inner, ast.Call)
                    and isinstance(inner.func, ast.Name)
                    and inner.func.id == "ParallelResult"
                ):
                    calls.append(inner.lineno)
    return calls


def test_single_query_executors_build_their_result_only_through_the_backend_factory():
    runner_tree = ast.parse((PACKAGE_ROOT / "smt" / "parallel.py").read_text(encoding="utf-8"))
    assert _direct_parallel_result_calls(runner_tree, "ParallelSolverRunner") == []
    session_tree = ast.parse(
        (PACKAGE_ROOT / "proof" / "monolithic_authority.py").read_text(encoding="utf-8")
    )
    assert _direct_parallel_result_calls(session_tree, "SharedZ3RegionSession") == []


def test_the_runner_result_carries_its_backend_aggregate():
    result = _run_in_completion_order([("only", UNSAT, True, None)], (0,))
    assert result.backend_aggregate is not None
    assert ParallelSolverRunner(timeout=1, solver_classes=[]).run_parallel(QUERY).backend_aggregate is not None
