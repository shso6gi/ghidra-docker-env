# -*- coding: utf-8 -*-
"""Issue #106 PR-106-A（レビュー 4 巡目）: 故障を残しても、打ち切った問いの答えは採用されない。

4 つの責務を分けて固定する:

1. 観測の保持: backend が返した行・故障は残る（ERROR・witness の契約違反の行はそのまま）
2. 後続の実行: 期限後・余裕以下なら始めない（呼び出し 0 回）
3. 答えの採否: 期限が問いを打ち切ったら（開始の拒否・返却後の確認・待ちの打ち切り）、
   残した行に SAT / UNSAT があっても、判定・反例を返さない。行から答えを外すので、集約の
   し直し・producer の合成・receipt（行の status から作る）でも採用し直せない
4. 最終の UNKNOWN / ERROR と receipt: 既存の authority（ここでは台帳の stop state と、次の
   境界の raise までを見る）

期待値は上の契約から決めた literal で、実装の条件式を写さない。時計は `ShiftedClock`
（`time.monotonic` + 定数）と、backend の中・次の開始の直前に進める hook で制御する。
"""

from __future__ import annotations

import threading

import pytest

from scripts.function_tracer_pcode.core import deadline as deadline_module
from scripts.function_tracer_pcode.core.deadline import (
    DeadlinePolicy,
    TimeUnit,
    checkpoint,
    deadline_scope,
)
from scripts.function_tracer_pcode.core.errors import (
    DeadlineExceeded,
    PairStopState,
    pair_failure_scope,
    reset_pair_failure_scopes,
)
from scripts.function_tracer_pcode.smt.aggregation import CONTRACT_VIOLATION, SAT_UNSAT_CONFLICT
from scripts.function_tracer_pcode.smt.execution import CANCELLED
from scripts.function_tracer_pcode.smt.interface import (
    BackendTermination,
    SMTSolver,
    SolverBackendCapabilities,
    SolverResult,
    SolverStatus,
    interrupted_result,
)
from scripts.function_tracer_pcode.smt.parallel import ParallelResult, ParallelSolverRunner
from scripts.function_tracer_pcode.tests.unit.test_issue106a_deadline import ShiftedClock


#: canonical witness の対象が x 1 つの script（witness {"x": 1} は契約どおりの形）
QUERY = "(declare-const x (_ BitVec 8))\n(assert (bvugt x #x00))\n(check-sat)"
MS = SolverBackendCapabilities(
    native_timeout=True, timeout_unit=TimeUnit.MILLISECONDS, absolute_deadline=True,
)
ANSWER = (SolverStatus.SAT, SolverStatus.UNSAT)


@pytest.fixture(autouse=True)
def _clean_ledgers():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


def _rows_of(kind, name):
    """行の種類 → その backend が返す行（契約の語彙で名付ける）。"""

    return {
        "error": lambda: SolverResult(name, SolverStatus.ERROR, error_message=f"{name} failed"),
        "unsat": lambda: SolverResult(name, SolverStatus.UNSAT, raw_output="unsat"),
        "sat": lambda: SolverResult(name, SolverStatus.SAT, model={"x": 1}, raw_output="sat (model x 1)"),
        "no_witness": lambda: SolverResult(name, SolverStatus.SAT, model=None),
        "cancelled": lambda: interrupted_result(name, CANCELLED, "the caller cancelled", 0.0),
        "timeout": lambda: SolverResult(name, SolverStatus.TIMEOUT),
    }[kind]


def _backend(name, kind, calls, *, clock=None, advance=0.0, barrier=None):
    produce = _rows_of(kind, name)

    class _Backend(SMTSolver):
        CAPABILITIES = MS
        PROVIDES_CANONICAL_WITNESS = True

        def __init__(self, timeout=10, debug=False):
            super().__init__(timeout)

        @property
        def name(self):
            return name

        def check_availability(self):
            return True, "test"

        def check_equivalence_direct(self, smt_script, cancellation_token=None):
            raise AssertionError("the adapter path must be used")

        def execute(self, smt_script, *, timeout_seconds, not_after=None, cancellation_token=None):
            calls.append(name)
            if barrier is not None:
                barrier.wait(10)
            if advance:
                clock.jump(advance)
            return produce()

    _Backend.__name__ = f"_Backend_{name}"
    return _Backend


def _jump_before_start(monkeypatch, clock, *, start_index, to_elapsed):
    """``start_index`` 番目（1 始まり）の開始の確認の直前に、時計を期限の起点から ``to_elapsed`` 秒へ。"""

    original = deadline_module.Deadline.begin_execution
    seen = [0]

    def _begin(self, query, configured_seconds, unit):
        seen[0] += 1
        if seen[0] == start_index:
            clock.jump(self.started + to_elapsed - clock())
        return original(self, query, configured_seconds, unit)

    monkeypatch.setattr(deadline_module.Deadline, "begin_execution", _begin)


def _assert_withheld(result, *, failures):
    """期限が打ち切った問いの結果の契約（責務 1 と 3）。"""

    # 3: 判定・反例を返さない。行に答えは残らないので、集約し直しても合成し直しても採用されない
    assert result.is_equivalent is None
    assert result.first_definitive is None
    assert result.get_counterexample() is None
    assert all(row.status not in ANSWER for row in result.results)
    # 外した答えの行は反例を持たない（query receipt は行の model を写すので、残すと反例が漏れる）
    assert all(row.model is None for row in result.results if row.withheld_status is not None)
    # raw_output（答えの中身。query receipt へ写る）も残さない（レビュー 5 巡目）
    assert all(row.raw_output is None for row in result.results if row.withheld_status is not None)
    assert ParallelResult.from_backend_results(list(result.results)).is_equivalent is None
    assert ParallelResult(results=list(result.results)).is_equivalent is None
    # 1: 故障の行はそのまま残る
    by_name = {row.solver_name: row for row in result.results}
    for name, message in failures.items():
        assert by_name[name].status is SolverStatus.ERROR
        assert message in by_name[name].error_message


def _assert_deadline_recorded(ledger, *, next_raised):
    pending = ledger.pending_failure()
    assert pending is not None and pending.stop_state is PairStopState.PAIR_TERMINAL_DEADLINE
    assert "failure_kept" in pending.exception.evidence_refs
    assert next_raised is True


def _sequential(monkeypatch, kinds, *, start_at=None, budget=5.0):
    """逐次の 3 backend。``start_at`` = (何番目の開始の直前に, 起点からの秒) へ時計を進める。"""

    clock = ShiftedClock()
    calls = []
    runner = ParallelSolverRunner(timeout=10, solver_classes=[
        _backend(f"b{index}", kind, calls) for index, kind in enumerate(kinds, 1)
    ])
    if start_at is not None:
        _jump_before_start(monkeypatch, clock, start_index=start_at[0], to_elapsed=start_at[1])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(DeadlinePolicy(
            budget_seconds=budget, sub_operation_margin_seconds=0.5, clock=clock,
        )) as deadline:
            try:
                outcome = runner.run_sequential(QUERY)
            except DeadlineExceeded as raised:
                outcome = raised
            try:
                checkpoint("next_stage")
                next_raised = False
            except DeadlineExceeded:
                next_raised = True
    return outcome, calls, ledger, deadline, next_raised


# ---------------------------------------------------------------------------
# 逐次: 故障 → 答え → 開始の拒否（レビュー 4 巡目の再現と、その組み替え）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("refused_at", [5.1, 4.7], ids=["past_the_deadline", "below_the_margin"])
@pytest.mark.parametrize("kinds,failures", [
    (("error", "unsat", "unsat"), {"b1": "b1 failed"}),   # 再現（ERROR, UNSAT, 開始の拒否）
    (("error", "sat", "unsat"), {"b1": "b1 failed"}),     # SAT（canonical witness つき）
    (("unsat", "error", "unsat"), {"b2": "b2 failed"}),   # 順序の入れ替え
])
def test_a_refused_start_after_a_failure_withholds_the_answer(monkeypatch, kinds, failures, refused_at):
    outcome, calls, ledger, deadline, next_raised = _sequential(
        monkeypatch, kinds, start_at=(3, refused_at),
    )
    assert not isinstance(outcome, DeadlineExceeded), outcome
    assert calls == ["b1", "b2"]  # 2: b3 は呼ばれない
    _assert_withheld(outcome, failures=failures)
    answer_row = next(row for row in outcome.results if row.withheld_status is not None)
    assert answer_row.withheld_status is {"unsat": SolverStatus.UNSAT, "sat": SolverStatus.SAT}[
        next(kind for kind in kinds[:2] if kind in ("unsat", "sat"))
    ]
    assert outcome.results[2].termination is BackendTermination.NOT_STARTED
    assert deadline.tripped
    _assert_deadline_recorded(ledger, next_raised=next_raised)


def test_a_contract_violation_stays_visible_while_the_answer_is_withheld(monkeypatch):
    outcome, calls, ledger, _deadline, next_raised = _sequential(
        monkeypatch, ("no_witness", "unsat", "unsat"), start_at=(3, 5.1),
    )
    assert calls == ["b1", "b2"]
    assert outcome.is_equivalent is None and outcome.get_counterexample() is None
    violation = outcome.results[0]
    assert violation.status is SolverStatus.ERROR and violation.witness_contract_violation is not None
    assert outcome.backend_conflict == CONTRACT_VIOLATION
    assert outcome.results[1].withheld_status is SolverStatus.UNSAT
    _assert_deadline_recorded(ledger, next_raised=next_raised)


def test_a_cancellation_without_a_failure_still_stops_the_query_with_the_deadline(monkeypatch):
    """中止の UNKNOWN は故障ではない: 開始の拒否は従来どおり限界を raise する（答えは返らない）。"""
    outcome, calls, ledger, _deadline, _next = _sequential(
        monkeypatch, ("cancelled", "unsat", "unsat"), start_at=(3, 5.1),
    )
    assert isinstance(outcome, DeadlineExceeded)
    assert "boundary=before" in outcome.evidence_refs
    assert calls == ["b1", "b2"]
    assert ledger.pending_failure().stop_state is PairStopState.PAIR_TERMINAL_DEADLINE


@pytest.mark.parametrize("deadline", [False, True], ids=["no_deadline", "deadline_not_reached"])
def test_the_existing_aggregation_of_an_error_and_an_unsat_is_kept(monkeypatch, deadline):
    """期限が問いを打ち切らなければ、ERROR + UNSAT は従来どおり等価（集約の規則）。"""
    calls = []
    runner = ParallelSolverRunner(timeout=10, solver_classes=[
        _backend("b1", "error", calls), _backend("b2", "unsat", calls), _backend("b3", "unsat", calls),
    ])
    if deadline:
        with deadline_scope(DeadlinePolicy(budget_seconds=60.0)) as scope:
            result = runner.run_sequential(QUERY)
        assert not scope.tripped
    else:
        result = runner.run_sequential(QUERY)
    assert calls == ["b1", "b2", "b3"]
    assert result.is_equivalent is True
    assert [row.withheld_status for row in result.results] == [None, None, None]


# ---------------------------------------------------------------------------
# 並列: 返却後の確認・待ちの打ち切りも同じ採否
# ---------------------------------------------------------------------------


def _parallel(kinds, *, advance=None):
    clock = ShiftedClock()
    calls = []
    barrier = threading.Barrier(len(kinds))
    advance = advance or {}
    runner = ParallelSolverRunner(timeout=10, solver_classes=[
        _backend(f"b{index}", kind, calls, clock=clock, advance=advance.get(index, 0.0), barrier=barrier)
        for index, kind in enumerate(kinds, 1)
    ])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(DeadlinePolicy(
            budget_seconds=5.0, sub_operation_margin_seconds=0.5, clock=clock,
        )) as deadline:
            try:
                outcome = runner.run_parallel(QUERY)
            except DeadlineExceeded as raised:
                outcome = raised
            try:
                checkpoint("next_stage")
                next_raised = False
            except DeadlineExceeded:
                next_raised = True
    return outcome, sorted(calls), ledger, deadline, next_raised


def test_parallel_a_cut_worker_beside_a_failure_withholds_the_other_answer():
    """b3 は期限で短くした窓で止まった（TIMEOUT・limited）。b1 の故障を残し、b2 の UNSAT は採用しない。"""
    outcome, calls, ledger, deadline, next_raised = _parallel(("error", "unsat", "timeout"))
    assert calls == ["b1", "b2", "b3"]
    _assert_withheld(outcome, failures={"b1": "b1 failed"})
    assert {row.solver_name: row.withheld_status for row in outcome.results}["b2"] is SolverStatus.UNSAT
    assert deadline.tripped
    _assert_deadline_recorded(ledger, next_raised=next_raised)


def test_parallel_answers_returned_after_the_deadline_beside_a_failure_are_withheld():
    """SAT と UNSAT（食い違い）と故障。b2 が返る間に期限を過ぎた。判定も反例も返さない。"""
    outcome, calls, ledger, _deadline, next_raised = _parallel(
        ("error", "sat", "unsat"), advance={2: 5.2},
    )
    _assert_withheld(outcome, failures={"b1": "b1 failed"})
    assert sorted(row.withheld_status.name for row in outcome.results if row.withheld_status) == ["SAT", "UNSAT"]
    _assert_deadline_recorded(ledger, next_raised=next_raised)


def test_parallel_a_sat_unsat_conflict_in_time_is_still_detected():
    outcome, _calls, _ledger, deadline, next_raised = _parallel(("sat", "unsat"))
    assert not deadline.tripped and next_raised is False
    assert outcome.is_equivalent is None
    assert outcome.backend_conflict == SAT_UNSAT_CONFLICT


def test_parallel_a_cut_worker_without_a_failure_raises_the_deadline():
    outcome, _calls, ledger, _deadline, _next = _parallel(("unsat", "timeout"))
    assert isinstance(outcome, DeadlineExceeded)
    assert "cut_by_deadline" in outcome.evidence_refs
    assert ledger.pending_failure().stop_state is PairStopState.PAIR_TERMINAL_DEADLINE


# ---------------------------------------------------------------------------
# 単独 / 直接の問い合わせ: 1 実行の結果も同じ採否を通る
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("entry", ["run_single", "run_backend_query"])
def test_a_single_failure_past_the_deadline_is_kept_and_not_an_answer(entry):
    from scripts.function_tracer_pcode.smt.parallel import run_backend_query

    clock = ShiftedClock()
    backend = _backend("b1", "error", [], clock=clock, advance=5.2)(timeout=10)
    runner = ParallelSolverRunner(timeout=10, solver_classes=[])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(DeadlinePolicy(
            budget_seconds=5.0, sub_operation_margin_seconds=0.5, clock=clock,
        )):
            row = runner.run_single(backend, QUERY, timeout=10) if entry == "run_single" else run_backend_query(backend, QUERY)
            with pytest.raises(DeadlineExceeded):
                checkpoint("next_stage")
    assert row.status is SolverStatus.ERROR and row.error_message == "b1 failed"
    assert ledger.pending_failure().stop_state is PairStopState.PAIR_TERMINAL_DEADLINE


# ---------------------------------------------------------------------------
# 構造: 行を返す入口はすべて採否（`apply_adoption`）を通る
# ---------------------------------------------------------------------------


def _function(tree, name, owner=None):
    import ast

    scopes = [tree]
    if owner is not None:
        scopes = [node for node in ast.walk(tree) if isinstance(node, ast.ClassDef) and node.name == owner]
    for scope in scopes:
        for node in ast.walk(scope):
            if isinstance(node, ast.FunctionDef) and node.name == name:
                return node
    raise AssertionError(f"{owner}.{name} not found")


def test_every_row_returning_entry_applies_the_adoption():
    """runner の逐次 / 並列 / 単独 / 直接の問い合わせと共有 session は、集約へ渡す行・返す行を
    `apply_adoption` に通す（新しい入口を足したらここに足す。backend 名の分岐は要らない）。"""
    import ast
    import pathlib

    root = pathlib.Path(__file__).resolve().parents[2]
    parallel = ast.parse((root / "smt" / "parallel.py").read_text(encoding="utf-8"))
    monolithic = ast.parse((root / "proof" / "monolithic_authority.py").read_text(encoding="utf-8"))
    entries = [
        _function(parallel, "run_single", "ParallelSolverRunner"),
        _function(parallel, "run_parallel", "ParallelSolverRunner"),
        _function(parallel, "run_sequential", "ParallelSolverRunner"),
        _function(parallel, "run_backend_query"),
        _function(monolithic, "execute", "SharedZ3RegionSession"),
    ]
    for entry in entries:
        calls = [node for node in ast.walk(entry) if isinstance(node, ast.Call)]
        names = {getattr(call.func, "id", getattr(call.func, "attr", None)) for call in calls}
        assert "apply_adoption" in names, entry.name
        for call in calls:
            if getattr(call.func, "attr", None) == "from_backend_results":
                [argument] = call.args
                if isinstance(argument, ast.List) and not argument.elts:
                    continue  # backend が 1 つも無い（問いを開く前）
                assert isinstance(argument, ast.Call) and getattr(argument.func, "id", None) == "apply_adoption", entry.name


def test_parallel_an_answer_collected_after_the_stop_beside_a_failure_is_withheld():
    """停止の後の回収: 待つのを期限でやめた（1.0 s）後に grace の中で返った UNSAT は、外した答えの
    行になる（何を返したかは残し、model と raw_output は残さない）。同じ問いの故障はそのまま。"""
    import time

    released = threading.Event()

    def _late(name):
        class _Late(SMTSolver):
            CAPABILITIES = MS

            @property
            def name(self):
                return name

            def check_availability(self):
                return True, "test"

            def check_equivalence_direct(self, smt_script, cancellation_token=None):
                raise AssertionError("the adapter path must be used")

            def execute(self, smt_script, *, timeout_seconds, not_after=None, cancellation_token=None):
                time.sleep(1.3)  # 待ちの終わり（期限 1.0 s）の後、grace（1.0 s）の中で返る
                released.set()
                return SolverResult(name, SolverStatus.UNSAT, raw_output="unsat")

        return _Late

    runner = ParallelSolverRunner(timeout=10, solver_classes=[_backend("b1", "error", []), _late("b2")])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(DeadlinePolicy(budget_seconds=1.0, sub_operation_margin_seconds=0.5)):
            result = runner.run_parallel(QUERY)
            with pytest.raises(DeadlineExceeded):
                checkpoint("next_stage")
    assert released.is_set()
    _assert_withheld(result, failures={"b1": "b1 failed"})
    late = {row.solver_name: row for row in result.results}["b2"]
    assert late.termination is BackendTermination.RETURNED_LATE
    assert late.withheld_status is SolverStatus.UNSAT
    assert late.model is None and late.raw_output is None
    _assert_deadline_recorded(ledger, next_raised=True)
