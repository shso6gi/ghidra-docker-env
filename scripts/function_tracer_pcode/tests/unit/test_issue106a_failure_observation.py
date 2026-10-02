# -*- coding: utf-8 -*-
"""Issue #106 PR-106-A（レビュー 3 巡目）: 故障の事実が settle と結果まで届くこと。

実際の z3 adapter（`Z3Solver`）→ runner（`run_parallel` / `run_sequential`）→ `core.deadline` の
settle を通し、**故障の起きた時点 × 停止の状態** を組み合わせる。期待値は表の literal で、
実装の判定式から作らない。

時点（解析の期限 2.0 s・余裕 0.5 s・設定 10 s → 実行の窓は 1.5 s、並列の待ちは 2.0 s、停止の
grace は 1.0 s）:

* ``before``   0.3 s: 窓の中（停止は求めない）
* ``limited``  1.7 s: 期限で短くした窓（1.5 s）の後・期限（2.0 s）の前（停止は求めない）
* ``stopping`` 2.4 s: 期限の後。runner は 2.0 s で待つのをやめて停止を求め、grace の中で返る
* ``stuck``    3.4 s: grace（3.0 s）も過ぎてから返る（止められない worker）

z3 の check は時点まで眠ってから結果を出す本物の solver の包み（`_Timed`）。`request_stop` の
`Context.interrupt` は Python の sleep を起こさないので、worker が返る時刻は表のとおりになる。
"""

from __future__ import annotations

import time

import pytest
import z3

from scripts.function_tracer_pcode.core.deadline import (
    DeadlinePolicy,
    ExecutionEnd,
    checkpoint,
    deadline_scope,
)
from scripts.function_tracer_pcode.core.errors import (
    DeadlineExceeded,
    PairStopState,
    pair_failure_scope,
    reset_pair_failure_scopes,
)
from scripts.function_tracer_pcode.smt.aggregation import CONTRACT_VIOLATION
from scripts.function_tracer_pcode.smt.interface import (
    BackendTermination,
    SolverResult,
    SolverStatus,
    execution_end,
)
from scripts.function_tracer_pcode.smt.parallel import WORKER_NOT_STOPPABLE_EVIDENCE, ParallelSolverRunner
from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver


UNSAT_QUERY = "(declare-const x (_ BitVec 8))\n(assert (= x #x01))\n(assert (= x #x02))\n(check-sat)"
SAT_QUERY = "(declare-const x (_ BitVec 8))\n(assert (bvugt x #x00))\n(check-sat)"
AT = {"before": 0.3, "limited": 1.7, "stopping": 2.4, "stuck": 3.4}


@pytest.fixture(autouse=True)
def _clean_ledgers():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


class _Timed:
    """本物の z3 の solver を包み、check を ``at`` まで待たせてから ``outcome`` を出す。"""

    def __init__(self, inner, at, outcome):
        self._inner = inner
        self._at = at
        self._outcome = outcome

    def check(self, *args):
        time.sleep(max(0.0, self._at - time.monotonic()))
        if self._outcome == "error":
            raise RuntimeError("independent backend failure")
        if self._outcome == "interrupted":
            raise z3.Z3Exception("canceled")  # z3 の中断の合図（実測: interrupt された API）
        return self._inner.check(*args)

    def __getattr__(self, name):
        return getattr(self._inner, name)


def _first_check_at(monkeypatch, offset, outcome):
    """最初に作られる z3 の solver（adapter の初回の check）だけを時点つきにする。"""

    real = z3.Solver
    made = []
    at = time.monotonic() + offset

    def _factory(*args, **kwargs):
        solver = real(*args, **kwargs)
        if made:
            return solver
        made.append(True)
        return _Timed(solver, at, outcome)

    monkeypatch.setattr(z3, "Solver", _factory)


class _NoWitnessAt(Z3Solver):
    """canonical witness の無い SAT を時点で返す（witness の契約違反。境界は runner の run_single）。"""

    AT = 0.0

    def check_equivalence_direct(self, smt_script, cancellation_token=None, **kwargs):
        time.sleep(max(0.0, self.AT - time.monotonic()))
        return SolverResult(self.name, SolverStatus.SAT, model=None)


def _policy():
    return DeadlinePolicy(budget_seconds=2.0, sub_operation_margin_seconds=0.5)


def _run_parallel(runner, query):
    """(結果 or 例外, 期限, 台帳の pending, 次の境界が raise したか)。"""

    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy()) as deadline:
            try:
                outcome = runner.run_parallel(query)
            except DeadlineExceeded as raised:
                outcome = raised
            try:
                checkpoint("next_stage")
                next_raised = False
            except DeadlineExceeded:
                next_raised = True
        return outcome, deadline, ledger.pending_failure(), next_raised


# (失敗の種類, 時点) → 期待（literal）
#   row: 行の status / 終了原因 / runner の終わり方。"raise" は settle が限界を raise する
#   kept: 故障を結果に残し、限界は記録だけ（次の境界で raise）
_MATRIX = [
    # 独立した故障（Python の例外）
    ("error", "before", dict(status="ERROR", end="failed", termination="completed", outcome="result", tripped=False)),
    ("error", "limited", dict(status="ERROR", end="failed", termination="completed", outcome="result", tripped=False)),
    ("error", "stopping", dict(status="ERROR", end="failed", termination="stopped", outcome="kept", tripped=True)),
    ("error", "stuck", dict(status="ERROR", end="failed", termination="not_stoppable", outcome="kept", tripped=True)),
    # 想定内の中断（z3 の中断の合図）
    ("interrupted", "before", dict(status="ERROR", end="failed", termination="completed", outcome="result", tripped=False)),
    ("interrupted", "stopping", dict(status="TIMEOUT", end="time_limit", termination="stopped", outcome="raise", tripped=True)),
    # 答え（期限の後に返ったものは採らない）
    ("answer", "before", dict(status="UNSAT", end="answered", termination="completed", outcome="result", tripped=False)),
    ("answer", "stopping", dict(status="TIMEOUT", end="time_limit", termination="stopped", outcome="raise", tripped=True)),
]


@pytest.mark.parametrize("kind,when,expected", _MATRIX)
def test_the_observed_end_reaches_settle_through_adapter_and_runner(monkeypatch, kind, when, expected):
    _first_check_at(monkeypatch, AT[when], kind)
    runner = ParallelSolverRunner(timeout=10, solver_classes=[Z3Solver])
    outcome, deadline, pending, next_raised = _run_parallel(runner, UNSAT_QUERY)
    assert deadline.tripped is expected["tripped"]
    if expected["outcome"] == "raise":
        assert isinstance(outcome, DeadlineExceeded)
        assert "boundary=after" in outcome.evidence_refs
        assert pending is not None and pending.stop_state is PairStopState.PAIR_TERMINAL_DEADLINE
        return
    assert not isinstance(outcome, DeadlineExceeded), outcome
    [row] = outcome.results
    assert row.status.name == expected["status"]
    assert execution_end(row).value == expected["end"]
    assert row.termination.value == expected["termination"]
    if expected["status"] == "ERROR":
        assert "independent backend failure" in row.error_message or "canceled" in row.error_message
        assert outcome.is_equivalent is None  # 故障は答えにならない
    if expected["status"] == "UNSAT":
        assert outcome.is_equivalent is True
    if expected["outcome"] == "kept":
        # 故障は結果に残り、期限の限界は記録だけ（次の境界で raise）
        assert pending is not None and pending.stop_state is PairStopState.PAIR_TERMINAL_DEADLINE
        assert "failure_kept" in pending.exception.evidence_refs
        assert next_raised is True
        if when == "stuck":
            assert WORKER_NOT_STOPPABLE_EVIDENCE in pending.exception.evidence_refs
    else:
        assert pending is None and next_raised is False


@pytest.mark.parametrize("when,termination,kept", [
    ("limited", "completed", False),
    # 停止の手段が無い（実行中の context を持たない）ので求められず、grace の中で自分で返った
    ("stopping", "returned_late", True),
])
def test_a_witness_contract_violation_reaches_settle_and_the_aggregate(when, termination, kept):
    _NoWitnessAt.AT = time.monotonic() + AT[when]
    runner = ParallelSolverRunner(timeout=10, solver_classes=[_NoWitnessAt])
    outcome, deadline, pending, next_raised = _run_parallel(runner, SAT_QUERY)
    [row] = outcome.results
    assert row.status is SolverStatus.ERROR and row.witness_contract_violation is not None
    assert execution_end(row) is ExecutionEnd.CONTRACT_VIOLATION
    assert row.termination.value == termination
    assert outcome.backend_conflict == CONTRACT_VIOLATION
    assert deadline.tripped is kept and next_raised is kept
    assert (pending is not None) is kept


def test_a_failure_before_a_refused_start_is_kept_in_a_sequential_query(monkeypatch):
    """逐次: 先の backend の故障の後、残りが余裕以下で後の backend を始めないとき、故障を消さない。"""
    _first_check_at(monkeypatch, AT["limited"], "error")
    calls = []

    class _Second(Z3Solver):
        def check_equivalence_direct(self, smt_script, cancellation_token=None, **kwargs):
            calls.append("second")
            return super().check_equivalence_direct(smt_script, cancellation_token, **kwargs)

    runner = ParallelSolverRunner(timeout=10, solver_classes=[Z3Solver, _Second])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy()) as deadline:
            result = runner.run_sequential(UNSAT_QUERY)
            assert deadline.tripped
            with pytest.raises(DeadlineExceeded):
                checkpoint("next_stage")
    assert calls == []
    first, second = result.results
    assert first.status is SolverStatus.ERROR and "independent backend failure" in first.error_message
    assert second.termination is BackendTermination.NOT_STARTED
    pending = ledger.pending_failure()
    assert pending.stop_state is PairStopState.PAIR_TERMINAL_DEADLINE
    assert "failure_kept" in pending.exception.evidence_refs
    assert "remaining_below_margin" in pending.exception.evidence_refs


def test_the_same_independent_failure_is_an_error_with_and_without_the_deadline(monkeypatch):
    """レビュー 3 巡目の再現 2（縮尺 1/2.5）: 期限が上限を短くした後の独立した例外は、期限なしと同じ ERROR。"""
    _first_check_at(monkeypatch, AT["limited"], "error")
    without = Z3Solver(timeout=10).check_equivalence_direct(UNSAT_QUERY)
    _first_check_at(monkeypatch, AT["limited"], "error")
    runner = ParallelSolverRunner(timeout=10, solver_classes=[Z3Solver])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy()) as deadline:
            within = runner.run_sequential(UNSAT_QUERY).results[0]
    assert (within.status, within.error_message) == (without.status, without.error_message)
    assert within.status is SolverStatus.ERROR
    assert within.deadline_limited is True  # 上限は期限で短くなっていた
    assert not deadline.tripped and ledger.pending_failure() is None


def test_a_real_z3_check_stopped_by_request_stop_is_a_stop_not_an_inconclusive_unknown():
    """実 z3: 走っている check に `request_stop`（Context.interrupt）→ reason "interrupted" の unknown。
    token が中止されていなくても停止の結果（CANCELLED）で、判定不能の unknown にも故障にもしない。"""
    import threading

    from scripts.function_tracer_pcode.tests.unit.test_issue106a_execution_ends import HARD_QUERY

    backend = Z3Solver(timeout=30)
    rows = []
    worker = threading.Thread(
        target=lambda: rows.append(backend.execute(HARD_QUERY, timeout_seconds=30)), daemon=True,
    )
    worker.start()
    deadline = time.monotonic() + 10
    while backend._running_context is None and time.monotonic() < deadline:
        time.sleep(0.01)
    time.sleep(0.2)
    assert backend.request_stop() is True
    worker.join(10)
    [row] = rows
    assert row.status is SolverStatus.UNKNOWN
    assert execution_end(row) is ExecutionEnd.CANCELLED
    assert row.observed_failure is None
