# -*- coding: utf-8 -*-
"""Issue #106 PR-106-A（レビュー 2 巡目）: 観測された終了原因と、返却直後の確認の契約。

状態表（PR 本文の「契約」表と同じもの）を test の case にする。期待値は表の literal で書き、
実装の条件式を test 側で組み立て直さない。

* 実行 1 回の終わり方は `core.deadline.ExecutionEnd`（ANSWERED / INCONCLUSIVE / TIME_LIMIT /
  CANCELLED / FAILED / CONTRACT_VIOLATION / NOT_STARTED）で、「期限が上限を短くした」
  （``limited``）とは別の軸（指摘 1: 上限を短くしただけで期限の限界にしていた）
* 逐次の問いは 開始前 → 実行 → **返却直後の確認** → 次の実行。期限で切られた実行の後の
  backend は呼ばない（指摘 2: 確認が全 backend の後にあった）
* backend の失敗・契約違反は期限で隠さない（台帳の「内部バグ > 限界」と同じ向き）

時間は `DeadlinePolicy.clock`（`time.monotonic` + 定数の `ShiftedClock`）と、同じ時計を進める
test の backend で制御する。実 z3 の case（parse error・時間の上限での停止）だけは本物の時計。
"""

from __future__ import annotations

import concurrent.futures
import threading
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.core.deadline import (
    NOT_STARTED_FACT,
    DeadlinePolicy,
    ExecutionEnd,
    ExecutionFact,
    Settlement,
    TimeUnit,
    checkpoint,
    deadline_query,
    deadline_scope,
    settlement,
)
from scripts.function_tracer_pcode.core.errors import (
    DeadlineExceeded,
    PairStopState,
    pair_failure_scope,
    reset_pair_failure_scopes,
)
from scripts.function_tracer_pcode.smt.aggregation import CONTRACT_VIOLATION
from scripts.function_tracer_pcode.smt.execution import BUDGET_EXHAUSTED, CANCELLED
from scripts.function_tracer_pcode.smt.interface import (
    BackendTermination,
    SMTSolver,
    SolverBackendCapabilities,
    SolverResult,
    SolverStatus,
    enforce_witness_contract,
    execution_end,
    interrupted_result,
    not_started_result,
)
from scripts.function_tracer_pcode.smt.parallel import ParallelSolverRunner
from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver, isolated_check_end
from scripts.function_tracer_pcode.smt.witness import INCONCLUSIVE
from scripts.function_tracer_pcode.tests.unit.test_issue106a_deadline import ShiftedClock


QUERY = "(declare-const x (_ BitVec 8))\n(assert (bvugt x #x00))\n(check-sat)"
#: z3 が parse できない script（未宣言の関数）
BAD_QUERY = "(declare-const x Int)\n(assert (undefined_fn x))\n(check-sat)"
#: 32 bit の素数 2 つの積の分解（実 z3 は 3 s でも timeout で返る。時間の上限で止まる実行の実物）
HARD_QUERY = (
    "(declare-const a (_ BitVec 32))\n(declare-const b (_ BitVec 32))\n"
    f"(assert (= (bvmul ((_ zero_extend 32) a) ((_ zero_extend 32) b)) #x{2654435761 * 3266489917:016x}))\n"
    "(assert (bvugt a #x00000001))\n(assert (bvugt b #x00000001))\n(check-sat)"
)
MS = SolverBackendCapabilities(
    native_timeout=True, timeout_unit=TimeUnit.MILLISECONDS, absolute_deadline=True,
)
SECONDS = SolverBackendCapabilities(
    native_timeout=True, timeout_unit=TimeUnit.SECONDS, absolute_deadline=True,
)


@pytest.fixture(autouse=True)
def _clean_ledgers():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


def _policy(budget, clock=None, margin=0.5):
    kwargs = {} if clock is None else {"clock": clock}
    return DeadlinePolicy(budget_seconds=budget, sub_operation_margin_seconds=margin, **kwargs)


def _backend(name, calls, produce, *, capabilities=MS, canonical=False):
    """``produce(timeout_seconds, not_after) -> SolverResult`` を返す adapter（呼ばれた回数を数える）。"""

    class _Backend(SMTSolver):
        CAPABILITIES = capabilities
        PROVIDES_CANONICAL_WITNESS = canonical

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
            return produce(timeout_seconds, not_after)

    _Backend.__name__ = f"_Backend_{name}"
    return _Backend


def _counted_z3(calls, name="Z3Counted"):
    class _Counted(Z3Solver):
        def check_equivalence_direct(self, smt_script, cancellation_token=None, **kwargs):
            calls.append(name)
            return super().check_equivalence_direct(smt_script, cancellation_token, **kwargs)

    return _Counted


# ---------------------------------------------------------------------------
# 契約 1: 終了原因の語彙と写像（backend の結果 → 共通の実行の事実）
# ---------------------------------------------------------------------------

# 行 → 終了原因（status だけで決まらないものは作る側が明示する）
_ROW_TABLE = [
    (SolverResult("s", SolverStatus.SAT), ExecutionEnd.ANSWERED),
    (SolverResult("s", SolverStatus.UNSAT), ExecutionEnd.ANSWERED),
    (SolverResult("s", SolverStatus.UNKNOWN, error_message="incomplete quantifiers"), ExecutionEnd.INCONCLUSIVE),
    (SolverResult("s", SolverStatus.TIMEOUT), ExecutionEnd.TIME_LIMIT),
    (SolverResult("s", SolverStatus.UNKNOWN, cause=ExecutionEnd.TIME_LIMIT), ExecutionEnd.TIME_LIMIT),
    (SolverResult("s", SolverStatus.ERROR, error_message="Parse error"), ExecutionEnd.FAILED),
    (interrupted_result("s", CANCELLED, "token", 0.0), ExecutionEnd.CANCELLED),
    (interrupted_result("s", BUDGET_EXHAUSTED, "budget", 0.0), ExecutionEnd.TIME_LIMIT),
    (interrupted_result("s", INCONCLUSIVE, "witness", 0.0), ExecutionEnd.INCONCLUSIVE),
    (not_started_result("s"), ExecutionEnd.NOT_STARTED),
    (enforce_witness_contract(
        SolverResult("s", SolverStatus.SAT, model=None), QUERY, canonical=True,
    ), ExecutionEnd.CONTRACT_VIOLATION),
]


@pytest.mark.parametrize("row,end", _ROW_TABLE)
def test_each_solver_row_maps_to_its_observed_end(row, end):
    assert execution_end(row) is end


def test_the_row_table_covers_every_execution_end():
    assert {end for _row, end in _ROW_TABLE} == set(ExecutionEnd)


def test_the_mapping_does_not_read_error_messages():
    """中止も通常の unknown も status は UNKNOWN。区別は型（`cause`）で、文字列ではない。"""
    looks_cancelled = SolverResult("s", SolverStatus.UNKNOWN, error_message="cancelled: the token")
    assert execution_end(looks_cancelled) is ExecutionEnd.INCONCLUSIVE
    looks_timed_out = SolverResult("s", SolverStatus.UNKNOWN, error_message="timeout")
    assert execution_end(looks_timed_out) is ExecutionEnd.INCONCLUSIVE


@pytest.mark.parametrize("status,cause", [
    (SolverStatus.UNSAT, ExecutionEnd.TIME_LIMIT),
    (SolverStatus.TIMEOUT, ExecutionEnd.ANSWERED),
    (SolverStatus.ERROR, ExecutionEnd.CANCELLED),
    (SolverStatus.UNKNOWN, ExecutionEnd.FAILED),
])
def test_a_cause_that_contradicts_the_status_cannot_be_constructed(status, cause):
    with pytest.raises(ValueError):
        SolverResult("s", status, cause=cause)
    with pytest.raises(TypeError):
        SolverResult("s", SolverStatus.UNKNOWN, cause="cancelled")


# ---------------------------------------------------------------------------
# 契約 2: 返ってきた結果をどうするか（`settlement` の表）
# ---------------------------------------------------------------------------

A = ExecutionFact(ExecutionEnd.ANSWERED, False)
A_L = ExecutionFact(ExecutionEnd.ANSWERED, True)
INC_L = ExecutionFact(ExecutionEnd.INCONCLUSIVE, True)
T = ExecutionFact(ExecutionEnd.TIME_LIMIT, False)
T_L = ExecutionFact(ExecutionEnd.TIME_LIMIT, True)
C_L = ExecutionFact(ExecutionEnd.CANCELLED, True)
F_L = ExecutionFact(ExecutionEnd.FAILED, True)
V_L = ExecutionFact(ExecutionEnd.CONTRACT_VIOLATION, True)
NS = NOT_STARTED_FACT

_SETTLEMENT_TABLE = [
    # (facts, 期限前の結論, 期限後の結論)
    ((A,), Settlement.ACCEPT, Settlement.DEADLINE),
    ((A_L,), Settlement.ACCEPT, Settlement.DEADLINE),          # 上限を短くされても答えは答え
    ((INC_L,), Settlement.ACCEPT, Settlement.DEADLINE),        # 上限の前に返った通常の unknown
    ((T,), Settlement.ACCEPT, Settlement.DEADLINE),            # 通常の solver timeout
    ((T_L,), Settlement.DEADLINE, Settlement.DEADLINE),        # 期限が決めた上限で止まった
    ((C_L,), Settlement.ACCEPT, Settlement.DEADLINE),          # 明示の中止
    ((F_L,), Settlement.ACCEPT, Settlement.KEEP_FAILURE),      # parse error など: 隠さない
    ((V_L,), Settlement.ACCEPT, Settlement.KEEP_FAILURE),      # 契約違反: 隠さない
    ((NS,), Settlement.DEADLINE, Settlement.DEADLINE),
    ((F_L, T_L), Settlement.KEEP_FAILURE, Settlement.KEEP_FAILURE),  # 失敗が限界より先
    ((V_L, A), Settlement.ACCEPT, Settlement.KEEP_FAILURE),    # 違反があれば答えは集約で採られない
    ((F_L, A), Settlement.ACCEPT, Settlement.DEADLINE),        # 答えが採られてしまうので期限で止める
    ((F_L, NS), Settlement.KEEP_FAILURE, Settlement.KEEP_FAILURE),
    ((A, T), Settlement.ACCEPT, Settlement.DEADLINE),
    ((A, T_L), Settlement.DEADLINE, Settlement.DEADLINE),
]


@pytest.mark.parametrize("facts,before,after", _SETTLEMENT_TABLE)
def test_the_settlement_table(facts, before, after):
    assert settlement(facts, expired=False) is before
    assert settlement(facts, expired=True) is after


def test_the_settlement_table_covers_every_single_execution_end():
    singles = {facts[0].end for facts, _b, _a in _SETTLEMENT_TABLE if len(facts) == 1}
    assert singles == set(ExecutionEnd)


# ---------------------------------------------------------------------------
# 契約 3: 実 z3 と各経路で、期限を「確認できた停止」だけに使う
# ---------------------------------------------------------------------------


def _rows(result):
    return [(row.solver_name, row.status, row.error_message) for row in result.results]


def test_a_real_z3_parse_error_stays_an_error_with_a_deadline():
    """指摘 1（退行）: 期限が上限を短くしていても parse error は ERROR（期限の限界にしない）。"""
    runner = ParallelSolverRunner(timeout=10, solver_classes=[Z3Solver])
    without = runner.run_sequential(BAD_QUERY)
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(5.0)) as deadline:
            within = runner.run_sequential(BAD_QUERY)
            assert within.results[0].deadline_limited is True  # 上限は期限で短くなっていた
    assert _rows(within) == _rows(without)
    assert within.results[0].status is SolverStatus.ERROR
    assert not deadline.tripped
    assert ledger.pending_failure() is None


def test_a_real_z3_parse_error_past_the_deadline_is_kept_and_later_backends_do_not_run():
    """期限を過ぎて返った失敗は結果に残す（限界は記録だけ）。後の backend は始めない。"""
    clock = ShiftedClock()
    calls = []

    class _SlowBadZ3(Z3Solver):
        def check_equivalence_direct(self, smt_script, cancellation_token=None, **kwargs):
            calls.append("slow-bad")
            clock.jump(6.0)
            return super().check_equivalence_direct(smt_script, cancellation_token, **kwargs)

    runner = ParallelSolverRunner(timeout=10, solver_classes=[_SlowBadZ3, _counted_z3(calls)])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(5.0, clock)) as deadline:
            result = runner.run_sequential(BAD_QUERY)
            assert deadline.tripped  # 限界は記録済み
            with pytest.raises(DeadlineExceeded):
                checkpoint("next_stage")  # 次の境界が raise する
    assert calls == ["slow-bad"]  # 後の backend は 0 回
    assert [row.status for row in result.results] == [SolverStatus.ERROR, SolverStatus.TIMEOUT]
    assert "Parse error" in result.results[0].error_message
    assert result.results[1].termination is BackendTermination.NOT_STARTED
    assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_DEADLINE


def test_a_witness_contract_violation_stays_an_error_with_a_deadline():
    calls = []

    class _NoWitnessZ3(Z3Solver):
        def check_equivalence_direct(self, smt_script, cancellation_token=None, **kwargs):
            calls.append("no-witness")
            return SolverResult(self.name, SolverStatus.SAT, model=None)

    runner = ParallelSolverRunner(timeout=10, solver_classes=[_NoWitnessZ3])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(5.0)) as deadline:
            result = runner.run_sequential(QUERY)
    assert result.results[0].status is SolverStatus.ERROR
    assert result.results[0].witness_contract_violation is not None
    assert result.backend_conflict == CONTRACT_VIOLATION
    assert not deadline.tripped and ledger.pending_failure() is None


@pytest.mark.parametrize("row", [
    SolverResult("b", SolverStatus.UNKNOWN, error_message="incomplete quantifiers"),
    interrupted_result("b", CANCELLED, "the caller cancelled", 0.0),
])
def test_an_unknown_or_a_cancellation_under_a_shortened_limit_is_not_a_deadline(row):
    calls = []
    runner = ParallelSolverRunner(timeout=10, solver_classes=[
        _backend("b", calls, lambda _t, _n: row),
    ])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(5.0)) as deadline:
            result = runner.run_sequential(QUERY)
    assert result.results[0].deadline_limited is True
    assert result.results[0].status is SolverStatus.UNKNOWN
    assert execution_end(result.results[0]) is execution_end(row)
    assert not deadline.tripped and ledger.pending_failure() is None


def test_a_real_z3_stopped_at_the_deadline_limit_is_a_deadline():
    """実際に期限の上限で止まった実行（実 z3 の timeout）だけが期限の限界。"""
    calls = []
    runner = ParallelSolverRunner(timeout=10, solver_classes=[_counted_z3(calls, "first"), _counted_z3(calls, "second")])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(1.0, margin=0.5)):
            with pytest.raises(DeadlineExceeded) as raised:
                runner.run_sequential(HARD_QUERY)
    assert calls == ["first"]
    assert "cut_by_deadline" in raised.value.evidence_refs
    assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_DEADLINE


def test_a_real_z3_normal_timeout_is_not_a_deadline():
    """期限が上限を決めなかった timeout（設定値 1 s、期限 60 s）は通常の solver timeout。"""
    runner = ParallelSolverRunner(timeout=1, solver_classes=[Z3Solver])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(60.0)) as deadline:
            result = runner.run_sequential(HARD_QUERY)
    assert result.results[0].status is SolverStatus.TIMEOUT
    assert result.results[0].deadline_limited is False
    assert not deadline.tripped and ledger.pending_failure() is None


# ---------------------------------------------------------------------------
# 指摘 2: 逐次の返却直後の確認は次の backend を始める前
# ---------------------------------------------------------------------------


def test_a_seconds_backend_cut_by_the_deadline_stops_the_sequence_before_the_next_backend():
    """解析予算 1.9 s・余裕 0.5 s・設定 10 s。秒の backend は 1 s に切られて TIMEOUT → 後の z3 は 0 回。"""
    clock = ShiftedClock()
    calls = []

    class _Seconds(SMTSolver):
        CAPABILITIES = SECONDS

        @property
        def name(self):
            return "seconds"

        def check_availability(self):
            return True, "test"

        def check_equivalence_direct(self, smt_script, cancellation_token=None):
            calls.append(("seconds", self.timeout))
            clock.jump(self.timeout)  # 渡された秒の timeout まで走って止まる
            return SolverResult("seconds", SolverStatus.TIMEOUT)

    runner = ParallelSolverRunner(timeout=10, solver_classes=[_Seconds, _counted_z3(calls)])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(1.9, clock, margin=0.5)) as deadline:
            with pytest.raises(DeadlineExceeded) as raised:
                runner.run_sequential(QUERY)
            elapsed = clock() - deadline.started
    assert calls == [("seconds", 1)]  # 後の z3 は呼ばれていない
    assert elapsed < 1.9  # 期限の前に、返った直後に止まった
    assert "boundary=after" in raised.value.evidence_refs
    assert "cut_by_deadline" in raised.value.evidence_refs
    assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_DEADLINE


def test_a_failure_before_the_deadline_lets_the_next_backend_run():
    calls = []
    runner = ParallelSolverRunner(timeout=10, solver_classes=[
        _backend("broken", calls, lambda _t, _n: SolverResult("broken", SolverStatus.ERROR, error_message="boom")),
        _backend("fine", calls, lambda _t, _n: SolverResult("fine", SolverStatus.UNSAT)),
    ])
    with deadline_scope(_policy(5.0)) as deadline:
        result = runner.run_sequential(QUERY)
    assert calls == ["broken", "fine"]
    assert result.is_equivalent is True  # 集約の規則は期限なしと同じ（ERROR 行は判定を止めない）
    assert not deadline.tripped


def test_an_answer_after_the_deadline_is_not_adopted_even_beside_a_failure():
    clock = ShiftedClock()
    calls = []

    def _late_unsat(_t, _n):
        clock.jump(6.0)
        return SolverResult("late", SolverStatus.UNSAT)

    runner = ParallelSolverRunner(timeout=10, solver_classes=[
        _backend("broken", calls, lambda _t, _n: SolverResult("broken", SolverStatus.ERROR, error_message="boom")),
        _backend("late", calls, _late_unsat),
    ])
    with pair_failure_scope(("pair",), None):
        with deadline_scope(_policy(5.0, clock)):
            with pytest.raises(DeadlineExceeded) as raised:
                runner.run_sequential(QUERY)
    assert calls == ["broken", "late"]
    assert "boundary=after" in raised.value.evidence_refs


# ---------------------------------------------------------------------------
# 並列: 停止 → 回収 → 確認 → 集約。失敗は期限で隠さない
# ---------------------------------------------------------------------------


def test_parallel_failure_beside_a_cut_worker_is_kept_and_the_deadline_is_recorded():
    clock = ShiftedClock()
    gate = threading.Barrier(2, timeout=10)
    calls = []

    def _broken(_t, _n):
        gate.wait()
        return SolverResult("broken", SolverStatus.ERROR, error_message="boom")

    def _cut(_t, not_after):
        gate.wait()
        return SolverResult("cut", SolverStatus.TIMEOUT)  # 自分の窓（期限が決めた）で止まった

    runner = ParallelSolverRunner(timeout=30, solver_classes=[
        _backend("broken", calls, _broken), _backend("cut", calls, _cut),
    ])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(3.0, clock)) as deadline:
            result = runner.run_parallel(QUERY)
            assert deadline.tripped
    assert [row.status for row in result.results] == [SolverStatus.ERROR, SolverStatus.TIMEOUT]
    assert result.results[1].deadline_limited is True
    assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_DEADLINE


def test_parallel_normal_unknown_under_a_shortened_limit_is_not_a_deadline():
    calls = []
    runner = ParallelSolverRunner(timeout=30, solver_classes=[
        _backend("u", calls, lambda _t, _n: SolverResult("u", SolverStatus.UNKNOWN, error_message="incomplete")),
    ])
    with deadline_scope(_policy(3.0)) as deadline:
        result = runner.run_parallel(QUERY)
    assert result.results[0].deadline_limited is True
    assert result.results[0].status is SolverStatus.UNKNOWN
    assert not deadline.tripped


# ---------------------------------------------------------------------------
# decompile / 条件 oracle の写像
# ---------------------------------------------------------------------------


def _decompile_results(**flags):
    names = ("decompileCompleted", "isTimedOut", "isCancelled", "failedToStart")
    return SimpleNamespace(
        getHighFunction=lambda: None,
        **{name: (lambda value=flags.get(name, False): value) for name in names},
    )


@pytest.mark.parametrize("flags,end", [
    ({"decompileCompleted": True}, ExecutionEnd.ANSWERED),
    ({"isTimedOut": True}, ExecutionEnd.TIME_LIMIT),
    ({"isCancelled": True}, ExecutionEnd.CANCELLED),
    ({"failedToStart": True}, ExecutionEnd.FAILED),
    ({}, ExecutionEnd.FAILED),  # 異常終了
])
def test_decompile_results_map_to_their_observed_end(flags, end):
    from scripts.function_tracer_pcode.ghidra.decompilation_broker import decompile_execution_end

    assert decompile_execution_end(_decompile_results(**flags)) is end


def test_an_authority_blocked_decompile_is_a_failure_not_a_deadline():
    from scripts.function_tracer_pcode.ghidra.decompilation_broker import (
        _AuthorityBlockedDecompileResults,
        decompile_execution_end,
    )

    assert decompile_execution_end(_AuthorityBlockedDecompileResults(diagnostic=None)) is ExecutionEnd.FAILED


def _decompiler_returning(results, recorded):
    class _Decompiler:
        def decompileFunction(self, function, timeout, monitor):
            recorded.append(timeout)
            return results

    return SimpleNamespace(_get_decompiler=lambda: _Decompiler())


@pytest.mark.parametrize("flags,trips", [
    ({"failedToStart": True}, False),
    ({}, False),
    ({"isCancelled": True}, False),
    ({"isTimedOut": True}, True),
])
def test_decompile_under_a_shortened_limit_trips_only_when_it_timed_out(flags, trips):
    from scripts.function_tracer_pcode.ghidra.decompilation_broker import (
        TOP_LEVEL_SOURCE_CONTRACT,
        decompile_within_deadline,
    )

    recorded = []
    analyzer = _decompiler_returning(_decompile_results(**flags), recorded)
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(6.0)) as deadline:
            call = lambda: decompile_within_deadline(  # noqa: E731
                analyzer, object(), 60, None,
                source_contract_id=TOP_LEVEL_SOURCE_CONTRACT, semantic_owner="slice6",
            )
            if trips:
                with pytest.raises(DeadlineExceeded):
                    call()
            else:
                call()
    assert recorded and recorded[0] < 60  # 上限は期限で短くなっていた
    assert deadline.tripped is trips
    assert (ledger.pending_failure() is not None) is trips


class _FakeZ3:
    sat = "sat"
    unsat = "unsat"
    unknown = "unknown"


@pytest.mark.parametrize("verdict,reason,end", [
    ("sat", "", ExecutionEnd.ANSWERED),
    ("unsat", "", ExecutionEnd.ANSWERED),
    ("unknown", "timeout", ExecutionEnd.TIME_LIMIT),
    ("unknown", "canceled", ExecutionEnd.TIME_LIMIT),
    ("unknown", "(incomplete quantifiers)", ExecutionEnd.INCONCLUSIVE),
    ("unknown", "smt tactic failed to show goal to be sat/unsat", ExecutionEnd.INCONCLUSIVE),
])
def test_the_condition_oracle_check_maps_to_its_observed_end(verdict, reason, end):
    solver = SimpleNamespace(reason_unknown=lambda: reason)
    assert isolated_check_end(_FakeZ3, verdict, solver) is end


def test_the_condition_oracle_keeps_a_normal_unknown_under_a_shortened_limit(monkeypatch):
    """oracle の 250 ms が期限で短くなっていても、上限の前の unknown は通常の unknown（覚えもする）。"""
    from scripts.function_tracer_pcode.analysis.condition import smt_oracle

    class _Solver:
        def check(self):
            return "unknown"

        def reason_unknown(self):
            return "incomplete quantifiers"

    monkeypatch.setattr(smt_oracle, "isolated_solver", lambda z3, script, timeout_ms: _Solver())
    query = deadline_query("condition_oracle")
    assert query.begin(0.25, TimeUnit.MILLISECONDS)  # 期限の無い handle（owner の scope 外）
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(0.6, margin=0.5)) as deadline:
            q = deadline_query("condition_oracle")
            window = q.bound.window(0.25, TimeUnit.MILLISECONDS)
            assert window.limited is True
            q.begin(0.25, TimeUnit.MILLISECONDS)
            end = isolated_check_end(_FakeZ3, "unknown", _Solver())
            assert q.settle([ExecutionFact(end, window.limited)]) is Settlement.ACCEPT
    assert not deadline.tripped and ledger.pending_failure() is None


# ---------------------------------------------------------------------------
# 並列の worker の開始遅延（同期で制御）
# ---------------------------------------------------------------------------


def test_a_worker_whose_start_is_delayed_is_cut_by_its_own_window_only_if_it_hits_the_limit():
    clock = ShiftedClock()
    started = threading.Event()
    proceed = threading.Event()
    seen = []

    def _delayed(_t, not_after):
        seen.append(not_after)
        return SolverResult("delayed", SolverStatus.UNKNOWN, error_message="incomplete")

    runner = ParallelSolverRunner(timeout=30, solver_classes=[_backend("delayed", [], _delayed)])
    original_submit = concurrent.futures.ThreadPoolExecutor.submit

    def _slow_submit(self, fn, *args, **kwargs):
        def _wrapped():
            started.set()
            assert proceed.wait(10)
            return fn(*args, **kwargs)
        return original_submit(self, _wrapped)

    with deadline_scope(_policy(3.0, clock)) as deadline:
        concurrent.futures.ThreadPoolExecutor.submit = _slow_submit
        try:
            threading.Timer(0.0, lambda: (started.wait(10), clock.jump(1.0), proceed.set())).start()
            result = runner.run_parallel(QUERY)
        finally:
            concurrent.futures.ThreadPoolExecutor.submit = original_submit
    assert seen == [pytest.approx(deadline.absolute - 0.5)]  # 遅れて始まった worker の窓も期限が決めた
    assert result.results[0].status is SolverStatus.UNKNOWN  # 上限の前に返った unknown は通常の結果
    assert not deadline.tripped


# ---------------------------------------------------------------------------
# 共有 region session（monolithic）: 同じ写像と同じ規則
# ---------------------------------------------------------------------------


def _session(formula):
    from scripts.function_tracer_pcode.tests.unit.test_issue161_canonical_witness import _shared_session

    return _shared_session([formula])


def test_the_shared_session_answer_under_a_shortened_limit_is_accepted():
    session = _session(QUERY)
    with deadline_scope(_policy(5.0)) as deadline:
        result = session.execute(QUERY, 10)
    item = result.results[0]
    assert item.status is SolverStatus.SAT and item.deadline_limited is True
    assert not deadline.tripped


def test_the_shared_session_stopped_at_the_deadline_limit_is_a_deadline():
    session = _session(HARD_QUERY)
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(1.0, margin=0.5)):
            with pytest.raises(DeadlineExceeded) as raised:
                session.execute(HARD_QUERY, 10)
    assert "cut_by_deadline" in raised.value.evidence_refs
    assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_DEADLINE


def test_the_shared_session_normal_timeout_is_not_a_deadline():
    """incremental の z3 は timeout を "canceled" と報告する。status は期限なしと同じ UNKNOWN の
    まま、観測された終了原因は TIME_LIMIT（期限が上限を決めていないので通常の timeout）。"""
    session = _session(HARD_QUERY)
    without = _session(HARD_QUERY).execute(HARD_QUERY, 1).results[0]
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(60.0)) as deadline:
            result = session.execute(HARD_QUERY, 1)
    item = result.results[0]
    assert (item.status, item.error_message) == (without.status, without.error_message)
    assert item.status is SolverStatus.UNKNOWN and "canceled" in item.error_message
    assert execution_end(item) is ExecutionEnd.TIME_LIMIT
    assert item.deadline_limited is False
    assert not deadline.tripped and ledger.pending_failure() is None


def test_a_witness_question_stopped_by_time_is_observed_as_a_time_limit():
    """witness の探索の問い（push した solver）が上限で止まると z3 は "canceled" を返す。"""
    from scripts.function_tracer_pcode.smt.execution import ExecutionBudget
    from scripts.function_tracer_pcode.smt.interface import witness_failure_result
    from scripts.function_tracer_pcode.smt.witness import WitnessUnavailable

    budget = ExecutionBudget.starting_now(10)
    assert budget.unknown_end("canceled") is ExecutionEnd.TIME_LIMIT
    assert budget.unknown_end("timeout") is ExecutionEnd.TIME_LIMIT
    assert budget.unknown_end("(incomplete quantifiers)") is ExecutionEnd.INCONCLUSIVE
    failure = WitnessUnavailable(INCONCLUSIVE, "canceled", end=budget.unknown_end("canceled"))
    row = witness_failure_result("z3", failure, 0.1)
    assert row.status is SolverStatus.UNKNOWN  # status は期限なしと同じ
    assert execution_end(row) is ExecutionEnd.TIME_LIMIT
    plain = witness_failure_result("z3", WitnessUnavailable(INCONCLUSIVE, "incomplete"), 0.1)
    assert execution_end(plain) is ExecutionEnd.INCONCLUSIVE


# ---------------------------------------------------------------------------
# 開始の確認は backend の単位で・単独 / 直接の問い合わせも同じ規則
# ---------------------------------------------------------------------------


def test_the_start_check_uses_the_backend_unit():
    """残り 0.9 s（期限 − 余裕）: 秒の backend は 0 秒になるので始めない（ms で確かめない）。"""
    clock = ShiftedClock()
    calls = []

    class _Seconds(SMTSolver):
        CAPABILITIES = SECONDS

        @property
        def name(self):
            return "seconds"

        def check_availability(self):
            return True, "test"

        def check_equivalence_direct(self, smt_script, cancellation_token=None):
            calls.append("seconds")
            return SolverResult("seconds", SolverStatus.UNSAT)

    runner = ParallelSolverRunner(timeout=10, solver_classes=[_Seconds])
    with pair_failure_scope(("pair",), None):
        with deadline_scope(_policy(1.4, clock, margin=0.5)):
            with pytest.raises(DeadlineExceeded) as raised:
                runner.run_sequential(QUERY)
    assert calls == []
    assert "boundary=before" in raised.value.evidence_refs
    assert "remaining_below_margin" in raised.value.evidence_refs


@pytest.mark.parametrize("entry", ["run_single", "run_backend_query"])
@pytest.mark.parametrize("row,trips", [
    (SolverResult("b", SolverStatus.ERROR, error_message="Parse error"), False),
    (SolverResult("b", SolverStatus.UNKNOWN, error_message="incomplete"), False),
    (SolverResult("b", SolverStatus.TIMEOUT), True),  # 期限が決めた上限で止まった
])
def test_single_and_direct_queries_follow_the_same_table(entry, row, trips):
    from scripts.function_tracer_pcode.smt.parallel import run_backend_query

    calls = []
    backend = _backend("b", calls, lambda _t, _n: row)(timeout=10)
    runner = ParallelSolverRunner(timeout=10, solver_classes=[])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(5.0)) as deadline:
            call = (
                (lambda: runner.run_single(backend, QUERY, timeout=10)) if entry == "run_single"
                else (lambda: run_backend_query(backend, QUERY))
            )
            if trips:
                with pytest.raises(DeadlineExceeded):
                    call()
            else:
                assert call().status is row.status
    assert deadline.tripped is trips
    assert (ledger.pending_failure() is not None) is trips


def test_a_kept_failure_records_the_deadline_with_its_evidence():
    clock = ShiftedClock()

    def _late_error(_t, _n):
        clock.jump(6.0)
        return SolverResult("late", SolverStatus.ERROR, error_message="boom")

    runner = ParallelSolverRunner(timeout=10, solver_classes=[_backend("late", [], _late_error)])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(5.0, clock)):
            result = runner.run_sequential(QUERY)
    assert result.results[0].status is SolverStatus.ERROR
    failure = ledger.pending_failure()
    assert failure is not None and failure.stop_state is PairStopState.PAIR_TERMINAL_DEADLINE
    assert "failure_kept" in failure.exception.evidence_refs
    assert "boundary=after" in failure.exception.evidence_refs
