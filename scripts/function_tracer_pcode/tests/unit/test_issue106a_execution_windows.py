# -*- coding: utf-8 -*-
"""Issue #106 PR-106-A（レビュー 1 巡目）: 論理的な問いと backend の実行の境界。

* 期限の開始確認は **実行を 1 回始める前ごと**（逐次の backend ごと）。先の backend が期限を越えて
  返ったら、後の backend は始めない（指摘 1）
* 「解析の期限が時間を決めたか」は実行を始める瞬間に実行ごとに求める。先の backend が時間を使えば
  後の backend の窓は期限で決まり、その timeout は期限の限界になる（指摘 2）
* 期限が時間を決めなかった timeout は通常の solver timeout のまま（誤変換しない）
* 能力の宣言と停止操作は 1 つの契約（`running_stop` と `request_stop`）。宣言して実装しない
  backend は定義できない（指摘 4）。M-2: 追加した backend が契約どおり実行・停止・集約される
* 受理判定は ground truth で確かめられない判定を accepted にしない（指摘 3）

時間は `DeadlinePolicy.clock`（`time.monotonic` + 定数）と、同じ時計を読む test の backend で進める
（偶然の sleep に依らない）。
"""

from __future__ import annotations

import concurrent.futures
import threading
import time

import pytest

from scripts.function_tracer_pcode.core.deadline import (
    DeadlinePolicy,
    ExecutionBound,
    TimeUnit,
    deadline_scope,
    deadline_query,
)
from scripts.function_tracer_pcode.core.errors import (
    DeadlineExceeded,
    PairStopState,
    pair_failure_scope,
    reset_pair_failure_scopes,
)
from scripts.function_tracer_pcode.reporting.deadline_acceptance import (
    CLASS_A,
    CLASS_B,
    TRUTH_CONSISTENT,
    TRUTH_CONTRADICTED,
    TRUTH_NOT_APPLICABLE,
    TRUTH_UNCONFIRMED,
    VERDICT_ACCEPTED,
    VERDICT_FALLBACK_SAFE,
    VERDICT_NOT_ACCEPTED,
    VERDICT_UNCONFIRMED,
    VERDICT_UNSAFE,
    TargetObservation,
    classify_target,
    summarize,
)
from scripts.function_tracer_pcode.smt import parallel as parallel_module
from scripts.function_tracer_pcode.smt.interface import (
    BackendTermination,
    SMTSolver,
    SolverBackendCapabilities,
    SolverResult,
    SolverStatus,
    StopMethod,
)
from scripts.function_tracer_pcode.smt.parallel import (
    CancellationToken,
    ParallelSolverRunner,
    run_backend_query,
    stop_unfinished,
)
from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver
from scripts.function_tracer_pcode.tests.unit.test_issue106a_deadline import ShiftedClock


QUERY = "(declare-const x (_ BitVec 8))\n(assert (bvugt x #x00))\n(check-sat)"
MS = SolverBackendCapabilities(
    native_timeout=True, timeout_unit=TimeUnit.MILLISECONDS, absolute_deadline=True,
)


@pytest.fixture(autouse=True)
def _clean_ledgers():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


class _Log:
    def __init__(self):
        self.calls = []


def _scripted(name, log, script, *, capabilities=MS, canonical=False):
    """``script(clock, timeout_seconds, not_after) -> (status, model)`` を返す backend。"""

    class _Scripted(SMTSolver):
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
            log.calls.append({"name": name, "timeout": timeout_seconds, "not_after": not_after})
            status, model = script(timeout_seconds, not_after)
            return SolverResult(name, status, model=model)

    _Scripted.__name__ = f"_Scripted_{name}"
    return _Scripted


def _policy(budget, clock, margin):
    return DeadlinePolicy(budget_seconds=budget, clock=clock, sub_operation_margin_seconds=margin)


# ---------------------------------------------------------------------------
# 指摘 1: 先の backend が期限を越えて返ったら、後の backend を始めない
# ---------------------------------------------------------------------------


def test_review1_a_later_backend_does_not_start_after_an_earlier_one_crossed_the_deadline():
    clock = ShiftedClock()
    log = _Log()

    def _slow_unsat(_timeout, _not_after):
        clock.jump(0.5)  # 期限（0.3 s）を越えて返る
        return SolverStatus.UNSAT, None

    runner = ParallelSolverRunner(timeout=5, solver_classes=[
        _scripted("first", log, _slow_unsat),
        _scripted("second", log, lambda *_: (SolverStatus.UNSAT, None)),
    ])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(0.3, clock, 0.05)):
            with pytest.raises(DeadlineExceeded) as raised:
                runner.run_sequential(QUERY)
    assert [call["name"] for call in log.calls] == ["first"]  # second は始まっていない
    assert "boundary=before" in raised.value.evidence_refs
    assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_DEADLINE


# ---------------------------------------------------------------------------
# 指摘 2: 後の backend の窓は、その実行を始める瞬間に期限で決まる
# ---------------------------------------------------------------------------


def test_review1_the_later_backend_window_is_decided_when_it_starts():
    """解析予算 400 ms・余裕 50 ms・backend 予算 250 ms。先が 200 ms で UNSAT、後が残り 150 ms で TIMEOUT。"""
    clock = ShiftedClock()
    log = _Log()

    def _unsat_after_200ms(_timeout, _not_after):
        clock.jump(0.2)
        return SolverStatus.UNSAT, None

    def _timeout_at_its_end(_timeout, not_after):
        clock.jump(not_after - clock())  # 自分の窓の終わりまで走って timeout
        return SolverStatus.TIMEOUT, None

    runner = ParallelSolverRunner(timeout=0.25, solver_classes=[
        _scripted("first", log, _unsat_after_200ms),
        _scripted("second", log, _timeout_at_its_end),
    ])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(0.4, clock, 0.05)) as deadline:
            not_after = deadline.absolute - 0.05
            with pytest.raises(DeadlineExceeded) as raised:
                runner.run_sequential(QUERY, timeout=0.25)
    first, second = log.calls
    assert first["not_after"] is None  # 先は設定値の 250 ms で終わる窓（期限は決めていない）
    assert second["not_after"] == pytest.approx(not_after)  # 後は期限が終わりを決めた
    assert "cut_by_deadline" in raised.value.evidence_refs
    assert deadline.tripped
    assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_DEADLINE


def test_review1_a_worker_started_late_gets_its_own_window():
    """並列の worker の起動が遅れても、窓はその worker が始める瞬間に決まる。"""
    clock = ShiftedClock()
    log = _Log()
    backend = _scripted("late", log, lambda *_: (SolverStatus.TIMEOUT, None))()
    bound = ExecutionBound(not_after=clock() + 1.0, clock=clock)
    early = parallel_module._execute_within(backend, QUERY, 0.8, bound, None)
    clock.jump(0.5)  # 起動の遅れ
    late = parallel_module._execute_within(backend, QUERY, 0.8, bound, None)
    assert early.deadline_limited is False
    assert late.deadline_limited is True
    assert log.calls[0]["not_after"] is None
    assert log.calls[1]["not_after"] == pytest.approx(bound.not_after)


def test_review1_an_execution_the_deadline_does_not_shape_gets_exactly_the_configured_timeout():
    """期限があっても、期限が時間を決めない実行には設定値をそのまま渡す（開始時刻から丸め直さない）。

    丸め直すと秒の API に 60 → 59 が渡り、期限なしの実行と値が変わる（記録済み replay が検出した）。
    """
    from scripts.function_tracer_pcode.core.deadline import execution_window
    from scripts.function_tracer_pcode.ghidra.decompilation_broker import (
        TOP_LEVEL_SOURCE_CONTRACT,
        decompile_within_deadline,
    )
    from scripts.function_tracer_pcode.tests.unit.test_issue106a_solver_adapter import (
        _fake_decompile_analyzer,
    )

    window = execution_window(60, 1000.0, TimeUnit.SECONDS, now=100.0)
    assert window.limited is False and window.adapter_end is None
    for later in (100.0, 100.3, 100.999):
        assert window.timeout(60, TimeUnit.SECONDS, now=later) == 60
        assert window.timeout(0.25, TimeUnit.MILLISECONDS, now=later) == 250
    recorded = []
    with deadline_scope(_policy(1.0e6, ShiftedClock(), 0.5)):
        decompile_within_deadline(
            _fake_decompile_analyzer(recorded), object(), 60, None,
            source_contract_id=TOP_LEVEL_SOURCE_CONTRACT, semantic_owner="slice6",
        )
    assert recorded == [60]


@pytest.mark.parametrize("mode", ["run_sequential", "run_parallel"])
def test_review1_a_normal_solver_timeout_is_not_a_deadline_limitation(mode):
    """期限が時間を決めなかった timeout は通常の solver timeout（限界にしない・集約はそのまま）。"""
    clock = ShiftedClock()
    log = _Log()
    runner = ParallelSolverRunner(timeout=0.25, solver_classes=[
        _scripted("unsat", log, lambda *_: (SolverStatus.UNSAT, None)),
        _scripted("timeout", log, lambda *_: (SolverStatus.TIMEOUT, None)),
    ])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(60.0, clock, 0.5)) as deadline:
            result = getattr(runner, mode)(QUERY, timeout=0.25)
    assert not deadline.tripped
    assert ledger.pending_failure() is None
    assert [row.deadline_limited for row in result.results] == [False, False]
    # 集約の規則は変わらない（UNSAT と TIMEOUT の行: #161 の aggregation が決める）
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult

    assert result.is_equivalent == ParallelResult.from_backend_results(result.results).is_equivalent


@pytest.mark.parametrize("mode", ["run_sequential", "run_parallel"])
def test_review1_without_a_deadline_every_backend_runs_with_the_configured_timeout(mode):
    log = _Log()
    runner = ParallelSolverRunner(timeout=7, solver_classes=[
        _scripted("a", log, lambda *_: (SolverStatus.UNSAT, None)),
        _scripted("b", log, lambda *_: (SolverStatus.UNSAT, None)),
    ])
    result = getattr(runner, mode)(QUERY)
    assert sorted(call["name"] for call in log.calls) == ["a", "b"]
    assert [call["not_after"] for call in log.calls] == [None, None]
    assert [call["timeout"] for call in log.calls] == [7, 7]
    assert result.is_equivalent is True


def test_review1_the_direct_query_uses_the_same_window_rule():
    clock = ShiftedClock()
    log = _Log()

    def _timeout_at_its_end(_timeout, not_after):
        clock.jump(not_after - clock())
        return SolverStatus.TIMEOUT, None

    with deadline_scope(_policy(1.0, clock, 0.1)):
        backend = _scripted("direct", log, _timeout_at_its_end)(timeout=5)
        with pytest.raises(DeadlineExceeded) as raised:
            run_backend_query(backend, QUERY)
    assert "cut_by_deadline" in raised.value.evidence_refs


# ---------------------------------------------------------------------------
# 指摘 4: 能力の宣言と停止操作は 1 つの契約。M-2: 追加 backend の実行・停止・集約
# ---------------------------------------------------------------------------


def test_review1_a_claimed_stop_method_without_request_stop_cannot_be_defined():
    for method in (StopMethod.INTERRUPT, StopMethod.HARD_STOP):
        with pytest.raises(TypeError, match="request_stop"):
            type("_Claims", (SMTSolver,), {
                "CAPABILITIES": SolverBackendCapabilities(running_stop=method),
                "name": property(lambda self: "x"),
                "check_availability": lambda self: (True, ""),
                "check_equivalence_direct": lambda self, s, t=None: None,
            })


def test_review1_other_inconsistent_claims_cannot_be_defined():
    base = {
        "name": property(lambda self: "x"),
        "check_availability": lambda self: (True, ""),
        "check_equivalence_direct": lambda self, s, t=None: None,
    }
    for capabilities in (
        SolverBackendCapabilities(absolute_deadline=True),  # native timeout 無し
        SolverBackendCapabilities(native_timeout=True),  # 単位無し
        # 既定の実行（整数秒）のままミリ秒を主張
        SolverBackendCapabilities(native_timeout=True, timeout_unit=TimeUnit.MILLISECONDS),
    ):
        with pytest.raises(TypeError):
            type("_Claims", (SMTSolver,), {"CAPABILITIES": capabilities, **base})


def _stoppable(name, method, log, released):
    """``method`` で止まる backend（止めるまで返らない）。止められたら UNKNOWN。"""

    class _Stoppable(SMTSolver):
        CAPABILITIES = SolverBackendCapabilities(
            native_timeout=True, timeout_unit=TimeUnit.MILLISECONDS, absolute_deadline=True,
            running_stop=method,
        )

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
            log.calls.append({"name": name, "not_after": not_after})
            assert released.wait(20), "never stopped"
            return SolverResult(name, SolverStatus.UNKNOWN, error_message="stopped")

        def request_stop(self):
            log.calls.append({"name": name, "stop": method.value})
            released.set()
            return True

    return _Stoppable


def test_review1_a_hard_stop_backend_is_stopped_through_its_contract():
    log = _Log()
    released = threading.Event()
    backend = _stoppable("killer", StopMethod.HARD_STOP, log, released)()
    token = CancellationToken()
    executor = concurrent.futures.ThreadPoolExecutor(max_workers=1)
    try:
        future = executor.submit(backend.execute, QUERY, timeout_seconds=5)
        while not log.calls:
            time.sleep(0.001)
        stopped = stop_unfinished([(backend, future)], {future}, token, grace_seconds=5)
    finally:
        executor.shutdown(wait=True)
    assert stopped[future] is BackendTermination.STOPPED
    assert {"name": "killer", "stop": "hard_stop"} in log.calls


def test_review1_a_backend_without_a_stop_method_that_returns_late_is_not_called_stopped():
    returned = threading.Event()

    class _Late(SMTSolver):
        @property
        def name(self):
            return "late"

        def check_availability(self):
            return True, ""

        def check_equivalence_direct(self, smt_script, cancellation_token=None):
            returned.wait(5)
            return SolverResult("late", SolverStatus.UNSAT)

    backend = _Late()
    executor = concurrent.futures.ThreadPoolExecutor(max_workers=1)
    try:
        future = executor.submit(backend.check_equivalence_direct, QUERY)
        threading.Timer(0.05, returned.set).start()
        stopped = stop_unfinished([(backend, future)], {future}, CancellationToken(), grace_seconds=5)
    finally:
        executor.shutdown(wait=True)
    assert stopped[future] is BackendTermination.RETURNED_LATE


def test_review1_m2_an_added_backend_runs_stops_and_aggregates_through_the_contract(monkeypatch):
    """M-2: registry に足した backend（止め方つき）が、z3 と並んで窓・停止・集約の契約どおりに動く。"""
    clock = ShiftedClock()
    log = _Log()
    released = threading.Event()
    added = _stoppable("added", StopMethod.HARD_STOP, log, released)
    monkeypatch.setattr(ParallelSolverRunner, "DEFAULT_SOLVERS", [Z3Solver, added])
    runner = ParallelSolverRunner(timeout=30)
    assert runner.get_available_solvers() == ["Z3", "added"]
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(1.0, clock, 0.2)) as deadline:
            with pytest.raises(DeadlineExceeded) as raised:
                runner.run_parallel(QUERY)
    # 実行: 追加 backend は自分の窓の終わり（期限 − 余裕）を引数で受けた
    [execute_call] = [call for call in log.calls if "not_after" in call]
    assert execute_call["not_after"] == pytest.approx(deadline.absolute - 0.2)
    # 停止: 待つのを期限でやめ、止め方の契約（request_stop）で止めた
    assert {"name": "added", "stop": "hard_stop"} in log.calls
    assert "backend=added:stopped" in raised.value.evidence_refs
    assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_DEADLINE


def test_review1_m2_an_added_backend_is_aggregated_by_the_existing_rules(monkeypatch):
    """集約: 追加 backend の SAT と z3 の UNSAT は食い違い（判定しない）、非 canonical の model は捨てる。"""
    log = _Log()
    added = _scripted("added", log, lambda *_: (SolverStatus.SAT, {"x": 7}))
    monkeypatch.setattr(ParallelSolverRunner, "DEFAULT_SOLVERS", [Z3Solver, added])
    runner = ParallelSolverRunner(timeout=5)
    unsat_query = "(declare-const x (_ BitVec 8))\n(assert (= x #x01))\n(assert (= x #x02))\n(check-sat)"
    result = runner.run_sequential(unsat_query)
    by_name = {row.solver_name: row for row in result.results}
    assert by_name["Z3"].status is SolverStatus.UNSAT
    assert by_name["added"].status is SolverStatus.SAT and by_name["added"].model is None
    assert result.is_equivalent is None and result.backend_conflict is not None


def test_review1_mixed_class_a_and_b_backends_in_one_query():
    """Class A（止め方つき）と Class B（主張なし）を 1 つの並列の問いに並べる。"""
    clock = ShiftedClock()
    log = _Log()
    released_a = threading.Event()
    released_b = threading.Event()

    class _ClassB(SMTSolver):
        @property
        def name(self):
            return "class-b"

        def check_availability(self):
            return True, ""

        def check_equivalence_direct(self, smt_script, cancellation_token=None):
            log.calls.append({"name": "class-b", "timeout": self.timeout})
            assert released_b.wait(20)
            return SolverResult("class-b", SolverStatus.UNSAT)

    notes = []

    def _note(note, payload=None):
        notes.append(note)
        threading.Timer(0.05, released_b.set).start()

    runner = ParallelSolverRunner(timeout=30, solver_classes=[
        _stoppable("class-a", StopMethod.INTERRUPT, log, released_a), _ClassB,
    ])
    original = parallel_module.journal_note
    parallel_module.journal_note = _note
    try:
        with pair_failure_scope(("pair",), None):
            with deadline_scope(_policy(3.0, clock, 0.2)):
                with pytest.raises(DeadlineExceeded) as raised:
                    runner.run_parallel(QUERY)
    finally:
        parallel_module.journal_note = original
    evidence = raised.value.evidence_refs
    assert "backend=class-a:stopped" in evidence
    assert "backend=class-b:not_stoppable" in evidence and "worker_stop=not_stoppable" in evidence
    assert notes == ["solver_worker_not_stoppable"]
    assert released_b.is_set()  # 止められない worker が自分で返るまで待った


# ---------------------------------------------------------------------------
# 指摘 3: ground truth で確かめられない判定を accepted にしない
# ---------------------------------------------------------------------------


def _decided(guarantee_class, truth, outcome="EQUIVALENT"):
    return TargetObservation(
        key="k", guarantee_class=guarantee_class, before_outcome="TIMEOUT",
        after_outcome=outcome, after_truth=truth,
    )


@pytest.mark.parametrize(("guarantee_class", "truth", "verdict", "improvement", "violation"), [
    (CLASS_A, TRUTH_CONSISTENT, VERDICT_ACCEPTED, True, False),
    (CLASS_A, TRUTH_CONTRADICTED, VERDICT_NOT_ACCEPTED, False, True),
    (CLASS_A, TRUTH_UNCONFIRMED, VERDICT_UNCONFIRMED, False, False),
    (CLASS_A, None, VERDICT_UNCONFIRMED, False, False),
    (CLASS_A, TRUTH_NOT_APPLICABLE, VERDICT_UNCONFIRMED, False, False),
    (CLASS_B, TRUTH_CONSISTENT, VERDICT_FALLBACK_SAFE, False, False),
    (CLASS_B, TRUTH_CONTRADICTED, VERDICT_UNSAFE, False, True),
    (CLASS_B, TRUTH_UNCONFIRMED, VERDICT_UNCONFIRMED, False, False),
    (CLASS_B, None, VERDICT_UNCONFIRMED, False, False),
])
@pytest.mark.parametrize("outcome", ["EQUIVALENT", "NOT_EQ"])
def test_review1_decisions_need_a_confirming_ground_truth(guarantee_class, truth, verdict, improvement, violation, outcome):
    row = classify_target(_decided(guarantee_class, truth, outcome))
    assert (row.verdict, row.improvement, row.soundness_violation) == (verdict, improvement, violation)


def test_review1_an_unconfirmed_decision_blocks_completion():
    unconfirmed = classify_target(_decided(CLASS_A, TRUTH_UNCONFIRMED))
    confirmed = classify_target(_decided(CLASS_A, TRUTH_CONSISTENT))
    assert summarize([confirmed]).complete is True
    assert summarize([confirmed, unconfirmed]).complete is False
    assert summarize([confirmed, unconfirmed]).unconfirmed == 1
    assert summarize([unconfirmed]).improvements == 0


def test_review1_an_unknown_ground_truth_value_is_refused():
    with pytest.raises(ValueError):
        classify_target(_decided(CLASS_A, "looks_fine"))
