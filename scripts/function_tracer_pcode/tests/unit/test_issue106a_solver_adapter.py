# -*- coding: utf-8 -*-
"""Issue #106 PR-106-A: solver backend adapter と解析の期限（E5 / E9 / E11 / E12 / M-2）。

* 期限は問い合わせの入口（owner の thread）で 1 回だけ許可に直し、worker へは absolute な
  終わり（``not_after``）を **引数で** 渡す（worker は contextvar の期限を読まない）
* 待つのをやめる・pending を取り消す・走っている実行を止める・process が終われる、を別々に
  扱う（`BackendTermination`）。止められない実行を「正常な UNKNOWN」にしない
* backend の違いは adapter の能力（`SolverBackendCapabilities`）だけで表し、runner /
  workflow / 台帳 / boundary / CLI は backend 名で分岐しない（M-2）
"""

from __future__ import annotations

import ast
import concurrent.futures
import pathlib
import threading
import time
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.core.deadline import (
    DeadlinePolicy,
    TimeUnit,
    active_deadline,
    deadline_scope,
    finalization,
)
from scripts.function_tracer_pcode.core.errors import (
    DeadlineExceeded,
    PairStopState,
    pair_failure_scope,
    reset_pair_failure_scopes,
)
from scripts.function_tracer_pcode.smt import parallel as parallel_module
from scripts.function_tracer_pcode.smt.interface import (
    NO_CAPABILITIES,
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


PACKAGE_ROOT = pathlib.Path(__file__).resolve().parents[2]
QUERY = "(declare-const x (_ BitVec 8))\n(assert (bvugt x #x00))\n(check-sat)"

#: z3 が timeout まで解き続ける問い（64 bit の因数分解）
HARD_QUERY = """
(declare-const x (_ BitVec 64))
(declare-const y (_ BitVec 64))
(assert (= (bvmul x y) #x0fffffff7fffffff))
(assert (bvugt x #x0000000000000001))
(assert (bvugt y #x0000000000000001))
(assert (bvult x #x0000010000000000))
(assert (bvult y #x0000010000000000))
(assert (not (= x #x000000007fffffff)))
(assert (not (= y #x000000007fffffff)))
(check-sat)
"""


@pytest.fixture(autouse=True)
def _clean_ledgers():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


def _policy(budget, clock=None, margin=0.2):
    return DeadlinePolicy(
        budget_seconds=budget, clock=clock or ShiftedClock(), sub_operation_margin_seconds=margin,
    )


# ---------------------------------------------------------------------------
# test 用の backend adapter（capability の組み合わせ）
# ---------------------------------------------------------------------------


class _Recorder:
    def __init__(self):
        self.calls = []
        self.release = threading.Event()
        self.returned = threading.Event()


def _cooperative_backend(recorder, *, honour_not_after=True, status_when_done=SolverStatus.TIMEOUT):
    """期限を自分で守り、中断の要求にも応じる backend（Class A）。"""

    class _Cooperative(SMTSolver):
        CAPABILITIES = SolverBackendCapabilities(
            native_timeout=True, timeout_unit=TimeUnit.MILLISECONDS,
            absolute_deadline=True, running_stop=StopMethod.INTERRUPT,
        )

        def __init__(self, timeout=10, debug=False):
            super().__init__(timeout)
            self._interrupted = threading.Event()

        @property
        def name(self):
            return "cooperative"

        def check_availability(self):
            return True, "test"

        def check_equivalence_direct(self, smt_script, cancellation_token=None):
            raise AssertionError("the adapter path must be used")

        def execute(self, smt_script, *, timeout_seconds, not_after=None, cancellation_token=None):
            recorder.calls.append({
                "not_after": not_after,
                "thread": threading.get_ident(),
                "sees_deadline": active_deadline() is not None,
            })
            end = time.monotonic() + timeout_seconds
            if honour_not_after and not_after is not None:
                end = min(end, not_after)
            interrupted = self._interrupted.wait(max(0.0, end - time.monotonic()))
            recorder.returned.set()
            if interrupted:
                return SolverResult(self.name, SolverStatus.UNKNOWN, error_message="cancelled: interrupt")
            return SolverResult(self.name, status_when_done)

        def request_stop(self):
            self._interrupted.set()
            return True

    return _Cooperative


def _non_cooperative_backend(recorder):
    """期限も中断も知らない backend（主張なし = Class B）。release されるまで返らない。"""

    class _NonCooperative(SMTSolver):
        def __init__(self, timeout=10, debug=False):
            super().__init__(timeout)

        @property
        def name(self):
            return "non-cooperative"

        def check_availability(self):
            return True, "test"

        def check_equivalence_direct(self, smt_script, cancellation_token=None):
            recorder.calls.append({"thread": threading.get_ident(), "timeout": self.timeout})
            assert recorder.release.wait(20), "the test never released the blocked backend"
            recorder.returned.set()
            return SolverResult(self.name, SolverStatus.UNSAT)

    return _NonCooperative


def _counting_backend(recorder, status=SolverStatus.UNSAT, on_call=None):
    class _Counting(SMTSolver):
        CAPABILITIES = SolverBackendCapabilities(
            native_timeout=True, timeout_unit=TimeUnit.MILLISECONDS, absolute_deadline=True,
        )

        @property
        def name(self):
            return "counting"

        def check_availability(self):
            return True, "test"

        def check_equivalence_direct(self, smt_script, cancellation_token=None):
            raise AssertionError("the adapter path must be used")

        def execute(self, smt_script, *, timeout_seconds, not_after=None, cancellation_token=None):
            recorder.calls.append({"not_after": not_after, "timeout": timeout_seconds})
            if on_call is not None:
                on_call()
            return SolverResult(self.name, status)

    return _Counting


# ---------------------------------------------------------------------------
# E11: cooperative backend
# ---------------------------------------------------------------------------


def test_e11_a_cooperative_worker_gets_the_absolute_deadline_as_an_argument_and_stops():
    recorder = _Recorder()
    runner = ParallelSolverRunner(timeout=30, solver_classes=[_cooperative_backend(recorder)])
    started = time.monotonic()
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(1.0)) as deadline:
            with pytest.raises(DeadlineExceeded) as raised:
                runner.run_parallel(QUERY)
            expected_not_after = deadline.absolute - deadline.policy.sub_operation_margin_seconds
    elapsed = time.monotonic() - started
    [call] = recorder.calls
    assert call["thread"] != threading.get_ident()  # worker thread で走った
    assert call["sees_deadline"] is False  # worker は contextvar の期限を読めない
    assert call["not_after"] == pytest.approx(expected_not_after)  # 引数で受け取った
    assert recorder.returned.is_set()  # 自分で止まった（join 済み）
    assert elapsed < 1.0 + 0.5  # 期限 + 余裕の中で戻った
    assert "cut_by_deadline" in raised.value.evidence_refs or "boundary=after" in raised.value.evidence_refs
    assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_DEADLINE


def test_e11_a_cooperative_backend_that_overruns_is_interrupted_within_the_deadline(monkeypatch):
    """期限を守らない（壊れた）adapter でも、止め方を主張していれば期限で止める。"""
    recorder = _Recorder()
    notes = []
    monkeypatch.setattr(parallel_module, "journal_note", lambda note, payload=None: notes.append(note))
    runner = ParallelSolverRunner(
        timeout=30, solver_classes=[_cooperative_backend(recorder, honour_not_after=False)],
    )
    started = time.monotonic()
    with deadline_scope(_policy(1.0)):
        with pytest.raises(DeadlineExceeded) as raised:
            runner.run_parallel(QUERY)
    elapsed = time.monotonic() - started
    assert recorder.returned.is_set()
    assert elapsed < 1.0 + parallel_module.RUNNING_STOP_GRACE_SECONDS
    assert "backend=cooperative:stopped" in raised.value.evidence_refs
    assert "solver_worker_not_stoppable" not in notes


# ---------------------------------------------------------------------------
# E11 / E14: non-cooperative backend（止められない実行を正常な UNKNOWN にしない）
# ---------------------------------------------------------------------------


def test_e11_a_non_cooperative_worker_is_detected_and_never_reported_as_a_normal_result(monkeypatch):
    recorder = _Recorder()
    events = []

    def _note(note, payload=None):
        events.append((note, time.monotonic(), payload))
        # 止められないと検出した後で、backend が自分で返れるようにする
        threading.Timer(0.3, recorder.release.set).start()

    monkeypatch.setattr(parallel_module, "journal_note", _note)
    runner = ParallelSolverRunner(timeout=30, solver_classes=[_non_cooperative_backend(recorder)])
    started = time.monotonic()
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(3.0)) as deadline:
            absolute = deadline.absolute
            with pytest.raises(DeadlineExceeded) as raised:
                runner.run_parallel(QUERY)
    # (1) main の待ちは期限を越えない: 止められないと検出した時刻は期限 + grace の中
    [(note, detected_at, payload)] = events
    assert note == "solver_worker_not_stoppable"
    assert detected_at <= absolute + parallel_module.RUNNING_STOP_GRACE_SECONDS + 0.3
    assert payload["guarantee_classes"] == ["B"]
    # (2) 走っている worker は止められない（検出して記録した）
    assert "worker_stop=not_stoppable" in raised.value.evidence_refs
    assert "backend=non-cooperative:not_stoppable" in raised.value.evidence_refs
    # (3) worker が自分で返るまで待った（worker を残したまま結果を確定しない）
    assert recorder.returned.is_set()
    # (4) その backend が返した UNSAT は判定にならない（期限の限界として raise した）
    assert ledger.pending_failure().exception.reason_id == DeadlineExceeded.REASON_ID
    # 能力を主張しない adapter の既定の実行: 秒の timeout を期限までに切って渡した（0 ではない）
    assert recorder.calls[0]["timeout"] == 2
    assert time.monotonic() - started >= 3.0


def test_e11_pending_futures_are_cancelled_and_running_ones_are_told_to_stop():
    recorder = _Recorder()
    backend_cls = _non_cooperative_backend(recorder)
    blocked, queued = backend_cls(), backend_cls()
    token = CancellationToken()
    executor = concurrent.futures.ThreadPoolExecutor(max_workers=1)
    try:
        running = executor.submit(blocked.check_equivalence_direct, QUERY)
        pending = executor.submit(queued.check_equivalence_direct, QUERY)
        while not recorder.calls:
            time.sleep(0.01)
        threading.Timer(0.5, recorder.release.set).start()
        stopped = stop_unfinished(
            [(blocked, running), (queued, pending)], {running, pending}, token, grace_seconds=0.1,
        )
    finally:
        executor.shutdown(wait=True)
    assert token.is_cancelled()
    assert stopped[pending] is BackendTermination.CANCELLED_PENDING
    assert stopped[running] is BackendTermination.NOT_STOPPABLE
    assert len(recorder.calls) == 1  # 取り消した方は始まっていない


def test_e11_capabilities_decide_the_guarantee_class_not_the_backend_name():
    assert NO_CAPABILITIES.guarantee_class == "B"
    assert SMTSolver.CAPABILITIES is NO_CAPABILITIES
    assert Z3Solver.CAPABILITIES.guarantee_class == "A"
    assert SolverBackendCapabilities(native_timeout=True).guarantee_class == "B"
    assert SolverBackendCapabilities(native_timeout=True, absolute_deadline=True).guarantee_class == "A"


# ---------------------------------------------------------------------------
# E12: 返った直後の確認（runner の問い合わせ）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("mode", ["run_sequential", "run_parallel"])
def test_e12_a_sat_that_returns_after_the_deadline_is_not_adopted(mode):
    recorder = _Recorder()
    clock = ShiftedClock()
    backend = _counting_backend(recorder, status=SolverStatus.SAT, on_call=lambda: clock.jump(100))
    runner = ParallelSolverRunner(timeout=5, solver_classes=[backend])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(10.0, clock=clock)):
            with pytest.raises(DeadlineExceeded) as raised:
                getattr(runner, mode)(QUERY)
    assert len(recorder.calls) == 1
    assert "boundary=after" in raised.value.evidence_refs
    assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_DEADLINE


def test_e12_the_direct_single_backend_query_is_settled_the_same_way():
    recorder = _Recorder()
    clock = ShiftedClock()
    backend = _counting_backend(recorder, status=SolverStatus.UNSAT, on_call=lambda: clock.jump(100))()
    with deadline_scope(_policy(10.0, clock=clock)):
        with pytest.raises(DeadlineExceeded):
            run_backend_query(backend, QUERY)


# ---------------------------------------------------------------------------
# E5: 期限の後に新しい問い合わせを始めない（`_resolve_timeout` の後も）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("entry", ["run_sequential", "run_parallel", "run_single", "direct"])
def test_e5_no_backend_is_started_after_the_deadline(entry):
    recorder = _Recorder()
    clock = ShiftedClock()
    backend_cls = _counting_backend(recorder)
    runner = ParallelSolverRunner(timeout=5, solver_classes=[backend_cls])
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(1.0, clock=clock)):
            clock.jump(2)
            with pytest.raises(DeadlineExceeded) as raised:
                if entry == "run_single":
                    runner.run_single(runner._solvers[0], QUERY, timeout=5)
                elif entry == "direct":
                    run_backend_query(backend_cls(timeout=5), QUERY)
                else:
                    getattr(runner, entry)(QUERY, timeout=5)
    assert recorder.calls == []
    assert raised.value.site == parallel_module.SOLVER_STAGE
    assert "boundary=before" in raised.value.evidence_refs
    assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_DEADLINE


def test_e5_after_a_trip_finalization_queries_are_not_started_and_do_not_raise():
    recorder = _Recorder()
    clock = ShiftedClock()
    runner = ParallelSolverRunner(timeout=5, solver_classes=[_counting_backend(recorder)])
    with deadline_scope(_policy(1.0, clock=clock)):
        clock.jump(2)
        with pytest.raises(DeadlineExceeded):
            runner.run_sequential(QUERY)
        with finalization():
            for mode in ("run_sequential", "run_parallel"):
                result = getattr(runner, mode)(QUERY)
                [row] = result.results
                assert row.status is SolverStatus.TIMEOUT
                assert row.termination is BackendTermination.NOT_STARTED
                assert result.is_equivalent is None
    assert recorder.calls == []


def test_e3_without_a_deadline_the_runner_passes_no_absolute_end():
    recorder = _Recorder()
    runner = ParallelSolverRunner(timeout=7, solver_classes=[_counting_backend(recorder)])
    for mode in ("run_sequential", "run_parallel"):
        assert getattr(runner, mode)(QUERY).is_equivalent is True
    assert [call["not_after"] for call in recorder.calls] == [None, None]
    assert [call["timeout"] for call in recorder.calls] == [7, 7]


# ---------------------------------------------------------------------------
# E9: 3 点の clamp（decompile / condition oracle / solver）
# ---------------------------------------------------------------------------


def _fake_decompile_analyzer(recorded):
    class _Results:
        def decompileCompleted(self):
            return True

        def getHighFunction(self):
            return object()

    class _Decompiler:
        def decompileFunction(self, function, timeout, monitor):
            recorded.append(timeout)
            return _Results()

    return SimpleNamespace(_get_decompiler=lambda: _Decompiler())


def test_e9_decompile_gets_whole_seconds_up_to_the_deadline_and_never_zero():
    from scripts.function_tracer_pcode.ghidra.decompilation_broker import (
        TOP_LEVEL_SOURCE_CONTRACT,
        decompile_within_deadline,
    )

    recorded = []
    analyzer = _fake_decompile_analyzer(recorded)
    kwargs = dict(source_contract_id=TOP_LEVEL_SOURCE_CONTRACT, semantic_owner="slice6")
    decompile_within_deadline(analyzer, object(), 60, None, **kwargs)  # 期限なし: そのまま
    with deadline_scope(_policy(6.0, margin=0.5)):
        decompile_within_deadline(analyzer, object(), 60, None, **kwargs)
    assert recorded[0] == 60
    assert recorded[1] in (4, 5)  # 残り ~5.5 s を秒へ切り捨て
    clock = ShiftedClock()
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(1.2, clock=clock, margin=0.5)):
            with pytest.raises(DeadlineExceeded) as raised:
                decompile_within_deadline(analyzer, object(), 60, None, **kwargs)
    assert len(recorded) == 2  # 0 秒で decompile しない
    assert raised.value.site == "decompile"
    assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_DEADLINE


def test_e9_the_condition_oracle_gets_milliseconds_up_to_the_deadline(monkeypatch):
    from scripts.function_tracer_pcode.analysis.condition import smt_oracle
    from scripts.function_tracer_pcode.analysis.condition.condition_cache import condition_cache_scope
    from scripts.function_tracer_pcode.analysis.condition.smt_oracle import ConditionSMTOracle
    from scripts.function_tracer_pcode.core.condition_metrics import condition_metrics_scope
    from scripts.function_tracer_pcode.tests.unit.test_issue105b_simplify_budgets import _FakeZ3, _slt

    fake = _FakeZ3()
    monkeypatch.setattr(ConditionSMTOracle, "_z3", fake)
    monkeypatch.setattr(ConditionSMTOracle, "_available", True)
    monkeypatch.setattr(ConditionSMTOracle, "_availability_checked", True)
    timeouts = []
    original = smt_oracle.isolated_solver
    monkeypatch.setattr(
        smt_oracle, "isolated_solver",
        lambda z3, script, timeout_ms: timeouts.append(timeout_ms) or original(z3, script, timeout_ms),
    )
    with condition_cache_scope(), condition_metrics_scope():
        assert ConditionSMTOracle.conjunction_is_unsat([_slt(0, 1)]) is True
        with deadline_scope(_policy(0.3, margin=0.2)):
            assert ConditionSMTOracle.conjunction_is_unsat([_slt(1, 2)]) is True
        clock = ShiftedClock()
        with pair_failure_scope(("pair",), None):
            with deadline_scope(_policy(1.0, clock=clock)):
                clock.jump(2)
                with pytest.raises(DeadlineExceeded) as raised:
                    ConditionSMTOracle.conjunction_is_unsat([_slt(2, 3)])
    assert timeouts[0] == 250  # 期限なし: 従来の 250 ms
    assert 1 <= timeouts[1] <= 100  # 期限まで（残り ~0.1 s）に切る。0 にしない
    assert len(timeouts) == 2 and fake.checks == 2  # 期限の後は発行しない
    assert raised.value.site == smt_oracle.CONDITION_ORACLE_STAGE


def test_e9_the_z3_adapter_stops_a_hard_query_at_the_absolute_end():
    solver = Z3Solver(timeout=30)
    started = time.monotonic()
    result = solver.execute(HARD_QUERY, timeout_seconds=30, not_after=started + 0.5)
    elapsed = time.monotonic() - started
    assert result.status in (SolverStatus.TIMEOUT, SolverStatus.UNKNOWN)
    assert elapsed < 0.5 + 0.5  # 実測の越え（最大 0.12 s）より十分大きい余裕


def test_the_z3_adapter_honours_a_stop_request_from_another_thread():
    """z3 の ``running_stop=INTERRUPT`` の主張の根拠（別 thread からの中断で走っている check が返る）。"""
    solver = Z3Solver(timeout=30)
    box = {}

    def _run():
        box["result"] = solver.execute(HARD_QUERY, timeout_seconds=30)
        box["returned"] = time.monotonic()

    thread = threading.Thread(target=_run)
    thread.start()
    time.sleep(0.5)
    requested = time.monotonic()
    assert solver.request_stop() is True
    thread.join(5)
    assert not thread.is_alive()
    assert box["returned"] - requested < 1.0
    assert box["result"].status in (SolverStatus.UNKNOWN, SolverStatus.TIMEOUT)
    assert solver.request_stop() is False  # 実行していなければ何もしない


# ---------------------------------------------------------------------------
# M-2: backend の追加は adapter + registry 登録 + backend の test に閉じる
# ---------------------------------------------------------------------------


class DummyDeadlineBackend(SMTSolver):
    """registry に足す dummy backend（adapter の契約だけを実装する）。"""

    CAPABILITIES = SolverBackendCapabilities(
        native_timeout=True, timeout_unit=TimeUnit.MILLISECONDS, absolute_deadline=True,
    )
    received = []

    @property
    def name(self):
        return "dummy"

    def check_availability(self):
        return True, "test"

    def check_equivalence_direct(self, smt_script, cancellation_token=None):
        raise AssertionError("the adapter path must be used")

    def execute(self, smt_script, *, timeout_seconds, not_after=None, cancellation_token=None):
        type(self).received.append(not_after)
        return SolverResult(self.name, SolverStatus.UNSAT)


def test_m2_a_registered_dummy_backend_gets_the_deadline_through_the_adapter_only(monkeypatch):
    DummyDeadlineBackend.received = []
    monkeypatch.setattr(
        ParallelSolverRunner, "DEFAULT_SOLVERS", [*ParallelSolverRunner.DEFAULT_SOLVERS, DummyDeadlineBackend],
    )
    runner = ParallelSolverRunner(timeout=5)
    assert "dummy" in runner.get_available_solvers()
    with deadline_scope(_policy(30.0)) as deadline:
        result = runner.run_sequential(QUERY)
    # 設定値（5 s）が期限（30 s − 余裕）より先に終わる: 期限は時間を決めていないので adapter には
    # 設定値の timeout だけを渡す（終わりを渡さない。期限なしと同じ値）
    assert DummyDeadlineBackend.received == [None]
    rows = {row.solver_name: row for row in result.results}
    assert rows["dummy"].deadline_limited is False
    assert any(row.solver_name == "dummy" for row in result.results)


def test_m2_every_registered_backend_declares_its_capabilities_explicitly():
    """registry に載る backend は能力を自分で宣言する（宣言漏れを既定の「主張なし」に紛れさせない）。"""
    from scripts.function_tracer_pcode.smt.solvers import (
        BoolectorSolver,
        CVC5Solver,
        Yices2Solver,
    )

    for backend in ParallelSolverRunner.DEFAULT_SOLVERS:
        assert "CAPABILITIES" in vars(backend), backend
    # production で使っていない backend は何も主張しない（実測していない能力を宣言しない）
    for backend in (CVC5Solver, Yices2Solver, BoolectorSolver):
        assert backend.CAPABILITIES is NO_CAPABILITIES


_BACKEND_NAMES = ("z3", "cvc5", "yices", "boolector")
_BACKEND_CLASSES = ("Z3Solver", "CVC5Solver", "Yices2Solver", "BoolectorSolver")


def _modules_that_must_not_know_backends():
    yield PACKAGE_ROOT / "checker" / "workflow.py"
    yield PACKAGE_ROOT / "checker" / "pair_execution.py"
    yield PACKAGE_ROOT / "core" / "errors.py"
    yield PACKAGE_ROOT / "core" / "deadline.py"
    yield PACKAGE_ROOT / "authority" / "lifecycle" / "production_boundary.py"
    yield from sorted((PACKAGE_ROOT / "authority").rglob("*.py"))
    yield from sorted((PACKAGE_ROOT / "cli").rglob("*.py"))
    yield PACKAGE_ROOT / "smt" / "parallel.py"


def test_m2_no_backend_name_branch_outside_the_adapters():
    """runner / workflow / 台帳 / boundary / authority / CLI は backend 名も具体 class も比べない。

    `smt/parallel.py` は registry（`DEFAULT_SOLVERS`）の登録行だけが具体 class を名指ししてよい。
    """
    offenders = []
    for path in _modules_that_must_not_know_backends():
        tree = ast.parse(path.read_text(encoding="utf-8"))
        registry_lines = set()
        if path.name == "parallel.py":
            for node in ast.walk(tree):
                if isinstance(node, ast.AnnAssign) and getattr(node.target, "id", None) == "DEFAULT_SOLVERS":
                    registry_lines.update(range(node.lineno, node.end_lineno + 1))
                if isinstance(node, ast.ImportFrom) and node.module and node.module.endswith("solvers.z3"):
                    registry_lines.add(node.lineno)
        for node in ast.walk(tree):
            if isinstance(node, ast.Constant) and isinstance(node.value, str):
                lowered = node.value.lower()
                if any(name == lowered or lowered.startswith(name + "(") for name in _BACKEND_NAMES):
                    offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{node.lineno}: {node.value!r}")
            if isinstance(node, ast.Name) and node.id in _BACKEND_CLASSES:
                if node.lineno not in registry_lines:
                    offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{node.lineno}: {node.id}")
    assert offenders == []


def test_adapters_receive_the_deadline_only_by_argument():
    """adapter（`smt/solvers/*`・`smt/interface.py`）は期限の scope を読まない（引数と純関数だけ）。"""
    allowed = {
        "TimeUnit", "bounded_timeout", "execution_window", "ExecutionFact", "ExecutionWindow",
        "ExecutionBound", "UNBOUNDED", "UNBOUNDED_WINDOW", "NOT_STARTED_FACT", "ExecutionEnd",
    }
    offenders = []
    for path in [PACKAGE_ROOT / "smt" / "interface.py", *sorted((PACKAGE_ROOT / "smt" / "solvers").glob("*.py"))]:
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom) and node.module and node.module.endswith("core.deadline"):
                names = {alias.name for alias in node.names}
                if names - allowed:
                    offenders.append(f"{path.name}: {sorted(names - allowed)}")
    assert offenders == []


def test_workers_never_open_a_query():
    """worker で走る `run_single`（orchestration の内側）は問いの handle を作らない（owner だけが作る）。"""
    source = (PACKAGE_ROOT / "smt" / "parallel.py").read_text(encoding="utf-8")
    tree = ast.parse(source)
    run_single = next(
        node for node in ast.walk(tree) if isinstance(node, ast.FunctionDef) and node.name == "run_single"
    )
    query_calls = [
        node for node in ast.walk(run_single)
        if isinstance(node, ast.Call) and getattr(node.func, "id", None) == "deadline_query"
    ]
    assert len(query_calls) == 1
    guard = next(
        node for node in ast.walk(run_single)
        if isinstance(node, ast.If) and any(call in list(ast.walk(node)) for call in query_calls)
    )
    assert ast.unparse(guard.test) == "not orchestrated"


def test_e12_an_oracle_answer_after_the_deadline_is_neither_used_nor_remembered(monkeypatch):
    from scripts.function_tracer_pcode.analysis.condition.condition_cache import (
        cache_lookup,
        condition_cache_scope,
    )
    from scripts.function_tracer_pcode.analysis.condition.query_identity import SolverQueryIdentity
    from scripts.function_tracer_pcode.analysis.condition.smt_oracle import ConditionSMTOracle
    from scripts.function_tracer_pcode.core.condition_metrics import condition_metrics_scope
    from scripts.function_tracer_pcode.tests.unit.test_issue105b_simplify_budgets import _FakeZ3, _slt

    clock = ShiftedClock()

    class _SlowZ3(_FakeZ3):
        def Solver(self, ctx=None):
            solver = super().Solver(ctx)
            original = solver.check

            def _check():
                clock.jump(100)  # 答え（UNSAT）は返るが、その間に期限を過ぎる
                return original()

            solver.check = _check
            return solver

    fake = _SlowZ3()
    monkeypatch.setattr(ConditionSMTOracle, "_z3", fake)
    monkeypatch.setattr(ConditionSMTOracle, "_available", True)
    monkeypatch.setattr(ConditionSMTOracle, "_availability_checked", True)
    conditions = [_slt(7, 1)]
    with condition_cache_scope(), condition_metrics_scope():
        with pair_failure_scope(("pair",), None):
            with deadline_scope(_policy(10.0, clock=clock)):
                with pytest.raises(DeadlineExceeded) as raised:
                    ConditionSMTOracle.conjunction_is_unsat(conditions)
        key = SolverQueryIdentity.from_conditions(conditions)
        assert cache_lookup(ConditionSMTOracle.VERDICT_TABLE, key, limit=4096) == (False, None)
    assert fake.checks == 1
    assert "boundary=after" in raised.value.evidence_refs
