# -*- coding: utf-8 -*-
"""Issue #106 PR-106-A: 解析の期限の owner（`core/deadline.py`）の契約。

E3（期限なしは no-op）/ E4（時計を読む頻度）/ E8（worker thread は暗黙の期限を読まない）/
E9（丸め・0 を渡さない）/ E10（打ち切りの stack snapshot）/ E12（返った直後の確認）と、
sticky な打ち切り・finalization・入れ子の scope を固定する。
"""

from __future__ import annotations

import contextvars
import io
import os
import tempfile
import threading
import time

import pytest

from scripts.function_tracer_pcode.core import deadline as deadline_module
from scripts.function_tracer_pcode.core.deadline import (
    ANALYSIS_COMPLETE_STAGE,
    DEADLINE_TARGET,
    Deadline,
    DeadlinePolicy,
    TimeUnit,
    NOT_STARTED_FACT,
    UNBOUNDED_WINDOW,
    ExecutionFact,
    ExecutionWindow,
    active_deadline,
    bounded_timeout,
    checkpoint,
    deadline_query,
    deadline_scope,
    execution_window,
    finalization,
    hot_checkpoint,
    poller,
    unbounded_timeout,
)
from scripts.function_tracer_pcode.core.errors import (
    DeadlineExceeded,
    PairStopState,
    pair_failure_scope,
    reset_pair_failure_scopes,
)


@pytest.fixture(autouse=True)
def _clean_ledgers():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


class ShiftedClock:
    """`time.monotonic` と同じ時間軸で、test が任意に先へ進められる時計。"""

    def __init__(self) -> None:
        self.offset = 0.0
        self.reads = 0

    def __call__(self) -> float:
        self.reads += 1
        return time.monotonic() + self.offset

    def jump(self, seconds: float) -> None:
        self.offset += seconds


def _policy(budget=60.0, clock=None, **kwargs):
    return DeadlinePolicy(budget_seconds=budget, clock=clock or ShiftedClock(), **kwargs)


# ---------------------------------------------------------------------------
# E3: 期限なしは何もしない
# ---------------------------------------------------------------------------

def test_e3_without_a_deadline_every_api_is_a_no_op():
    assert active_deadline() is None
    with deadline_scope(None) as scoped:
        assert scoped is None
        checkpoint("anything")
        hot_checkpoint("anything")
        poller("anything")()
        query = deadline_query("solver")
        assert not query.bounded and query.begin(3)
        assert query.bound.not_after is None
        assert query.bound.window(3, TimeUnit.MILLISECONDS) is UNBOUNDED_WINDOW
        assert UNBOUNDED_WINDOW.timeout(3, TimeUnit.MILLISECONDS, now=0.0) == 3000
        assert UNBOUNDED_WINDOW.timeout(3, TimeUnit.SECONDS, now=0.0) == 3
        assert query.wait_timeout(13) == (13.0, False)
        query.settle([NOT_STARTED_FACT])  # 期限の無い handle は何もしない
        with finalization():
            checkpoint("anything")


def test_e3_unbounded_conversion_matches_the_previous_timeouts():
    """期限なしの換算は従来の値（oracle 250 ms、秒の timeout はそのまま）。"""
    assert unbounded_timeout(0.25, TimeUnit.MILLISECONDS) == 250
    assert unbounded_timeout(10, TimeUnit.SECONDS) == 10
    assert unbounded_timeout(5, TimeUnit.MILLISECONDS) == 5000


# ---------------------------------------------------------------------------
# 基本: 期限を過ぎたら限界を記録してから raise する（stop state は型で決まる）
# ---------------------------------------------------------------------------

def test_an_expired_checkpoint_records_a_deadline_limitation_before_raising():
    clock = ShiftedClock()
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(budget=10, clock=clock)):
            checkpoint("trace_returns")  # 期限内: 何もしない
            clock.jump(11)
            with pytest.raises(DeadlineExceeded) as raised:
                checkpoint("trace_returns")
        failure = ledger.pending_failure()
    assert failure is not None
    assert failure.exception.reason_id == DeadlineExceeded.REASON_ID
    assert failure.site == "trace_returns"
    assert failure.exception.target_key == (DEADLINE_TARGET, "trace_returns")
    assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_DEADLINE
    evidence = dict(item.split("=", 1) for item in raised.value.evidence_refs if "=" in item)
    assert evidence["stage"] == "trace_returns"
    assert evidence["boundary"] == "before"
    assert float(evidence["budget_seconds"]) == 10.0


def test_the_trip_is_sticky_and_folds_into_one_ledger_record():
    """握り潰されても次の境界でまた止まり、台帳は 1 件（最初の site / target）に畳む。"""
    clock = ShiftedClock()
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(budget=5, clock=clock)):
            clock.jump(6)
            for stage in ("decompile", "condition_simplify", "solver"):
                try:
                    checkpoint(stage)
                except DeadlineExceeded:
                    pass  # 深部の except Exception が握り潰した想定
            # 時計を戻しても（期限内に見えても）打ち切りは解けない
            clock.jump(-100)
            with pytest.raises(DeadlineExceeded) as raised:
                checkpoint("obligation")
            with pytest.raises(DeadlineExceeded):
                deadline_query("solver").begin(1)  # 新しい問いも始めない
            with pytest.raises(DeadlineExceeded):
                hot_checkpoint("trace_pcode")
        assert ledger.recorded_failure_count() == 1
        assert ledger.pending_failure().site == "decompile"
    assert raised.value.site == "decompile"


def test_only_the_deadline_owner_raises_the_limitation_and_nested_scopes_never_extend():
    clock = ShiftedClock()
    with deadline_scope(_policy(budget=10, clock=clock)) as outer:
        with deadline_scope(_policy(budget=1000, clock=clock)) as inner:
            assert inner is outer  # 内側が後なら外側のまま（延びない）
        with deadline_scope(_policy(budget=1, clock=clock)) as shorter:
            assert shorter is not outer and shorter.absolute < outer.absolute
        with deadline_scope(None) as inherited:
            assert inherited is outer
    assert active_deadline() is None


def test_policy_rejects_non_positive_budgets():
    for bad in (0, -1, float("nan"), float("inf")):
        with pytest.raises((ValueError, TypeError)):
            DeadlinePolicy(budget_seconds=bad)
    with pytest.raises(TypeError):
        DeadlinePolicy(budget_seconds=True)
    with pytest.raises(ValueError):
        DeadlinePolicy(budget_seconds=1, poll_interval=0)


# ---------------------------------------------------------------------------
# E4: hot loop の時計の読み方
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("interval", [1, 16, 256])
def test_e4_hot_checkpoints_read_the_clock_once_per_poll_interval(interval):
    clock = ShiftedClock()
    with deadline_scope(_policy(clock=clock, poll_interval=interval)) as deadline:
        before = deadline.clock_reads
        poll = poller("identity_graph")
        for _ in range(interval * 10):
            poll()
        assert deadline.clock_reads - before == 10
        before = deadline.clock_reads
        for _ in range(interval * 3):
            hot_checkpoint("trace_pcode")
        assert deadline.clock_reads - before == 3


def test_e4_without_a_deadline_hot_checkpoints_never_read_the_clock(monkeypatch):
    reads = []
    monkeypatch.setattr(deadline_module.time, "monotonic", lambda: reads.append(1) or 0.0)
    poll = poller("x")
    for _ in range(1000):
        poll()
        hot_checkpoint("x")
        checkpoint("x")
    assert reads == []


def test_e4_a_tripped_deadline_stops_every_hot_call_not_only_every_nth():
    clock = ShiftedClock()
    with deadline_scope(_policy(budget=5, clock=clock, poll_interval=1000)):
        clock.jump(6)
        with pytest.raises(DeadlineExceeded):
            checkpoint("condition_simplify")
        poll = poller("identity_graph")
        with pytest.raises(DeadlineExceeded):
            poll()  # 1 回目でも止まる（打ち切り後は間引かない）


# ---------------------------------------------------------------------------
# E8: worker thread は暗黙の期限を読まない
# ---------------------------------------------------------------------------

def test_e8_a_worker_thread_never_sees_the_owner_deadline():
    clock = ShiftedClock()
    seen = {}
    with deadline_scope(_policy(budget=1, clock=clock)):
        clock.jump(5)

        def _worker():
            seen["active"] = active_deadline()
            checkpoint("solver")  # 何もしない（raise しない）
            hot_checkpoint("solver")
            query = deadline_query("solver")
            seen["bounded"] = query.bounded
            seen["begin"] = query.begin(3)

        thread = threading.Thread(target=_worker)
        thread.start()
        thread.join()
    assert seen["active"] is None
    assert seen["bounded"] is False and seen["begin"] is True  # 期限の無い handle（従来どおり）


def test_e8_a_copied_context_does_not_hand_the_deadline_to_another_thread():
    """context を複製して別 thread で走らせても owner の thread でなければ効かない。"""
    clock = ShiftedClock()
    seen = {}
    with deadline_scope(_policy(budget=1, clock=clock)):
        clock.jump(5)
        context = contextvars.copy_context()

        def _worker():
            seen["active"] = context.run(active_deadline)
            context.run(checkpoint, "solver")
            poll = context.run(poller, "identity_graph")
            for _ in range(10000):
                poll()

        thread = threading.Thread(target=_worker)
        thread.start()
        thread.join()
    assert seen["active"] is None


# ---------------------------------------------------------------------------
# E9: 丸め（0 を timeout 無しとして渡さない）
# ---------------------------------------------------------------------------

def test_e9_bounded_timeout_rounding_rules():
    now = 100.0
    # ミリ秒: 切り捨て、1 以上
    assert bounded_timeout(10, now + 2.5, TimeUnit.MILLISECONDS, now=now) == 2500
    assert bounded_timeout(10, now + 0.0004, TimeUnit.MILLISECONDS, now=now) == 1
    assert bounded_timeout(0.25, now + 5, TimeUnit.MILLISECONDS, now=now) == 250
    # 秒: 切り捨て、0 なら始めない
    assert bounded_timeout(10, now + 2.9, TimeUnit.SECONDS, now=now) == 2
    assert bounded_timeout(10, now + 0.9, TimeUnit.SECONDS, now=now) is None
    assert bounded_timeout(3, now + 60, TimeUnit.SECONDS, now=now) == 3
    # 残りが 0 以下なら始めない
    for unit in TimeUnit:
        assert bounded_timeout(10, now, unit, now=now) is None
        assert bounded_timeout(10, now - 1, unit, now=now) is None


def test_e9_begin_below_the_margin_is_a_deadline_before_the_execution_starts():
    clock = ShiftedClock()
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(budget=10, clock=clock, sub_operation_margin_seconds=0.5)):
            query = deadline_query("solver")
            assert query.begin(30)
            window = query.bound.window(30, TimeUnit.MILLISECONDS)
            assert window.limited  # 期限（< 30 s）が時間を決める
            assert 0 < window.timeout(30, TimeUnit.MILLISECONDS, now=clock()) <= 9500
            clock.jump(9.6)  # 残り 0.4 s < 余裕 0.5 s
            with pytest.raises(DeadlineExceeded) as raised:
                query.begin(30)
        assert "remaining_below_margin" in raised.value.evidence_refs
        assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_DEADLINE


def test_e9_a_seconds_api_never_receives_zero():
    clock = ShiftedClock()
    with deadline_scope(_policy(budget=1.8, clock=clock, sub_operation_margin_seconds=0.5)):
        # 残り 1.3 s → 秒に直すと 1
        query = deadline_query("decompile")
        assert query.begin(60, TimeUnit.SECONDS)
        window = query.bound.window(60, TimeUnit.SECONDS)
        assert window.timeout(60, TimeUnit.SECONDS, now=clock()) == 1
    clock = ShiftedClock()
    with deadline_scope(_policy(budget=1.2, clock=clock, sub_operation_margin_seconds=0.5)):
        # 残り 0.7 s → 秒に直すと 0: 始めない（0 を渡さない）
        with pytest.raises(DeadlineExceeded):
            deadline_query("decompile").begin(60, TimeUnit.SECONDS)


def test_e9_the_wait_is_clamped_to_the_deadline_and_says_so():
    clock = ShiftedClock()
    with deadline_scope(_policy(budget=4, clock=clock)):
        query = deadline_query("solver")
        waited, limited = query.wait_timeout(40)
        assert waited <= 4.0 and limited is True
        assert query.wait_timeout(1) == (1.0, False)  # 設定値が短ければ期限は決めていない
        clock.jump(10)
        assert query.wait_timeout(40) == (0.0, True)


# ---------------------------------------------------------------------------
# 実行 1 回の窓（実行を始める瞬間に求める。問いの入口で固定しない）
# ---------------------------------------------------------------------------

def test_the_execution_window_rule():
    now = 100.0
    assert execution_window(5, None, TimeUnit.MILLISECONDS, now=now) is UNBOUNDED_WINDOW
    assert execution_window(5, 110.0, TimeUnit.MILLISECONDS, now=now) == ExecutionWindow(105.0, False)
    assert execution_window(5, 103.0, TimeUnit.MILLISECONDS, now=now) == ExecutionWindow(103.0, True)
    assert execution_window(5, 100.0, TimeUnit.MILLISECONDS, now=now) is None
    assert execution_window(5, 100.7, TimeUnit.SECONDS, now=now) is None  # 秒に直すと 0
    assert execution_window(5, 105.0, TimeUnit.MILLISECONDS, now=now) == ExecutionWindow(105.0, False)


def test_a_later_execution_of_the_same_query_gets_its_own_window():
    """指摘 2: 先の実行が時間を使えば、後の実行の窓は期限で決まる（入口で固定しない）。"""
    clock = ShiftedClock()
    with deadline_scope(_policy(budget=0.4, clock=clock, sub_operation_margin_seconds=0.05)):
        query = deadline_query("solver")
        assert query.begin(0.25)
        first = query.bound.window(0.25, TimeUnit.MILLISECONDS)
        assert first.limited is False  # 0.25 s < 残り 0.35 s
        clock.jump(0.2)
        assert query.begin(0.25)
        second = query.bound.window(0.25, TimeUnit.MILLISECONDS)
        assert second.limited is True  # 残り 0.15 s < 0.25 s
        assert second.end == pytest.approx(first.end - 0.25 + 0.35)


def test_the_cut_by_deadline_rule():
    assert ExecutionFact(limited=True, definitive=False).cut_by_deadline
    assert not ExecutionFact(limited=True, definitive=True).cut_by_deadline
    # 期限が時間を決めなかった timeout / unknown は通常の結果（期限の限界にしない）
    assert not ExecutionFact(limited=False, definitive=False).cut_by_deadline
    assert NOT_STARTED_FACT.cut_by_deadline


# ---------------------------------------------------------------------------
# E12: 返った直後の確認（始めたときに期限内だったことは理由にならない）
# ---------------------------------------------------------------------------

def test_e12_an_answer_that_returns_after_the_deadline_is_not_accepted():
    clock = ShiftedClock()
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(budget=10, clock=clock)):
            query = deadline_query("solver")
            assert query.begin(5)
            clock.jump(11)  # 答え（SAT / UNSAT）は返ったが、その間に期限を過ぎた
            with pytest.raises(DeadlineExceeded) as raised:
                query.settle([ExecutionFact(limited=False, definitive=True)])
    assert "boundary=after" in raised.value.evidence_refs
    assert ledger.pending_failure() is not None


def test_e12_a_timeout_cut_by_the_deadline_is_a_deadline_even_before_it_expires():
    clock = ShiftedClock()
    with deadline_scope(_policy(budget=3, clock=clock, sub_operation_margin_seconds=0.5)):
        query = deadline_query("solver")
        assert query.begin(30)
        window = query.bound.window(30, TimeUnit.MILLISECONDS)
        clock.jump(2.6)  # 窓の終わり（2.5 s）で solver が止まり、期限（3 s）の手前で返った
        with pytest.raises(DeadlineExceeded) as raised:
            query.settle([ExecutionFact(limited=window.limited, definitive=False)])
    assert "cut_by_deadline" in raised.value.evidence_refs


def test_e12_a_normal_solver_timeout_is_not_turned_into_a_deadline():
    clock = ShiftedClock()
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(budget=3, clock=clock)):
            query = deadline_query("solver")
            assert query.begin(0.5)
            window = query.bound.window(0.5, TimeUnit.MILLISECONDS)
            assert window.limited is False
            clock.jump(0.5)
            query.settle([ExecutionFact(limited=window.limited, definitive=False)])  # raise しない
            query.settle([ExecutionFact(limited=False, definitive=True)])
        assert ledger.pending_failure() is None


# ---------------------------------------------------------------------------
# finalization: 確定処理は期限で止めない。打ち切った後は新しい問いを始めない
# ---------------------------------------------------------------------------

def test_finalization_never_raises_and_refuses_new_work_after_a_trip():
    clock = ShiftedClock()
    with pair_failure_scope(("pair",), None) as ledger:
        with deadline_scope(_policy(budget=3, clock=clock)):
            clock.jump(4)
            with finalization():
                # 期限を過ぎても確定処理は止まらない（打ち切りはまだ無い）
                checkpoint("authority_finalize")
                hot_checkpoint("render")
                query = deadline_query("solver")
                assert query.begin(5) and not query.bounded and query.bound.not_after is None
            with pytest.raises(DeadlineExceeded):
                checkpoint(ANALYSIS_COMPLETE_STAGE)
            with finalization():
                refused = deadline_query("solver")
                assert refused.begin(5) is False
                refused.settle([NOT_STARTED_FACT])  # raise しない
        assert ledger.recorded_failure_count() == 1


# ---------------------------------------------------------------------------
# E10: 打ち切りの stack snapshot（無くても判定は同じ）
# ---------------------------------------------------------------------------

def test_e10_the_first_trip_writes_a_header_and_every_thread_stack():
    clock = ShiftedClock()
    with tempfile.TemporaryDirectory() as directory:
        path = os.path.join(directory, "dump.txt")
        with open(path, "ab", buffering=0) as sink:
            with deadline_scope(_policy(budget=1, clock=clock, snapshot_sink=sink)):
                clock.jump(2)
                for stage in ("decompile", "solver"):
                    with pytest.raises(DeadlineExceeded):
                        checkpoint(stage)
        text = open(path, encoding="utf-8", errors="replace").read()
    assert text.count("=== deadline_tripped stage=decompile boundary=before") == 1
    assert "stage=solver" not in text  # 2 回目は書かない
    assert "test_e10_the_first_trip_writes_a_header_and_every_thread_stack" in text


def test_e10_the_decision_does_not_depend_on_the_snapshot_sink():
    def _run(sink):
        clock = ShiftedClock()
        with pair_failure_scope(("pair",), None) as ledger:
            with deadline_scope(_policy(budget=1, clock=clock, snapshot_sink=sink)):
                clock.jump(2)
                with pytest.raises(DeadlineExceeded) as raised:
                    checkpoint("expand")
            failure = ledger.pending_failure()
        return (
            raised.value.reason_id, raised.value.site, raised.value.target_key,
            failure.site, ledger.stop_state(),
        )

    class _BrokenSink:
        def write(self, _data):
            raise OSError("disk full")

    with tempfile.TemporaryDirectory() as directory:
        with open(os.path.join(directory, "d"), "ab", buffering=0) as sink:
            with_sink = _run(sink)
    assert _run(None) == with_sink == _run(_BrokenSink())


def test_the_trip_writes_a_journal_note(monkeypatch):
    notes = []
    monkeypatch.setattr(deadline_module, "journal_note", lambda note, payload=None: notes.append((note, payload)))
    clock = ShiftedClock()
    with deadline_scope(_policy(budget=1, clock=clock)):
        clock.jump(2)
        with pytest.raises(DeadlineExceeded):
            checkpoint("obligation")
    assert [note for note, _ in notes] == ["deadline_tripped"]
    assert notes[0][1]["stage"] == "obligation"
