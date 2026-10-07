# -*- coding: utf-8 -*-
"""Issue #106 PR-106-A: pair の実行制御と期限の契約（E5 / E0o / E6 / E13 / E14 と fitness）。

再生（記録済み P-code）を使わない側。再生で production の全経路を通す E1 / E2 / E3 は
`test_issue106a_pair_deadline.py`（`recorded_replay`）。
"""

from __future__ import annotations

import ast
import json
import pathlib
import time
from unittest.mock import Mock, patch

import pytest

from scripts.function_tracer_pcode.core.deadline import DeadlinePolicy
from scripts.function_tracer_pcode.core.errors import (
    DeadlineExceeded,
    reset_pair_failure_scopes,
)
from scripts.function_tracer_pcode.reporting.deadline_acceptance import (
    CLASS_A,
    CLASS_B,
    TRUTH_CONSISTENT,
    TRUTH_CONTRADICTED,
    VERDICT_ACCEPTED,
    VERDICT_FALLBACK_SAFE,
    VERDICT_NOT_ACCEPTED,
    VERDICT_UNSAFE,
    TargetObservation,
    classify_target,
    summarize,
)
from scripts.function_tracer_pcode.tests.unit.test_issue106a_deadline import ShiftedClock


#: この module の test は実の時計で動く期限（`ShiftedClock` / `clock=` の無い `DeadlinePolicy`）の結果を確かめる:
#: 短い予算では GC の一時停止が結果を変えるので、call の間は古い heap を freeze する（Issue #239）
pytestmark = pytest.mark.wall_clock

PACKAGE_ROOT = pathlib.Path(__file__).resolve().parents[2]
BUDGET_REASON = DeadlineExceeded.REASON_ID


@pytest.fixture(autouse=True)
def _clean_ledgers():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


# ---------------------------------------------------------------------------
# E5: 期限の後に phase / 再試行を始めない（workflow の境界）
# ---------------------------------------------------------------------------


def test_e5_the_next_phase_is_not_started_after_the_deadline():
    from scripts.function_tracer_pcode.checker.phases.handler import PhaseHandler
    from scripts.function_tracer_pcode.tests.unit.test_issue106_pair_limitation_propagation import (
        _analyses,
        _connector,
        _emit_one_production_signal,
        _new_checker,
    )
    from conftest import MockProgram, create_mock_result
    from scripts.function_tracer_pcode.smt import SolverStatus

    analysis1, analysis2 = _analyses()
    clock = ShiftedClock()
    checker = _new_checker(_connector())
    handler = Mock(wraps=PhaseHandler(checker))
    checker.phase_handler = handler

    def _analyze(self, name, timeout):
        return analysis1 if name == "func1" else analysis2

    def _stage_plan(*_args, **_kwargs):
        # 1 つ目の phase の間に期限を過ぎる（この中では checkpoint を通らない）
        _emit_one_production_signal()
        clock.jump(1000)
        return create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)

    program1 = MockProgram(name="binary1.exe", architecture="x86:LE:64:default")
    program2 = MockProgram(name="binary2.exe", architecture="x86:LE:64:default")
    with patch(
        "scripts.function_tracer_pcode.analysis.returns.analyzer.ReturnAnalyzer.analyze_function_by_name",
        _analyze,
    ), patch.object(checker, "_run_stage_plan", side_effect=_stage_plan) as stage_plan, patch(
        "scripts.function_tracer_pcode.checker.checker.TypeFixer",
    ) as fixer:
        fixer.side_effect = lambda *args, **kwargs: Mock()
        result = checker.check_from_binaries(
            program1=program1, program2=program2, function_name1="func1", function_name2="func2",
            decompile_timeout=60, retry_with_type_fix=True,
            analysis_deadline=DeadlinePolicy(budget_seconds=100, clock=clock),
        )
    assert stage_plan.call_count == 1  # 2 つ目の phase の stage plan は始まらない
    assert handler.execute_phase.call_count == 0  # phase の型修正も始めない
    assert result.final_outcome == "UNKNOWN"
    # 期限の限界が reason に出る（対照群の producer 信号の reason は残ってよい）
    assert BUDGET_REASON in [reason.reason_id for reason in result.unknown_reasons]
    failure = result.diagnostics["failures"]["analysis_limitation"]
    assert failure["site"] in ("phase_plan", "analysis_complete")
    assert result.diagnostics["analysis_deadline"]["tripped"] is True


def test_e0o_crossing_the_deadline_inside_finalization_keeps_the_decision():
    """authority の確定の途中で期限を過ぎても、確定した判定を捨てない（限界にしない）。"""
    from scripts.function_tracer_pcode.tests.unit.test_issue106_pair_limitation_propagation import (
        _analyses,
        _connector,
        _healthy_stage_plan,
        _run_pair,
    )

    def _run(with_deadline):
        clock = ShiftedClock()
        connector = _connector()
        original_finish = connector.finish

        def _finish(*args, **kwargs):
            clock.jump(1000)  # finish の間に期限を過ぎる
            # finish は authority の確定の中で solver を問うことがある（ABI / 幅の保留中の問い）。
            # 期限を過ぎた後でも、打ち切っていなければ確定処理として問えて、限界にならない
            from scripts.function_tracer_pcode.smt.parallel import ParallelSolverRunner

            ParallelSolverRunner(timeout=1).run_sequential(
                "(declare-const x (_ BitVec 8))\n(assert (= x #x01))\n(check-sat)"
            )
            return original_finish(*args, **kwargs)

        connector.finish = _finish
        analysis1, analysis2 = _analyses()
        checker = None
        if with_deadline:
            from scripts.function_tracer_pcode.tests.unit.test_issue106_pair_limitation_propagation import (
                _new_checker,
            )

            checker = _new_checker(connector)
            original = checker.check_from_binaries

            def _with_deadline(*args, **kwargs):
                return original(*args, analysis_deadline=DeadlinePolicy(budget_seconds=100, clock=clock), **kwargs)

            checker.check_from_binaries = _with_deadline
        return _run_pair(
            analyze=lambda self, name, timeout: analysis1 if name == "func1" else analysis2,
            stage_plan=_healthy_stage_plan, connector=connector, checker=checker,
        )

    baseline = _run(False)
    crossed = _run(True)
    assert crossed.final_outcome == baseline.final_outcome
    assert [r.reason_id for r in crossed.unknown_reasons] == [r.reason_id for r in baseline.unknown_reasons]
    assert BUDGET_REASON not in [r.reason_id for r in crossed.unknown_reasons]
    assert crossed.decision_receipt is not None
    assert "analysis_limitation" not in (crossed.diagnostics.get("failures") or {})


# ---------------------------------------------------------------------------
# E6 / E14: supervisor の TIMEOUT と期限の UNKNOWN は別物。止められない worker は TIMEOUT
# ---------------------------------------------------------------------------


def test_e6_a_deadline_unknown_resolves_as_unknown_not_as_a_process_timeout(tmp_path):
    from scripts.function_tracer_pcode.tests.unit._supervisor_child import (
        Checkpoint,
        ChildScript,
        Envelope,
        Exit,
    )
    from scripts.function_tracer_pcode.tests.unit._supervisor_process import run_supervisor
    from scripts.function_tracer_pcode.tests.unit._supervisor_support import classify, supervisor_case
    from scripts.function_tracer_pcode.authority.process import store_layout as layout

    script = ChildScript((Checkpoint(), Envelope("UNKNOWN", driver="deadline"), Exit()))
    with supervisor_case(tmp_path, script, allow_child_exit_resolution=True) as case:
        run = run_supervisor(case)
        classified = classify(run)
    assert run.projection["status"] == "RESOLVED"
    assert run.projection["child_returncode"] == 2  # UNKNOWN の exit code（TIMEOUT は 3）
    assert classified["canonical_outcome"] == "UNKNOWN"
    assert classified["supervisor_status"] == "RESOLVED"
    # その UNKNOWN の理由は解析の期限（authority の cause として封印された結果に載る）
    envelope = (case.store_directory / layout.RESULT_ENVELOPE).read_text(encoding="utf-8")
    assert BUDGET_REASON in envelope


def test_e14_a_worker_that_cannot_be_stopped_ends_as_a_durable_timeout_not_unknown(tmp_path):
    from scripts.function_tracer_pcode.tests.unit._supervisor_child import (
        ChildScript,
        StuckSolverWorker,
    )
    from scripts.function_tracer_pcode.tests.unit._supervisor_process import run_supervisor
    from scripts.function_tracer_pcode.tests.unit._supervisor_support import classify, supervisor_case

    script = ChildScript((StuckSolverWorker(budget=3.0),))
    with supervisor_case(tmp_path, script, timeout=12.0) as case:
        started = time.monotonic()
        run = run_supervisor(case)
        classified = classify(run)
        records = case.records.root
        detected = sorted(path.name for path in records.rglob("solver_worker_not_stoppable.json"))
        worker_started = sorted(path.name for path in records.rglob("stuck_worker_started.json"))
    assert worker_started, "the blocking worker never started"
    assert detected, "the runner did not detect the worker it could not stop"
    assert run.projection["status"] == "TIMEOUT"
    assert classified["canonical_outcome"] == "TIMEOUT"
    assert classified["supervisor_status"] == "TIMEOUT"
    # 結果を出していない（UNKNOWN を偽って報告しない）
    log = case.pair_log.read_text(errors="replace") if case.pair_log.exists() else ""
    assert "EQUIVALENCE_RESULT_JSON_BEGIN" not in log
    assert time.monotonic() - started >= 12.0


# ---------------------------------------------------------------------------
# E13: targeted pair の受理判定（機械化）
# ---------------------------------------------------------------------------


def _observation(**fields):
    base = dict(
        key="ell|rd|B12|B16", guarantee_class=CLASS_A, before_outcome="TIMEOUT",
        after_outcome="UNKNOWN", after_reasons=(BUDGET_REASON,), limitation_site="identity_graph",
        pair_stop_state="PAIR_TERMINAL_DEADLINE", stack_snapshot=True,
        # PR-106-B review 1: "before was TIMEOUT" counts as a process TIMEOUT only
        # with the termination evidence that says so
        before_timeout_kind="process_wall_clock",
    )
    base.update(fields)
    return TargetObservation(**base)


@pytest.mark.parametrize(("fields", "verdict", "improvement", "violation"), [
    ({}, VERDICT_ACCEPTED, True, False),
    ({"after_outcome": "EQUIVALENT", "after_truth": TRUTH_CONSISTENT, "after_reasons": ()}, VERDICT_ACCEPTED, True, False),
    ({"after_outcome": "EQUIVALENT", "after_truth": TRUTH_CONTRADICTED, "after_reasons": ()}, VERDICT_NOT_ACCEPTED, False, True),
    ({"after_outcome": "TIMEOUT", "after_reasons": ()}, VERDICT_NOT_ACCEPTED, False, False),
    ({"after_outcome": "ERROR", "after_reasons": ()}, VERDICT_NOT_ACCEPTED, False, False),
    ({"after_reasons": ()}, VERDICT_NOT_ACCEPTED, False, False),
    ({"limitation_evidence": ("worker_stop=not_stoppable",)}, VERDICT_NOT_ACCEPTED, False, False),
    ({"before_outcome": "UNKNOWN"}, VERDICT_ACCEPTED, False, False),
    # a TIMEOUT the checker resolved itself, or one without evidence, is not a process TIMEOUT
    ({"before_timeout_kind": "child_solver_timeout"}, VERDICT_ACCEPTED, False, False),
    ({"before_timeout_kind": "unknown"}, VERDICT_ACCEPTED, False, False),
    ({"before_timeout_kind": None}, VERDICT_ACCEPTED, False, False),
    ({"before_timeout_kind": "both_signals"}, VERDICT_ACCEPTED, True, False),
    ({"guarantee_class": CLASS_B, "after_outcome": "TIMEOUT", "after_reasons": (), "after_timeout_kind": "process_wall_clock"}, VERDICT_FALLBACK_SAFE, False, False),
    ({"guarantee_class": CLASS_B, "after_outcome": "TIMEOUT", "after_reasons": (), "after_timeout_kind": "child_solver_timeout"}, VERDICT_FALLBACK_SAFE, False, False),
    ({"guarantee_class": CLASS_B, "limitation_evidence": ("worker_stop=not_stoppable",)}, VERDICT_FALLBACK_SAFE, False, False),
    ({"guarantee_class": CLASS_B}, VERDICT_FALLBACK_SAFE, False, False),
    ({"guarantee_class": CLASS_B, "after_outcome": "ERROR", "after_reasons": ()}, VERDICT_UNSAFE, False, False),
    ({"guarantee_class": CLASS_B, "after_outcome": "NOT_EQ", "after_truth": TRUTH_CONTRADICTED}, VERDICT_UNSAFE, False, True),
])
def test_e13_target_acceptance_rules(fields, verdict, improvement, violation):
    row = classify_target(_observation(**fields))
    assert (row.verdict, row.improvement, row.soundness_violation) == (verdict, improvement, violation)


def test_e13_completion_needs_every_class_a_accepted_and_at_least_one_improvement():
    accepted = classify_target(_observation())
    no_gain = classify_target(_observation(before_outcome="UNKNOWN"))
    timeout = classify_target(_observation(after_outcome="TIMEOUT", after_reasons=()))
    fallback = classify_target(_observation(guarantee_class=CLASS_B, after_outcome="TIMEOUT", after_reasons=()))
    assert summarize([accepted, fallback]).complete is True
    assert summarize([no_gain, fallback]).complete is False  # 改善 0 件
    assert summarize([accepted, timeout]).complete is False  # Class A の rc143
    assert summarize([fallback]).complete is False  # Class B だけは改善にならない
    assert summarize([]).complete is False
    with pytest.raises(ValueError):
        classify_target(_observation(guarantee_class="C"))


# ---------------------------------------------------------------------------
# fitness: 規則の owner は 1 つ
# ---------------------------------------------------------------------------


def _production_modules():
    for path in sorted(PACKAGE_ROOT.rglob("*.py")):
        relative = path.relative_to(PACKAGE_ROOT).as_posix()
        if relative.startswith("tests/"):
            continue
        yield relative, ast.parse(path.read_text(encoding="utf-8"))


def test_decompilation_goes_through_the_deadline_entry_only():
    """broker の `decompile_function` を直接呼ぶ production code は broker 自身だけ。"""
    offenders = []
    for relative, tree in _production_modules():
        if relative == "ghidra/decompilation_broker.py":
            continue
        for node in ast.walk(tree):
            if isinstance(node, ast.Call):
                name = getattr(node.func, "id", None) or getattr(node.func, "attr", None)
                if name == "decompile_function" and not isinstance(node.func, ast.Attribute):
                    offenders.append(f"{relative}:{node.lineno}")
            if isinstance(node, ast.ImportFrom) and node.module and node.module.endswith("decompilation_broker"):
                if any(alias.name == "decompile_function" for alias in node.names):
                    offenders.append(f"{relative}:{node.lineno} imports decompile_function")
    assert offenders == []


def test_checkpoints_only_use_the_deadline_api():
    """期限を読むのは `core.deadline` の API だけ（`time.monotonic` と期限を比べる別実装を作らない）。"""
    offenders = []
    for relative, tree in _production_modules():
        if relative == "core/deadline.py":
            continue
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom) and node.module and node.module.endswith("core.deadline"):
                names = {alias.name for alias in node.names}
                if "Deadline" in names or "_ACTIVE_DEADLINE" in names:
                    offenders.append(f"{relative}:{node.lineno}: {sorted(names)}")
    assert offenders == []


def test_the_production_boundary_closes_the_analysis_before_finalizing():
    """legacy workflow の直後（G5 の try の中）に解析の完了点の checkpoint がある。"""
    from scripts.function_tracer_pcode.authority.lifecycle import production_boundary

    source = pathlib.Path(production_boundary.__file__).read_text(encoding="utf-8")
    tree = ast.parse(source)
    gate = next(
        node for node in ast.walk(tree)
        if isinstance(node, ast.FunctionDef) and node.name == "_run_legacy_with_pair_gate"
    )
    tries = [node for node in ast.walk(gate) if isinstance(node, ast.Try)]
    body_calls = [
        ast.unparse(stmt) for node in tries for stmt in node.body
    ]
    assert any("deadline_checkpoint(ANALYSIS_COMPLETE_STAGE)" in text for text in body_calls)


# ---------------------------------------------------------------------------
# 再生では通らない checkpoint（stage の境界ごとに 1 件ずつ）
# ---------------------------------------------------------------------------


def _expired(stage_under_test):
    """`stage_under_test` を即座に打ち切る期限（hot な境界も 1 回目で時計を読む）。"""

    from scripts.function_tracer_pcode.core.deadline import deadline_scope
    from scripts.function_tracer_pcode.core.errors import pair_failure_scope
    from contextlib import ExitStack

    clock = ShiftedClock()
    stack = ExitStack()
    ledger = stack.enter_context(pair_failure_scope((stage_under_test,), None))
    stack.enter_context(deadline_scope(DeadlinePolicy(budget_seconds=1, clock=clock, poll_interval=1)))
    clock.jump(5)
    return stack, ledger


def test_e5_a_sat_retry_is_not_started_after_the_deadline():
    from types import SimpleNamespace

    from scripts.function_tracer_pcode.checker import workflow

    checker = Mock()
    checker.phase_handler.should_fix_return_type.return_value = True
    ctx = SimpleNamespace(analysis1=object(), analysis2=object())
    result = SimpleNamespace(is_equivalent=False)
    stack, ledger = _expired("phase_retry")
    with stack:
        with pytest.raises(DeadlineExceeded) as raised:
            workflow._maybe_retry_sat_return_type_fix(
                checker, ctx, result, Mock(), 0, 1, object(), object(), True,
            )
        assert ledger.stop_state().value == "PAIR_TERMINAL_DEADLINE"
    assert raised.value.site == workflow.PHASE_RETRY_STAGE
    checker.phase_handler.run_phase2_return_type_fix.assert_not_called()
    checker._selective_reanalysis_and_check.assert_not_called()


def test_the_identity_graph_of_a_large_root_stops_inside_the_walk():
    from scripts.function_tracer_pcode.analysis.condition import query_identity
    from scripts.function_tracer_pcode.core.expression import Expression

    root = Expression.constant(0, size=4)
    for index in range(40):
        root = Expression.binary_op("INT_ADD", root, Expression.constant(index + 1, size=4))
    stack, _ledger = _expired("identity_graph")
    with stack:
        with pytest.raises(DeadlineExceeded) as raised:
            query_identity._build_root_graph(root)
    assert raised.value.site == query_identity.IDENTITY_GRAPH_STAGE
    assert "boundary=poll" in raised.value.evidence_refs


def test_the_expander_stops_before_expanding_an_operation():
    from scripts.function_tracer_pcode.semantics.transform import expander as expander_module
    from scripts.function_tracer_pcode.semantics.transform.expander import ExpressionExpander

    expander = object.__new__(ExpressionExpander)
    pcode_op = Mock()
    stack, _ledger = _expired("expand")
    with stack:
        with pytest.raises(DeadlineExceeded) as raised:
            ExpressionExpander._expand_input_operation(expander, pcode_op, [], 0)
    assert raised.value.site == expander_module.EXPAND_STAGE
    pcode_op.getMnemonic.assert_not_called()  # 展開を始めていない


def test_the_tracer_stops_before_tracing_an_operation():
    from scripts.function_tracer_pcode.analysis import tracer as tracer_module
    from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer

    tracer = object.__new__(PcodeTracer)
    tracer._trace_cache = {}
    tracer._trace_stack = set()
    tracer._get_op_key = lambda op: ("op", 1)
    tracer._trace_pcode_op_internal = Mock()
    stack, _ledger = _expired("trace_pcode")
    with stack:
        with pytest.raises(DeadlineExceeded) as raised:
            PcodeTracer._trace_pcode_op(tracer, Mock(), 0)
    assert raised.value.site == tracer_module.TRACE_PCODE_STAGE
    tracer._trace_pcode_op_internal.assert_not_called()
    assert tracer._trace_stack == set()  # 途中の状態を残さない


def test_failure_result_conversion_never_trips_the_deadline(monkeypatch):
    """failure を結果に変える処理（`checker.pair_execution`）は確定処理: 途中の境界で止めない。"""
    from scripts.function_tracer_pcode.checker import pair_execution
    from scripts.function_tracer_pcode.core import deadline as deadline_module
    from scripts.function_tracer_pcode.core.errors import pending_pair_failure

    reached = []

    def _build(kind, checker, failure, **common):
        deadline_module.checkpoint("result_conversion")  # 変換の中から境界に触れても
        reached.append(kind)
        from types import SimpleNamespace

        return SimpleNamespace()

    monkeypatch.setattr(pair_execution, "_build_result_for", _build)
    stack, _ledger = _expired("result_conversion")
    with stack:
        with pytest.raises(DeadlineExceeded):
            deadline_module.checkpoint("solver")  # 打ち切り（台帳に 1 件）
        failure = pending_pair_failure()
        pair_execution.pair_failure_result(
            Mock(), failure, function_name1="f", function_name2="f",
            binary1_name="l", binary2_name="r", start_time=time.time(),
        )
    assert len(reached) == 1
