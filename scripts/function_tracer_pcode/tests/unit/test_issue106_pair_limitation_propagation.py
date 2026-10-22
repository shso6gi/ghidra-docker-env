# -*- coding: utf-8 -*-
"""Issue #106 PR-106-0: pair 単位の限界伝搬（E0a〜E0r）。

このPRは **新しい限界の raise 箇所を作らない**。作るのは「限界が起きたら pair
全体をどう止め、どう結果化するか」の土台だけなので、test は

* 台帳（`PairExecutionControl`）の lifecycle と共有条件
* G1〜G5 の各経路で限界 / 内部バグが失われないこと
* 限界の後に **新しい意味解析** を始めないこと（phase / conditional lane）
* 逆に **確定処理**（`connector.finish` / receipt / serialization）は続くこと
* 帰属できた限界は reason 付き UNKNOWN、帰属できなければ ERROR（fail-closed）
* 限界が無い pair の挙動が従来と同じであること

を固定する。深部で `except Exception` に握り潰される場合を明示的に作るのは、
「例外が消えても台帳には残る」という契約が本 PR の中心だから。
"""

from __future__ import annotations

import ast
import pathlib
from types import SimpleNamespace
from unittest.mock import Mock, patch

import pytest

from scripts.function_tracer_pcode.authority.lifecycle import production_boundary
from scripts.function_tracer_pcode.checker.checker import (
    _CHECK_SITE,
    EquivalenceChecker,
)
from scripts.function_tracer_pcode.checker.pair_execution import (
    PAIR_FAILURE_IDENTITY_ATTRIBUTE,
)
from scripts.function_tracer_pcode.checker.phases.handler import (
    PhaseHandler,
    PhaseID,
    PhaseResult,
)
from scripts.function_tracer_pcode.core.errors import (
    AnalysisFailureError,
    AnalysisLimitation,
    DeadlineExceeded,
    ExpressionCycleError,
    FrozenExpressionError,
    InternalError,
    PairExecutionControl,
    PairFailureKind,
    PairStopState,
    current_pair_ledger,
    pair_failure_scope,
    raise_limitation,
    record_internal_bug,
    reset_pair_failure_scopes,
)
from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
    production_signal_scope,
)
from scripts.function_tracer_pcode.smt import SolverStatus
from scripts.function_tracer_pcode.tests.unit.test_issue125_limitation_finalization import (
    _connector,
    _sat_blocker,
)
from scripts.function_tracer_pcode.tests.unit.test_monolithic_region_split import (
    _analysis,
)

from conftest import MockProgram, create_mock_analysis, create_mock_result


BUDGET_REASON = DeadlineExceeded.REASON_ID
PACKAGE_ROOT = pathlib.Path(__file__).resolve().parents[2]


# ---------------------------------------------------------------------------
# harness
# ---------------------------------------------------------------------------

@pytest.fixture(autouse=True)
def _clean_pair_ledger_stack():
    """test 間で台帳 stack を持ち越さない（本番の pair 冒頭 reset と同じ）。"""
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


def _budget_limitation(site="trace_returns", target=("left", "right")):
    return DeadlineExceeded(
        "analysis budget exhausted", site=site, target_key=target,
        evidence_refs=("issue106-budget",),
    )


def _plain_limitation(site="expand", target=("left", "right")):
    """deadline ではない限界（stop state を `PAIR_TERMINAL_LIMITATION` にする）。

    sealed registry にある解析限界 reason は 1 つだけなので reason id は共有し、
    型と stop state だけを変えて「時間予算以外の限界」を作る。
    """
    return AnalysisLimitation(
        BUDGET_REASON, "expression budget exhausted", site=site, target_key=target,
        evidence_refs=("issue106-size",),
    )


def _new_checker(connector):
    checker = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5,
        canonical_decision_cutover=False,
    )
    if connector is not None:
        checker.v2_dual_write_pilot_connector = connector
    else:
        checker.v2_dual_write_pilot_connector = None
    return checker


def _run_pair(
    *,
    analyze,
    stage_plan,
    connector=None,
    checker=None,
    function_name1="func1",
    function_name2="func2",
    retry_with_type_fix=False,
    phase_handler=None,
    binary_ids=(None, None),
):
    """1 pair ぶんを `check_from_binaries` の本物の制御フローで走らせる。"""
    checker = checker if checker is not None else _new_checker(connector)
    if phase_handler is not None:
        checker.phase_handler = phase_handler
    program1 = MockProgram(name="binary1.exe", architecture="x86:LE:64:default")
    program2 = MockProgram(name="binary2.exe", architecture="x86:LE:64:default")
    with patch(
        "scripts.function_tracer_pcode.analysis.returns.analyzer."
        "ReturnAnalyzer.analyze_function_by_name",
        analyze,
    ):
        with patch.object(checker, "_run_stage_plan", side_effect=stage_plan):
            with patch(
                "scripts.function_tracer_pcode.checker.checker.TypeFixer"
            ) as fixer:
                fixer.side_effect = lambda *args, **kwargs: Mock()
                return checker.check_from_binaries(
                    program1=program1,
                    program2=program2,
                    function_name1=function_name1,
                    function_name2=function_name2,
                    decompile_timeout=60,
                    retry_with_type_fix=retry_with_type_fix,
                    binary1_id=binary_ids[0],
                    binary2_id=binary_ids[1],
                )


def _analyses():
    return (
        create_mock_analysis("func1", return_type="int"),
        create_mock_analysis("func2", return_type="int"),
    )


def _emit_one_production_signal():
    """健全な pair でも event stream を空にしない（`finish` は空 stream を拒む）。

    この PR の対象は限界の伝搬なので、対照群の pair には既存の producer 信号を
    1 件だけ出して「普通に判定が出る pair」を作る。
    """
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        emit_sat_safety_signal,
    )

    emit_sat_safety_signal(
        _sat_blocker(), producer_site_manifest_id="sat-safety-blocker-observed",
    )


def _equivalent_stage_plan(*_args, **_kwargs):
    return create_mock_result(is_equivalent=True, solver_status=SolverStatus.UNSAT)


def _healthy_stage_plan(*_args, **_kwargs):
    """限界が無く、producer 信号が 1 件出る pair（対照群）。"""
    _emit_one_production_signal()
    return create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)


def _reason_ids(result):
    return [reason.reason_id for reason in result.unknown_reasons]


def _failure_block(result, kind):
    return (result.diagnostics or {}).get("failures", {}).get(kind)


# ---------------------------------------------------------------------------
# E0a / E0b: 初回解析中の限界（左右それぞれ）
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "failing_side, function_name", [("function1", "func1"), ("function2", "func2")],
)
def test_e0ab_initial_analysis_limitation_becomes_unknown_with_receipt(
    failing_side, function_name,
):
    """E0a / E0b: 初回解析中の限界が reason 付き UNKNOWN + receipt になる。"""
    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        if name == function_name:
            raise_limitation(_budget_limitation(site=f"decompile:{failing_side}"))
        return analysis1 if name == "func1" else analysis2

    result = _run_pair(
        analyze=_analyze, stage_plan=_equivalent_stage_plan, connector=_connector(),
    )

    assert result.is_equivalent is None
    assert result.error_message is None
    assert result.final_outcome == "UNKNOWN"
    assert result.decision_receipt is not None
    assert _reason_ids(result) == [BUDGET_REASON]
    assert result.pair_stop_state == PairStopState.PAIR_TERMINAL_DEADLINE.value
    failure = _failure_block(result, "analysis_limitation")
    assert failure["disposition"] == "ATTRIBUTED_NEW_CAUSE"
    assert failure["site"] == f"decompile:{failing_side}"
    assert failure["pair_scoped"] is True
    assert _failure_block(result, "pair_stop_state") == (
        PairStopState.PAIR_TERMINAL_DEADLINE.value
    )


# ---------------------------------------------------------------------------
# E0c: tracer / expander 深部で raise した限界が回復経路に吸われない
# ---------------------------------------------------------------------------

def test_e0c_expander_does_not_swallow_a_limitation_from_the_tracer():
    """E0c: `_trace_operation_expression` の `except Exception` を通り抜ける。"""
    from scripts.function_tracer_pcode.semantics.transform.expander import (
        ExpressionExpander,
    )

    expander = object.__new__(ExpressionExpander)
    expander.tracer = SimpleNamespace(
        _trace_pcode_op=Mock(side_effect=_budget_limitation(site="trace_returns")),
    )

    with pytest.raises(AnalysisLimitation):
        ExpressionExpander._trace_operation_expression(
            expander, pcode_op=Mock(), conditions=[], depth=0,
        )
    # 同じ handler は通常の失敗を今までどおり None へ畳む（振る舞いを狭めない）。
    expander.tracer._trace_pcode_op = Mock(side_effect=ValueError("boom"))
    assert ExpressionExpander._trace_operation_expression(
        expander, pcode_op=Mock(), conditions=[], depth=0,
    ) is None


def test_e0c_condition_oracle_does_not_swallow_a_limitation_from_the_solver():
    """E0c: 条件 oracle の z3 区間の `except Exception` を通り抜ける。"""
    from scripts.function_tracer_pcode.analysis.condition.smt_oracle import (
        ConditionSMTOracle,
    )

    limitation = _budget_limitation(site="condition_oracle")
    fake_z3 = SimpleNamespace(Solver=Mock(side_effect=limitation), Context=Mock())
    with patch.object(ConditionSMTOracle, "_z3", fake_z3):
        with patch.object(
            ConditionSMTOracle, "_build_script",
            classmethod(lambda cls, conditions, **_kwargs: (True, "(check-sat)")),
        ):
            with pytest.raises(AnalysisLimitation):
                ConditionSMTOracle.conjunction_is_unsat([], use_cache=False)

            fake_z3.Solver = Mock(side_effect=ValueError("boom"))
            assert ConditionSMTOracle.conjunction_is_unsat(
                [], use_cache=False,
            ) is None


# ---------------------------------------------------------------------------
# E0d / E0e: 深部で握り潰されても台帳に残る
# ---------------------------------------------------------------------------

def test_e0d_a_swallowed_limitation_still_becomes_the_same_unknown():
    """E0d: `except Exception: pass` に握り潰されても UNKNOWN と reason は同じ。"""
    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        if name == "func1":
            try:
                raise_limitation(_budget_limitation(site="trace_returns"))
            except Exception:  # 深部の包括捕捉を再現する（test 側の模擬）
                pass
        return analysis1 if name == "func1" else analysis2

    result = _run_pair(
        analyze=_analyze, stage_plan=_equivalent_stage_plan, connector=_connector(),
    )

    assert result.is_equivalent is None and result.error_message is None
    assert _reason_ids(result) == [BUDGET_REASON]
    assert result.final_outcome == "UNKNOWN"


def test_e0e_a_swallowed_limitation_wins_over_the_early_return():
    """E0e: 握り潰しで analysis が `None` になっても ERROR にはしない。"""
    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        if name == "func1":
            try:
                raise_limitation(_budget_limitation(site="decompile"))
            except Exception:
                return None  # 握り潰した結果、解析結果が無いまま戻る
        return analysis2

    result = _run_pair(
        analyze=_analyze, stage_plan=_equivalent_stage_plan, connector=_connector(),
    )

    assert result.error_message is None
    assert result.failure_status is None
    assert _reason_ids(result) == [BUDGET_REASON]
    assert result.final_outcome == "UNKNOWN"


# ---------------------------------------------------------------------------
# E0f: phase 再解析中の限界
# ---------------------------------------------------------------------------

def test_e0f_limitation_during_phase_reanalysis_is_not_lost():
    """E0f: P1 の `selective_reanalysis_and_check` 中の限界も UNKNOWN になる。"""
    analysis1, analysis2 = _analyses()
    calls = {"func1": 0, "func2": 0}

    def _analyze(self, name, timeout):
        calls[name] += 1
        if name == "func1" and calls["func1"] == 2:
            raise_limitation(_budget_limitation(site="phase_reanalysis"))
        return analysis1 if name == "func1" else analysis2

    def _stage_plan(*_args, **_kwargs):
        result = create_mock_result(
            is_equivalent=None, solver_status=SolverStatus.UNKNOWN,
        )
        return result

    phase_handler = Mock(spec=PhaseHandler)
    phase_handler.execute_phase.return_value = PhaseResult(
        PhaseID.P1_SIGNEDNESS, applied=True, retry_name="signedness_fix",
        changed_binary1=True, changed_binary2=False,
    )
    phase_handler.should_retry.return_value = True
    phase_handler.get_retry_reason.return_value = "UNKNOWN"

    result = _run_pair(
        analyze=_analyze, stage_plan=_stage_plan, connector=_connector(),
        retry_with_type_fix=True, phase_handler=phase_handler,
    )

    assert calls["func1"] == 2, "P1 の再解析まで到達していない（test が空振り）"
    assert result.is_equivalent is None and result.error_message is None
    assert _reason_ids(result) == [BUDGET_REASON]
    assert result.pair_stop_state == PairStopState.PAIR_TERMINAL_DEADLINE.value


def test_e0f_phase_loop_stops_after_a_swallowed_limitation():
    """E0f 補: 限界が握り潰されても次 phase の再解析を始めない。

    限界は **初回解析より後**（stage plan の中）で握り潰させる。解析中に置くと
    G1 がその場で例外に戻してしまい、phase loop の停止そのものを通らない。
    """
    analysis1, analysis2 = _analyses()
    calls = {"func1": 0, "func2": 0}

    def _analyze(self, name, timeout):
        calls[name] += 1
        return analysis1 if name == "func1" else analysis2

    def _stage_plan(*_args, **_kwargs):
        try:
            raise_limitation(_plain_limitation(site="effect_summary"))
        except Exception:
            pass
        return create_mock_result(
            is_equivalent=None, solver_status=SolverStatus.UNKNOWN,
        )

    phase_handler = Mock(spec=PhaseHandler)
    phase_handler.execute_phase.return_value = PhaseResult(
        PhaseID.P1_SIGNEDNESS, applied=True, retry_name="signedness_fix",
        changed_binary1=True, changed_binary2=False,
    )
    phase_handler.should_retry.return_value = True
    phase_handler.get_retry_reason.return_value = "UNKNOWN"

    result = _run_pair(
        analyze=_analyze, stage_plan=_stage_plan, connector=_connector(),
        retry_with_type_fix=True, phase_handler=phase_handler,
    )

    # 初回解析の 2 回だけ。P1 の再解析（3 回目）は始まらない。
    assert calls == {"func1": 1, "func2": 1}
    assert phase_handler.execute_phase.call_count == 0
    assert result.pair_stop_state == PairStopState.PAIR_TERMINAL_LIMITATION.value


def test_e0f_sat_retries_stop_inside_the_phase_that_went_terminal():
    """E0f 補: phase の途中で terminal になったら SAT 後の再試行も始めない。

    phase の先頭 gate では止められない区画（4-C / 4-A）を通るので、
    phase 内側の gate が無いと型修正リトライが走ってしまう。
    """
    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        return analysis1 if name == "func1" else analysis2

    def _stage_plan(*_args, **_kwargs):
        try:
            raise_limitation(_plain_limitation(site="query_build"))
        except Exception:
            pass
        return create_mock_result(
            is_equivalent=False, solver_status=SolverStatus.SAT,
        )

    phase_handler = Mock(spec=PhaseHandler)
    phase_handler.should_fix_return_type.return_value = True
    phase_handler.should_retry.return_value = False
    phase_handler.get_retry_reason.return_value = "NOT_EQUIVALENT"

    result = _run_pair(
        analyze=_analyze, stage_plan=_stage_plan, connector=_connector(),
        retry_with_type_fix=True, phase_handler=phase_handler,
    )

    # SAT の後の再試行（P4C / P4A tail）は始めない。
    assert phase_handler.should_fix_return_type.call_count == 0
    assert phase_handler.execute_phase.call_count == 0
    assert result.pair_stop_state == PairStopState.PAIR_TERMINAL_LIMITATION.value
    assert result.is_equivalent is None, "限界の残った pair を NOT_EQ で返さない"


def test_e0f_g2_gate_turns_a_swallowed_limitation_into_unknown_inside_check():
    """G2: `check()` の中で握り潰された限界を、結果を組む直前に拾い直す。

    `check()` の内側だけを通す（stage plan を差し替えない）ので、G2 が無ければ
    monolithic strategy が同一 analysis 2 件から EQUIVALENT を返してしまう。
    """
    connector = _connector()
    session = connector.begin({"case": "issue106-g2"})
    checker = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5,
        canonical_decision_cutover=False,
    )
    checker._active_v2_dual_write_pilot_session = session
    pair = ("b1", "b2", None, None, "L", "R")

    with production_signal_scope(session):
        with pair_failure_scope(pair, session.identity.result_occurrence_id):
            try:
                raise_limitation(_budget_limitation(site="expand"))
            except Exception:
                pass
            result = checker.check(
                _analysis("left", 7), _analysis("right", 7), "L", "R",
            )

    assert result.is_equivalent is None
    assert result.error_message is None
    assert _reason_ids(result) == [BUDGET_REASON]
    assert _failure_block(result, "analysis_limitation")["site"] == "expand"


def test_a_healthy_check_without_a_limitation_still_reaches_its_verdict():
    """G2 対照: 台帳が空なら `check()` は従来どおり判定まで進む。"""
    connector = _connector()
    session = connector.begin({"case": "issue106-g2-control"})
    checker = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5,
        canonical_decision_cutover=False,
    )
    checker._active_v2_dual_write_pilot_session = session
    pair = ("b1", "b2", None, None, "L", "R")

    with production_signal_scope(session):
        with pair_failure_scope(pair, session.identity.result_occurrence_id):
            result = checker.check(
                _analysis("left", 7), _analysis("right", 7), "L", "R",
            )

    assert result.is_equivalent is True
    assert result.pair_stop_state is None


# ---------------------------------------------------------------------------
# E0g: 再帰的 check()
# ---------------------------------------------------------------------------

def test_e0g_recursive_check_reports_one_unknown_with_one_cause():
    """E0g: 同 pair の再帰 `check()` で 2 回限界が出ても cause は 1 件。"""
    from scripts.function_tracer_pcode.checker import checker as checker_module

    analysis1, analysis2 = _analyses()
    seen_ledgers = []

    def _analyze(self, name, timeout):
        return analysis1 if name == "func1" else analysis2

    def _stage_plan(a1, a2, *args, **kwargs):
        checker = stage_checker["value"]
        last = None
        for _ in range(2):
            seen_ledgers.append(current_pair_ledger())
            last = checker.check(a1, a2, "binary1.exe", "binary2.exe")
        return last

    stage_checker = {"value": None}
    checker = _new_checker(_connector())
    stage_checker["value"] = checker

    def _raise(*_args, **_kwargs):
        raise_limitation(_budget_limitation(site="result_assembly"))

    with patch.object(
        checker_module, "assemble_equivalence_result", side_effect=_raise,
    ):
        result = _run_pair(
            analyze=_analyze, stage_plan=_stage_plan, checker=checker,
        )

    assert len(seen_ledgers) == 2
    assert seen_ledgers[0] is seen_ledgers[1] is not None
    # 同じ `(site, target_key)` の再 raise は 1 件に畳む。
    assert seen_ledgers[0].recorded_failure_count() == 1
    assert result.is_equivalent is None and result.error_message is None
    assert _reason_ids(result) == [BUDGET_REASON]
    assert len(result.canonical_c_active_base) == 1


# ---------------------------------------------------------------------------
# E0h: 次の pair へ漏らさない
# ---------------------------------------------------------------------------

def test_e0h_the_next_pair_in_the_same_process_starts_with_an_empty_ledger():
    """E0h: 限界 pair のあと、同じ process の次 pair は EQ になれる。"""
    analysis1, analysis2 = _analyses()
    connector = _connector()

    def _failing(self, name, timeout):
        if name == "func1":
            raise_limitation(_budget_limitation(site="decompile"))
        return analysis2

    def _healthy(self, name, timeout):
        return analysis1 if name == "func1" else analysis2

    first = _run_pair(
        analyze=_failing, stage_plan=_equivalent_stage_plan, connector=connector,
    )
    assert first.is_equivalent is None
    assert _reason_ids(first) == [BUDGET_REASON]

    assert current_pair_ledger() is None
    second = _run_pair(
        analyze=_healthy, stage_plan=_healthy_stage_plan, connector=_connector(),
    )
    # 2 本目は前の pair の限界を引き継がない: 台帳由来の reason も stop state も無い。
    assert second.error_message is None
    assert second.pair_stop_state is None
    assert BUDGET_REASON not in _reason_ids(second)
    assert _failure_block(second, "analysis_limitation") is None


# ---------------------------------------------------------------------------
# E0i: 限界のあとに成立した EQ を採らない
# ---------------------------------------------------------------------------

def test_e0i_an_equivalence_closure_after_a_limitation_is_discarded():
    """E0i: 台帳に限界があるのに EQ が出たら UNKNOWN へ差し替える。"""
    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        return analysis1 if name == "func1" else analysis2

    def _stage_plan(*_args, **_kwargs):
        try:
            raise_limitation(_plain_limitation(site="query_build"))
        except Exception:
            pass
        return create_mock_result(
            is_equivalent=True, solver_status=SolverStatus.UNSAT,
        )

    result = _run_pair(
        analyze=_analyze, stage_plan=_stage_plan, connector=_connector(),
    )

    assert result.is_equivalent is None
    assert result.final_outcome == "UNKNOWN"
    assert _reason_ids(result) == [BUDGET_REASON]
    assert result.pair_stop_state == PairStopState.PAIR_TERMINAL_LIMITATION.value


def test_a_swallowed_limitation_is_reported_on_an_otherwise_unknown_pair():
    """E0i 補: 既に UNKNOWN の pair でも、限界の reason を落とさない。"""
    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        return analysis1 if name == "func1" else analysis2

    def _stage_plan(*_args, **_kwargs):
        try:
            raise_limitation(_plain_limitation(site="query_build"))
        except Exception:
            pass
        return create_mock_result(
            is_equivalent=None, solver_status=SolverStatus.UNKNOWN,
        )

    result = _run_pair(
        analyze=_analyze, stage_plan=_stage_plan, connector=_connector(),
    )

    assert result.final_outcome == "UNKNOWN"
    # G3 で 1 回だけ組み直す。G4-a は同じ reason を見て作り直さない。
    assert _reason_ids(result) == [BUDGET_REASON]
    assert result.pair_stop_state == PairStopState.PAIR_TERMINAL_LIMITATION.value


def test_a_limitation_does_not_downgrade_an_existing_error_result():
    """限界があっても、基盤側の ERROR を意味的な UNKNOWN へ格下げしない。"""
    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        return analysis1 if name == "func1" else analysis2

    def _stage_plan(*_args, **_kwargs):
        try:
            raise_limitation(_plain_limitation(site="query_build"))
        except Exception:
            pass
        return create_mock_result(
            is_equivalent=None, error_message="function_lookup_miss",
        )

    result = _run_pair(
        analyze=_analyze, stage_plan=_stage_plan, connector=_connector(),
    )

    assert result.final_outcome == "ERROR"
    assert result.error_message == "function_lookup_miss"
    # 止めた事実は残す（判定は置き換えない）。
    assert result.pair_stop_state == PairStopState.PAIR_TERMINAL_LIMITATION.value


def test_every_stop_state_allows_finalization():
    """解析の打ち切りと確定処理の停止は別物（全 stop state で確定は許可）。"""
    assert [state for state in PairStopState if not state.allows_finalization()] == []
    assert [
        state for state in PairStopState if state.allows_semantic_analysis()
    ] == [PairStopState.NONE]


# ---------------------------------------------------------------------------
# E0j: 静的契約（回復可能 tuple / hot path の再 raise）
# ---------------------------------------------------------------------------

#: 限界の raise 箇所（PR-106-A 以降の checkpoint 置き場）へ入る呼び出し。
HOT_PATH_CALLS = frozenset({
    "_trace_pcode_op", "_trace_varnode", "analyze_function",
    "conjunction_is_unsat", "object_centric_is_contradiction",
})

#: 呼び出し名では拾えない hot path（限界の発生源そのもの / producer 側）。
HOT_PATH_QUALNAMES = frozenset({
    ("analysis/condition/smt_oracle.py", "ConditionSMTOracle.conjunction_is_unsat"),
    ("analysis/tracer.py", "PcodeTracer._trace_pcode_op_internal"),
    ("proof/strategies/pairwise_services/orchestration.py", "_impl_check"),
})

#: 包括捕捉の本体が必ず再 raise で終わる module（別の形で契約を満たす）。
HOT_PATH_RERAISING_MODULES = frozenset({"analysis/returns/lifecycle.py"})

BROAD_NAMES = frozenset({"Exception", "BaseException"})
FORBIDDEN_IN_RECOVERABLE = frozenset({
    "Exception", "BaseException", "AnalysisFailureError", "AnalysisLimitation",
    "DeadlineExceeded", "FrozenExpressionError", "ExpressionCycleError",
})


def _source_modules():
    for path in sorted(PACKAGE_ROOT.rglob("*.py")):
        rel = path.relative_to(PACKAGE_ROOT).as_posix()
        if rel.startswith("tests/"):
            continue
        yield rel, path, ast.parse(path.read_text(encoding="utf-8"))


def _is_broad(handler):
    node = handler.type
    if node is None:
        return True
    if isinstance(node, ast.Name):
        return node.id in BROAD_NAMES
    if isinstance(node, ast.Tuple):
        return any(
            isinstance(e, ast.Name) and e.id in BROAD_NAMES for e in node.elts
        )
    return False


def _guards_limitation(try_node):
    for handler in try_node.handlers:
        node = handler.type
        names = []
        if isinstance(node, ast.Name):
            names = [node.id]
        elif isinstance(node, ast.Tuple):
            names = [e.id for e in node.elts if isinstance(e, ast.Name)]
        if "AnalysisLimitation" in names:
            return True
    return False


def _reraises(handler):
    return (
        bool(handler.body)
        and isinstance(handler.body[-1], ast.Raise)
        and handler.body[-1].exc is None
    )


def _hot_path_try_nodes(rel, tree):
    stack, found = [], []

    class Visitor(ast.NodeVisitor):
        def visit_FunctionDef(self, node):
            stack.append(node.name)
            self.generic_visit(node)
            stack.pop()

        visit_AsyncFunctionDef = visit_FunctionDef

        def visit_ClassDef(self, node):
            stack.append(node.name)
            self.generic_visit(node)
            stack.pop()

        def visit_Try(self, node):
            broad = [h for h in node.handlers if _is_broad(h)]
            if broad:
                calls = set()
                for statement in node.body:
                    for inner in ast.walk(statement):
                        if not isinstance(inner, ast.Call):
                            continue
                        func = inner.func
                        name = (
                            func.attr if isinstance(func, ast.Attribute)
                            else func.id if isinstance(func, ast.Name) else None
                        )
                        if name in HOT_PATH_CALLS:
                            calls.add(name)
                on_hot_path = bool(calls) or (rel, ".".join(stack)) in HOT_PATH_QUALNAMES
                if on_hot_path:
                    found.append((node, broad, ".".join(stack)))
            self.generic_visit(node)

    Visitor().visit(tree)
    return found


def test_e0j_hot_path_broad_handlers_reraise_analysis_limitations():
    """E0j: hot path の包括捕捉は限界を握り潰さない（AST で固定）。"""
    missing = []
    checked = 0
    for rel, _path, tree in _source_modules():
        for node, broad, qualname in _hot_path_try_nodes(rel, tree):
            if all(_reraises(handler) for handler in broad):
                assert rel in HOT_PATH_RERAISING_MODULES, (
                    f"{rel}:{node.lineno} は再 raise だけで終わる包括捕捉。"
                    " 意図した形なら HOT_PATH_RERAISING_MODULES に入れる。"
                )
                continue
            checked += 1
            if not _guards_limitation(node):
                missing.append(f"{rel}:{node.lineno} ({qualname})")
    assert checked >= 30, "hot path の棚卸しが空振りしている（検出規則を確認する）"
    assert missing == [], (
        "hot path の包括捕捉に `except AnalysisLimitation: raise` が無い:\n"
        + "\n".join(missing)
    )


def test_e0j_recoverable_error_tuples_never_absorb_limitations():
    """E0j: `except` に使う回復可能 tuple に限界 / 包括例外を混ぜない。"""
    offenders = []
    tuple_names = set()
    for rel, _path, tree in _source_modules():
        for node in ast.walk(tree):
            if isinstance(node, ast.ExceptHandler) and isinstance(node.type, ast.Name):
                tuple_names.add(node.type.id)
            if isinstance(node, ast.ExceptHandler) and isinstance(
                node.type, ast.Attribute
            ):
                tuple_names.add(node.type.attr)
    assert "_CONDITION_RECOVERABLE_ERRORS" in tuple_names, (
        "回復可能 tuple の棚卸しが空振りしている"
    )
    for rel, _path, tree in _source_modules():
        for node in ast.walk(tree):
            targets = []
            if isinstance(node, ast.Assign):
                targets = [t.id for t in node.targets if isinstance(t, ast.Name)]
            elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
                targets = [node.target.id]
            if not targets or not isinstance(node.value, ast.Tuple):
                continue
            if not any(name in tuple_names for name in targets):
                continue
            for element in node.value.elts:
                if isinstance(element, ast.Name) and element.id in (
                    FORBIDDEN_IN_RECOVERABLE
                ):
                    offenders.append(f"{rel}:{node.lineno} {targets[0]} -> {element.id}")
    assert offenders == [], "\n".join(offenders)


# ---------------------------------------------------------------------------
# E0k: 内部バグが限界より優先される
# ---------------------------------------------------------------------------

def test_e0k_a_swallowed_internal_bug_becomes_an_internal_exception_error():
    """E0k: 凍結違反を握り潰しても ERROR `internal_exception` になる。"""
    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        return analysis1 if name == "func1" else analysis2

    def _stage_plan(*_args, **_kwargs):
        try:
            bug = FrozenExpressionError("frozen expression was mutated")
            record_internal_bug(bug, site="core.expression.__setattr__")
            raise bug
        except Exception:
            pass
        return create_mock_result(
            is_equivalent=True, solver_status=SolverStatus.UNSAT,
        )

    result = _run_pair(
        analyze=_analyze, stage_plan=_stage_plan, connector=_connector(),
    )

    assert result.is_equivalent is None
    assert result.final_outcome == "ERROR"
    assert result.failure_status == "internal_exception"
    assert result.unknown_reasons == []
    failure = _failure_block(result, "internal_exception")
    assert failure["exception_type"] == "FrozenExpressionError"
    assert failure["site"] == "core.expression.__setattr__"
    assert result.pair_stop_state == PairStopState.INTERNAL_BUG.value


def test_e0k_an_internal_bug_outranks_a_limitation_in_the_same_pair():
    """E0k 補: 限界と内部バグが同居したら ERROR（限界の UNKNOWN に落とさない）。"""
    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        if name == "func1":
            try:
                raise_limitation(_budget_limitation(site="decompile"))
            except Exception:
                pass
            record_internal_bug(
                FrozenExpressionError("frozen"), site="core.expression.__setattr__",
            )
        return analysis1 if name == "func1" else analysis2

    def _stage_plan(*_args, **_kwargs):
        return create_mock_result(is_equivalent=True)

    result = _run_pair(
        analyze=_analyze, stage_plan=_stage_plan, connector=_connector(),
    )
    assert result.final_outcome == "ERROR"
    assert result.failure_status == "internal_exception"
    assert result.unknown_reasons == []
    assert _failure_block(result, "internal_exception")["site"] == (
        "core.expression.__setattr__"
    )
    assert result.pair_stop_state == PairStopState.INTERNAL_BUG.value


# ---------------------------------------------------------------------------
# 握り潰されずに上がってきた内部バグ（PR-22-B が使う経路）
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "bug_factory, exception_type",
    [
        (lambda: FrozenExpressionError("frozen expression was mutated"),
         "FrozenExpressionError"),
        (lambda: ExpressionCycleError("expression graph has a cycle"),
         "ExpressionCycleError"),
    ],
    ids=["frozen", "cycle"],
)
def test_an_unswallowed_internal_bug_becomes_an_internal_exception_error(
    bug_factory, exception_type,
):
    """記録してそのまま raise した内部バグが、pair 境界で ERROR になる。

    PR-22-B の freeze violation はこの形（`record_internal_bug` → `raise`）で
    上がってくる。握り潰されないので G1 には届かず、`AnalysisLimitation` でも
    `InternalError` でもないため、型を catch list へ足す設計だと素通りする。
    2 つの型を同じ test で通しているのは、**型を足さずに** 乗ることの確認。
    """
    analysis1, analysis2 = _analyses()
    site = "core.expression.__setattr__"

    def _analyze(self, name, timeout):
        if name == "func1":
            bug = bug_factory()
            record_internal_bug(bug, site=site)
            raise bug
        return analysis2

    result = _run_pair(
        analyze=_analyze, stage_plan=_equivalent_stage_plan, connector=_connector(),
    )

    assert result.is_equivalent is None
    assert result.final_outcome == "ERROR"
    assert result.failure_status == "internal_exception"
    assert result.unknown_reasons == [], "限界の UNKNOWN へ化けさせない"
    assert result.pair_stop_state == PairStopState.INTERNAL_BUG.value
    failure = _failure_block(result, "internal_exception")
    assert failure["exception_type"] == exception_type
    assert failure["site"] == site


def test_an_unswallowed_internal_bug_outranks_a_recorded_limitation():
    """限界を記録したあとに内部バグを raw で投げたら、内部バグが勝つ。"""
    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        if name == "func1":
            try:
                raise_limitation(_budget_limitation(site="decompile"))
            except Exception:
                pass
            bug = FrozenExpressionError("frozen")
            record_internal_bug(bug, site="core.expression.__setattr__")
            raise bug
        return analysis2

    result = _run_pair(
        analyze=_analyze, stage_plan=_equivalent_stage_plan, connector=_connector(),
    )

    assert result.final_outcome == "ERROR"
    assert result.failure_status == "internal_exception"
    assert result.unknown_reasons == [], "限界の UNKNOWN へ格下げしない"
    assert result.pair_stop_state == PairStopState.INTERNAL_BUG.value


def test_a_raw_limitation_that_skipped_raise_limitation_is_still_adopted():
    """`raise_limitation` を経由せず raise された限界も同じ経路に乗る。"""
    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        if name == "func1":
            raise _budget_limitation(site="decompile")
        return analysis2

    result = _run_pair(
        analyze=_analyze, stage_plan=_equivalent_stage_plan, connector=_connector(),
    )

    assert result.is_equivalent is None and result.error_message is None
    assert result.final_outcome == "UNKNOWN"
    assert _reason_ids(result) == [BUDGET_REASON]
    assert result.pair_stop_state == PairStopState.PAIR_TERMINAL_DEADLINE.value


def test_a_generic_exception_without_a_recorded_failure_keeps_the_old_path():
    """台帳にも型にも根拠が無い例外は、従来どおりの経路のまま（勝手に握らない）。"""
    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        if name == "func1":
            raise RuntimeError("something unrelated")
        return analysis2

    with pytest.raises(RuntimeError, match="something unrelated"):
        _run_pair(
            analyze=_analyze, stage_plan=_equivalent_stage_plan,
            connector=_connector(),
        )


def test_the_ledger_folds_an_exception_that_is_recorded_and_then_adopted():
    """記録 → raise → 境界で拾い直し、を 1 件として数える。"""
    from scripts.function_tracer_pcode.core.errors import adopt_pair_failure

    with pair_failure_scope(("b1", "b2", None, None, "f", "f"), "s") as ledger:
        bug = FrozenExpressionError("frozen")
        record_internal_bug(bug, site="core.expression.__setattr__")
        first = adopt_pair_failure(bug)
        # 上位が `InternalError` に包み直してから再度拾っても増えない。
        second = adopt_pair_failure(InternalError(bug, site="checker.workflow"))
        assert ledger.recorded_failure_count() == 1
        assert first.site == second.site == "core.expression.__setattr__"
        assert first.exception.exception_type == "FrozenExpressionError"


# ---------------------------------------------------------------------------
# `check()` の中で起きた typed failure も台帳の winner を通る
# ---------------------------------------------------------------------------

def _run_check_in_scope(checker, session, raiser, pair=("b1", "b2", None, None, "L", "R")):
    """pair scope + pilot session の中で `check()` を 1 回だけ回す。"""
    from scripts.function_tracer_pcode.checker import checker as checker_module

    with production_signal_scope(session):
        with pair_failure_scope(pair, session.identity.result_occurrence_id) as ledger:
            with patch.object(
                checker_module, "assemble_equivalence_result", side_effect=raiser,
            ):
                result = checker.check(
                    _analysis("left", 7), _analysis("right", 7), "L", "R",
                )
            return result, ledger


def _checker_with(session):
    checker = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5,
        canonical_decision_cutover=False,
    )
    checker._active_v2_dual_write_pilot_session = session
    return checker


@pytest.mark.parametrize(
    "bug_factory, exception_type",
    [
        (lambda: FrozenExpressionError("frozen"), "FrozenExpressionError"),
        (lambda: ExpressionCycleError("cycle"), "ExpressionCycleError"),
    ],
    ids=["frozen", "cycle"],
)
def test_a_raw_typed_bug_inside_check_keeps_its_recorded_site(
    bug_factory, exception_type,
):
    """`check()` の中で記録 → raw raise した内部バグが、記録した観測点のまま ERROR。

    `check()` には generic な `except Exception` があるので、型付きの failure を
    そこへ落とすと観測点が `check` に書き換わり、台帳の winner とも無関係な結果に
    なる。2 つの型を同じ test で通しているのは、**型ごとの catch を足さずに**
    乗ることの確認。
    """
    site = "core.expression.__setattr__"
    connector = _connector()
    session = connector.begin({"case": f"issue106-raw-{exception_type}"})

    def _raise(*_args, **_kwargs):
        bug = bug_factory()
        record_internal_bug(bug, site=site)
        raise bug

    result, ledger = _run_check_in_scope(_checker_with(session), session, _raise)

    assert result.is_equivalent is None
    assert result.failure_status == "internal_exception"
    assert result.unknown_reasons == []
    failure = _failure_block(result, "internal_exception")
    assert failure["exception_type"] == exception_type
    assert failure["site"] == site, "`check()` の観測点へ書き換えない"
    assert failure["site"] != _CHECK_SITE
    # 台帳の winner と結果が同じ failure を指している。
    assert getattr(result, PAIR_FAILURE_IDENTITY_ATTRIBUTE) == (
        ledger.pending_failure().identity
    )


def test_the_result_represents_the_ledger_winner_not_the_raised_exception():
    """同 kind が 2 件あるとき、結果は **winner（先に記録した A）** を表す。

    A を記録して握り潰し、その後 B を記録して raw raise する。`check()` が
    捕まえるのは B だが、台帳の winner は A（同 kind は記録順で先頭）なので、
    結果も A でなければならない。
    """
    connector = _connector()
    session = connector.begin({"case": "issue106-winner-vs-raised"})

    def _raise(*_args, **_kwargs):
        swallowed = FrozenExpressionError("A")
        record_internal_bug(swallowed, site="core.expression.A")
        try:
            raise swallowed
        except Exception:
            pass
        raised = ExpressionCycleError("B")
        record_internal_bug(raised, site="core.structural.B")
        raise raised

    result, ledger = _run_check_in_scope(_checker_with(session), session, _raise)

    winner = ledger.pending_failure()
    assert winner.site == "core.expression.A", "同 kind は記録順で先頭が winner"
    assert ledger.recorded_failure_count() == 2
    failure = _failure_block(result, "internal_exception")
    assert failure["site"] == "core.expression.A"
    assert failure["exception_type"] == "FrozenExpressionError"
    assert getattr(result, PAIR_FAILURE_IDENTITY_ATTRIBUTE) == winner.identity


def test_a_limitation_inside_check_still_reports_through_the_winner():
    """`check()` の中の限界も winner 経由（内部バグが居れば内部バグが勝つ）。"""
    connector = _connector()
    session = connector.begin({"case": "issue106-check-precedence"})

    def _raise(*_args, **_kwargs):
        bug = FrozenExpressionError("frozen")
        record_internal_bug(bug, site="core.expression.__setattr__")
        raise_limitation(_budget_limitation(site="result_assembly"))

    result, ledger = _run_check_in_scope(_checker_with(session), session, _raise)

    assert ledger.pending_failure().kind is PairFailureKind.INTERNAL_BUG
    assert result.failure_status == "internal_exception"
    assert result.unknown_reasons == [], "限界の UNKNOWN へ格下げしない"


def test_a_generic_exception_inside_check_keeps_the_legacy_path():
    """族の外の例外は従来どおり `check` の観測点で `internal_exception` にする。"""
    connector = _connector()
    session = connector.begin({"case": "issue106-check-generic"})

    def _raise(*_args, **_kwargs):
        raise RuntimeError("generic")

    result, ledger = _run_check_in_scope(_checker_with(session), session, _raise)

    assert result.failure_status == "internal_exception"
    failure = _failure_block(result, "internal_exception")
    assert failure["exception_type"] == "RuntimeError"
    assert failure["site"] == _CHECK_SITE
    # pair failure としては採用しない（台帳は空のまま）。
    assert ledger.pending_failure() is None
    assert getattr(result, PAIR_FAILURE_IDENTITY_ATTRIBUTE, None) is None


# ---------------------------------------------------------------------------
# already-materialized 判定は identity で行う
# ---------------------------------------------------------------------------

def _pending(site, exception_type=FrozenExpressionError):
    with _scope() as ledger:
        record_internal_bug(exception_type("x"), site=site)
        return ledger.pending_failure()


def test_a_result_for_the_same_failure_is_not_rebuilt():
    from scripts.function_tracer_pcode.checker.pair_execution import (
        _failure_already_in_result,
    )

    failure = _pending("core.expression.A")
    result = create_mock_result(is_equivalent=None, error_message="internal")
    result.failure_status = "internal_exception"
    setattr(result, PAIR_FAILURE_IDENTITY_ATTRIBUTE, failure.identity)
    assert _failure_already_in_result(result, failure) is True


def test_a_result_for_a_different_failure_of_the_same_kind_is_rebuilt():
    """同じ `internal_exception` でも、別 failure を表す結果は作り直す。

    種別だけで「既に出ている」と判定すると、winner ではない failure の結果が
    そのまま最終結果になってしまう。
    """
    from scripts.function_tracer_pcode.checker.pair_execution import (
        _failure_already_in_result,
    )

    winner = _pending("core.expression.A")
    other = _pending("core.structural.B", ExpressionCycleError)
    assert winner.identity != other.identity
    result = create_mock_result(is_equivalent=None, error_message="internal")
    result.failure_status = "internal_exception"
    setattr(result, PAIR_FAILURE_IDENTITY_ATTRIBUTE, other.identity)
    assert _failure_already_in_result(result, winner) is False


# ---------------------------------------------------------------------------
# 変更軸の分離（failure kind / stop state / 例外型 を混ぜない）
# ---------------------------------------------------------------------------

def _scope():
    return pair_failure_scope(("b1", "b2", None, None, "f", "f"), "session-axis")


@pytest.mark.parametrize("bug_first", [False, True], ids=["limitation_first", "bug_first"])
def test_failure_precedence_does_not_depend_on_the_recording_order(bug_first):
    """内部バグ > 限界 は記録順に依らない。"""
    def _record_limitation():
        try:
            raise_limitation(_budget_limitation(site="oracle"))
        except AnalysisLimitation:
            pass

    def _record_bug():
        record_internal_bug(
            FrozenExpressionError("frozen"), site="core.expression.__setattr__",
        )

    with _scope() as ledger:
        steps = [_record_bug, _record_limitation] if bug_first else [
            _record_limitation, _record_bug
        ]
        for step in steps:
            step()
        failure = ledger.pending_failure()
        assert failure.kind is PairFailureKind.INTERNAL_BUG
        assert failure.site == "core.expression.__setattr__"
        assert ledger.recorded_failure_count() == 2


def test_stop_state_rank_does_not_decide_the_failure_winner(monkeypatch):
    """stop state の強さ（軸 D）を入れ替えても、勝つ failure（軸 B）は変わらない。

    2 つを同じ rank で代用していると、この monkeypatch で winner が反転する。
    """
    from scripts.function_tracer_pcode.core import errors as errors_module

    inverted = {
        PairStopState.NONE: 0,
        PairStopState.PAIR_TERMINAL_LIMITATION: 9,
        PairStopState.PAIR_TERMINAL_DEADLINE: 9,
        PairStopState.INTERNAL_BUG: 1,
    }
    monkeypatch.setattr(errors_module, "_STOP_STATE_RANK", inverted)
    with _scope() as ledger:
        try:
            raise_limitation(_budget_limitation(site="oracle"))
        except AnalysisLimitation:
            pass
        record_internal_bug(
            FrozenExpressionError("frozen"), site="core.expression.__setattr__",
        )
        assert ledger.pending_failure().kind is PairFailureKind.INTERNAL_BUG


def test_stop_state_escalation_still_follows_its_own_rank():
    """軸 D は軸 B と独立に効く: 限界のあとの内部バグで stop state も上がる。"""
    with _scope() as ledger:
        try:
            raise_limitation(_budget_limitation(site="oracle"))
        except AnalysisLimitation:
            pass
        assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_DEADLINE
        record_internal_bug(FrozenExpressionError("frozen"), site="core.expression")
        assert ledger.stop_state() is PairStopState.INTERNAL_BUG
        # 逆順（内部バグのあとに限界）でも stop state は下がらない。
    with _scope() as ledger:
        record_internal_bug(FrozenExpressionError("frozen"), site="core.expression")
        try:
            raise_limitation(_budget_limitation(site="oracle"))
        except AnalysisLimitation:
            pass
        assert ledger.stop_state() is PairStopState.INTERNAL_BUG


@pytest.mark.parametrize(
    "stop_state",
    [PairStopState.PAIR_TERMINAL_LIMITATION, PairStopState.PAIR_TERMINAL_DEADLINE],
)
def test_a_limitation_accepts_the_stop_states_that_mean_something_for_it(stop_state):
    with _scope() as ledger:
        ledger.record_limitation(_plain_limitation(site="expand"), stop=stop_state)
        assert ledger.stop_state() is stop_state
        assert ledger.pending_failure().stop_state is stop_state


@pytest.mark.parametrize(
    "stop_state", [PairStopState.NONE, PairStopState.INTERNAL_BUG],
)
def test_a_limitation_rejects_a_stop_state_that_is_not_its_own(stop_state):
    """`stop=INTERNAL_BUG` のような組み合わせを黙って通さない。

    通すと、限界が内部バグと同じ強さで記録され、順位の解釈が壊れる。
    """
    with _scope() as ledger:
        with pytest.raises(ValueError, match="not meaningful"):
            ledger.record_limitation(_plain_limitation(site="expand"), stop=stop_state)
        assert ledger.pending_failure() is None
        assert ledger.recorded_failure_count() == 0


# ---------------------------------------------------------------------------
# producer API と gate の catch 族が一致していること
# ---------------------------------------------------------------------------

#: gate（G3 / G5）が catch する族。producer の受理範囲と一致していること。
GATE_CATCH_FAMILY = AnalysisFailureError

_SAMPLE_EXCEPTIONS = (
    DeadlineExceeded("budget", site="s"),
    AnalysisLimitation(BUDGET_REASON, "detail", site="s"),
    FrozenExpressionError("frozen"),
    ExpressionCycleError("cycle"),
    InternalError(ValueError("boom"), site="s"),
    RuntimeError("generic"),
    ValueError("generic"),
    KeyboardInterrupt(),
)


def test_the_producer_api_accepts_exactly_what_the_gate_can_catch():
    """`record_*` が受理する集合 == gate が catch する族。

    ずれていると「台帳には残ったのに raw exception が境界を抜ける」状態ができる。
    """
    from scripts.function_tracer_pcode.core.errors import classify_failure_kind

    for exc in _SAMPLE_EXCEPTIONS:
        kind = classify_failure_kind(exc)
        catchable = isinstance(exc, GATE_CATCH_FAMILY)
        assert (kind is not None) is catchable, type(exc).__name__
        with _scope() as ledger:
            if kind is PairFailureKind.LIMITATION:
                ledger.record_limitation(exc)
                accepted = True
            else:
                try:
                    ledger.record_internal_bug(exc, site="probe")
                    accepted = True
                except TypeError:
                    accepted = False
            assert accepted is catchable, type(exc).__name__


def test_record_internal_bug_refuses_what_the_boundary_could_not_catch():
    """族の外を渡したら **記録時に** 失敗する（記録だけ成功させない）。"""
    with _scope() as ledger:
        with pytest.raises(TypeError, match="InternalError"):
            record_internal_bug(RuntimeError("generic"), site="probe")
        assert ledger.pending_failure() is None
        assert ledger.recorded_failure_count() == 0
        # 明示的に包めば受理され、以後は通常の内部バグと同じ経路に乗る。
        record_internal_bug(
            InternalError(RuntimeError("generic"), site="probe"), site="probe",
        )
        assert ledger.pending_failure().kind is PairFailureKind.INTERNAL_BUG


def test_an_internal_bug_wrapped_by_hand_still_ends_as_internal_exception():
    """generic な例外を `InternalError` に包んで記録 → raise でも ERROR になる。"""
    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        if name == "func1":
            bug = InternalError(RuntimeError("generic"), site="analysis.probe")
            record_internal_bug(bug, site="analysis.probe")
            raise bug
        return analysis2

    result = _run_pair(
        analyze=_analyze, stage_plan=_equivalent_stage_plan, connector=_connector(),
    )
    assert result.final_outcome == "ERROR"
    assert result.failure_status == "internal_exception"
    assert result.pair_stop_state == PairStopState.INTERNAL_BUG.value
    assert _failure_block(result, "internal_exception")["site"] == "analysis.probe"


# ---------------------------------------------------------------------------
# stable interface（consumer が具象台帳の内部を読まない）
# ---------------------------------------------------------------------------

#: `PairExecutionControl` が公開する契約。consumer はこれ以外を呼ばない。
STABLE_CONTROL_API = frozenset({
    "record_limitation", "record_internal_bug", "pending_failure",
    "stop_state", "allows_semantic_analysis", "allows_finalization",
})

#: 具象台帳が診断・test 向けに出している窓口（安定 contract には含めない）。
LEDGER_DIAGNOSTIC_API = frozenset({"recorded_failure_count"})

#: 台帳 object に対して consumer が呼んでよい名前（安定 contract + identity）。
LEDGER_ALLOWED_ATTRIBUTES = STABLE_CONTROL_API | {
    "matches", "pair_identity", "session_identity",
}


def test_the_stable_control_contract_is_exactly_what_consumers_need():
    """`PairExecutionControl` の公開面が増減していないことを固定する。

    診断・test 専用の窓口（`recorded_failure_count`）は **契約に入れない**。
    入れると、production consumer が畳み込みの件数に依存してよいことになる。
    """
    public = {
        name for name in vars(PairExecutionControl)
        if not name.startswith("_")
    }
    assert public == STABLE_CONTROL_API
    assert not (public & LEDGER_DIAGNOSTIC_API)
    ledger_cls = type(_ledger_for_contract_check())
    assert issubclass(ledger_cls, PairExecutionControl)
    for name in STABLE_CONTROL_API:
        assert callable(getattr(ledger_cls, name)), name
    for name in LEDGER_DIAGNOSTIC_API:
        assert callable(getattr(ledger_cls, name)), name
    # 使われなくなった窓口を公開したままにしない。
    assert not hasattr(ledger_cls, "is_empty")
    assert not hasattr(ledger_cls, "internal_bugs")
    assert not hasattr(ledger_cls, "limitations")


def _ledger_for_contract_check():
    with pair_failure_scope(("x", "y", None, None, "f", "f"), None) as ledger:
        return ledger


def _ledger_bound_names(tree):
    """その module で台帳 object を束縛している名前を集める。

    `with pair_failure_scope(...) as name` と `name = current_pair_ledger()` の
    2 形だけを追う。どちらでもない形で台帳を持ち回る consumer が現れたら、
    この規則では検出できないので形ごと足すこと。
    """
    names = set()

    def _call_name(node):
        func = getattr(node, "func", None)
        if isinstance(func, ast.Name):
            return func.id
        if isinstance(func, ast.Attribute):
            return func.attr
        return None

    for node in ast.walk(tree):
        if isinstance(node, ast.withitem):
            if (
                isinstance(node.context_expr, ast.Call)
                and _call_name(node.context_expr) == "pair_failure_scope"
                and isinstance(node.optional_vars, ast.Name)
            ):
                names.add(node.optional_vars.id)
        if isinstance(node, ast.Assign) and isinstance(node.value, ast.Call):
            if _call_name(node.value) == "current_pair_ledger":
                names.update(
                    t.id for t in node.targets if isinstance(t, ast.Name)
                )
    return names


def test_consumers_do_not_read_concrete_ledger_internals():
    """`core/errors.py` の外が台帳の内部表現に触れていないことを AST で固定。

    触れていると、保存形式・畳み込み・優先順位を変えるたびに checker / authority
    まで変更が波及する。優先順位の解決は台帳側の責務として閉じておく。
    """
    offenders = []
    for rel, _path, tree in _source_modules():
        if rel == "core/errors.py":
            continue
        bound = _ledger_bound_names(tree)
        for node in ast.walk(tree):
            if (
                isinstance(node, ast.Attribute)
                and isinstance(node.value, ast.Name)
                and node.value.id in bound
                and node.attr not in LEDGER_ALLOWED_ATTRIBUTES
            ):
                offenders.append(f"{rel}:{node.lineno} {node.value.id}.{node.attr}")
            if isinstance(node, ast.Name) and node.id == "PairFailureLedger":
                offenders.append(f"{rel}:{node.lineno} PairFailureLedger")
    assert offenders == [], (
        "具象台帳の内部を consumer が読んでいる:\n" + "\n".join(offenders)
    )


#: 変更軸ごとの唯一の owner。名前は `core/errors.py` の外に現れてはいけない。
AXIS_OWNER_TABLES = {
    "B: failure kind -> precedence": "_FAILURE_KIND_RANK",
    "C: failure kind -> stop states": "_STOP_STATES_BY_KIND",
    "D: stop state -> severity": "_STOP_STATE_RANK",
}


def test_each_change_axis_has_exactly_one_owner_and_it_is_in_core_errors():
    """軸ごとの規則表が 1 つずつ、`core/errors.py` にだけ在ることを固定する。

    どれかが外へ漏れていると、その軸を変えたときに無関係な module まで
    変更が波及する。`core/errors.py` の中でも定義は 1 回だけ。
    """
    from scripts.function_tracer_pcode.core import errors as errors_module

    core_source = pathlib.Path(errors_module.__file__).read_text(encoding="utf-8")
    core_tree = ast.parse(core_source)
    for axis, table in AXIS_OWNER_TABLES.items():
        assert hasattr(errors_module, table), axis
        definitions = [
            node for node in core_tree.body
            if isinstance(node, ast.Assign)
            and any(
                isinstance(t, ast.Name) and t.id == table for t in node.targets
            )
        ]
        assert len(definitions) == 1, f"{axis}: {table} は 1 回だけ定義する"
    offenders = []
    for rel, _path, tree in _source_modules():
        if rel == "core/errors.py":
            continue
        for node in ast.walk(tree):
            if isinstance(node, ast.Name) and node.id in AXIS_OWNER_TABLES.values():
                offenders.append(f"{rel}:{node.lineno} {node.id}")
    assert offenders == [], "\n".join(offenders)


#: pair failure を結果へ変える関数（定義は `result_assembly`）。
PAIR_RESULT_BUILDERS = frozenset({
    "analysis_limitation_result", "internal_error_result",
    "analysis_limitation_result_for_pair", "internal_error_result_for_pair",
})

#: それらを呼んでよい唯一の module（軸 E の owner）と、定義 module。
RESULT_CONVERSION_OWNERS = frozenset({
    "checker/pair_execution.py", "checker/result_assembly.py",
})


def test_pair_failures_are_turned_into_results_in_exactly_one_place():
    """結果化の owner が 1 つであることを固定する（軸 E）。

    別の module が直接 builder を呼ぶと、そこが 2 つ目の owner になり、台帳の
    winner を通らない結果が生まれる（`checker.check()` がまさにそれだった）。
    """
    offenders = []
    for rel, _path, tree in _source_modules():
        if rel in RESULT_CONVERSION_OWNERS:
            continue
        for node in ast.walk(tree):
            if (
                isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id in PAIR_RESULT_BUILDERS
            ):
                offenders.append(f"{rel}:{node.lineno} {node.func.id}()")
    assert offenders == [], (
        "pair failure の結果化が owner の外にある:\n" + "\n".join(offenders)
    )


def test_no_gate_branches_on_a_concrete_failure_exception_type():
    """gate（`check()` / workflow / boundary）が failure の **型名** を見ないこと。

    型名で分岐し始めると、新しい failure class を足すたびに gate を触ることに
    なる。gate が知ってよいのは族（`AnalysisFailureError`）だけ。
    """
    gates = {
        "checker/checker.py",
        "checker/workflow.py",
        "authority/lifecycle/production_boundary.py",
    }
    concrete = {
        "AnalysisLimitation", "DeadlineExceeded",
        "FrozenExpressionError", "ExpressionCycleError",
    }
    offenders = []
    for rel, _path, tree in _source_modules():
        if rel not in gates:
            continue
        for node in ast.walk(tree):
            if isinstance(node, ast.ExceptHandler) and node.type is not None:
                names = (
                    [node.type.id] if isinstance(node.type, ast.Name)
                    else [e.id for e in getattr(node.type, "elts", [])
                          if isinstance(e, ast.Name)]
                )
                for name in names:
                    if name in concrete:
                        offenders.append(f"{rel}:{node.lineno} except {name}")
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                if node.func.id == "isinstance" and len(node.args) == 2:
                    target = node.args[1]
                    names = (
                        [target.id] if isinstance(target, ast.Name)
                        else [e.id for e in getattr(target, "elts", [])
                              if isinstance(e, ast.Name)]
                    )
                    for name in names:
                        if name in concrete:
                            offenders.append(
                                f"{rel}:{node.lineno} isinstance(..., {name})"
                            )
    assert offenders == [], "\n".join(offenders)


def test_the_classification_rule_is_not_duplicated_outside_its_owner():
    """例外型 → 種別（軸 A）の `isinstance` 判定が owner の外に無いこと。

    `classify_failure_kind` 以外で `AnalysisLimitation` / `AnalysisFailureError`
    を `isinstance` で振り分け始めたら、分類規則が二重化している。
    """
    from scripts.function_tracer_pcode.core import errors as errors_module

    classified = {"AnalysisLimitation", "AnalysisFailureError"}
    owner_functions = {
        "classify_failure_kind", "_represented_exception_ids",
        "record_limitation", "adopt_pair_failure", "raise_limitation",
        "classify_typed_failure", "_default_stop_state",
    }
    core_tree = ast.parse(
        pathlib.Path(errors_module.__file__).read_text(encoding="utf-8")
    )
    stack, offenders = [], []

    class Visitor(ast.NodeVisitor):
        def visit_FunctionDef(self, node):
            stack.append(node.name)
            self.generic_visit(node)
            stack.pop()

        visit_AsyncFunctionDef = visit_FunctionDef

        def visit_Call(self, node):
            if (
                isinstance(node.func, ast.Name)
                and node.func.id == "isinstance"
                and len(node.args) == 2
                and isinstance(node.args[1], ast.Name)
                and node.args[1].id in classified
                and not (set(stack) & owner_functions)
            ):
                offenders.append(f"core/errors.py:{node.lineno} {'.'.join(stack)}")
            self.generic_visit(node)

    Visitor().visit(core_tree)
    assert offenders == [], "\n".join(offenders)


# ---------------------------------------------------------------------------
# thread / 入れ子 pair の契約
# ---------------------------------------------------------------------------

def test_the_pair_scope_is_process_wide_and_not_thread_local():
    """scope は process 単位。**worker thread からの producer は保証しない**。

    別 thread から見えるのは「そのとき最内の scope」なので、入れ子で別 pair の
    scope が開いている最中に外側 pair の worker が記録すると内側へ入る。この
    test はその挙動を契約として固定するためのもので、worker から
    `raise_limitation` してよいという意味ではない（`core/errors.py` の
    `_PAIR_LEDGERS` のコメントを参照）。
    """
    import threading

    seen = {}

    def _look():
        seen["ledger"] = current_pair_ledger()

    outer_pair = ("b1", "b2", None, None, "f", "f")
    with pair_failure_scope(outer_pair, "s") as outer:
        worker = threading.Thread(target=_look)
        worker.start()
        worker.join()
        assert seen["ledger"] is outer, "thread local ではない（process 単位）"

        with pair_failure_scope(("c1", "c2", None, None, "g", "g"), "s") as inner:
            worker = threading.Thread(target=_look)
            worker.start()
            worker.join()
            # 入れ子の最中は内側が見える = 外側 pair の worker は誤帰属し得る。
            assert seen["ledger"] is inner


# ---------------------------------------------------------------------------
# E0l: 台帳の生存範囲（boundary 全体）
# ---------------------------------------------------------------------------

def test_e0l_the_ledger_is_readable_while_the_connector_finishes():
    """E0l: workflow が戻ったあと、`connector.finish` 中も台帳が読める。"""
    analysis1, analysis2 = _analyses()
    observed = {}

    def _analyze(self, name, timeout):
        if name == "func1":
            try:
                raise_limitation(_budget_limitation(site="decompile"))
            except Exception:
                pass
        return analysis1 if name == "func1" else analysis2

    original_finish = production_boundary._profiled_finish

    def _spy_finish(connector, session, result):
        ledger = current_pair_ledger()
        observed["ledger"] = ledger
        observed["pending"] = None if ledger is None else ledger.pending_failure()
        return original_finish(connector, session, result)

    with patch.object(production_boundary, "_profiled_finish", _spy_finish):
        result = _run_pair(
            analyze=_analyze, stage_plan=_equivalent_stage_plan,
            connector=_connector(),
        )

    assert isinstance(observed["ledger"], PairExecutionControl)
    assert observed["pending"].kind is PairFailureKind.LIMITATION
    assert isinstance(observed["pending"].exception, AnalysisLimitation)
    assert result.final_outcome == "UNKNOWN"


# ---------------------------------------------------------------------------
# E0m / E0n: conditional lane の抑止と finalization の続行
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "limitation_factory, expected_stop",
    [
        (_plain_limitation, PairStopState.PAIR_TERMINAL_LIMITATION),
        (_budget_limitation, PairStopState.PAIR_TERMINAL_DEADLINE),
    ],
    ids=["e0m_limitation", "e0n_deadline"],
)
def test_e0mn_conditional_lane_is_skipped_but_finalization_continues(
    limitation_factory, expected_stop,
):
    """E0m / E0n: terminal な pair では lane を起動せず、確定処理は続ける。"""
    from scripts.function_tracer_pcode.authority.decision import conditional_lane

    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        if name == "func1":
            raise_limitation(limitation_factory(site="condition_oracle"))
        return analysis2

    lane = Mock(return_value={"ran": True})
    with patch.object(conditional_lane, "run_production_conditional_lane", lane):
        result = _run_pair(
            analyze=_analyze, stage_plan=_equivalent_stage_plan,
            connector=_connector(),
        )

    assert lane.call_count == 0
    assert result.diagnostics["conditional_lane"] == {
        "skipped": "pair_terminal", "pair_stop_state": expected_stop.value,
    }
    # 確定処理は止めない: receipt が出ていて JSON も組める。
    assert result.decision_receipt is not None
    assert result.final_outcome == "UNKNOWN"
    assert result._canonical_finalization_context is not None
    assert result.to_dict()["final_outcome"] == "UNKNOWN"


def test_e0mn_healthy_pairs_still_run_the_conditional_lane():
    """E0m / E0n 対照: 限界が無ければ lane は今までどおり起動する。"""
    from scripts.function_tracer_pcode.authority.decision import conditional_lane

    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        return analysis1 if name == "func1" else analysis2

    lane = Mock(return_value={"ran": True})
    with patch.object(conditional_lane, "run_production_conditional_lane", lane):
        result = _run_pair(
            analyze=_analyze, stage_plan=_healthy_stage_plan, connector=_connector(),
        )

    assert lane.call_count == 1
    assert result.diagnostics["conditional_lane"] == {"ran": True}


# ---------------------------------------------------------------------------
# E0o: 確定後に届いた限界で確定 UNKNOWN を壊さない
# ---------------------------------------------------------------------------

def test_e0o_a_limitation_recorded_during_finalization_keeps_the_decided_unknown():
    """E0o: finalization 中に限界が増えても、確定した UNKNOWN を捨てない。"""
    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        if name == "func1":
            raise_limitation(_budget_limitation(site="decompile"))
        return analysis2

    original_finish = production_boundary._profiled_finish

    def _finish_then_trip(connector, session, result):
        evidence = original_finish(connector, session, result)
        try:
            raise_limitation(_plain_limitation(site="output_preparation"))
        except Exception:
            pass
        return evidence

    with patch.object(production_boundary, "_profiled_finish", _finish_then_trip):
        result = _run_pair(
            analyze=_analyze, stage_plan=_equivalent_stage_plan,
            connector=_connector(),
        )

    assert result.final_outcome == "UNKNOWN"
    assert result.decision_receipt is not None
    assert _reason_ids(result) == [BUDGET_REASON]


# ---------------------------------------------------------------------------
# E0p / E0q: scope の共有条件
# ---------------------------------------------------------------------------

def test_e0p_the_same_pair_and_session_reenter_the_same_ledger():
    """E0p: pair / session が一致する再入は同じ台帳を使う。"""
    pair = ("b1", "b2", ("sha256", "a" * 64), ("sha256", "b" * 64), "f", "f")
    with pair_failure_scope(pair, "session-1") as outer:
        try:
            raise_limitation(_budget_limitation())
        except AnalysisLimitation:
            pass
        with pair_failure_scope(pair, "session-1") as inner:
            assert inner is outer
            assert isinstance(inner.pending_failure().exception, AnalysisLimitation)
        # 内側の scope を抜けても外側の台帳は残る。
        assert isinstance(outer.pending_failure().exception, AnalysisLimitation)
        assert current_pair_ledger() is outer
    assert current_pair_ledger() is None


@pytest.mark.parametrize(
    "other_pair, other_session",
    [
        (("b1", "b2", None, None, "g", "g"), "session-1"),
        (("b1", "b2", None, None, "f", "f"), "session-2"),
        (("b1", "b2", None, None, "f", "f"), None),
    ],
    ids=["other_pair", "other_session", "no_session"],
)
def test_e0q_a_different_pair_or_session_gets_its_own_ledger(
    other_pair, other_session,
):
    """E0q: pair か session が違えば台帳を共有しない（入れ子でも漏らさない）。"""
    pair = ("b1", "b2", None, None, "f", "f")
    with pair_failure_scope(pair, "session-1") as outer:
        try:
            raise_limitation(_budget_limitation())
        except AnalysisLimitation:
            pass
        with pair_failure_scope(other_pair, other_session) as inner:
            assert inner is not outer
            assert inner.recorded_failure_count() == 0
            assert inner.pending_failure() is None
            assert inner.allows_semantic_analysis() is True
        # 内側で新しく積んだ台帳は抜けるときに捨てる。
        assert current_pair_ledger() is outer
        assert outer.stop_state() is PairStopState.PAIR_TERMINAL_DEADLINE


# ---------------------------------------------------------------------------
# E0r: pilot の有無
# ---------------------------------------------------------------------------

def test_e0r_a_limitation_without_a_pilot_session_fails_closed_as_error():
    """E0r: pilot 無しの限界は ERROR `limitation_unattributed`（UNKNOWN に偽装しない）。"""
    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        if name == "func1":
            raise_limitation(_budget_limitation(site="decompile"))
        return analysis2

    result = _run_pair(
        analyze=_analyze, stage_plan=_equivalent_stage_plan, connector=None,
    )

    assert result.is_equivalent is None
    assert result.error_message == "limitation_unattributed"
    assert result.failure_status == "limitation_unattributed"
    assert result.unknown_reasons == []
    failure = _failure_block(result, "analysis_limitation")
    assert failure["disposition"] == "UNATTRIBUTED"
    assert result.pair_stop_state == PairStopState.PAIR_TERMINAL_DEADLINE.value


def test_e0r_the_same_limitation_with_a_pilot_is_unknown_with_a_receipt():
    """E0r 対照: connector があれば同じ限界が reason 付き UNKNOWN になる。"""
    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        if name == "func1":
            raise_limitation(_budget_limitation(site="decompile"))
        return analysis2

    result = _run_pair(
        analyze=_analyze, stage_plan=_equivalent_stage_plan, connector=_connector(),
    )

    assert result.error_message is None
    assert result.final_outcome == "UNKNOWN"
    assert result.decision_receipt is not None
    assert _reason_ids(result) == [BUDGET_REASON]


# ---------------------------------------------------------------------------
# raise 箇所 0 の通常経路が変わっていないこと
# ---------------------------------------------------------------------------

def test_a_pair_without_any_limitation_is_unchanged():
    """限界が 1 件も無ければ stop state も診断も出ない（production 挙動不変）。"""
    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        return analysis1 if name == "func1" else analysis2

    # pilot connector 無しの legacy 経路。EQ がそのまま返ることを見る。
    legacy = _run_pair(
        analyze=_analyze, stage_plan=_equivalent_stage_plan, connector=None,
    )
    assert legacy.is_equivalent is True
    assert legacy.error_message is None
    assert legacy.pair_stop_state is None

    # pilot connector ありの通常経路。stop state も限界診断も出ない。
    result = _run_pair(
        analyze=_analyze, stage_plan=_healthy_stage_plan, connector=_connector(),
    )
    assert result.error_message is None
    assert result.pair_stop_state is None
    failures = (result.diagnostics or {}).get("failures", {})
    assert "pair_stop_state" not in failures
    assert "analysis_limitation" not in failures
    payload = result.to_dict()
    assert "pair_stop_state" not in payload
    assert "pair_stop_state" not in payload["diagnostics"]["failures"]


def test_the_ledger_is_inert_outside_a_pair_scope():
    """scope の外では台帳が無く、限界はそのまま例外として上がるだけ。"""
    from scripts.function_tracer_pcode.checker.pair_execution import (
        pair_allows_semantic_analysis,
        pending_pair_failure,
    )

    assert current_pair_ledger() is None
    assert pair_allows_semantic_analysis() is True
    assert pending_pair_failure() is None
    with pytest.raises(AnalysisLimitation):
        raise_limitation(_budget_limitation())
    assert current_pair_ledger() is None


def test_record_internal_bug_outside_a_scope_is_a_no_op():
    """scope の外の `record_internal_bug` は記録先が無いだけで失敗しない。"""
    record_internal_bug(FrozenExpressionError("x"), site="core.expression")
    assert current_pair_ledger() is None



def test_every_failure_kind_is_handled_by_every_dispatcher():
    """種別 → 扱い方の 3 つの振り分け（`pair_execution`）は、どれも `PairFailureKind` の全 member の分岐を
    持つ（member を足して 1 つでも足し忘れると、実行時の `KeyError` を待たずにここで落ちる）。"""

    import ast
    import inspect

    from scripts.function_tracer_pcode.checker import pair_execution
    from scripts.function_tracer_pcode.core.errors import PairFailureKind

    members = {member.name for member in PairFailureKind}
    for dispatcher in (
        pair_execution._build_result_for,
        pair_execution._build_result_with_analyses_for,
        pair_execution._replaces_unrelated_result_for,
    ):
        tree = ast.parse(inspect.getsource(dispatcher))
        handled = {
            node.test.comparators[0].attr
            for node in ast.walk(tree)
            if isinstance(node, ast.If) and isinstance(node.test, ast.Compare)
            and isinstance(node.test.comparators[0], ast.Attribute)
            and isinstance(node.test.comparators[0].value, ast.Name)
            and node.test.comparators[0].value.id == "PairFailureKind"
        }
        assert handled == members, (dispatcher.__name__, handled)
