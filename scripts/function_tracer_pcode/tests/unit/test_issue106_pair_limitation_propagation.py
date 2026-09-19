# -*- coding: utf-8 -*-
"""Issue #106 PR-106-0: pair 単位の限界伝搬（E0a〜E0r）。

このPRは **新しい限界の raise 箇所を作らない**。作るのは「限界が起きたら pair
全体をどう止め、どう結果化するか」の土台だけなので、test は

* 台帳（`PairFailureLedger`）の lifecycle と共有条件
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
from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
from scripts.function_tracer_pcode.checker.phases.handler import (
    PhaseHandler,
    PhaseID,
    PhaseResult,
)
from scripts.function_tracer_pcode.core.errors import (
    AnalysisLimitation,
    DeadlineExceeded,
    FrozenExpressionError,
    PairFailureLedger,
    PairStopState,
    current_pair_ledger,
    pair_failure_scope,
    raise_limitation,
    record_internal_bug,
    reset_pair_failure_scopes,
)
from scripts.function_tracer_pcode.smt import SolverStatus
from scripts.function_tracer_pcode.tests.unit.test_issue125_limitation_finalization import (
    _connector,
    _sat_blocker,
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
    fake_z3 = SimpleNamespace(Solver=Mock(side_effect=limitation))
    with patch.object(ConditionSMTOracle, "_z3", fake_z3):
        with patch.object(
            ConditionSMTOracle, "_build_script",
            classmethod(lambda cls, conditions: (True, "(check-sat)")),
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
    phase_handler.run_phase4_mips64_retry.return_value = None

    result = _run_pair(
        analyze=_analyze, stage_plan=_stage_plan, connector=_connector(),
        retry_with_type_fix=True, phase_handler=phase_handler,
    )

    assert calls["func1"] == 2, "P1 の再解析まで到達していない（test が空振り）"
    assert result.is_equivalent is None and result.error_message is None
    assert _reason_ids(result) == [BUDGET_REASON]
    assert result.pair_stop_state == PairStopState.PAIR_TERMINAL_DEADLINE.value


def test_e0f_phase_loop_stops_after_a_swallowed_limitation():
    """E0f 補: 限界が握り潰されても次 phase の再解析を始めない。"""
    analysis1, analysis2 = _analyses()
    calls = {"func1": 0, "func2": 0}

    def _analyze(self, name, timeout):
        calls[name] += 1
        if name == "func2" and calls["func2"] == 1:
            try:
                raise_limitation(_plain_limitation(site="effect_summary"))
            except Exception:
                pass
        return analysis1 if name == "func1" else analysis2

    def _stage_plan(*_args, **_kwargs):
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
    phase_handler.run_phase4_mips64_retry.return_value = None

    result = _run_pair(
        analyze=_analyze, stage_plan=_stage_plan, connector=_connector(),
        retry_with_type_fix=True, phase_handler=phase_handler,
    )

    # 初回解析の 2 回だけ。P1 の再解析（3 回目）は始まらない。
    assert calls == {"func1": 1, "func2": 1}
    assert phase_handler.execute_phase.call_count == 0
    assert result.pair_stop_state == PairStopState.PAIR_TERMINAL_LIMITATION.value


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
    assert len(seen_ledgers[0].limitations()) == 1
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
# E0l: 台詞の生存範囲（boundary 全体）
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
        observed["pending"] = None if ledger is None else ledger.pending()
        return original_finish(connector, session, result)

    with patch.object(production_boundary, "_profiled_finish", _spy_finish):
        result = _run_pair(
            analyze=_analyze, stage_plan=_equivalent_stage_plan,
            connector=_connector(),
        )

    assert isinstance(observed["ledger"], PairFailureLedger)
    assert isinstance(observed["pending"], AnalysisLimitation)
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
            assert isinstance(inner.pending(), AnalysisLimitation)
        # 内側の scope を抜けても外側の台帳は残る。
        assert isinstance(outer.pending(), AnalysisLimitation)
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
            assert inner.is_empty()
            assert inner.pending() is None
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
