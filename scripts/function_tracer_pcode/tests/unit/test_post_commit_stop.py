# -*- coding: utf-8 -*-
"""安全な counterexample を commit した後は新しい意味解析を始めない（#130 S3 / A-5）。

commit した判定は authority の記録で、後の解析では消えない。修正前は commit の後も新しい解析が
始まっていた（下の各 test の修正前の挙動）。

境界（新しい意味解析 = 止める / 既存の証拠の検証と確定 = 止めない）:

* 止める: 次の phase（P1 / P2）、SAT の後の再試行（P4C・P4A tail）、stage の fallback、完了証拠からの
  派生 view とその依存 query、同じ branch の replan、再帰の昇格、conditional lane、新しい比較
  （``EquivalenceChecker.check``）。
* 止めない: proof gate（記録済みの証拠の検証。solver を呼ばない）、集約、receipt、final gate、
  authority の確定。

規則の owner は authority の ``counterexample_commit_stop_reason``（legacy の bool を読まない）。
checker の開始点は ``semantic_analysis_stop_reason`` でそれを合成し、stage runner は authority の
規則を直接読む。開始点はそれぞれ自分で止まり、``check()`` の入口は止め忘れを内部バグとして拒否する。
commit が無ければ流れは変わらない（各 test の対照）。
"""

from __future__ import annotations

from contextlib import contextmanager

import pytest

from scripts.function_tracer_pcode.authority.lifecycle.production_signals import committed_safe_counterexample
from scripts.function_tracer_pcode.proof.sat_safety_resolution import COUNTEREXAMPLE_ANALYSIS_SAFETY_UNPROVEN

from scripts.function_tracer_pcode.checker.pair_execution import (
    SEMANTIC_ANALYSIS_STOP_COUNTEREXAMPLE_COMMITTED,
    SEMANTIC_ANALYSIS_STOP_PAIR_TERMINAL,
    semantic_analysis_stop_reason,
)
from scripts.function_tracer_pcode.checker.phases.handler import PhaseHandler, PhaseID
from scripts.function_tracer_pcode.tests.unit.test_post_commit_veto import (
    _CONFIGS,
    _active,
    _eq_pair,
    _not_eq_pair,
    _run,
)


def _attempt_phases(result):
    return [attempt.get("phase") for attempt in (result.get("debug_trace") or {}).get("attempts") or ()]


@contextmanager
def _sat_retries_eligible():
    """SAT の後の再試行（P4C、続く P4A tail）を始める条件を満たさせ、始まったかを記録する。

    P4C は ``should_fix_return_type`` が真なら戻り値型の修正（``run_phase2_return_type_fix``）を
    始める。修正を適用しない（``applied=False``）ので再解析はしないが、試みたことで P4A tail
    （``execute_phase`` の P4A）へ進む。記録はその 2 つの開始。
    """

    started = []
    original_should = PhaseHandler.should_fix_return_type
    original_fix = PhaseHandler.run_phase2_return_type_fix
    original_execute = PhaseHandler.execute_phase

    def should_fix(self, *_args, **_kwargs):
        return True

    def fix(self, *_args, **_kwargs):
        started.append("P4C_RETURN_TYPE_FIX")
        return False, False, False

    def execute(self, phase_spec, *args, **kwargs):
        if phase_spec.phase_id is PhaseID.P4A_MIPS64_ABI:
            started.append(PhaseID.P4A_MIPS64_ABI.value)
        return original_execute(self, phase_spec, *args, **kwargs)

    PhaseHandler.should_fix_return_type = should_fix
    PhaseHandler.run_phase2_return_type_fix = fix
    PhaseHandler.execute_phase = execute
    try:
        yield started
    finally:
        PhaseHandler.should_fix_return_type = original_should
        PhaseHandler.run_phase2_return_type_fix = original_fix
        PhaseHandler.execute_phase = original_execute


@pytest.mark.parametrize("config", sorted(_CONFIGS))
def test_no_phase_or_fallback_starts_after_a_vetoed_commit(config):
    """commit + veto: 修正前は veto の後に次の phase / fallback が走り、final gate が 2 回以上呼ばれた。"""

    result, calls = _run("stop_after_veto", config, _not_eq_pair, veto=True, debug=True)
    assert calls[0]["committed"], calls
    assert len(calls) == 1, calls
    assert _attempt_phases(result) == [PhaseID.P0_BASE.value], _attempt_phases(result)
    assert len(result["stage_path"]) == 1, result["stage_path"]
    assert result["final_outcome"] == "UNKNOWN"


@pytest.mark.parametrize("config", sorted(_CONFIGS))
def test_no_sat_retry_starts_after_a_commit(config):
    """commit（veto 無し）: 修正前は P4C と P4A tail が始まった。判定は NOT_EQ のまま。"""

    with _sat_retries_eligible() as started:
        result, calls = _run("stop_sat_retry", config, _not_eq_pair, debug=True)
    assert calls[0]["committed"], calls
    assert started == [], started
    assert _attempt_phases(result) == [PhaseID.P0_BASE.value], _attempt_phases(result)
    assert result["final_outcome"] == "NOT_EQ"


def test_conditional_lane_is_skipped_after_a_commit():
    """commit + veto で最終 UNKNOWN になっても、conditional lane（新しい意味解析）は始めない。"""

    result, _calls = _run("stop_lane", "pairwise", _not_eq_pair, veto=True)
    lane = (result.get("diagnostics") or {}).get("conditional_lane") or {}
    assert result["final_outcome"] == "UNKNOWN"
    assert lane.get("skipped") == SEMANTIC_ANALYSIS_STOP_COUNTEREXAMPLE_COMMITTED, lane


def test_flow_without_a_commit_continues_after_a_veto():
    """対照: commit が無ければ veto の後も次の解析（stage の fallback）が走る（今どおり）。"""

    result, calls = _run("no_commit_veto", "pairwise", _eq_pair, veto=True, debug=True)
    assert not any(call["committed"] for call in calls), calls
    assert len(calls) >= 2, calls
    assert len(result["stage_path"]) >= 2, result["stage_path"]
    assert result["final_outcome"] == "EQUIVALENT"


def test_stop_reason_reads_the_terminal_state_before_the_commit(monkeypatch):
    """terminal の pair は commit の有無にかかわらず ``pair_terminal``（診断の既存の値を保つ）。"""

    from scripts.function_tracer_pcode.checker import pair_execution
    from scripts.function_tracer_pcode.core.errors import PairStopState

    committed = lambda _session=None: SEMANTIC_ANALYSIS_STOP_COUNTEREXAMPLE_COMMITTED  # noqa: E731
    monkeypatch.setattr(pair_execution, "counterexample_commit_stop_reason", committed)
    monkeypatch.setattr(pair_execution, "pair_stop_state", lambda: PairStopState.NONE)
    assert semantic_analysis_stop_reason() == SEMANTIC_ANALYSIS_STOP_COUNTEREXAMPLE_COMMITTED
    monkeypatch.setattr(pair_execution, "pair_stop_state", lambda: PairStopState.PAIR_TERMINAL_DEADLINE)
    assert semantic_analysis_stop_reason() == SEMANTIC_ANALYSIS_STOP_PAIR_TERMINAL
    monkeypatch.setattr(pair_execution, "counterexample_commit_stop_reason", lambda _session=None: None)
    monkeypatch.setattr(pair_execution, "pair_stop_state", lambda: PairStopState.NONE)
    assert semantic_analysis_stop_reason() is None


# --------------------------------------------------------------------------------------------
# stage plan の中の開始点（レビュー指摘 1）: 完了した証拠からの派生 view・依存 query・同じ branch の
# replan も新しい意味解析。final gate の veto は check() の中で結果を INCONCLUSIVE にするので、
# commit 済みの branch の結果が「再計画できる完了証拠」を持つと、修正前は派生 view を作って replan
# し、check() がもう 1 回呼ばれた。
# --------------------------------------------------------------------------------------------


def _replannable_branch(case_id, *, commit):
    """1 段の pairwise stage plan。1 回目の branch は完了した return coverage の証明を持つ INCONCLUSIVE。

    ``commit`` なら 1 回目の branch の中で、本物の SAT-safety の encoder で安全な counterexample を
    commit する（reader を差し替えない）。戻り値は (最終結果, check の呼び出しの view 列, runtime)。
    """

    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import production_signal_scope
    from scripts.function_tracer_pcode.checker.checker import StageID, StageSpec
    from scripts.function_tracer_pcode.proof.cause_identity import ProofRequirementContract, ProofRequirementId
    from scripts.function_tracer_pcode.proof.obligations import PairLedgerBinding
    from scripts.function_tracer_pcode.proof.obligations.pair_disposition import (
        emit_safe_counterexample_production_signal,
    )
    from scripts.function_tracer_pcode.tests.unit import test_obligation_stage_runner as sr
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_sat_safety import (
        _connector,
        _safe_pairwise_receipt,
    )
    from types import SimpleNamespace
    from unittest.mock import Mock

    requirement = ProofRequirementId.create(
        "return_coverage_completion", ("coverage", "f"), ProofRequirementContract("return coverage complete"),
    )
    reason = SimpleNamespace(
        reason_id="return_coverage_gap", recovery_proof_kind="return_coverage_completion",
        proof_requirement_ids=(requirement.to_dict(),), object_target_key=("coverage", "f"),
        pair_or_case="(0,0)", stage="S_PAIRWISE",
    )
    comparison = sr._comparison()
    first = sr._result(None, (reason,))
    first.completed_recovery_proof_evidence = [{"evidence": sr._comparison_evidence(comparison, {
        "proof_requirement_id": requirement.to_dict(), "status": "complete", "proof_source": "coverage_test_producer",
    })}]
    second = sr._result(True)
    second.completed_recovery_proof_evidence = []
    checker = sr._checker([])
    checker.stage_plan = [StageSpec(StageID.S_PAIRWISE, "pairwise", "pairwise")]
    checker.pairwise_strategy = SimpleNamespace(
        _return_coverage_proof_is_complete=lambda *_args: True,
        _call_effect_summary_proof_is_complete=lambda *_args: False,
        _recovery_proof_is_complete=lambda *_args: False,
    )
    receipt = _safe_pairwise_receipt() if commit else None  # scope の外で作る（中で作ると commit する）
    session = _connector().begin({"phase": "a5", "case": case_id})
    views = []

    def execute(*_args, **kwargs):
        runtime = checker._obligation_runtime_session
        views.append(runtime.current_view.view_id)
        if len(views) == 1:
            if commit:
                emit_safe_counterexample_production_signal(safety_receipt=receipt)
            binding = PairLedgerBinding(
                "session", "S_PAIRWISE", "surface", "projection", 1,
                runtime.current_view.view_id, runtime.premise_digest, 1, comparison.digest,
            )
            first._prepared_dispatch_frame = sr._frame(comparison, pair_disposition_ledger=runtime.open_pair_ledger(binding, 1))
            return first
        plan = runtime.pair_ledger_manager.pending_successor
        runtime.open_pair_ledger(PairLedgerBinding(
            plan.comparison_session_id, plan.branch_id, "new-surface", "new-projection", 2,
            plan.derived_view_id, plan.premise_digest, 2, comparison.digest,
        ), 2)
        return second

    checker.check = Mock(side_effect=execute)
    with production_signal_scope(session):
        final = sr._run(checker, "_run_stage_plan")
        assert (committed_safe_counterexample() is not None) is commit
    return final, views, checker._obligation_runtime_session


def test_no_successor_view_or_replan_starts_after_a_commit():
    """commit 済みの INCONCLUSIVE branch: 完了証拠は派生 view にならず、replan の check() も始まらない。

    修正前は派生 view を作って replan し、check() が 2 回呼ばれた。proof gate（記録済みの証拠の検証）は走る。
    """

    final, views, runtime = _replannable_branch("committed", commit=True)
    assert len(views) == 1, views
    assert runtime.current_view.view_id == views[0]
    assert not runtime.artifacts
    assert runtime.pair_ledger_manager.pending_successor is None
    assert not any(event.event == "pair_ledger_replan_required" for event in runtime.events)
    assert runtime.proof_outcomes, "the proof gate (validation of recorded evidence) still runs"
    assert final.is_equivalent is None


def test_completed_evidence_still_replans_without_a_commit():
    """対照: commit が無ければ、完了証拠は派生 view を作り、同じ branch を replan する（今どおり）。"""

    _final, views, runtime = _replannable_branch("no-commit", commit=False)
    assert len(views) == 2 and views[0] != views[1], views
    assert any(event.event == "pair_ledger_replan_required" for event in runtime.events)
    assert runtime.artifacts


@contextmanager
def _replannable_completed_evidence():
    """production の branch の 1 回目の結果を「replan できる完了証拠を持つ INCONCLUSIVE」にする。

    production で commit 済みの branch の結果が INCONCLUSIVE のまま stage runner の証拠の段に届くのは、
    monolithic が commit の後に未完了の obligation で UNKNOWN へ下げたときと、timeout と decisive の
    矛盾を ``normalize_timeout_contradiction`` が None にしたとき。ここでは後者と同じく、結果と
    strategy の結果の legacy の値を None にする（commit・gate・証拠の適用・final gate・authority の確定は
    本物）。証拠はその結果を作った比較に束縛し、gate はその証拠を完了と認める。記録は check() の
    呼び出しごとの legacy の値（branch の比較の開始ごとに 1 つ）。
    """

    from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
    from scripts.function_tracer_pcode.checker.unknown_reason import make_unknown_reason
    from scripts.function_tracer_pcode.proof.cause_identity import ProofRequirementContract, ProofRequirementId
    from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
        CrossSideIdentification,
        bind_evidence_to_comparison,
    )
    from scripts.function_tracer_pcode.proof.strategies.base import CheckStrategy

    requirement = ProofRequirementId.create(
        "return_coverage_completion", ("coverage", "a5"), ProofRequirementContract("return coverage complete"),
    )
    calls = []
    original_check = EquivalenceChecker.check
    original_complete = CheckStrategy._return_coverage_proof_is_complete

    def check(self, *args, **kwargs):
        result = original_check(self, *args, **kwargs)
        calls.append(result.is_equivalent)
        frame = getattr(result, "_prepared_dispatch_frame", None)
        if len(calls) == 1 and frame is not None:
            result.is_equivalent = None
            strategy_result = getattr(result, "_strategy_result", None)
            if strategy_result is not None:
                strategy_result.is_equivalent = None
            result.unknown_reasons.append(make_unknown_reason(
                "return_coverage_gap", stage="S_PAIRWISE", pair_or_case="(0,0)",
                recovery_proof_kind="return_coverage_completion",
                proof_requirement_ids=(requirement.to_dict(),), object_target_key=("coverage", "a5"),
            ))
            result.completed_recovery_proof_evidence = list(
                getattr(result, "completed_recovery_proof_evidence", None) or ()
            ) + [{"evidence": bind_evidence_to_comparison(
                {"proof_requirement_id": requirement.to_dict(), "status": "complete", "proof_source": "a5_test"},
                frame.comparison_binding, identification=CrossSideIdentification.CORRESPONDENCE,
            )}]
        return result

    def complete(self, reason, *args, **kwargs):
        if getattr(reason, "object_target_key", None) == ("coverage", "a5"):
            return True
        return original_complete(self, reason, *args, **kwargs)

    EquivalenceChecker.check = check
    CheckStrategy._return_coverage_proof_is_complete = complete
    try:
        yield calls
    finally:
        EquivalenceChecker.check = original_check
        CheckStrategy._return_coverage_proof_is_complete = original_complete


def test_vetoed_commit_with_replannable_evidence_finalizes_unknown_without_new_analysis():
    """production 経路: commit + veto + replan できる完了証拠。新しい view・query・branch を始めず、
    final gate と authority の確定を経て UNKNOWN（N-4）。修正前は replan の check() が始まった。"""

    with _replannable_completed_evidence() as checks:
        result, calls = _run("veto_replannable", "pairwise", _not_eq_pair, veto=True, debug=True)
    assert calls[0]["committed"], calls
    assert checks == [False], checks  # 1 回の比較だけ（その中で commit した）
    assert len(result["stage_path"]) == 1, result["stage_path"]
    assert result["final_outcome"] == "UNKNOWN"
    assert COUNTEREXAMPLE_ANALYSIS_SAFETY_UNPROVEN in _active(result)
    assert (result.get("pairwise_debug_stats") or {}).get("derived_view_pair_replans", 0) == 0


def test_replannable_evidence_without_a_commit_still_replans_in_production():
    """対照: commit の無い（EQ への）veto + 同じ完了証拠は、今どおり派生 view で replan する。"""

    with _replannable_completed_evidence() as checks:
        result, calls = _run("veto_replannable_no_commit", "pairwise", _eq_pair, veto=True, debug=True)
    assert not any(call["committed"] for call in calls), calls
    assert len(checks) >= 2, checks
    assert (result.get("pairwise_debug_stats") or {}).get("derived_view_pair_replans", 0) >= 1, (
        result.get("pairwise_debug_stats")
    )


def test_a_comparison_started_after_a_commit_is_an_internal_bug():
    """backstop: 止め忘れた開始点が check() を呼んでも、黙って新しい比較を始めない（内部バグ）。"""

    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import production_signal_scope
    from scripts.function_tracer_pcode.checker.pair_execution import refuse_comparison_after_commit
    from scripts.function_tracer_pcode.core.errors import (
        PairFailureKind,
        SemanticAnalysisAfterCommitError,
        classify_failure_kind,
    )
    from scripts.function_tracer_pcode.proof.obligations.pair_disposition import (
        emit_safe_counterexample_production_signal,
    )
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_sat_safety import (
        _connector,
        _safe_pairwise_receipt,
    )

    receipt = _safe_pairwise_receipt()
    session = _connector().begin({"phase": "a5", "case": "backstop"})
    with production_signal_scope(session):
        refuse_comparison_after_commit("test")  # commit の前は通す
        emit_safe_counterexample_production_signal(safety_receipt=receipt)
        with pytest.raises(SemanticAnalysisAfterCommitError) as raised:
            refuse_comparison_after_commit("EquivalenceChecker.check")
    assert classify_failure_kind(raised.value) is PairFailureKind.INTERNAL_BUG


def test_check_refuses_to_start_a_comparison_after_a_commit():
    """check() の入口が backstop を読む（production の check() を直接呼んで確かめる）。"""

    import inspect

    from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker

    source = inspect.getsource(EquivalenceChecker.check)
    first_try = source.index("try:", source.index("check_region = open_stage_region"))
    inner_try = source.index("try:", first_try + 4)
    guard = source.index('refuse_comparison_after_commit("EquivalenceChecker.check")')
    strategy = source.index("strategy = force_strategy")
    assert inner_try < guard < strategy


# --------------------------------------------------------------------------------------------
# 途中の phase で commit した後の遷移: P0 は UNKNOWN、P1 の再解析の中で commit する。
# --------------------------------------------------------------------------------------------


@pytest.mark.parametrize("legacy_after_commit", [False, None], ids=["not_eq", "vetoed_to_none"])
def test_no_later_phase_or_sat_retry_starts_after_a_mid_plan_commit(legacy_after_commit):
    """P1 で commit したら P2・P4C・P4A tail を始めない（legacy の値が None でも）。"""

    from unittest.mock import Mock

    from scripts.function_tracer_pcode.checker.phases.handler import PhaseResult
    from scripts.function_tracer_pcode.proof.obligations.pair_disposition import (
        emit_safe_counterexample_production_signal,
    )
    from scripts.function_tracer_pcode.smt import SolverStatus
    from scripts.function_tracer_pcode.tests.conftest import create_mock_result
    from scripts.function_tracer_pcode.tests.unit import test_issue106_pair_limitation_propagation as e0f
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_sat_safety import (
        _connector,
        _safe_pairwise_receipt,
    )

    receipt = _safe_pairwise_receipt()  # session の外で作る（中で作ると commit する）
    analysis1, analysis2 = e0f._analyses()
    plans = []

    def _stage_plan(*_args, **_kwargs):
        plans.append(len(plans))
        if len(plans) == 1:
            e0f._emit_one_production_signal()
            return create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)
        emit_safe_counterexample_production_signal(safety_receipt=receipt)
        status = SolverStatus.SAT if legacy_after_commit is False else SolverStatus.UNKNOWN
        return create_mock_result(is_equivalent=legacy_after_commit, solver_status=status)

    phase_handler = _mid_plan_phase_handler(PhaseResult)
    e0f._run_pair(
        analyze=lambda _self, name, _timeout: analysis1 if name == "func1" else analysis2,
        stage_plan=_stage_plan, connector=_connector(),
        retry_with_type_fix=True, phase_handler=phase_handler,
    )

    assert plans == [0, 1], plans  # P0 と P1 の stage plan だけ
    assert [call.args[0].phase_id for call in phase_handler.execute_phase.call_args_list] == [
        PhaseID.P1_SIGNEDNESS,
    ]
    phase_handler.should_fix_return_type.assert_not_called()  # P4C


def test_later_phases_continue_after_a_mid_plan_unknown_without_a_commit():
    """対照: P1 が commit なしの UNKNOWN なら、今どおり P2 へ進む。"""

    from scripts.function_tracer_pcode.checker.phases.handler import PhaseResult
    from scripts.function_tracer_pcode.smt import SolverStatus
    from scripts.function_tracer_pcode.tests.conftest import create_mock_result
    from scripts.function_tracer_pcode.tests.unit import test_issue106_pair_limitation_propagation as e0f
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_sat_safety import _connector

    analysis1, analysis2 = e0f._analyses()
    plans = []

    def _stage_plan(*_args, **_kwargs):
        plans.append(len(plans))
        if len(plans) == 1:
            e0f._emit_one_production_signal()
        return create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)

    phase_handler = _mid_plan_phase_handler(PhaseResult)
    e0f._run_pair(
        analyze=lambda _self, name, _timeout: analysis1 if name == "func1" else analysis2,
        stage_plan=_stage_plan, connector=_connector(),
        retry_with_type_fix=True, phase_handler=phase_handler,
    )

    assert len(plans) >= 3, plans  # P0・P1・P2（と P4A tail）
    assert [call.args[0].phase_id for call in phase_handler.execute_phase.call_args_list][:2] == [
        PhaseID.P1_SIGNEDNESS, PhaseID.P2_PATTERN_INT,
    ]


def _mid_plan_phase_handler(phase_result_type):
    from unittest.mock import Mock

    from scripts.function_tracer_pcode.checker.phases.handler import PhaseHandler

    handler = Mock(spec=PhaseHandler)
    handler.execute_phase.side_effect = lambda spec, *_args, **_kwargs: phase_result_type(
        spec.phase_id, applied=True, retry_name=spec.phase_id.value,
        changed_binary1=True, changed_binary2=False,
    )
    handler.should_retry.return_value = True
    handler.get_retry_reason.return_value = "UNKNOWN"
    handler.should_fix_return_type.return_value = True
    handler.run_phase2_return_type_fix.return_value = (False, False, False)
    return handler


# --------------------------------------------------------------------------------------------
# 開始点の規則（静的）: 新しい意味解析を始める API を production で呼ぶ関数は、呼ぶ前に停止の
# 規則を読む。開始点を足すときに規則を読み忘れると、ここが落ちる。
# --------------------------------------------------------------------------------------------

#: 新しい意味解析を始める API（新しい比較・派生 view・phase の型修正・再試行・昇格・lane）。
#: ``EquivalenceChecker.check`` 自体は入口の backstop（``refuse_comparison_after_commit``）を持つ。
_ANALYSIS_START_APIS = frozenset({
    "apply_completed_evidence",
    "execute_phase",
    "run_phase2_return_type_fix",
    "_selective_reanalysis_and_check",
    "_run_phase4a_tail",
    "_maybe_retry_sat_return_type_fix",
    "_run_recursive_abstraction_stage",
    "prepare_recurrence_promotion",
    "run_production_conditional_lane",
})

#: 停止の規則を読む名前（authority の owner と、それを合成する checker の入口）。
_STOP_RULE_READERS = frozenset({
    "counterexample_commit_stop_reason",
    "_counterexample_commit_stop_reason",
    "semantic_analysis_stop_reason",
    "pair_allows_semantic_analysis",
})


def test_every_production_caller_of_an_analysis_start_reads_the_stop_rule():
    import ast
    from pathlib import Path

    package = Path(__file__).resolve().parents[2]
    unguarded = []
    callers = set()
    for path in sorted(package.rglob("*.py")):
        if "tests" in path.relative_to(package).parts:
            continue
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for top in ast.walk(tree):
            if not isinstance(top, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            names = {
                getattr(node, "attr", getattr(node, "id", None))
                for node in ast.walk(top) if isinstance(node, (ast.Name, ast.Attribute))
            }
            called = {
                getattr(node.func, "attr", getattr(node.func, "id", None))
                for node in ast.walk(top) if isinstance(node, ast.Call)
            } & _ANALYSIS_START_APIS
            if not called:
                continue
            # 入れ子の関数は外側の関数ごと見る（外側が規則を読めばよい）。
            callers.add((str(path.relative_to(package)), top.name))
            if not names & _STOP_RULE_READERS:
                unguarded.append((str(path.relative_to(package)), top.name, sorted(called)))
    # 除くのは次の 2 種類だけ:
    # * 入れ子の関数（stage runner の execute_branch）: 外側の関数（run_obligation_branch_plan）の
    #   走査で規則を読んでいればよい。
    # * API 自身の実装の内側の振り分け（PhaseHandler.execute_phase → 各 phase の修正）: 呼び手の
    #   execute_phase の開始点が規則を読む。
    nested_ok = {
        ("proof/obligations/stage_runner.py", "execute_branch"),
        ("checker/phases/handler.py", "execute_phase"),
    }
    assert [row for row in unguarded if row[:2] not in nested_ok] == []
    assert ("proof/obligations/stage_runner.py", "run_obligation_branch_plan") in callers
