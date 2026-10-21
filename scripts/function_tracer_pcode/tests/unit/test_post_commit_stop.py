# -*- coding: utf-8 -*-
"""安全な counterexample を commit した後は新しい意味解析を始めない（#130 S3 / A-5）。

commit した判定は authority の記録で、後の解析では消えない。修正前は commit の後も、legacy の
結果しだいで次の解析が始まっていた:

* final gate の veto で legacy の結果が None になると、次の phase（P1 / P2）と stage の fallback
  （monolithic）が走り、final gate が 2 回呼ばれた。
* legacy の結果が False なら、SAT の後の再試行（P4C の戻り値型の修正と、その後の P4A tail）が走った。

守る契約（owner は ``checker/pair_execution.py::semantic_analysis_stop_reason``）: commit の記録が
あれば、phase・SAT の後の再試行・stage の fallback・再帰の昇格・conditional lane を始めない。
legacy の結果の値では判定しない。commit が無ければ流れは今どおり。
"""

from __future__ import annotations

from contextlib import contextmanager

import pytest

from scripts.function_tracer_pcode.checker.pair_execution import (
    SEMANTIC_ANALYSIS_STOP_COUNTEREXAMPLE_COMMITTED,
    SEMANTIC_ANALYSIS_STOP_PAIR_TERMINAL,
    semantic_analysis_stop_reason,
)
from scripts.function_tracer_pcode.checker.phases.handler import PhaseHandler, PhaseID
from scripts.function_tracer_pcode.tests.unit.test_post_commit_veto import (
    _CONFIGS,
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

    monkeypatch.setattr(pair_execution, "pair_counterexample_committed", lambda _session=None: True)
    monkeypatch.setattr(pair_execution, "pair_stop_state", lambda: PairStopState.NONE)
    assert semantic_analysis_stop_reason() == SEMANTIC_ANALYSIS_STOP_COUNTEREXAMPLE_COMMITTED
    monkeypatch.setattr(pair_execution, "pair_stop_state", lambda: PairStopState.PAIR_TERMINAL_DEADLINE)
    assert semantic_analysis_stop_reason() == SEMANTIC_ANALYSIS_STOP_PAIR_TERMINAL
    monkeypatch.setattr(pair_execution, "pair_counterexample_committed", lambda _session=None: False)
    monkeypatch.setattr(pair_execution, "pair_stop_state", lambda: PairStopState.NONE)
    assert semantic_analysis_stop_reason() is None
