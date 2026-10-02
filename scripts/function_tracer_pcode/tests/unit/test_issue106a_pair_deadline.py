# -*- coding: utf-8 -*-
"""Issue #106 PR-106-A: pair 全体の協調的 deadline の再生（E1 / E2 / E3）。

E1 / E2 / E3 は記録済み P-code を **production の `check_from_binaries`**（pilot connector・
worker authority・receipt・canonical bundle）で再生する。1 process 1 pair の条件を保つため
各再生は子 process（`_deadline_replay_driver`）で 1 回だけ走らせ、期限は
`DeadlinePolicy.clock` だけで切る（他の仕組みには手を入れない）。
"""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys

import pytest

from scripts.function_tracer_pcode.core.errors import (
    DeadlineExceeded,
    PairStopState,
    reset_pair_failure_scopes,
)

pytestmark = pytest.mark.recorded_replay

PACKAGE_ROOT = pathlib.Path(__file__).resolve().parents[2]
REPO_ROOT = PACKAGE_ROOT.parents[1]
FIXTURES = PACKAGE_ROOT / "tests" / "fixtures" / "pcode"
DRIVER = "scripts.function_tracer_pcode.tests.unit._deadline_replay_driver"
BUDGET_REASON = DeadlineExceeded.REASON_ID
REPLAY_TIMEOUT_SECONDS = 240


@pytest.fixture(autouse=True)
def _clean_ledgers():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


def _replay_with_deadline(case_id, trip_stage, *, fast_path="recorded", tmp_path, extra=()):
    """子 process で 1 回だけ再生して観測を読む（採点は呼び出し側）。"""

    output = tmp_path / f"{case_id}.{trip_stage}.{'-'.join(extra) or 'plain'}.json"
    completed = subprocess.run(
        [
            sys.executable, "-B", "-m", DRIVER,
            "--case-dir", str(FIXTURES / case_id), "--case-id", case_id,
            "--trip-stage", trip_stage, "--fast-path", fast_path, "--output", str(output),
            *extra,
        ],
        cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=REPLAY_TIMEOUT_SECONDS,
    )
    assert completed.returncode == 0, completed.stderr[-4000:]
    return json.loads(output.read_text(encoding="utf-8"))


def _expected(case_id, variant="default"):
    name = case_id if variant == "default" else f"{case_id}.{variant}"
    return json.loads((FIXTURES / "expected" / f"{name}.json").read_text(encoding="utf-8"))


def _assert_deadline_unknown(report, stage):
    assert report["failure"] is None, report["failure"]
    assert report["tripped_at"] == [stage]
    assert report["final_outcome"] == "UNKNOWN"
    assert report["error_message"] is None
    # 期限の cause が判定を止める（打ち切りより前に active だった他の cause の reason は残ってよい）
    assert BUDGET_REASON in report["reason_ids"]
    assert report["limitation_site"] == stage
    assert report["limitation_type"] == "DeadlineExceeded"
    assert report["limitation_disposition"] == "ATTRIBUTED_NEW_CAUSE"
    assert report["pair_stop_state"] == PairStopState.PAIR_TERMINAL_DEADLINE.value
    # authority の確定・receipt・canonical bundle は期限の後も作られる（検証済み）
    assert report["has_decision_receipt"] is True
    assert report["has_finalization_bundle"] is True
    assert report["analysis_deadline"]["tripped"] is True
    assert report["analysis_deadline"]["trip_stage"] == stage
    # 期限の後に conditional lane を始めない
    assert report["conditional_lane"] == {
        "skipped": "pair_terminal",
        "pair_stop_state": PairStopState.PAIR_TERMINAL_DEADLINE.value,
    }


# ---------------------------------------------------------------------------
# E3: 期限を与えても切れなければ結果は同じ（観測）。E1 の対象 stage もここで知る
# ---------------------------------------------------------------------------

#: E1 の対象（case → その再生で通る checkpoint の stage）。E3 の観測と一致することを確かめる
E1_CASES = {
    "max_snippet_N_B2_O_B4": (
        "decompile", "effect_summary", "trace_returns", "recurrence_summary",
        "condition_simplify", "condition_oracle", "phase_plan", "obligation",
        "query_build", "solver", "analysis_complete",
    ),
    # typed producer（call effect）の solver 実行・obligation を通る
    "gammln_snippet_B1_B2": ("bounded_refinement", "trace_pcode", "solver", "obligation"),
    # pairwise → monolithic fallback を通る
    "sign_snippet_N_B2_O_B4": ("solver", "phase_plan", "query_build"),
}


@pytest.mark.parametrize("case_id", sorted(E1_CASES))
def test_e3_a_long_deadline_keeps_the_recorded_result_and_reaches_the_e1_stages(case_id, tmp_path):
    report = _replay_with_deadline(case_id, "none", tmp_path=tmp_path)
    expected = _expected(case_id)
    assert report["failure"] is None
    assert report["final_outcome"] == expected["final_outcome"]
    assert set(expected["expected_stable_reason_ids"]) <= set(report["reason_ids"])
    assert BUDGET_REASON not in report["reason_ids"]
    deadline = report["analysis_deadline"]
    assert deadline["tripped"] is False
    assert set(E1_CASES[case_id]) <= set(deadline["stage_reads"])


# ---------------------------------------------------------------------------
# E1: 各 checkpoint で期限が切れると reason 付き UNKNOWN（stage / terminal deadline / receipt）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("case_id", "stage"),
    [(case_id, stage) for case_id, stages in sorted(E1_CASES.items()) for stage in stages],
)
def test_e1_a_deadline_at_each_checkpoint_is_a_reasoned_unknown_with_a_receipt(case_id, stage, tmp_path):
    _assert_deadline_unknown(_replay_with_deadline(case_id, stage, tmp_path=tmp_path), stage)


# ---------------------------------------------------------------------------
# E2: EQ closure / NOT_EQ の後でも、解析の完了点で期限を過ぎていれば UNKNOWN（fail closed）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("case_id", "fast_path", "decided"),
    [
        ("bessj0_snippet_B10_B11", "on", "EQUIVALENT"),  # identity fast path の EQ closure
        ("max_snippet_N_B2_O_B4", "recorded", "NOT_EQ"),  # safe counterexample の NOT_EQ
    ],
)
def test_e2_a_decided_pair_past_the_deadline_fails_closed_to_unknown(case_id, fast_path, decided, tmp_path):
    decided_report = _replay_with_deadline(case_id, "none", fast_path=fast_path, tmp_path=tmp_path)
    assert decided_report["final_outcome"] == decided
    _assert_deadline_unknown(
        _replay_with_deadline(case_id, "analysis_complete", fast_path=fast_path, tmp_path=tmp_path),
        "analysis_complete",
    )




# ---------------------------------------------------------------------------
# レビュー 3 巡目: 期限が短くした上限の後の独立した故障は、期限なしと同じ最終結果になる
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("case_id", ["gammln_snippet_B1_B2", "max_snippet_N_B2_O_B4"])
def test_an_independent_solver_failure_after_a_shortened_limit_keeps_the_final_result(case_id, tmp_path):
    """最初の `Z3Solver` の実行だけ期限を 1.0 s 先（窓 0.5 s）にし、z3 の check が 0.7 s で独立した
    例外を上げる。同じ注入を期限なしで再生した結果と、final outcome・reason・error・receipt が同じ。

    修正前（23ace10）は、時計が実行の予算を過ぎていることだけで例外を時間切れ（TIMEOUT）に分類し、
    期限の切断として `analysis_budget_exceeded` の UNKNOWN にしていた（レビュー 3 巡目の再現 2）。
    """

    inject = ("--inject", "z3_error_after_limit")
    without = _replay_with_deadline(case_id, "none", tmp_path=tmp_path, extra=(*inject, "--no-deadline"))
    within = _replay_with_deadline(case_id, "none", tmp_path=tmp_path, extra=inject)
    for report in (without, within):
        assert report["failure"] is None, report["failure"]
        assert report["injected"]["injected"] is True
        assert report["injected"]["row_status"] == "ERROR"
        assert report["injected"]["row_end"] == "failed"
        assert "injected backend failure" in report["injected"]["row_error"]
    assert without["injected"]["row_limited"] is False
    assert within["injected"]["row_limited"] is True  # 上限は期限で短くなっていた
    for key in ("final_outcome", "reason_ids", "error_message", "has_decision_receipt", "has_finalization_bundle"):
        assert within[key] == without[key], key
    assert BUDGET_REASON not in within["reason_ids"]
    assert within["limitation_site"] is None
    assert within["pair_stop_state"] is None
    assert within["analysis_deadline"]["tripped"] is False
