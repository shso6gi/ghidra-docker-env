# -*- coding: utf-8 -*-
"""Issue #165: 終端の状態機械を model で検査する（計画 v5 §6.7、Phase 0 gate G4）。

model（``tests/fixtures/issue165/terminal_model.py``）は production の
``next_step`` をそのまま使い、production の公開操作を 1 回の durable な公開
ごとに写して、child と supervisor のあらゆる公開境界での crash / restart から
到達する状態を閉包まで辿る。期待終端（oracle）は ``next_step`` ではなく
scenario の事実（child がどこまで進んだか、どう終わったか、E が durable か、
mode、envelope）から決める。

実 process の crash test（``test_issue165_supervisor_terminal.py``）は同じ
oracle（``expected_terminal``）で期待値を作るので、model と実 store の結果は
同じ仕様で照合される。
"""

from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.authority.process import terminal_recovery as tr
from scripts.function_tracer_pcode.authority.process.checkpoint_vocabulary import CheckpointState
from scripts.function_tracer_pcode.tests.fixtures.issue165 import terminal_model as model


@pytest.fixture(scope="module")
def explored():
    return model.explore()


def test_every_reachable_state_converges_to_its_oracle(explored):
    # explore() が失敗（oracle と違う終端・cycle・状態を変えない操作・
    # next_step の例外・code の無い INVALID）を見つければ ModelFailure で落ちる。
    reachable = explored["reachable"]
    assert len(reachable) > 500
    assert explored["transitions"] > 5000
    terminals = {oracle[0] for oracle in reachable.values()}
    assert terminals == {"TIMEOUT", "ERROR", "RESOLVED", "INVALID"}


def test_the_reachable_set_covers_every_crash_window_the_plan_names(explored):
    """計画 §6.5 の窓（claimed durable / CAS 前、bundle 部分、A 途中 …）が到達集合にある。"""

    states = [state for state, _mode in explored["reachable"]]

    def any_state(predicate):
        return any(predicate(state) for state in states)

    assert any_state(lambda s: s.pending is not None and s.pending[2])  # bootstrap pending
    assert any_state(  # bootstrap commit が前任を退避している途中
        lambda s: s.pending is not None and s.pending[2] and s.live is not None
        and s.live.state == CheckpointState.RESOLVED.value and len(s.live.members) < 6
    )
    assert any_state(  # claimed durable / CAS 前
        lambda s: "claimed.json" in s.timeout_members and s.live is not None
        and s.live.state == CheckpointState.ACTIVE.value
    )
    assert any_state(  # timeout bundle の部分書込み
        lambda s: 1 < len(s.timeout_members) < 4
    )
    assert any_state(  # 完成した bundle、state 更新前
        lambda s: len(s.timeout_members) == 4 and s.live.state == CheckpointState.TIMED_OUT_CLAIMED.value
    )
    assert any_state(  # A durable、移動前
        lambda s: s.archive is not None and not s.archive[2]
    )
    assert any_state(  # A の途中（一部 member が history）
        lambda s: s.archive is not None and s.archive[2] and s.live is not None
    )
    assert any_state(  # ERROR member の部分書込み
        lambda s: 0 < len(s.error_members) < 4
    )
    assert any_state(lambda s: s.projection is not None)  # projection 直後


def test_malformed_and_conflicting_states_are_rejected_before_any_write(explored):
    counts = model.check_malformed(explored["reachable"])
    for name in (*model.TAMPERS, *model.CONFLICTS, "unrelated-history"):
        assert counts[name] > 0, name


def test_d_only_restart_is_invalid_without_inventing_an_exit():
    state = model.ModelState(deadline=True)
    for mode in tr.ExitMode:
        step = tr.next_step(model.snapshot(state, mode))
        assert step.kind is tr.StepKind.INVALID
        assert step.invalid_code is tr.InvalidCode.DEADLINE_WITHOUT_EXIT_OBSERVATION


def test_the_committed_model_summary_is_the_current_model(explored):
    """``terminal_model.head.json`` が今の model の結果と一致する（証拠の陳腐化を防ぐ）。"""

    import json
    from pathlib import Path

    committed = json.loads(
        (Path(model.__file__).parent / "terminal_model.head.json").read_text(encoding="utf-8")
    )
    reachable = explored["reachable"]
    terminals: dict = {}
    for oracle in reachable.values():
        key = f"{oracle[0]}:{oracle[1]}"
        terminals[key] = terminals.get(key, 0) + 1
    assert committed["reachable_states"] == len(reachable)
    assert committed["crash_transitions"] == explored["transitions"]
    assert committed["terminal_oracles"] == terminals
