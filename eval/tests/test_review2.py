# -*- coding: utf-8 -*-
"""PR #278 review 2 の契約を、本番の wrapper（fake docker）と本番の summarize で確かめる。

1. 外部応答の受理: reader の応答は「要求ごとの終了コード」と「要求に対応する応答の形」の両方を
   満たすときだけ受理する。非 0 終了 + 正しい形、0 終了 + 別の形、途中で切れた出力は、証拠として
   確定せず、container を残し、正常な応答での再試行（``stop``）で回復する。start の判定・status・
   summary の応答も同じ。
2. permanent が 1 つでもあれば、他の理由（resumable を含む）にかかわらず元の評価で再開しない。
   何も書かずに拒否する。
3. 中断・OOM は、その pair を実行した execution の launch に帰属させてから数える。前の execution
   の未完了の receipt が後の snapshot に残っても再計上せず、後の launch の OOM を結び付けない。
   同じ pair を後の execution で実際に再試行して止まったものは別の event として数える。帰属
   できない receipt は別に報告する。

``test_review2_regressions.py`` の 3 件は、この中から旧実装（106c1c35）の誤動作を検出するものを
CLI と記録の file だけで書き直したもの。
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import signal

import pytest

import records
import wrapper
from harness import Harness, repo_head


@pytest.fixture
def h(tmp_path, monkeypatch):
    harness = Harness(tmp_path, monkeypatch)
    yield harness
    try:
        harness.update(lambda d: d.update({"fail": {}, "respond": {}}))
        harness.end_container(exit_code=137)
        harness.wait_released(timeout=60)
    except (OSError, ValueError, KeyError, AssertionError):
        pass


# ---------------------------------------------------------------------------
# 1. 外部応答の受理
# ---------------------------------------------------------------------------

RESPONSES = {
    "nonzero_with_valid_json": {"returncode": 1},
    "zero_with_other_shape": {"stdout": json.dumps({"schema": "something-else"})},
    "zero_with_wrong_schema_fields": None,   # 要求ごと（下の _response）
    "truncated": {"truncate": True},
    "empty": {"stdout": ""},
}
#: 正しい schema のまま、その要求の中身の欄だけを壊す。
BROKEN_FIELD = {"launch-evidence": {"unterminated_pairs": "not a list"},
                "completion": {"reasons": "not a list"},
                "report": {"reasons": [{"code": "chain_open", "category": "blocking", "detail": ""}]}}


def _response(request, name):
    if name == "zero_with_wrong_schema_fields":
        return {"replace_json": BROKEN_FIELD[request]}
    return RESPONSES[name]


@pytest.mark.parametrize("response", sorted(RESPONSES))
def test_an_unaccepted_evidence_response_keeps_the_container_and_stop_recovers(h, capsys, response):
    assert h.start() == wrapper.EXIT_OK
    h.respond("launch-evidence", **_response("launch-evidence", response))
    h.end_container(exit_code=0)
    h.wait_released()
    directory = h.ev.launch_dir(1)
    check = h.records()
    assert not check.problems
    assert check.unfinished is not None and check.unfinished.state == records.STATE_EXIT
    assert not (directory / records.EVIDENCE).exists(), "an unaccepted response was recorded"
    assert [c["status"] for c in h.containers()] == ["exited"], "the container must be kept"
    assert h.start() == wrapper.EXIT_REFUSED  # 記録の済んでいない launch がある
    assert h.run("stop") == wrapper.EXIT_OK   # 正常な応答での再試行
    (launch,) = h.records().launches
    assert launch.state == records.STATE_RELEASED and launch.evidence["schema"] == records.EVIDENCE_SCHEMA
    assert h.containers() == []


@pytest.mark.parametrize("response", sorted(RESPONSES))
def test_an_unaccepted_completion_response_refuses_the_start_without_writing(h, capsys, response):
    h.finished_launch()
    h.respond("completion", **_response("completion", response))
    before = h.snapshot()
    calls = len(h.read_state()["calls"])
    assert h.start() == wrapper.EXIT_REFUSED
    assert "cannot judge the evaluation" in capsys.readouterr().err
    assert h.snapshot() == before
    assert not [c for c in h.read_state()["calls"][calls:] if c[:2] == ["run", "-d"]]


@pytest.mark.parametrize("response", sorted(RESPONSES) + ["exit_code_disagrees_with_verdict"])
def test_an_unaccepted_report_response_is_not_a_verdict(h, capsys, response):
    h.complete_evaluation()
    override = ({"returncode": 1} if response == "exit_code_disagrees_with_verdict"
                else _response("report", response))
    if response == "nonzero_with_valid_json":
        override = {"returncode": 3}
    h.respond("report", **override)
    capsys.readouterr()
    assert h.run("summary") == 2
    captured = capsys.readouterr()
    assert "VERDICT" not in captured.out and "cannot be produced" in captured.err
    assert h.run("summary") == 0  # 応答が正常なら同じ評価は完了


def test_an_unaccepted_verify_response_is_shown_as_unavailable(h, capsys):
    h.complete_evaluation()
    h.respond("verify", returncode=1)
    capsys.readouterr()
    assert h.run("status", "--verify") == wrapper.EXIT_OK
    assert "execution_chain verify: unavailable" in capsys.readouterr().out


def test_an_incomplete_environment_probe_is_not_recorded_as_conditions(h, capsys):
    probe = dict(h.read_state()["probe"])
    probe.pop("z3_version")
    h.update(lambda d: d.update({"probe": probe}))
    assert h.start() == wrapper.EXIT_REFUSED
    assert "did not report z3_version" in capsys.readouterr().err
    assert not h.ev.wrapper.exists()


@pytest.mark.parametrize("body", ["[]", "[{}]", '[{"Id": "x", "State": {}}]', "not json"])
def test_an_inspect_answer_that_is_not_a_container_is_unobservable_not_absent(h, capsys, body):
    """inspect が 0 で終わっても、container を記述しない応答は「存在しない」にしない。"""
    assert h.start() == wrapper.EXIT_OK
    h.update(lambda d: d.update({"inspect_stdout": body, "inspect_stdout_times": 3}))
    h.end_container(exit_code=0)
    h.wait_released()
    (launch,) = h.records().launches
    assert launch.state == records.STATE_RELEASED and launch.exit_kind == records.KIND_RAN


def test_a_ps_answer_that_does_not_list_containers_refuses_the_start(h, capsys):
    h.update(lambda d: d.update({"ps_stdout": "Got permission denied while trying to connect"}))
    assert h.start() == wrapper.EXIT_REFUSED
    assert "cannot observe the evaluation-slot containers" in capsys.readouterr().err
    assert not h.ev.wrapper.exists()


# ---------------------------------------------------------------------------
# 2. permanent は他の理由にかかわらず再開しない
# ---------------------------------------------------------------------------


def _unobserved_launch(h, *, open_chain):
    """container が wrapper の外で消された launch（permanent）を作る。"""
    assert h.start() == wrapper.EXIT_OK
    h.build_tree()
    if open_chain:
        next(h.ev.out.rglob("*.pair-status.json")).unlink()  # resumable（連鎖が OPEN）も同時に
    pid = (wrapper.lock_holders(h.ev) or [None])[0]
    os.kill(pid, signal.SIGKILL)
    h.wait_for(lambda: wrapper.lock_holders(h.ev) is None, message="the lock")
    h.remove_containers()
    assert h.run("stop") == wrapper.EXIT_OK


@pytest.mark.parametrize("shape", ["permanent_only", "permanent_and_resumable",
                                   "foreign_and_resumable"])
def test_a_permanent_reason_refuses_the_resume_whatever_else_is_there(h, capsys, shape):
    if shape == "foreign_and_resumable":
        assert h.start() == wrapper.EXIT_OK
        h.build_tree(fingerprint="eval-env-v1:" + "9" * 64)
        next(h.ev.out.rglob("*.pair-status.json")).unlink()
        h.end_container(exit_code=0)
        h.wait_released()
    else:
        _unobserved_launch(h, open_chain=shape == "permanent_and_resumable")
    capsys.readouterr()
    h.run("summary", "--json")
    categories = {r["category"] for r in json.loads(capsys.readouterr().out)["reasons"]}
    assert "permanent" in categories
    if shape != "permanent_only":
        assert "resumable" in categories
    before = h.snapshot()
    calls = len(h.read_state()["calls"])
    assert h.start() == wrapper.EXIT_REFUSED
    assert "separate evaluation (another --tag)" in capsys.readouterr().err
    assert h.snapshot() == before
    assert not [c for c in h.read_state()["calls"][calls:] if c[:2] == ["run", "-d"]]


# ---------------------------------------------------------------------------
# 3. 中断・OOM の帰属（E1 の未完了の receipt が E2 の snapshot に残る）
# ---------------------------------------------------------------------------

PAIR = "S/Neq/f/f_N_B1_O_B1.pair-status.json"


def _receipt(h, run_id, nonce, *, kind="killed", started=100.0, finished=110.0):
    metrics = h.ev.out / "S" / "Neq" / "f" / ".runtime-metrics"
    metrics.mkdir(parents=True, exist_ok=True)
    body = {"run_id": run_id, "execution_nonce": nonce, "started_at_epoch": started}
    if kind == "killed":
        body.update(state="COMPLETED", status="INCOMPLETE", child_returncode=-9,
                    finished_at_epoch=finished)
        (metrics / "f_N_B1_O_B1.runtime.json").write_text(json.dumps(body))
    else:
        body.update(state="RUNNING")
        (metrics / "f_N_B1_O_B1.runtime.json").unlink(missing_ok=True)
    (metrics / "f_N_B1_O_B1.progress.json").write_text(json.dumps(body))


def _execution(h, run_id):
    """この評価の条件で始まった execution の開始の記録（fingerprint と source digest）。"""
    from scripts.function_tracer_pcode.reporting.execution_identity import source_tree_digest

    directory = h.ev.out / ".executions" / run_id
    directory.mkdir(parents=True, exist_ok=True)
    text = (f"runtime_run_id={run_id}\nenvironment_fingerprint={h.meta()['fingerprint']}\n"
            f"analysis_source_digest_start={source_tree_digest(wrapper.REPO)}\n"
            f"git_commit={repo_head()}\ngit_dirty=0\n")
    (h.ev.out / "run_manifest.txt").write_text(text)  # runner は開始の記録より先にこれを置く
    (directory / "run_manifest.start.txt").write_text(text)


def _launch(h, run_id, *, receipt=None, oom_killed=False, stop=False):
    """1 回の launch: execution を作り、必要なら receipt を書き、終わらせて終端まで待つ。"""
    assert h.start() == wrapper.EXIT_OK
    _execution(h, run_id)
    if receipt is not None:
        _receipt(h, run_id, **receipt)
    if stop:
        h.update(lambda d: d.update({"stop_exit_code": 143}))
        if oom_killed:
            h.end_container(exit_code=137, oom_killed=True)
        assert h.run("stop") == wrapper.EXIT_OK
    else:
        h.end_container(exit_code=137 if oom_killed else 0, oom_killed=oom_killed)
        h.wait_released()


def _interruptions(h, capsys):
    capsys.readouterr()
    h.run("summary", "--json")
    return json.loads(capsys.readouterr().out)["interruptions"]


E1, E2, E3 = "1" * 32, "2" * 32, "3" * 32


@pytest.mark.parametrize("e2_end", ["finished", "stopped", "oom_killed"])
def test_a_kill_left_by_e1_is_counted_once_and_not_tied_to_e2(h, capsys, e2_end):
    _launch(h, E1, receipt={"nonce": "n1"})
    _launch(h, E2, oom_killed=e2_end == "oom_killed", stop=e2_end == "stopped")
    result = _interruptions(h, capsys)
    assert [(r["launch"], r["run_id"], r["cause"]) for r in result["pairs"]] == [(1, E1, "external_kill")]
    (row,) = result["pairs"]
    assert row["possible_oom"] != records.OOM_YES, "E2's OOM must not be tied to E1's kill"
    assert row["observed_in"] == [1, 2]
    assert result["totals"]["external_kill"] == 1 and result["totals"]["repeat_observations"] == 1
    assert result["unattributed"] == []


def test_the_same_pair_killed_again_in_e2_is_a_second_event(h, capsys):
    _launch(h, E1, receipt={"nonce": "n1"})
    _launch(h, E2, receipt={"nonce": "n2", "started": 200.0, "finished": 210.0}, oom_killed=True)
    result = _interruptions(h, capsys)
    rows = sorted((r["launch"], r["run_id"], r["execution_nonce"], r["possible_oom"])
                  for r in result["pairs"])
    assert rows == [(1, E1, "n1", "unobserved"), (2, E2, "n2", "yes")]
    assert result["totals"]["external_kill"] == 2


def test_a_running_receipt_left_by_e1_is_one_stop_of_e1(h, capsys):
    _launch(h, E1, receipt={"nonce": "n1", "kind": "running"}, stop=True)
    _launch(h, E2, oom_killed=True)
    _launch(h, E3)
    result = _interruptions(h, capsys)
    (row,) = result["pairs"]
    assert (row["launch"], row["cause"], row["possible_oom"]) == (1, "execution_stopped", "not_applicable")
    assert row["observed_in"] == [1, 2, 3]


def test_a_receipt_no_launch_recorded_is_reported_apart(h, capsys):
    _launch(h, E1)
    _receipt(h, "f" * 32, "nx")  # どの launch の execution でもない
    _launch(h, E2, oom_killed=True)
    result = _interruptions(h, capsys)
    assert result["pairs"] == []
    assert [(r["run_id"], r["observed_in"]) for r in result["unattributed"]] == [("f" * 32, [2])]
    assert result["totals"]["unattributed"] == 1


@pytest.mark.parametrize("body", [
    '[{"Id": "%s", "State": {"Status": "running"}}]' % ("0" * 63 + "1"),   # Running が無い
    '[{"Id": "x", "State": {"Status": "exited", "Running": false}}]',      # Id が container の形でない
])
def test_stop_does_not_take_a_malformed_inspect_answer_for_a_stopped_container(h, capsys, body):
    """動いている container について、形の違う inspect の応答を「止まった」と読まない。"""
    assert h.start() == wrapper.EXIT_OK
    pid = (wrapper.lock_holders(h.ev) or [None])[0]
    os.kill(pid, signal.SIGKILL)
    h.wait_for(lambda: wrapper.lock_holders(h.ev) is None, message="the lock")
    h.update(lambda d: d.update({"inspect_stdout": body, "inspect_stdout_times": 100}))
    assert h.run("stop", "--wait", "5") == wrapper.EXIT_FAILED
    assert "cannot observe the container" in capsys.readouterr().err
    assert not (h.ev.launch_dir(1) / records.EXIT).exists()
    assert [c["status"] for c in h.containers()] == ["running"]
    h.update(lambda d: d.update({"inspect_stdout_times": 0}))
    assert h.run("stop") == wrapper.EXIT_OK  # 正しい応答なら回収できる
    assert h.records().launches[0].state == records.STATE_RELEASED
