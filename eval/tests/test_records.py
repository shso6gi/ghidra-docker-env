# -*- coding: utf-8 -*-
"""eval/records.py の契約: launch の状態機械、破損の検出、OOM の帰属（評価計画 v2 PR-D）。

* 確定した記録の欠損・破損・不整合は ``problems``（破損）として報告し、隠さない。正常な中断で
  残る状態（未完了の最後の launch、書きかけの残骸）は破損にしない。両者を対で確かめる。
* OOM の増分は、直前の **有効な** counter の観測から今回の観測までの区間に結び付ける。観測の
  欠け・counter の reset・覆われていない区間は ``unobserved``（no にしない）。
"""

from __future__ import annotations

import json
import shutil

import pytest

import records
import summarize
import wrapper
from harness import Harness


@pytest.fixture
def h(tmp_path, monkeypatch):
    harness = Harness(tmp_path, monkeypatch)
    yield harness
    try:
        harness.end_container(exit_code=137)
        harness.wait_released(timeout=60)
    except (OSError, ValueError, KeyError, AssertionError):
        pass


# ---------------------------------------------------------------------------
# OOM の帰属
# ---------------------------------------------------------------------------


def _obs(at, oom_kill):
    return {"at_epoch": at, "observed": oom_kill is not None, "oom_kill": oom_kill}


def test_an_increment_belongs_to_the_interval_since_the_previous_valid_observation():
    """review 1 P2 の反例: 観測は 10 秒ごと、保存（旧実装）は 5 分ごと。

    pair A は t=10..20 で終わり、OOM の増分は t=290..300 の観測で初めて見えた。直前の
    有効な観測は t=290 なので、A とは結び付かない（旧実装は保存行の t=0 を始点にして A に付けた）。
    """
    watch = [_obs(t, 0) for t in range(0, 300, 10)] + [_obs(300, 1)]
    assert records.oom_attribution(watch, start=10.0, end=20.0, container_oom_killed=False) == "no"
    assert records.oom_attribution(watch, start=280.0, end=295.0,
                                   container_oom_killed=False) == "yes"
    # 旧実装が見た保存行だけ（t=0 と t=300）なら区間は 0..300 になる: 区間の定義が違うことの確認。
    sparse = [_obs(0, 0), _obs(300, 1)]
    assert records.oom_attribution(sparse, start=10.0, end=20.0, container_oom_killed=False) == "yes"


def test_unreadable_observations_widen_the_interval_instead_of_hiding_the_increment():
    watch = [_obs(0, 0), _obs(10, None), _obs(20, None), _obs(30, 1)]
    (interval,) = records.counter_intervals(watch)
    assert (interval.start, interval.end, interval.delta) == (0, 30, 1)
    assert records.oom_attribution(watch, start=12.0, end=15.0, container_oom_killed=False) == "yes"


def test_a_counter_reset_is_unknown_not_zero():
    watch = [_obs(0, 5), _obs(10, 2), _obs(20, 2)]
    assert records.counter_intervals(watch)[0].delta is None
    assert records.oom_attribution(watch, start=3.0, end=8.0, container_oom_killed=False) == "unobserved"
    assert records.oom_attribution(watch, start=12.0, end=18.0, container_oom_killed=False) == "no"


@pytest.mark.parametrize("watch, start, end", [
    ([], 1.0, 2.0),                                  # 観測が無い
    ([_obs(0, 0)], 1.0, 2.0),                        # 区間を作れない
    ([_obs(0, 0), _obs(10, 0)], 5.0, 30.0),          # 終わりが最後の観測より後
    ([_obs(10, 0), _obs(20, 0)], 1.0, 15.0),         # 始まりが最初の観測より前
    ([_obs(0, 0), _obs(10, 0)], None, 5.0),          # 時刻が無い
])
def test_an_uncovered_pair_is_unobserved_not_cleared(watch, start, end):
    assert records.oom_attribution(watch, start=start, end=end, container_oom_killed=False) == "unobserved"


def test_a_container_oom_kill_is_yes_whatever_the_observations():
    assert records.oom_attribution([], start=None, end=None, container_oom_killed=True) == "yes"


# ---------------------------------------------------------------------------
# 状態機械と破損（正常な中断の状態と、確定した記録の破損を対で）
# ---------------------------------------------------------------------------


def _released_launch(h, **tree_options):
    assert h.start() == wrapper.EXIT_OK
    h.build_tree(**tree_options)
    h.end_container(exit_code=0)
    h.wait_released()
    check = h.records()
    assert not check.problems and check.launches[0].state == records.STATE_RELEASED
    return h.ev.launch_dir(1)


@pytest.mark.parametrize("name", [records.LAUNCH, records.CONTAINER, records.EXIT,
                                  records.RUNNER_LOG, records.EVIDENCE, records.RELEASED])
@pytest.mark.parametrize("damage", ["delete", "corrupt"])
def test_a_damaged_committed_record_is_reported_and_blocks_start_and_summary(h, capsys, name, damage):
    directory = _released_launch(h)
    path = directory / name
    if damage == "delete":
        path.unlink()
    else:
        path.write_text("{corrupt" if name != records.RUNNER_LOG else "edited log\n")
    check = h.records()
    assert check.problems, f"{damage} of {name} must be reported"
    before = h.snapshot()
    assert h.start() == wrapper.EXIT_REFUSED
    assert "damaged" in capsys.readouterr().err
    assert h.run("stop") == wrapper.EXIT_FAILED
    capsys.readouterr()
    assert h.run("summary", "--json") == 2
    result = json.loads(capsys.readouterr().out)
    assert result["verdict"] == "UNVERIFIABLE"
    assert h.snapshot() == before


@pytest.mark.parametrize("damage", ["launch_dir", "launches_dir", "journal", "journal_line",
                                    "unknown_entry", "meta"])
def test_whole_or_partial_loss_of_the_records_is_reported(h, capsys, damage):
    # ledger が拒否する tree なので、2 回目の start も launch する（execution は作らない）。
    directory = _released_launch(h, end_overrides={"run_pair_failures": "1"})
    assert h.start() == wrapper.EXIT_OK
    h.end_container(exit_code=0)
    h.wait_released()
    if damage == "launch_dir":
        shutil.rmtree(directory)                                 # 番号の欠け + execution の帰属
    elif damage == "launches_dir":
        shutil.rmtree(h.ev.wrapper / records.LAUNCHES_DIR)        # execution の帰属
    elif damage == "journal":
        (h.ev.wrapper / records.JOURNAL).unlink()
    elif damage == "journal_line":
        shutil.rmtree(h.ev.launch_dir(2))                         # journal が名指す launch が無い
    elif damage == "unknown_entry":
        (directory / "notes.txt").write_text("x")
    else:
        (h.ev.wrapper / records.META).unlink()
    capsys.readouterr()
    assert h.run("summary", "--json") == 2
    output = capsys.readouterr().out
    if damage != "meta":  # meta が無ければ summary は判定の材料が無いと言って終わる
        result = json.loads(output)
        assert result["verdict"] == "UNVERIFIABLE", result["reasons"]
    assert h.start() == wrapper.EXIT_REFUSED


def test_states_left_by_a_normal_interruption_are_not_damage(h, tmp_path):
    root = h.ev.wrapper / records.LAUNCHES_DIR
    root.mkdir(parents=True)
    (h.ev.wrapper / records.JOURNAL).write_text("")
    # 書きかけの staging dir と一時 file は残骸（証拠ではない）。
    (root / records.staging_name(1, "abcd")).mkdir()
    check = records.read_records(h.ev.wrapper)
    assert not check.problems and check.debris == [records.staging_name(1, "abcd")]
    # 起動の要求だけが確定した launch は未完了（破損ではない）。
    directory = root / "1"
    directory.mkdir()
    wrapper.write_json(directory / records.LAUNCH, {"schema": records.LAUNCH_SCHEMA, "launch": 1,
                                                   "execution_ids_before": []})
    (directory / ".exit.json.tmp-1-abcdef01").write_text("partial")
    check = records.read_records(h.ev.wrapper)
    assert not check.problems
    assert check.unfinished is not None and check.unfinished.state == records.STATE_REQUESTED


def test_an_unfinished_launch_before_a_later_launch_is_damage(tmp_path):
    root = tmp_path / records.LAUNCHES_DIR
    for number in (1, 2):
        (root / str(number)).mkdir(parents=True)
        wrapper.write_json(root / str(number) / records.LAUNCH, {
            "schema": records.LAUNCH_SCHEMA, "launch": number, "execution_ids_before": []})
    (tmp_path / records.JOURNAL).write_text("")
    check = records.read_records(tmp_path)
    assert any("unfinished but a later launch exists" in p for p in check.problems)


def test_executions_must_match_the_launches_that_recorded_them(h, capsys):
    _released_launch(h)
    check = h.records()
    assert records.attribution_problems(check, records.started_executions(h.ev.out)) == []
    stray = h.ev.out / ".executions" / ("f" * 32)
    stray.mkdir()
    # 開始の記録の無い dir は execution ではない（pair を始めていない）。
    assert records.attribution_problems(check, records.started_executions(h.ev.out)) == []
    (stray / records.START_RECORD).write_text("runtime_run_id=" + "f" * 32 + "\n")
    problems = records.attribution_problems(check, records.started_executions(h.ev.out))
    assert any("not started by a recorded launch" in p for p in problems)


def test_a_gap_in_the_launch_numbers_is_damage_on_its_own(tmp_path):
    """journal も execution も手掛かりにならない欠番（launch 1 と 3 だけがある）。"""
    root = tmp_path / records.LAUNCHES_DIR
    for number in (1, 3):
        (root / str(number)).mkdir(parents=True)
        wrapper.write_json(root / str(number) / records.LAUNCH, {
            "schema": records.LAUNCH_SCHEMA, "launch": number, "execution_ids_before": []})
        wrapper.write_json(root / str(number) / records.EXIT, {
            "schema": records.EXIT_SCHEMA, "kind": records.KIND_NOT_STARTED, "launch": number,
            "container_id": None, "runtime_run_ids": []})
        wrapper.write_json(root / str(number) / records.RELEASED, {
            "schema": records.RELEASED_SCHEMA, "container_id": None})
    (tmp_path / records.JOURNAL).write_text("")
    check = records.read_records(tmp_path)
    assert check.problems == ["launch record(s) missing: [2]"]


def test_an_execution_no_launch_recorded_makes_the_evaluation_unverifiable(h, monkeypatch):
    """出力先に、どの launch も記録していない execution がある（wrapper の外で runner を動かした）。"""
    h.complete_evaluation()
    stray = h.ev.out / ".executions" / ("e" * 32)
    stray.mkdir()
    (stray / records.START_RECORD).write_text("runtime_run_id=" + "e" * 32 + "\n")
    monkeypatch.setenv("EVAL_HOST_STATE", json.dumps({"container": "absent", "observed": True}))
    result = summarize.completion(wrapper.REPO, h.ev.out, h.ev.wrapper, "neq")
    assert result["verdict"] == "UNVERIFIABLE"
    assert "execution_attribution" in [r["code"] for r in result["reasons"]]


def _synthetic_launch(directory, *, drop=(), change=None):
    """journal を使わずに、終端した ``ran`` の launch の記録を組み立てる（規則ごとの単体の検査用）。"""
    import hashlib

    directory.mkdir(parents=True)
    container = "a" * 64
    log = b"runner output\n"
    files = {
        records.LAUNCH: {"schema": records.LAUNCH_SCHEMA, "launch": 1, "execution_ids_before": []},
        records.CONTAINER: {"schema": records.CONTAINER_SCHEMA, "container_id": container},
        records.EXIT: {"schema": records.EXIT_SCHEMA, "kind": records.KIND_RAN, "launch": 1,
                       "container_id": container, "runtime_run_ids": [],
                       "runner_log": {"sha256": hashlib.sha256(log).hexdigest(), "bytes": len(log)}},
        records.EVIDENCE: {"schema": records.EVIDENCE_SCHEMA, "captured_at_epoch": 1.0,
                           "unterminated_pairs": [], "verify": None, "verify_error": "none"},
        records.RELEASED: {"schema": records.RELEASED_SCHEMA, "container_id": container},
    }
    if change:
        change(files)
    for name, payload in files.items():
        if name not in drop:
            wrapper.write_json(directory / name, payload)
    if records.RUNNER_LOG not in drop:
        (directory / records.RUNNER_LOG).write_bytes(log)


@pytest.mark.parametrize("drop, change, problem", [
    ((), None, None),
    ((records.EVIDENCE,), None, "released.json exists without evidence.json"),
    ((records.CONTAINER,), None, "container.json is missing for a launch whose container ran"),
    ((records.EXIT,), None, "released.json exists without exit.json"),
    ((records.RUNNER_LOG,), None, "runner.log is missing"),
    ((records.LAUNCH,), None, "launch.json is missing"),
    ((), lambda f: f[records.RELEASED].update(container_id="b" * 64), "released.json names another container"),
    ((), lambda f: f[records.EXIT].update(container_id="b" * 64), "exit.json and container.json name different containers"),
    ((), lambda f: f[records.EXIT].update(launch=2), "exit.json describes another launch"),
    ((), lambda f: f[records.EXIT].update(kind="maybe"), "exit.json is malformed"),
    ((), lambda f: f[records.EXIT].update(kind=records.KIND_NOT_STARTED), "has container records"),
    ((), lambda f: f[records.EXIT]["runner_log"].update(bytes=1), "runner.log differs"),
    ((), lambda f: f[records.LAUNCH].update(launch=7), "launch.json does not describe this launch"),
    ((), lambda f: f[records.EVIDENCE].update(unterminated_pairs="x"), "evidence.json is malformed"),
    ((), lambda f: f[records.EVIDENCE].update(unterminated_pairs=[{"pair": "p", "kind": "?"}]),
     "evidence.json is malformed"),
])
def test_each_record_rule_is_checked_on_its_own(tmp_path, drop, change, problem):
    _synthetic_launch(tmp_path / "1", drop=drop, change=change)
    launch = records.read_launch(tmp_path / "1", 1)
    if problem is None:
        assert launch.problems == [] and launch.state == records.STATE_RELEASED
    else:
        assert any(problem in item for item in launch.problems), launch.problems
        assert launch.state == records.STATE_DAMAGED
