# -*- coding: utf-8 -*-
"""GitHub Actions の起動方針を固定する。

要求はひとつ:

    **通常 CI (``unit.yml``) 以外の自動 CI は週 1 回だけ。**
    手動の ``workflow_dispatch`` は許可。

Actions の無料枠（2000 分/月）が制約なので、``unit.yml`` 以外の workflow は
「週 1 回の ``schedule``」と「人が押す ``workflow_dispatch``」しか持ってはいけない。
``push`` / ``pull_request`` / ``workflow_run`` / ``release`` などの自動 event は
1 つも許さない。

**重さでは分類しない。** ``timeout-minutes`` のような代理指標だと、timeout を
書かない workflow、30 分 × 大量 matrix、``.yaml`` 拡張子、``workflow_run`` の
ような別経路で方針をすり抜けられる。ここで見るのは「自動で起動するか」そのもの。

ここで縛るのは **いつ走るか**だけで、走った後の検証内容には触れない。
"""

from __future__ import annotations

from pathlib import Path
from typing import Dict, List, Set

import pytest
import yaml


WORKFLOW_DIR = Path(__file__).resolve().parents[4] / ".github" / "workflows"

#: 唯一の「通常 CI」。pull request ごとに走ってよいのはこれだけ。
NORMAL_CI_WORKFLOW = "unit.yml"

#: その通常 CI が必ず持つ job（安い gate を弱めていないことの確認）。
REQUIRED_PR_JOBS = ("unit-fast", "recorded-fast")

#: ``unit.yml`` 以外に許す trigger。``schedule`` は週 1 本だけ（下で確認）。
ALLOWED_TRIGGERS_ELSEWHERE = {"schedule", "workflow_dispatch"}


def _load(path: Path) -> dict:
    document = yaml.safe_load(path.read_text(encoding="utf-8"))
    # ``on:`` は YAML 1.1 で真偽値に読まれる。
    if True in document:
        document["on"] = document.pop(True)
    return document


def _workflow_files() -> List[Path]:
    """``.yml`` と ``.yaml`` の両方（拡張子で漏らさない）。"""

    return sorted(
        path
        for pattern in ("*.yml", "*.yaml")
        for path in WORKFLOW_DIR.glob(pattern)
    )


ALL_WORKFLOWS: Dict[str, dict] = {path.name: _load(path) for path in _workflow_files()}
OTHER_WORKFLOWS: List[str] = sorted(set(ALL_WORKFLOWS) - {NORMAL_CI_WORKFLOW})


def _triggers(name: str) -> Set[str]:
    declared = ALL_WORKFLOWS[name]["on"]
    if isinstance(declared, str):
        return {declared}
    if isinstance(declared, list):
        return set(declared)
    return set(declared)


def test_every_workflow_file_is_readable_and_classified():
    """棚卸しに漏れが無いこと（新しい workflow は自動でこの policy に掛かる）。"""

    assert ALL_WORKFLOWS, "no workflows found"
    assert NORMAL_CI_WORKFLOW in ALL_WORKFLOWS, f"{NORMAL_CI_WORKFLOW} is gone"
    for name, document in ALL_WORKFLOWS.items():
        assert "on" in document, f"{name} declares no triggers"
        assert document.get("jobs"), f"{name} declares no jobs"
    on_disk = {path.name for path in _workflow_files()}
    assert on_disk == set(ALL_WORKFLOWS), on_disk ^ set(ALL_WORKFLOWS)


@pytest.mark.parametrize("name", OTHER_WORKFLOWS)
def test_only_the_normal_ci_starts_itself_outside_a_weekly_schedule(name):
    """``unit.yml`` 以外の自動起動は weekly ``schedule`` だけ。

    ``push`` / ``pull_request`` / ``pull_request_target`` / ``workflow_run`` /
    ``repository_dispatch`` / ``release`` など、名前を問わず他の自動 event を
    許さない（allow list なので、新しい event 種別も既定で拒否される）。
    """

    extra = _triggers(name) - ALLOWED_TRIGGERS_ELSEWHERE
    assert not extra, f"{name} starts automatically on {sorted(extra)}"


@pytest.mark.parametrize("name", OTHER_WORKFLOWS)
def test_a_non_normal_workflow_has_exactly_one_weekly_schedule(name):
    """自動起動は週 1 回だけ。曜日を絞らない cron は毎日走るので拒否する。"""

    schedule = ALL_WORKFLOWS[name]["on"].get("schedule")
    assert schedule, f"{name} has no schedule"
    assert len(schedule) == 1, f"{name} declares {len(schedule)} schedules, not 1"
    minute, hour, day_of_month, month, day_of_week = schedule[0]["cron"].split()
    assert day_of_week not in ("*", "?"), f"{name} runs every day: {schedule[0]['cron']}"
    for separator in (",", "/", "-"):
        assert separator not in day_of_week, (
            f"{name} runs on more than one weekday: {schedule[0]['cron']}"
        )
    assert day_of_month == "*", f"{name} mixes day-of-month into a weekly cron"
    assert month == "*", f"{name} is not weekly: {schedule[0]['cron']}"
    assert minute.isdigit() and hour.isdigit(), (
        f"{name} fans its cron out over several times: {schedule[0]['cron']}"
    )


@pytest.mark.parametrize("name", OTHER_WORKFLOWS)
def test_a_non_normal_workflow_keeps_its_manual_escape_hatch(name):
    """手動起動は週 1 回の枠に含めない（障害時・任意検証用）。"""

    assert "workflow_dispatch" in _triggers(name), name


def test_the_weekly_workflows_do_not_share_a_day():
    """自動実行を同じ日に集中させない。"""

    days = {
        name: ALL_WORKFLOWS[name]["on"]["schedule"][0]["cron"].split()[4]
        for name in OTHER_WORKFLOWS
    }
    assert len(set(days.values())) == len(days), f"weekly workflows share a day: {days}"


def test_the_normal_ci_still_runs_on_every_pull_request():
    """安い gate を弱めていないこと。"""

    triggers = ALL_WORKFLOWS[NORMAL_CI_WORKFLOW]["on"]
    assert triggers["pull_request"]["branches"] == ["main"]
    assert triggers["push"]["branches"] == ["main"]
    jobs = ALL_WORKFLOWS[NORMAL_CI_WORKFLOW]["jobs"]
    for job in REQUIRED_PR_JOBS:
        assert job in jobs, f"{job} is gone from {NORMAL_CI_WORKFLOW}"
        assert "if" not in jobs[job], f"{job} became conditional"


def test_the_subset_checkout_leaves_the_ref_to_the_event():
    """schedule は event が決めた commit、dispatch は操作者が選んだ ref。

    ``ref:`` を書くと dispatch の選択を奪うので、checkout に ref を渡さない。
    """

    steps = ALL_WORKFLOWS["eqbench-subset.yml"]["jobs"]["subset"]["steps"]
    checkouts = [
        step for step in steps if str(step.get("uses", "")).startswith("actions/checkout")
    ]
    assert checkouts, "the subset job does not check anything out"
    for step in checkouts:
        assert "ref" not in (step.get("with") or {}), "the checkout pins a ref"


def test_a_scheduled_subset_run_is_verified_against_the_event_commit():
    """race にならない identity 確認: event が固定した commit と比べる。

    ``git fetch`` で「いまの branch head」を取り直すと、runner が割り当てられる
    間に main が進んだだけで正常な run が落ちる。
    """

    source = (WORKFLOW_DIR / "eqbench-subset.yml").read_text(encoding="utf-8")
    steps = ALL_WORKFLOWS["eqbench-subset.yml"]["jobs"]["subset"]["steps"]
    guards = [step for step in steps if step.get("if") == "github.event_name == 'schedule'"]
    assert guards, "nothing verifies what a scheduled run checked out"
    guard = guards[0]
    assert guard["env"]["EVENT_SHA"] == "${{ github.sha }}", guard["env"]
    assert '"$checked_out" == "$EVENT_SHA"' in guard["run"]
    assert "git fetch" not in guard["run"], "the identity check re-fetches the branch"
    assert "FETCH_HEAD" not in source, "a branch head is fetched somewhere in this workflow"


def test_the_subset_job_runs_only_for_a_schedule_or_a_manual_dispatch():
    condition = ALL_WORKFLOWS["eqbench-subset.yml"]["jobs"]["subset"]["if"]
    assert "github.event_name == 'schedule'" in condition
    assert "github.event_name == 'workflow_dispatch'" in condition
    assert "pull_request" not in condition


def test_the_dispatch_inputs_keep_their_meaning():
    """schedule でも一意に決まるよう、既定値は dispatch 側と同じものを使う。"""

    inputs = ALL_WORKFLOWS["eqbench-subset.yml"]["on"]["workflow_dispatch"]["inputs"]
    assert inputs["subset_scope"]["default"] == "all"
    assert inputs["subset_scope"]["options"] == ["all", "eq", "neq"]
    assert inputs["pair_process_timeout"]["default"] == "240s"
    assert inputs["identical_fast_path"]["default"] == "1"
    assert inputs["identical_fast_path"]["options"] == ["1", "0"]
    assert inputs["eqbench_ref"]["default"]


@pytest.mark.parametrize(
    "setting, default",
    [
        ("SUBSET_SCOPE", "all"),
        ("PAIR_PROCESS_TIMEOUT", "240s"),
        ("EQBENCH_IDENTICAL_FAST_PATH", "1"),
    ],
)
def test_the_normalisation_defaults_match_the_dispatch_form(setting, default):
    """入力の無い schedule run が、dispatch の既定と同じ設定で走ること。"""

    source = (WORKFLOW_DIR / "eqbench-subset.yml").read_text(encoding="utf-8")
    assert f'{setting}="${{RAW_' in source, f"{setting} is not normalised in one place"
    assert f':-{default}}}"' in source, f"{setting} does not default to {default}"


def test_no_workflow_still_reads_a_pull_request_payload():
    """merged-PR 前提が残っていないこと（``unit.yml`` 以外は PR で走らない）。"""

    for path in _workflow_files():
        if path.name == NORMAL_CI_WORKFLOW:
            continue
        source = path.read_text(encoding="utf-8")
        assert "github.event.pull_request" not in source, path.name
