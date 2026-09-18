# -*- coding: utf-8 -*-
"""GitHub Actions の起動方針を固定する。

無料枠が制約なので、**自動で走る重い workflow は各 1 本 / 週**に限る。安い gate
（``unit.yml`` の ``unit-fast`` / ``recorded-fast``）は従来どおり pull request
ごとに走る。ここで縛るのは **いつ走るか**だけで、走った後の検証内容には触れない。

重さは workflow 名ではなく **宣言された budget**（``timeout-minutes``）で決める。
新しく重い workflow を足した人が、この test の存在を知らなくても policy に
引っかかるようにするため。
"""

from __future__ import annotations

from pathlib import Path
from typing import Dict, List

import pytest
import yaml


WORKFLOW_DIR = Path(__file__).resolve().parents[4] / ".github" / "workflows"

#: 安い gate が自分に許している時間（``unit.yml`` の 2 job がともに 30 分）。
#: それより長い budget を要求する job を 1 つでも持つ workflow は「重い」。
#: 「PR gate より時間を要求するものは自動では週 1 回」という線の引き方なので、
#: 新しい workflow を足した人がこの test を知らなくても引っかかる。
CHEAP_GATE_TIMEOUT_MINUTES = 30

#: 安い gate を持つ workflow と、pull request で必ず走る job。
CHEAP_GATE_WORKFLOW = "unit.yml"
REQUIRED_PR_JOBS = ("unit-fast", "recorded-fast")


def _load(path: Path) -> dict:
    document = yaml.safe_load(path.read_text(encoding="utf-8"))
    # ``on:`` は YAML 1.1 で真偽値に読まれる。
    if True in document:
        document["on"] = document.pop(True)
    return document


def _workflows() -> Dict[str, dict]:
    return {path.name: _load(path) for path in sorted(WORKFLOW_DIR.glob("*.yml"))}


def _job_timeouts(document: dict) -> List[int]:
    return [
        job["timeout-minutes"]
        for job in document.get("jobs", {}).values()
        if isinstance(job, dict) and isinstance(job.get("timeout-minutes"), int)
    ]


def _is_heavy(document: dict) -> bool:
    return any(timeout > CHEAP_GATE_TIMEOUT_MINUTES for timeout in _job_timeouts(document))


ALL_WORKFLOWS = _workflows()
HEAVY_WORKFLOWS = sorted(name for name, doc in ALL_WORKFLOWS.items() if _is_heavy(doc))


def test_the_workflow_directory_is_readable_yaml():
    assert ALL_WORKFLOWS, "no workflows found"
    for name, document in ALL_WORKFLOWS.items():
        assert "on" in document, f"{name} declares no triggers"
        assert document.get("jobs"), f"{name} declares no jobs"


def test_the_expected_workflows_are_classified_as_heavy():
    """棚卸しが実態とずれたら FAIL（重い workflow を見落とさないため）。"""

    assert HEAVY_WORKFLOWS == ["eqbench-subset.yml", "recorded-full.yml"]
    assert not _is_heavy(ALL_WORKFLOWS[CHEAP_GATE_WORKFLOW])
    assert max(_job_timeouts(ALL_WORKFLOWS[CHEAP_GATE_WORKFLOW])) == CHEAP_GATE_TIMEOUT_MINUTES


@pytest.mark.parametrize("name", HEAVY_WORKFLOWS)
def test_a_heavy_workflow_does_not_start_on_a_push(name):
    """merge / push ごとに 1 時間超の仕事を始めない。"""

    assert "push" not in ALL_WORKFLOWS[name]["on"], f"{name} still starts on a push"


@pytest.mark.parametrize("name", HEAVY_WORKFLOWS)
def test_a_heavy_workflow_does_not_start_on_a_pull_request(name):
    """merged PR ごとの自動起動も含めて、pull request では始めない。"""

    assert "pull_request" not in ALL_WORKFLOWS[name]["on"], name
    assert "pull_request_target" not in ALL_WORKFLOWS[name]["on"], name


@pytest.mark.parametrize("name", HEAVY_WORKFLOWS)
def test_a_heavy_workflow_has_exactly_one_weekly_schedule(name):
    """自動起動は週 1 回だけ。日を指定しない cron は毎日走るので拒否する。"""

    schedule = ALL_WORKFLOWS[name]["on"].get("schedule")
    assert schedule, f"{name} has no schedule"
    assert len(schedule) == 1, f"{name} has {len(schedule)} schedules, not 1"
    minute, hour, day_of_month, month, day_of_week = schedule[0]["cron"].split()
    assert day_of_week not in ("*", "?"), f"{name} runs every day: {schedule[0]['cron']}"
    assert "," not in day_of_week and "/" not in day_of_week and "-" not in day_of_week, (
        f"{name} runs on more than one weekday: {schedule[0]['cron']}"
    )
    assert day_of_month == "*", f"{name} mixes day-of-month into a weekly cron"
    assert month == "*", f"{name} is not weekly: {schedule[0]['cron']}"
    assert minute.isdigit() and hour.isdigit(), f"{name} has a fanned-out cron"


@pytest.mark.parametrize("name", HEAVY_WORKFLOWS)
def test_a_heavy_workflow_keeps_its_manual_escape_hatch(name):
    """手動起動は週 1 回の制限に含めない（障害時・任意検証用）。"""

    assert "workflow_dispatch" in ALL_WORKFLOWS[name]["on"], name


def test_the_heavy_workflows_do_not_share_a_time_slot():
    """重い workflow を同じ時刻に集中させない。"""

    slots = [
        ALL_WORKFLOWS[name]["on"]["schedule"][0]["cron"]
        for name in HEAVY_WORKFLOWS
    ]
    weekdays = [cron.split()[4] for cron in slots]
    assert len(set(weekdays)) == len(weekdays), f"heavy workflows share a weekday: {slots}"


def test_the_cheap_gate_still_runs_on_every_pull_request():
    """安い gate を弱めていないこと。"""

    triggers = ALL_WORKFLOWS[CHEAP_GATE_WORKFLOW]["on"]
    assert "pull_request" in triggers
    assert triggers["pull_request"]["branches"] == ["main"]
    jobs = ALL_WORKFLOWS[CHEAP_GATE_WORKFLOW]["jobs"]
    for job in REQUIRED_PR_JOBS:
        assert job in jobs, f"{job} is gone from {CHEAP_GATE_WORKFLOW}"
        assert "if" not in jobs[job], f"{job} became conditional"


def test_the_subset_run_takes_the_branch_head_rather_than_a_named_ref():
    """schedule ではその時点の main HEAD、dispatch では操作者が選んだ ref。

    ``ref:`` を書くと dispatch の選択を奪うので、checkout に ref を渡さない
    （schedule event の既定が default branch の head）。
    """

    document = ALL_WORKFLOWS["eqbench-subset.yml"]
    steps = document["jobs"]["subset"]["steps"]
    checkouts = [step for step in steps if str(step.get("uses", "")).startswith("actions/checkout")]
    assert checkouts, "the subset job does not check anything out"
    for step in checkouts:
        assert "ref" not in (step.get("with") or {}), "the checkout pins a ref"
    guards = [step for step in steps if step.get("if") == "github.event_name == 'schedule'"]
    assert guards, "nothing verifies what a scheduled run checked out"


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
