# -*- coding: utf-8 -*-
"""Issue #123 / PR-123-A: run provenance（どの作業ツリーが run を出したか）。

`analysis_source_digest` は SOURCE_ROOTS 配下の内容だけを見るので、未コミット
変更は digest に黙って混ざり、後から「commit されたコードの結果」と区別できない。
`git_state()` は commit と「SOURCE_ROOTS に限定した汚れ」を独立に記録し、git が
使えない場合も欄を空にせず `unavailable` / `unknown` を残す。

ここで固定するのは次の 3 点:
1. clean / tracked 変更 / untracked 追加 / SOURCE_ROOTS 外 / git 不在の判定が安定していること。
2. provenance の行を足しても判定系の `analysis_config_digest` が変わらないこと。
3. SOURCE_ROOTS と runner の manifest が provenance を落とさないこと。
"""

import os
import shutil
import subprocess

import pytest

from scripts.function_tracer_pcode.reporting import execution_identity
from scripts.function_tracer_pcode.reporting.execution_identity import (
    SOURCE_ROOTS,
    format_git_state,
    git_state,
)
from scripts.function_tracer_pcode.reporting.execution_receipt import (
    analysis_config_from_run,
)


REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.abspath(__file__))
))))
_RUNNER_SCRIPTS = (
    "eqbench_run_all_32jobs.sh",
    "neqbench_run_all_32jobs.sh",
    "eqbench_run_subset.sh",
)


def _git(repo_root, *arguments):
    environment = {
        "PATH": os.environ.get("PATH", ""),
        "HOME": str(repo_root),
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_GLOBAL": os.path.join(str(repo_root), ".gitconfig-absent"),
        "GIT_AUTHOR_NAME": "provenance test",
        "GIT_AUTHOR_EMAIL": "provenance@example.invalid",
        "GIT_COMMITTER_NAME": "provenance test",
        "GIT_COMMITTER_EMAIL": "provenance@example.invalid",
    }
    subprocess.run(
        ("git", *arguments), cwd=str(repo_root), check=True,
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=environment,
    )


def _seed_repository(root):
    """SOURCE_ROOTS と同じ形の作業ツリーを 1 commit 分作る。"""
    for relative in _RUNNER_SCRIPTS + ("requirements-test.txt",):
        (root / relative).write_text(f"# {relative}\n", encoding="utf-8")
    (root / "scripts").mkdir()
    (root / "scripts" / "validation_matrix_common.sh").write_text("# common\n", encoding="utf-8")
    (root / "scripts" / "eqbench").mkdir()
    (root / "scripts" / "eqbench" / "compile_all_arm_mips.sh").write_text("# compile\n", encoding="utf-8")
    (root / "scripts" / "function_tracer_pcode").mkdir()
    (root / "scripts" / "function_tracer_pcode" / "checker.py").write_text("x = 1\n", encoding="utf-8")
    (root / "docs").mkdir()
    (root / "docs" / "note.md").write_text("outside the source roots\n", encoding="utf-8")
    _git(root, "init", "-q")
    _git(root, "add", "-A")
    _git(root, "commit", "-q", "-m", "seed")


@pytest.fixture()
def seeded_repository(tmp_path):
    if shutil.which("git") is None:
        pytest.skip("git is not available")
    root = tmp_path / "repo"
    root.mkdir()
    _seed_repository(root)
    return root


def test_git_state_reports_commit_dirty_and_digest(seeded_repository):
    root = seeded_repository
    clean = git_state(root)
    assert len(clean["commit"]) == 40 and clean["commit"] != "unavailable"
    assert clean["dirty"] == "0"
    assert clean["dirty_files"] == ()
    # clean でも digest は空欄にしない（"unavailable" と区別できる固定値）。
    assert clean["dirty_files_digest"] not in {"", "unavailable"}
    assert git_state(root) == clean

    # SOURCE_ROOTS の外の変更は解析結果に効かないので dirty にしない。
    (root / "docs" / "note.md").write_text("edited outside\n", encoding="utf-8")
    (root / "docs" / "new.md").write_text("added outside\n", encoding="utf-8")
    assert git_state(root) == clean

    # tracked file の変更。
    (root / "scripts" / "function_tracer_pcode" / "checker.py").write_text("x = 2\n", encoding="utf-8")
    modified = git_state(root)
    assert modified["commit"] == clean["commit"]
    assert modified["dirty"] == "1"
    assert [entry["path"] for entry in modified["dirty_files"]] == [
        "scripts/function_tracer_pcode/checker.py",
    ]
    assert modified["dirty_files_digest"] != clean["dirty_files_digest"]

    # 同じ file 集合でも中身が違えば digest が変わる。
    (root / "scripts" / "function_tracer_pcode" / "checker.py").write_text("x = 3\n", encoding="utf-8")
    other_content = git_state(root)
    assert [entry["path"] for entry in other_content["dirty_files"]] == [
        "scripts/function_tracer_pcode/checker.py",
    ]
    assert other_content["dirty_files_digest"] != modified["dirty_files_digest"]

    # untracked file の追加も dirty。
    (root / "scripts" / "function_tracer_pcode" / "extra.py").write_text("y = 1\n", encoding="utf-8")
    untracked = git_state(root)
    assert untracked["dirty"] == "1"
    assert [entry["path"] for entry in untracked["dirty_files"]] == [
        "scripts/function_tracer_pcode/checker.py",
        "scripts/function_tracer_pcode/extra.py",
    ]
    assert untracked["dirty_files_digest"] != other_content["dirty_files_digest"]

    lines = format_git_state(untracked).splitlines()
    assert lines == [
        f"git_commit={untracked['commit']}",
        "git_dirty=1",
        f"git_dirty_files_digest={untracked['dirty_files_digest']}",
    ]


def test_git_state_without_git_says_unavailable_not_clean(tmp_path, monkeypatch):
    outside = tmp_path / "not-a-repository"
    outside.mkdir()
    missing = git_state(outside)
    assert missing == {
        "commit": "unavailable",
        "dirty": "unknown",
        "dirty_files": (),
        "dirty_files_digest": "unavailable",
    }

    def _no_git(*args, **kwargs):
        raise FileNotFoundError("git")

    monkeypatch.setattr(execution_identity.subprocess, "run", _no_git)
    assert git_state(tmp_path) == missing
    assert format_git_state(missing).splitlines() == [
        "git_commit=unavailable",
        "git_dirty=unknown",
        "git_dirty_files_digest=unavailable",
    ]


def test_analysis_config_digest_ignores_provenance_keys():
    run = {
        "run_scope": "REPRESENTATIVE",
        "build_policy": "PREBUILT_ONLY",
        "max_samples": "0",
        "sample_filter": "",
        "pair_filter": "",
        "debug": "0",
        "dry_run": "0",
        "parallel_jobs": "20",
        "validation_summary_level": "compact",
        "equiv_timeout": "10",
        "decompile_timeout": "60",
        "pairwise_timeout": "5",
        "pairwise_timeout_hard": "30",
        "pair_process_timeout_seconds": "240",
        "pair_process_kill_after_seconds": "30",
        "prefilter_source_census_digest": "census-digest",
    }
    baseline = analysis_config_from_run(run)
    provenance = dict(run, **{
        "git_commit": "0" * 40,
        "git_dirty": "1",
        "git_dirty_files_digest": "dirty-digest",
        "start_time_utc": "2026-09-12T00:00:00Z",
        "end_time_utc": "2026-09-12T00:10:00Z",
        "hostname": "runner-host",
        "runner_script_sha256": "runner-digest",
    })
    assert analysis_config_from_run(provenance) == baseline


def test_execution_identity_source_roots_include_both_runners_and_subset_script():
    for script in _RUNNER_SCRIPTS:
        assert script in SOURCE_ROOTS, script
        assert os.path.isfile(os.path.join(REPO_ROOT, script)), script
    assert "scripts/validation_matrix_common.sh" in SOURCE_ROOTS
    assert "scripts/function_tracer_pcode" in SOURCE_ROOTS


@pytest.mark.parametrize("script,keys", [
    ("eqbench_run_all_32jobs.sh", (
        "runner_script_sha256=", "start_time_utc=", "hostname=",
        "$RUN_GIT_STATE_LINES", "end_time_utc=",
    )),
    ("neqbench_run_all_32jobs.sh", (
        "runner_script_sha256=", "start_time_utc=", "hostname=",
        "$RUN_GIT_STATE_LINES", "end_time_utc=",
    )),
    ("eqbench_run_subset.sh", (
        "before_run=", "before_commit=", "start_time_utc=", "end_time_utc=",
        "hostname=", "equiv_timeout=", "pairwise_timeout=",
        "pairwise_timeout_hard=", "decompile_timeout=",
        "pair_process_kill_after=", "issue=", "pr=",
        "$RUN_GIT_STATE_LINES",
    )),
])
def test_runner_manifests_record_run_provenance(script, keys):
    """manifest の provenance 行は shell 側にしかないので、ここで退行を止める。"""
    text = open(os.path.join(REPO_ROOT, script), encoding="utf-8").read()
    for key in keys:
        assert key in text, f"{script} lost {key}"
