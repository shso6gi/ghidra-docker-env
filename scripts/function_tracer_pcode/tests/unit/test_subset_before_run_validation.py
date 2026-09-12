# -*- coding: utf-8 -*-
"""Issue #123 / PR-123-A: `SUBSET_BEFORE` の fail-fast 検証。

`eqbench_run_subset.sh` は before run を「half が終わってから」読むので、誤指定は
10 分級の実行が終わるまで気付けなかった。pair を 1 つも走らせる前に、**今回走らせる
half だけ**について before が比較可能かを確かめる。

比較可能の基準は `reporting.outcome_transition` が before tree から実際に読むもの
（half 配下の `*.pair-status.json`）に揃える。`run_manifest.txt` や本 PR で足した
provenance は transition には要らないので要求しない: それらを持たない過去の run
（`logs/EqBench/subset_issue54b` 等）も before として使える。

script 側は runner を起動する前に落ちることまで固定する（`<half>.log` は
`run_half` の redirect で作られるので、その不在が「runner に到達していない」証拠）。
"""

import os
import shutil
import subprocess

import pytest


REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.abspath(__file__))
))))
COMMON_SH = os.path.join("scripts", "validation_matrix_common.sh")
SUBSET_SH = os.path.join(REPO_ROOT, "eqbench_run_subset.sh")
_PAIR_STATUS = '{"canonical_outcome": "UNKNOWN"}\n'


def _write_half(before_dir, half, *, with_pair_status=True):
    """before run の half を 1 つ作る（結果ツリーの形だけ再現する）。"""
    function_dir = before_dir / half / "CLEVER" / "LoopSub" / "Eq" / "new" / "foo"
    function_dir.mkdir(parents=True)
    (before_dir / half / "run_manifest.txt").write_text(
        "run_kind=eqbench_all_eq_matrix_current\n", encoding="utf-8",
    )
    if with_pair_status:
        (function_dir / "foo_B1_B2.pair-status.json").write_text(_PAIR_STATUS, encoding="utf-8")


def _half_is_comparable(half_dir):
    """script が使うのと同じ shell 関数をそのまま呼ぶ。"""
    completed = subprocess.run(
        ["bash", "-c",
         f'set -euo pipefail; source "{COMMON_SH}"; '
         'validation_before_run_half_is_comparable "$1"',
         "_", str(half_dir)],
        cwd=REPO_ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    assert completed.returncode in (0, 1), completed.stderr.decode()
    return completed.returncode == 0


def _run_subset_script(tmp_path, *, before, scope, output_name="out"):
    """runner に到達しても即座に終わる環境で subset script を動かす。

    `EQBENCH_ROOT` を空ディレクトリにしてあるので、validation を通ってしまった場合でも
    Eq runner は 1 秒以内に失敗する（test が実際の pair 実行を始めない）。
    """
    output_dir = tmp_path / output_name
    environment = dict(os.environ)
    environment.update({
        "OUTPUT_BASE_DIR": str(output_dir),
        "SUBSET_SCOPE": scope,
        "SUBSET_BEFORE": str(before),
        "EQBENCH_ROOT": str(tmp_path / "empty-eqbench-root"),
        "NEQ_ROOT": str(tmp_path / "empty-eqbench-root"),
        "EQBENCH_TMPDIR": str(tmp_path / "runner-tmp"),
        "EQBENCH_BUILD_POLICY": "PREBUILT_ONLY",
        "EQBENCH_RESOURCE_ADMISSION": "0",
        "PARALLEL_JOBS": "1",
    })
    (tmp_path / "empty-eqbench-root").mkdir(exist_ok=True)
    completed = subprocess.run(
        ["bash", SUBSET_SH], cwd=REPO_ROOT, env=environment, timeout=300,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    return completed, output_dir


@pytest.fixture()
def before_run(tmp_path):
    before = tmp_path / "subset_before"
    before.mkdir()
    return before


def test_complete_before_run_is_comparable_for_both_halves(before_run):
    _write_half(before_run, "eq")
    _write_half(before_run, "neq")
    assert _half_is_comparable(before_run / "eq")
    assert _half_is_comparable(before_run / "neq")


def test_missing_before_half_is_not_comparable(before_run):
    _write_half(before_run, "eq")
    assert _half_is_comparable(before_run / "eq")
    assert not _half_is_comparable(before_run / "neq")


def test_half_without_pair_status_is_not_comparable(before_run):
    """half は在るが比較対象 (`*.pair-status.json`) が無い run は通さない。"""
    _write_half(before_run, "eq", with_pair_status=False)
    assert (before_run / "eq" / "run_manifest.txt").is_file()
    assert not _half_is_comparable(before_run / "eq")


def test_missing_provenance_does_not_make_a_before_run_invalid(before_run):
    """PR #150 以前の run（`git_commit` 等を持たない）も before として有効。"""
    _write_half(before_run, "eq")
    manifest = (before_run / "eq" / "run_manifest.txt").read_text(encoding="utf-8")
    assert "git_commit" not in manifest and "start_time_utc" not in manifest
    assert _half_is_comparable(before_run / "eq")


def test_real_before_run_of_this_pr_stays_comparable():
    """実際に before として使っている run を壊していないこと。"""
    existing = os.path.join(REPO_ROOT, "logs", "EqBench", "subset_issue54b")
    if not os.path.isdir(existing):
        pytest.skip("the reference before run is not present in this checkout")
    assert _half_is_comparable(os.path.join(existing, "eq"))
    assert _half_is_comparable(os.path.join(existing, "neq"))


@pytest.mark.skipif(shutil.which("bash") is None, reason="bash is required")
def test_subset_script_rejects_incomplete_before_run_before_starting_a_runner(tmp_path, before_run):
    """`SUBSET_SCOPE=all` で neq half が無いなら、half を 1 つも走らせずに落ちる。"""
    _write_half(before_run, "eq")
    completed, output_dir = _run_subset_script(tmp_path, before=before_run, scope="all")
    assert completed.returncode != 0
    message = completed.stderr.decode()
    assert "SUBSET_BEFORE" in message and "neq" in message
    assert not (output_dir / "eq.log").exists(), "Eq runner was started despite an invalid before run"
    assert not (output_dir / "neq.log").exists()


@pytest.mark.skipif(shutil.which("bash") is None, reason="bash is required")
def test_subset_script_rejects_a_before_run_that_does_not_exist(tmp_path):
    completed, output_dir = _run_subset_script(
        tmp_path, before=tmp_path / "no-such-run", scope="eq",
    )
    assert completed.returncode != 0
    assert "SUBSET_BEFORE" in completed.stderr.decode()
    assert not (output_dir / "eq.log").exists()


@pytest.mark.skipif(shutil.which("bash") is None, reason="bash is required")
def test_subset_script_rejects_a_missing_eq_half_under_eq_scope(tmp_path, before_run):
    _write_half(before_run, "neq")
    completed, output_dir = _run_subset_script(tmp_path, before=before_run, scope="eq")
    assert completed.returncode != 0
    message = completed.stderr.decode()
    assert "SUBSET_BEFORE" in message and "eq" in message
    assert not (output_dir / "eq.log").exists()


@pytest.mark.skipif(shutil.which("bash") is None, reason="bash is required")
def test_subset_script_rejects_a_missing_neq_half_under_neq_scope(tmp_path, before_run):
    _write_half(before_run, "eq")
    completed, output_dir = _run_subset_script(tmp_path, before=before_run, scope="neq")
    assert completed.returncode != 0
    message = completed.stderr.decode()
    assert "SUBSET_BEFORE" in message and "neq" in message
    assert not (output_dir / "neq.log").exists()


@pytest.mark.skipif(shutil.which("bash") is None, reason="bash is required")
def test_subset_script_does_not_require_a_half_outside_the_scope(tmp_path, before_run):
    """`SUBSET_SCOPE=eq` なら neq half が無くても validation は通り、runner に進む。

    `eq.log` は `run_half` の redirect で作られるので、その存在が「validation を
    通って runner を起動した」証拠になる（runner 自体は空の EQBENCH_ROOT で失敗する）。
    """
    _write_half(before_run, "eq")
    completed, output_dir = _run_subset_script(tmp_path, before=before_run, scope="eq")
    assert "SUBSET_BEFORE" not in completed.stderr.decode()
    assert (output_dir / "eq.log").exists(), "the Eq runner was never started"
