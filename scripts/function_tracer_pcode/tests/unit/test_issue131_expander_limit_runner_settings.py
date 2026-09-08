# -*- coding: utf-8 -*-
"""Issue #131: ``FT_EXPANDER_DEDUP_CASE_LIMIT`` の要求値と実効値の記録契約。

runner は利用者が指定した生の値（requested）と、実際に子プロセスへ渡す正の整数
（effective）を分けて実行記録に残す。実効値の判定規則は解析器側
(`config/settings.py::_positive_int_setting`) へ委譲して 1 本化しており、runner 側で
規則を二重実装しない。
"""
from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.config.settings import _positive_int_setting

REPO_ROOT = Path(__file__).resolve().parents[4]
COMMON = REPO_ROOT / "scripts" / "validation_matrix_common.sh"
EQ_RUNNER = REPO_ROOT / "eqbench_run_all_32jobs.sh"
NEQ_RUNNER = REPO_ROOT / "neqbench_run_all_32jobs.sh"
BASH = shutil.which("bash")

pytestmark = pytest.mark.skipif(BASH is None, reason="bash is required")

# unset は None で表す。空文字は「指定はあるが空」。
REQUESTED_VALUES = [None, "", "0", "-1", "abc", "2"]
# 解析器の規則と一致していることを確認する追加ケース（bash の自前実装だと外しやすい）
EXTRA_VALUES = ["  3  ", "08", "+4", "2.5", "1e3"]
DEFAULT_LIMIT = 16


def _expected_effective(requested):
    environ = {} if requested is None else {"SETTING": requested}
    return _positive_int_setting("SETTING", DEFAULT_LIMIT, environ)


def _run_bash(script: str, requested, cwd: Path) -> str:
    env = dict(os.environ)
    env.pop("FT_EXPANDER_DEDUP_CASE_LIMIT", None)
    if requested is not None:
        env["FT_EXPANDER_DEDUP_CASE_LIMIT"] = requested
    result = subprocess.run(
        [BASH, str(script)], capture_output=True, text=True, env=env,
        cwd=str(cwd), timeout=120,
    )
    assert result.returncode == 0, result.stderr
    return result.stdout


def _runner_prologue(runner: Path, tmp_path: Path) -> Path:
    """runner の設定ブロックまでをそのまま切り出した harness を作る。

    ``SCRIPT_DIR`` の導出だけは harness の置き場所に依存するので固定値へ置き換える。
    上限の要求値・実効値を決めるコード自体は runner の本文をそのまま実行する。
    """
    lines = runner.read_text(encoding="utf-8").splitlines()
    end = next(
        index for index, line in enumerate(lines)
        if line.strip() == "export FT_EXPANDER_DEDUP_CASE_LIMIT"
    )
    prologue = []
    for line in lines[: end + 1]:
        if line.startswith("SCRIPT_DIR=") or line.startswith('SCRIPT_DIR="$('):
            prologue.append(f'SCRIPT_DIR="{REPO_ROOT}"')
        else:
            prologue.append(line)
    prologue.append(
        'printf "requested=[%s]\\neffective=[%s]\\n" '
        '"$FT_EXPANDER_DEDUP_CASE_LIMIT_REQUESTED" "$FT_EXPANDER_DEDUP_CASE_LIMIT"'
    )
    harness = tmp_path / f"{runner.stem}_prologue.sh"
    harness.write_text("\n".join(prologue) + "\n", encoding="utf-8")
    return harness


# ---------------------------------------------------------------------------
# 共通 helper が解析器の規則と一致する
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("requested", REQUESTED_VALUES + EXTRA_VALUES)
def test_shared_helper_matches_the_analyzer_rule(requested, tmp_path):
    harness = tmp_path / "helper.sh"
    harness.write_text(
        "set -euo pipefail\n"
        f'SCRIPT_DIR="{REPO_ROOT}"\n'
        f'source "{COMMON}"\n'
        'printf "%s\\n" "$(validation_positive_int_setting '
        f'"${{FT_EXPANDER_DEDUP_CASE_LIMIT-}}" {DEFAULT_LIMIT})"\n',
        encoding="utf-8",
    )
    observed = _run_bash(harness, requested, REPO_ROOT).strip()
    assert observed == str(_expected_effective(requested)), requested


def test_shared_helper_falls_back_to_the_default_when_python_is_unusable(tmp_path):
    """委譲に失敗しても正の整数（既定値）を返す。子へ不正値を渡さない。"""
    harness = tmp_path / "helper_broken_python.sh"
    harness.write_text(
        "set -euo pipefail\n"
        f'SCRIPT_DIR="{REPO_ROOT}"\n'
        f'source "{COMMON}"\n'
        f'printf "%s\\n" "$(validation_positive_int_setting "2" {DEFAULT_LIMIT} '
        '"/nonexistent/python")"\n',
        encoding="utf-8",
    )
    assert _run_bash(harness, None, REPO_ROOT).strip() == str(DEFAULT_LIMIT)


def test_manifest_value_keeps_the_record_on_one_line(tmp_path):
    harness = tmp_path / "manifest_value.sh"
    harness.write_text(
        "set -euo pipefail\n"
        f'SCRIPT_DIR="{REPO_ROOT}"\n'
        f'source "{COMMON}"\n'
        'printf "[%s]\\n" "$(validation_manifest_value "$(printf \'a\\nb\')")"\n',
        encoding="utf-8",
    )
    assert _run_bash(harness, None, REPO_ROOT).strip() == "[a b]"


# ---------------------------------------------------------------------------
# 両 runner が requested / effective を正しく決める
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("runner", [EQ_RUNNER, NEQ_RUNNER], ids=["eq", "neq"])
@pytest.mark.parametrize("requested", REQUESTED_VALUES)
def test_runner_separates_requested_and_effective(runner, requested, tmp_path):
    harness = _runner_prologue(runner, tmp_path)
    out = _run_bash(harness, requested, REPO_ROOT)
    observed = dict(
        line.split("=", 1) for line in out.strip().splitlines() if "=" in line
    )
    assert observed["requested"] == f"[{requested if requested is not None else ''}]"
    assert observed["effective"] == f"[{_expected_effective(requested)}]"


@pytest.mark.parametrize("runner", [EQ_RUNNER, NEQ_RUNNER], ids=["eq", "neq"])
def test_runner_manifest_records_both_values(runner):
    text = runner.read_text(encoding="utf-8")
    assert "expander_dedup_case_limit_requested=$(validation_manifest_value" in text
    assert "expander_dedup_case_limit_effective=$FT_EXPANDER_DEDUP_CASE_LIMIT" in text
    # 曖昧な単一キーは残さない
    assert "\nexpander_dedup_case_limit=" not in text


@pytest.mark.parametrize("runner", [EQ_RUNNER, NEQ_RUNNER], ids=["eq", "neq"])
def test_runner_hands_the_effective_value_to_the_pair_child(runner):
    text = runner.read_text(encoding="utf-8")
    assert 'FT_EXPANDER_DEDUP_CASE_LIMIT=$FT_EXPANDER_DEDUP_CASE_LIMIT"' in text or (
        'FT_EXPANDER_DEDUP_CASE_LIMIT="$FT_EXPANDER_DEDUP_CASE_LIMIT"' in text
    )


def test_eq_runner_receipt_command_records_the_requested_value():
    """receipt が残すコマンドは利用者の入力を再現する（実効値は runner が再導出）。"""
    text = EQ_RUNNER.read_text(encoding="utf-8")
    assert '"FT_EXPANDER_DEDUP_CASE_LIMIT=$FT_EXPANDER_DEDUP_CASE_LIMIT_REQUESTED"' in text


@pytest.mark.parametrize("runner", [EQ_RUNNER, NEQ_RUNNER], ids=["eq", "neq"])
def test_runners_do_not_reimplement_the_validation_rule(runner):
    """規則の二重実装を防ぐ: runner 側は共通 helper を呼ぶだけ。"""
    text = runner.read_text(encoding="utf-8")
    assert "validation_positive_int_setting" in text
    mentions = [
        line for line in text.splitlines()
        if "FT_EXPANDER_DEDUP_CASE_LIMIT" in line and not line.lstrip().startswith("#")
    ]
    assert mentions
    for line in mentions:
        # 自前の数値検証（正規表現照合・算術比較・既定値の直接代入）を持たない
        for token in ("=~", " -lt ", " -le ", " -gt ", " -ge ", "((", ":-16", ":-}"):
            assert token not in line, (runner.name, token, line)
    # 既定値 16 は helper へ渡す引数としてだけ現れる
    default_uses = [line for line in mentions if "16" in line]
    assert all("validation_positive_int_setting" in line or line.strip() == '"$FT_EXPANDER_DEDUP_CASE_LIMIT_REQUESTED" 16)"' for line in default_uses), default_uses
