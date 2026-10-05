# -*- coding: utf-8 -*-
"""Issue #15 PR-15-B: the runners choose the fast-path mode and record it.

``EQBENCH_IDENTICAL_FAST_PATH=0`` must reach the pair command as
``--no-identical-fast-path`` and must reach the run manifest as
``identical_fast_path=0`` next to ``analysis_config_schema=``.  Both halves
matter: the flag alone changes what a run means, and the manifest is the only
place a later reader (the soundness gate, the ledger, a transition report) can
learn which mode produced the results.

The command checks run the runner's own ``run_pair`` against stubs rather than
grepping the script, so a flag that is added to the wrong array or guarded by
the wrong variable fails here.
"""
from __future__ import annotations

import os
import subprocess
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.tests.unit.test_issue124c_runner_and_supervisor import (
    _HARNESS,
    _extract_shell_function,
)

REPO_ROOT = Path(__file__).resolve().parents[4]
RUNNERS = ("eqbench_run_all_32jobs.sh", "neqbench_run_all_32jobs.sh")
FLAG = "--no-identical-fast-path"

_ARGV_STUB = """#!/bin/sh
printf '%s\\n' "$*" >> "$ARGV_FILE"
echo stub
exit 0
"""


def _stub_dir(tmp_path: Path) -> Path:
    """Only the Python entry point is stubbed; every other tool stays real."""

    stubs = tmp_path / "stubs"
    stubs.mkdir(parents=True, exist_ok=True)
    (stubs / "python-stub").write_text(_ARGV_STUB, encoding="utf-8")
    (stubs / "python-stub").chmod(0o755)
    return stubs


def _run_pair_argv(tmp_path: Path, runner: str, mode: str) -> str:
    """Run the runner's own ``run_pair`` and return every argv it produced."""

    stubs = _stub_dir(tmp_path)
    out_dir = tmp_path / "out" / "sample" / "f"
    out_dir.mkdir(parents=True, exist_ok=True)
    # ``run_pair`` makes its per-pair temporary directory under the run tmpdir
    # and writes the resource-usage file there; without it the pair command is
    # never reached and the test would pass for the wrong reason.
    (tmp_path / "runtmp").mkdir(parents=True, exist_ok=True)
    source = (REPO_ROOT / runner).read_text(encoding="utf-8")
    function = _extract_shell_function(source, "run_pair")
    if runner.startswith("eq"):
        args = '"sample" "f" "B1" "B2" "/left" "/right" "%s" 1 1 "/target"' % out_dir
    else:
        args = ('"sample" "f" "N_B1" "O_B2" "/left" "/right" "%s" 1 1 "/target" 1 1 1'
                % out_dir)
    script = (
        _HARNESS
        .replace("__STUBS__", str(stubs))
        .replace("__TMP__", str(tmp_path))
        .replace("__FUNCTION__", function)
        .replace("__ARGS__", args)
        .replace("EQBENCH_IDENTICAL_FAST_PATH=1", f"EQBENCH_IDENTICAL_FAST_PATH={mode}")
    )
    env = dict(os.environ)
    env["ORDER_FILE"] = str(tmp_path / "order.txt")
    env["ARGV_FILE"] = str(tmp_path / "argv.txt")
    subprocess.run(["bash", "-c", script], env=env, capture_output=True, timeout=180)
    argv = tmp_path / "argv.txt"
    return argv.read_text(encoding="utf-8") if argv.is_file() else ""


@pytest.mark.parametrize("runner", RUNNERS)
@pytest.mark.parametrize("mode,expected", [("1", False), ("0", True)])
def test_the_mode_reaches_the_pair_command(tmp_path, runner, mode, expected):
    argv = _run_pair_argv(tmp_path, runner, mode)

    assert "cli.main" in argv, argv
    assert (FLAG in argv) is expected, argv


@pytest.mark.parametrize("runner", RUNNERS)
def test_the_mode_is_recorded_in_the_run_manifest(runner):
    """The manifest keys must be written before the config digest is taken."""

    source = (REPO_ROOT / runner).read_text(encoding="utf-8")

    assert "analysis_config_schema=eqbench-analysis-config-v4" in source
    assert "identical_fast_path=$EQBENCH_IDENTICAL_FAST_PATH" in source
    digest = source.index("--print-analysis-config-digest")
    assert source.index("identical_fast_path=$EQBENCH_IDENTICAL_FAST_PATH") < digest


@pytest.mark.parametrize("runner", RUNNERS)
def test_the_mode_defaults_to_on_and_only_accepts_zero_or_one(runner):
    source = (REPO_ROOT / runner).read_text(encoding="utf-8")

    assert (
        'EQBENCH_IDENTICAL_FAST_PATH="${EQBENCH_IDENTICAL_FAST_PATH:-1}"' in source
        or "default_value EQBENCH_IDENTICAL_FAST_PATH 1" in source
    )
    assert '"$EQBENCH_IDENTICAL_FAST_PATH" =~ ^[01]$' in source


def test_the_subset_runner_passes_the_mode_through_and_records_it():
    source = (REPO_ROOT / "eqbench_run_subset.sh").read_text(encoding="utf-8")

    assert 'export EQBENCH_IDENTICAL_FAST_PATH="${EQBENCH_IDENTICAL_FAST_PATH:-1}"' in source
    assert 'echo "identical_fast_path=$(half_setting identical_fast_path)"' in source
    assert 'echo "analysis_config_schema=$(half_setting analysis_config_schema)"' in source


def test_the_cli_accepts_the_flag_the_runners_pass():
    from scripts.function_tracer_pcode.cli.args import build_parser

    assert build_parser().parse_args(["--equiv", "a", "b", "-f", "x"]) \
        .no_identical_fast_path is False
    assert build_parser().parse_args(
        ["--equiv", "a", "b", "-f", "x", FLAG]
    ).no_identical_fast_path is True
