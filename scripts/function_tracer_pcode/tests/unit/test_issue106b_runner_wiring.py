# -*- coding: utf-8 -*-
"""Issue #106 PR-106-B: the runners hand the analysis deadline to every pair (E7).

These tests drive the real shell scripts -- the runners' own ``run_pair`` and
the scripts themselves in ``DRY_RUN=1`` -- instead of grepping them, so a
setting checked in one runner but not the other, a flag appended to the wrong
array, or a check placed after the point where a run starts doing work fails
here.  They import nothing that PR-106-B adds: on a tree without the wiring
they fail on their assertions (the flag is missing, the run is not stopped),
not on an import.

The rule itself (formats, defaults, ``0`` = off, the inequality) is tested
against ``reporting/runner_timeout_policy.py`` in
``test_issue106b_runner_timeout_policy.py``; here only its wiring is.
"""
from __future__ import annotations

import os
import re
import subprocess
import sys
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.tests.unit.test_issue124c_runner_and_supervisor import (
    _HARNESS,
    _extract_shell_function,
)

REPO_ROOT = Path(__file__).resolve().parents[4]
RUNNERS = ("eqbench_run_all_32jobs.sh", "neqbench_run_all_32jobs.sh")
COMMON = REPO_ROOT / "scripts" / "validation_matrix_common.sh"
FLAG = "--analysis-timeout"
POLICY_ERROR = "exceeds PAIR_PROCESS_TIMEOUT"

_ARGV_STUB = """#!/bin/sh
printf '%s\\n' "$*" >> "$ARGV_FILE"
echo stub
exit 0
"""


def _run_pair_argv(tmp_path: Path, runner: str, analysis_timeout: str) -> str:
    """Resolve the policy with the real rule, then run the runner's own ``run_pair``.

    The harness runs with ``PAIR_PROCESS_TIMEOUT=240s``, so the deadlines used
    here leave the default margin inside it.

    Only the pair's Python entry point is a stub (it records its argv); the
    policy is resolved by the real interpreter, exactly as the runner does it
    at start-up, so the two halves of the wiring are exercised together.
    """

    stubs = tmp_path / "stubs"
    stubs.mkdir(parents=True, exist_ok=True)
    (stubs / "python-stub").write_text(_ARGV_STUB, encoding="utf-8")
    (stubs / "python-stub").chmod(0o755)
    out_dir = tmp_path / "out" / "sample" / "f"
    out_dir.mkdir(parents=True, exist_ok=True)
    (tmp_path / "runtmp").mkdir(parents=True, exist_ok=True)
    source = (REPO_ROOT / runner).read_text(encoding="utf-8")
    function = _extract_shell_function(source, "run_pair")
    if runner.startswith("eq"):
        args = '"sample" "f" "B1" "B2" "/left" "/right" "%s" 1 1 "/target"' % out_dir
    else:
        args = ('"sample" "f" "N_B1" "O_B2" "/left" "/right" "%s" 1 1 "/target" 1 1 1'
                % out_dir)
    resolve = (
        f'source "{COMMON}"\n'
        f'ANALYSIS_TIMEOUT="{analysis_timeout}"\n'
        # `|| true`: on a tree without the resolver the pair still runs, so the
        # test fails on the missing flag rather than on a missing function.
        f'validation_resolve_analysis_timeout_policy "{sys.executable}" "" "{REPO_ROOT}" '
        "|| true\n"
    )
    script = (
        _HARNESS
        .replace("__FUNCTION__", resolve + "__FUNCTION__", 1)
        .replace("__STUBS__", str(stubs))
        .replace("__TMP__", str(tmp_path))
        .replace("__FUNCTION__", function)
        .replace("__ARGS__", args)
    )
    env = dict(os.environ)
    env.pop("ANALYSIS_TIMEOUT_MARGIN", None)
    env["ORDER_FILE"] = str(tmp_path / "order.txt")
    env["ARGV_FILE"] = str(tmp_path / "argv.txt")
    subprocess.run(["bash", "-c", script], env=env, capture_output=True, timeout=180)
    argv = tmp_path / "argv.txt"
    return argv.read_text(encoding="utf-8") if argv.is_file() else ""


def _pair_command(argv: str) -> str:
    lines = [line for line in argv.splitlines() if "cli.main" in line]
    assert len(lines) == 1, argv
    return lines[0]


@pytest.mark.parametrize("runner", RUNNERS)
def test_the_deadline_reaches_the_pair_command(tmp_path, runner):
    command = _pair_command(_run_pair_argv(tmp_path, runner, "100"))

    assert f"{FLAG} 100" in command, command
    assert command.count(FLAG) == 1, command


@pytest.mark.parametrize("runner", RUNNERS)
def test_off_hands_the_pair_exactly_the_pre_deadline_command(tmp_path, runner):
    """``ANALYSIS_TIMEOUT=0`` is the rollback: no flag at all, not ``--analysis-timeout 0``."""

    def normalised(root: Path, command: str) -> str:
        # the two runs live in different tmp roots and get random pair tmpdirs
        return re.sub(r"pair\.\w+", "pair.X", command.replace(str(root), "ROOT"))

    off = normalised(tmp_path / "off", _pair_command(_run_pair_argv(tmp_path / "off", runner, "0")))
    on = normalised(tmp_path / "on", _pair_command(_run_pair_argv(tmp_path / "on", runner, "100")))

    assert FLAG not in off, off
    assert on.replace(f" {FLAG} 100", "") == off


# --------------------------------------------------------------------------
# E7: an inconsistent setting stops the run before it does anything (DRY_RUN=1)
# --------------------------------------------------------------------------


def _script_env(tmp_path: Path, **settings: str) -> dict:
    env = {
        key: value for key, value in os.environ.items()
        if not key.startswith(("ANALYSIS_TIMEOUT", "PAIR_PROCESS", "EQBENCH_", "NEQ_"))
    }
    empty_root = tmp_path / "empty-eqbench"
    empty_root.mkdir(exist_ok=True)
    env.update(
        DRY_RUN="1",
        PYTHON_BIN=sys.executable,
        OUTPUT_BASE_DIR=str(tmp_path / "out"),
        EQBENCH_TMPDIR=str(tmp_path / "tmpdir"),
        EQBENCH_ROOT=str(empty_root),
        # The Neq runner insists on a root inside the repository and exits 1
        # silently without one -- which would make this test pass for the
        # wrong reason, so it gets a directory that exists.
        NEQ_ROOT=str(REPO_ROOT / "scripts"),
        # the subset runner appends to the repository's ledger by default
        VERIFICATION_LEDGER=str(tmp_path / "ledger.jsonl"),
    )
    env.update(settings)
    return env


SCRIPTS = RUNNERS + ("eqbench_run_subset.sh",)

#: (settings, the part of the error message that names the problem)
_INCONSISTENT = [
    pytest.param(
        {"ANALYSIS_TIMEOUT": "500", "ANALYSIS_TIMEOUT_MARGIN": "101",
         "PAIR_PROCESS_TIMEOUT": "600s"},
        POLICY_ERROR, id="one-second-over",
    ),
    pytest.param(
        {"ANALYSIS_TIMEOUT": "5m", "PAIR_PROCESS_TIMEOUT": "600s"},
        "ANALYSIS_TIMEOUT must be a number of seconds", id="unit-minutes",
    ),
    pytest.param(
        {"ANALYSIS_TIMEOUT": "100", "ANALYSIS_TIMEOUT_MARGIN": "0",
         "PAIR_PROCESS_TIMEOUT": "600s"},
        "ANALYSIS_TIMEOUT_MARGIN must be a positive", id="zero-margin",
    ),
    pytest.param(
        {"ANALYSIS_TIMEOUT": "-1", "PAIR_PROCESS_TIMEOUT": "600s"},
        "ANALYSIS_TIMEOUT must be a number of seconds", id="negative",
    ),
]


@pytest.mark.parametrize("script", SCRIPTS)
@pytest.mark.parametrize("settings,message", _INCONSISTENT)
def test_an_inconsistent_setting_exits_1_before_the_run_starts(
    tmp_path, script, settings, message,
):
    env = _script_env(tmp_path, **settings)
    completed = subprocess.run(
        ["bash", str(REPO_ROOT / script)], cwd=REPO_ROOT, env=env,
        capture_output=True, text=True, timeout=120,
    )

    assert completed.returncode == 1, (completed.stdout, completed.stderr)
    assert message in completed.stderr, completed.stderr
    # Nothing was made: no output tree, no run tmpdir.
    assert not (tmp_path / "out").exists()
    assert not (tmp_path / "tmpdir").exists()


def test_the_subset_default_is_checked_against_the_subset_process_timeout(tmp_path):
    """The subset's own ANALYSIS_TIMEOUT (manifest) meets a PAIR_PROCESS_TIMEOUT override.

    Lowering only the process timeout must not leave the manifest's deadline
    unchecked: the combination is rejected before either half runs.
    """

    env = _script_env(tmp_path, PAIR_PROCESS_TIMEOUT="60s")
    completed = subprocess.run(
        ["bash", str(REPO_ROOT / "eqbench_run_subset.sh")], cwd=REPO_ROOT, env=env,
        capture_output=True, text=True, timeout=120,
    )

    assert completed.returncode == 1, (completed.stdout, completed.stderr)
    assert POLICY_ERROR in completed.stderr, completed.stderr
    assert not (tmp_path / "out").exists()


@pytest.mark.parametrize("script", SCRIPTS)
@pytest.mark.parametrize(
    "settings",
    [
        pytest.param({"ANALYSIS_TIMEOUT": "0", "PAIR_PROCESS_TIMEOUT": "60s"}, id="off"),
        pytest.param(
            {"ANALYSIS_TIMEOUT": "499", "ANALYSIS_TIMEOUT_MARGIN": "101",
             "PAIR_PROCESS_TIMEOUT": "600s"},
            id="exactly-at-the-bound",
        ),
    ],
)
def test_a_consistent_setting_is_not_rejected(tmp_path, script, settings):
    """Control: the same check lets ``0`` and the boundary through.

    The run then stops later for reasons of this sandbox (no EqBench tree), so
    only the absence of the policy's refusal is asserted.
    """

    env = _script_env(tmp_path, **settings)
    completed = subprocess.run(
        ["bash", str(REPO_ROOT / script)], cwd=REPO_ROOT, env=env,
        capture_output=True, text=True, timeout=180,
    )

    assert POLICY_ERROR not in completed.stderr, completed.stderr
    assert "must be a number of seconds" not in completed.stderr, completed.stderr


# --------------------------------------------------------------------------
# what the runners record
# --------------------------------------------------------------------------


@pytest.mark.parametrize("runner", RUNNERS)
def test_the_effective_values_are_recorded_before_the_config_digest(runner):
    """The deadline is part of the analysis identity, so it is written before
    the digest is taken (a digest of a manifest without it would let a run
    with the deadline reuse pair statuses made without it)."""

    source = (REPO_ROOT / runner).read_text(encoding="utf-8")

    assert "analysis_config_schema=eqbench-analysis-config-v4" in source
    lines = source.index("$ANALYSIS_TIMEOUT_MANIFEST_LINES")
    assert lines < source.index("--print-analysis-config-digest")
    # one resolver call (the E7 tests above show it runs before anything is made)
    assert source.count("validation_resolve_analysis_timeout_policy") == 1


def test_the_subset_records_what_the_halves_recorded():
    source = (REPO_ROOT / "eqbench_run_subset.sh").read_text(encoding="utf-8")

    assert 'echo "$key=$(half_setting "$key")"' in source
    assert '<<< "$ANALYSIS_TIMEOUT_MANIFEST_LINES"' in source
    assert "manifest_value setting ANALYSIS_TIMEOUT" in source
