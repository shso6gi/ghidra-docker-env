# -*- coding: utf-8 -*-
"""Issue #106 PR-106-B: the runner's analysis deadline -- one rule, one record.

``reporting/runner_timeout_policy.py`` is the only place that decides what
``ANALYSIS_TIMEOUT`` / ``ANALYSIS_TIMEOUT_MARGIN`` / ``PAIR_PROCESS_TIMEOUT``
mean together.  These tests pin that rule (formats, defaults, ``0`` = off, the
inequality and its boundary), that every value it lets through is one the CLI
accepts, and that the recorded values reach every consumer that reads them:
the analysis config identity (v4), the publication manifest, the soundness
gate's run mode, the verification ledger and the shipped defaults.
"""
from __future__ import annotations

import ast
import json
import re
import subprocess
import sys
from decimal import Decimal
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.reporting import runner_timeout_policy as policy
from scripts.function_tracer_pcode.reporting.runner_timeout_policy import (
    TimeoutPolicyError,
    resolve_runner_timeout_policy,
)

REPO_ROOT = Path(__file__).resolve().parents[4]
COMMON = REPO_ROOT / "scripts" / "validation_matrix_common.sh"


def _resolve(analysis_timeout="", margin="", process="600s", **kwargs):
    return resolve_runner_timeout_policy(
        analysis_timeout=analysis_timeout, margin=margin,
        pair_process_timeout=process, **kwargs,
    )


# --------------------------------------------------------------------------
# the rule
# --------------------------------------------------------------------------


def test_unset_takes_the_runner_default_and_is_on():
    resolved = _resolve()

    assert resolved.enabled
    assert resolved.analysis_timeout == Decimal(policy.FULL_RUN_DEFAULT_ANALYSIS_TIMEOUT)
    assert resolved.margin == Decimal(policy.DEFAULT_ANALYSIS_TIMEOUT_MARGIN)
    assert resolved.cli_args() == ("--analysis-timeout", policy.FULL_RUN_DEFAULT_ANALYSIS_TIMEOUT)


def test_an_empty_value_is_unset_not_zero():
    """``ANALYSIS_TIMEOUT=`` means "not given" (the CI normalisation's reading too)."""

    assert _resolve(analysis_timeout="", margin="") == _resolve()


def test_a_runner_can_name_its_own_default():
    resolved = _resolve(process="240s", default_analysis_timeout="115s")

    assert resolved.analysis_timeout == Decimal(115)
    assert resolved.manifest_fields()["analysis_timeout"] == "115"


@pytest.mark.parametrize("spelling", ["0", "0s", "0.0", "000"])
def test_zero_turns_the_deadline_off(spelling):
    resolved = _resolve(analysis_timeout=spelling, process="60s")

    assert not resolved.enabled
    assert resolved.cli_args() == ()
    assert resolved.manifest_fields() == {
        "analysis_timeout": "0",
        "analysis_timeout_enabled": "0",
        "analysis_timeout_margin": policy.DEFAULT_ANALYSIS_TIMEOUT_MARGIN,
    }


def test_off_is_not_checked_against_the_process_timeout():
    """With no deadline there is nothing to leave room for."""

    assert not _resolve(analysis_timeout="0", margin="500", process="1s").enabled


@pytest.mark.parametrize(
    "timeout,margin,process",
    [
        ("500", "100", "600s"),         # exactly at the bound
        ("0.1", "0.2", "0.3"),          # 0.1 + 0.2 > 0.3 in binary floating point
        ("120", "120", "240s"),
    ],
)
def test_the_bound_is_inclusive_and_exact(timeout, margin, process):
    assert _resolve(analysis_timeout=timeout, margin=margin, process=process).enabled


@pytest.mark.parametrize(
    "timeout,margin,process",
    [
        ("500.001", "100", "600s"),
        ("480", "121", "600s"),
        ("121", "120", "240s"),
        ("1", "1", "1s"),
    ],
)
def test_a_deadline_without_its_margin_is_refused(timeout, margin, process):
    with pytest.raises(TimeoutPolicyError) as raised:
        _resolve(analysis_timeout=timeout, margin=margin, process=process)

    message = str(raised.value)
    for variable in ("ANALYSIS_TIMEOUT", "ANALYSIS_TIMEOUT_MARGIN", "PAIR_PROCESS_TIMEOUT"):
        assert variable in message
    assert "never raised automatically" in message


@pytest.mark.parametrize(
    "raw",
    ["-1", "+5", "1e3", "1E3", "inf", "nan", "5m", "2h", " 5", "5 ", ".5", "5.",
     "s", "0x10", "5ss", "５", "1_000", "480\n"],
)
@pytest.mark.parametrize("variable", ["analysis_timeout", "margin", "process"])
def test_a_malformed_value_is_refused_wherever_it_is(raw, variable):
    settings = {"analysis_timeout": "100", "margin": "100", "process": "600s"}
    settings[variable] = raw
    with pytest.raises(TimeoutPolicyError):
        _resolve(**settings)


def test_a_malformed_process_timeout_is_refused_even_when_off():
    with pytest.raises(TimeoutPolicyError):
        _resolve(analysis_timeout="0", process="ten minutes")


def test_a_zero_margin_is_refused():
    with pytest.raises(TimeoutPolicyError):
        _resolve(analysis_timeout="100", margin="0")


@pytest.mark.parametrize(
    "raw,text",
    [("480", "480"), ("480s", "480"), ("480.0", "480"), ("0480", "480"),
     ("120.50", "120.5"), ("0.25", "0.25"), ("1000000", "1000000")],
)
def test_values_are_recorded_in_one_spelling(raw, text):
    assert policy.seconds_text(policy.parse_seconds(raw, variable="X")) == text


@pytest.mark.parametrize("raw", ["1", "0.001", "120.5", "480s", "86400"])
def test_every_value_handed_to_a_pair_is_one_the_cli_accepts(raw):
    """The runner's rule is never looser than the CLI's (`--analysis-timeout`)."""

    from scripts.function_tracer_pcode.cli.args import build_parser

    resolved = _resolve(analysis_timeout=raw, margin="1", process="100000s")
    flag, value = resolved.cli_args()
    parsed = build_parser().parse_args(["--equiv", "a", "b", "-f", "x", flag, value])

    assert Decimal(str(parsed.analysis_timeout)) == resolved.analysis_timeout


def test_the_manifest_keys_have_one_owner():
    assert tuple(_resolve().manifest_fields()) == policy.MANIFEST_KEYS
    assert tuple(_resolve(analysis_timeout="0").manifest_fields()) == policy.MANIFEST_KEYS


# --------------------------------------------------------------------------
# the CLI and the shell function every runner calls
# --------------------------------------------------------------------------


def test_the_cli_prints_the_effective_values_or_exits_1():
    ok = subprocess.run(
        [sys.executable, "-B", "-m", "scripts.function_tracer_pcode.reporting.runner_timeout_policy",
         "resolve", "--analysis-timeout", "100s", "--pair-process-timeout", "240s"],
        cwd=REPO_ROOT, capture_output=True, text=True, timeout=60,
    )
    bad = subprocess.run(
        [sys.executable, "-B", "-m", "scripts.function_tracer_pcode.reporting.runner_timeout_policy",
         "resolve", "--analysis-timeout", "200", "--pair-process-timeout", "240s"],
        cwd=REPO_ROOT, capture_output=True, text=True, timeout=60,
    )

    assert ok.returncode == 0, ok.stderr
    assert ok.stdout.splitlines() == [
        "analysis_timeout=100", "analysis_timeout_enabled=1",
        f"analysis_timeout_margin={policy.DEFAULT_ANALYSIS_TIMEOUT_MARGIN}",
    ]
    assert bad.returncode == 1
    assert bad.stdout == ""
    assert "exceeds PAIR_PROCESS_TIMEOUT" in bad.stderr


def _shell_resolve(env_lines: str) -> subprocess.CompletedProcess:
    script = (
        f'set -u\nsource "{COMMON}"\n{env_lines}\n'
        f'validation_resolve_analysis_timeout_policy "{sys.executable}" "${{DEFAULT_AT-}}" '
        f'"{REPO_ROOT}" || {{ echo "rc=$?"; exit 0; }}\n'
        'printf "seconds=%s\\nmargin=%s\\nargs=%s|\\n" "$ANALYSIS_TIMEOUT_SECONDS" '
        '"$ANALYSIS_TIMEOUT_MARGIN_SECONDS" "${ANALYSIS_TIMEOUT_CLI_ARGS[*]-}"\n'
        'printf "%s\\n" "$ANALYSIS_TIMEOUT_MANIFEST_LINES"\n'
    )
    return subprocess.run(
        ["bash", "-c", script], capture_output=True, text=True, timeout=60,
        env={"PATH": "/usr/bin:/bin"},
    )


def test_the_shell_function_sets_the_runner_variables():
    on = _shell_resolve('ANALYSIS_TIMEOUT=300; ANALYSIS_TIMEOUT_MARGIN=50; PAIR_PROCESS_TIMEOUT=600s')
    off = _shell_resolve('ANALYSIS_TIMEOUT=0; PAIR_PROCESS_TIMEOUT=600s')
    default = _shell_resolve('PAIR_PROCESS_TIMEOUT=240s; DEFAULT_AT=115')

    assert "seconds=300\nmargin=50\nargs=--analysis-timeout 300|" in on.stdout, on
    assert "analysis_timeout_enabled=1" in on.stdout
    assert "seconds=0\n" in off.stdout and "args=|" in off.stdout, off
    assert "analysis_timeout_enabled=0" in off.stdout
    assert "seconds=115\n" in default.stdout, default


def test_the_shell_function_fails_closed():
    """Unlike ``validation_positive_int_setting`` it never falls back to a default."""

    bad = _shell_resolve('ANALYSIS_TIMEOUT=300; ANALYSIS_TIMEOUT_MARGIN=301; PAIR_PROCESS_TIMEOUT=600s')
    script_error = _shell_resolve('ANALYSIS_TIMEOUT=abc; PAIR_PROCESS_TIMEOUT=600s')

    assert "rc=1" in bad.stdout, bad
    assert "seconds=" not in bad.stdout
    assert "rc=1" in script_error.stdout, script_error


# --------------------------------------------------------------------------
# the shipped defaults are consistent with the process timeouts they meet
# --------------------------------------------------------------------------


def _runner_process_default(runner: str) -> str:
    source = (REPO_ROOT / runner).read_text(encoding="utf-8")
    match = re.search(
        r'PAIR_PROCESS_TIMEOUT="\$\{PAIR_PROCESS_TIMEOUT:-([0-9]+s)\}"'
        r"|default_value PAIR_PROCESS_TIMEOUT ([0-9]+s)",
        source,
    )
    assert match, runner
    return match.group(1) or match.group(2)


@pytest.mark.parametrize("runner", ["eqbench_run_all_32jobs.sh", "neqbench_run_all_32jobs.sh"])
def test_the_full_run_defaults_fit_the_full_run_process_timeout(runner):
    resolved = _resolve(process=_runner_process_default(runner))

    assert resolved.enabled


def test_the_subset_defaults_fit_the_subset_process_timeout():
    settings = json.loads(
        (REPO_ROOT / "scripts/function_tracer_pcode/reporting/eqbench_subset.json")
        .read_text(encoding="utf-8")
    )["run_settings"]
    resolved = _resolve(
        analysis_timeout=settings["ANALYSIS_TIMEOUT"], process=settings["PAIR_PROCESS_TIMEOUT"],
    )

    assert resolved.enabled
    assert resolved.analysis_timeout < Decimal(policy.FULL_RUN_DEFAULT_ANALYSIS_TIMEOUT)


# --------------------------------------------------------------------------
# the recorded values reach the analysis identity and its consumers
# --------------------------------------------------------------------------


def _manifest(**overrides: str) -> dict:
    run = {
        "run_scope": "REPRESENTATIVE", "build_policy": "PREBUILT_ONLY", "max_samples": "0",
        "sample_filter": "", "pair_filter": "", "debug": "0", "dry_run": "0",
        "parallel_jobs": "20", "validation_summary_level": "compact",
        "equiv_timeout": "10", "decompile_timeout": "60", "pairwise_timeout": "5",
        "pairwise_timeout_hard": "30", "pair_process_timeout_seconds": "240",
        "pair_process_kill_after_seconds": "30",
        "prefilter_source_census_digest": "0" * 64, "skip_completed_results": "1",
        "analysis_config_schema": "eqbench-analysis-config-v4", "identical_fast_path": "1",
        **_resolve(analysis_timeout="100", process="240s").manifest_fields(),
    }
    run.update(overrides)
    return run


def test_the_deadline_and_margin_are_part_of_the_analysis_identity():
    from scripts.function_tracer_pcode.authority.contracts import authority_digest
    from scripts.function_tracer_pcode.reporting.execution_receipt import (
        ANALYSIS_CONFIG_V4_FIELDS,
        ANALYSIS_CONFIG_V4_SCHEMA,
        analysis_config_from_run,
    )

    config = analysis_config_from_run(_manifest())
    assert config["schema"] == ANALYSIS_CONFIG_V4_SCHEMA
    assert set(config) == ANALYSIS_CONFIG_V4_FIELDS
    assert config["analysis_timeout_seconds"] == "100"
    assert config["analysis_timeout_margin_seconds"] == policy.DEFAULT_ANALYSIS_TIMEOUT_MARGIN
    digests = {
        authority_digest(analysis_config_from_run(_manifest(**change)))
        for change in ({}, {"analysis_timeout": "90"}, {"analysis_timeout_margin": "99"},
                       {"analysis_timeout": "0", "analysis_timeout_enabled": "0"})
    }
    assert len(digests) == 4


@pytest.mark.parametrize(
    "change",
    [{"analysis_timeout": None}, {"analysis_timeout_margin": None},
     {"analysis_timeout": "120s"}, {"analysis_timeout": "abc"}],
)
def test_a_v4_manifest_without_usable_values_has_no_identity(change):
    """No silent fall back to v3: that would let deadline and no-deadline runs share a digest."""

    from scripts.function_tracer_pcode.reporting.execution_receipt import analysis_config_from_run

    run = _manifest()
    for key, value in change.items():
        if value is None:
            run.pop(key)
        else:
            run[key] = value
    with pytest.raises(ValueError):
        analysis_config_from_run(run)


def test_only_an_off_run_reads_as_the_run_before_the_deadline_existed():
    from scripts.function_tracer_pcode.reporting.execution_receipt import (
        ANALYSIS_CONFIG_V3_SCHEMA,
        analysis_config_from_run,
        normalize_semantic_analysis_config,
    )

    v3_run = _manifest(analysis_config_schema=ANALYSIS_CONFIG_V3_SCHEMA)
    for key in policy.MANIFEST_KEYS:
        v3_run.pop(key)
    v3 = normalize_semantic_analysis_config(analysis_config_from_run(v3_run))
    off = normalize_semantic_analysis_config(analysis_config_from_run(
        _manifest(analysis_timeout="0", analysis_timeout_enabled="0", analysis_timeout_margin="7")
    ))
    on = normalize_semantic_analysis_config(analysis_config_from_run(_manifest()))

    assert off == v3
    assert on != v3


def test_an_off_run_can_resume_a_tree_written_before_the_deadline(tmp_path):
    from scripts.function_tracer_pcode.authority.contracts import authority_digest
    from scripts.function_tracer_pcode.reporting.execution_receipt import (
        ANALYSIS_CONFIG_V3_SCHEMA,
        analysis_config_from_run,
        compatible_previous_run_manifest_analysis_identity,
    )

    previous = _manifest(analysis_config_schema=ANALYSIS_CONFIG_V3_SCHEMA)
    for key in policy.MANIFEST_KEYS:
        previous.pop(key)
    previous["analysis_config_digest"] = authority_digest(analysis_config_from_run(previous))
    previous["analysis_source_digest_start"] = "a" * 64
    path = tmp_path / "previous.txt"
    path.write_text("".join(f"{k}={v}\n" for k, v in previous.items()), encoding="utf-8")

    off = analysis_config_from_run(_manifest(analysis_timeout="0", analysis_timeout_enabled="0"))
    on = analysis_config_from_run(_manifest())

    assert compatible_previous_run_manifest_analysis_identity(path, current_config=off) == (
        previous["analysis_config_digest"], "a" * 64,
    )
    assert compatible_previous_run_manifest_analysis_identity(path, current_config=on) is None


def test_the_soundness_gate_reads_a_v4_run_mode(tmp_path):
    from scripts.function_tracer_pcode.reporting import execution_receipt, soundness_gate

    assert (soundness_gate.ANALYSIS_CONFIG_SCHEMAS_WITH_FAST_PATH
            == execution_receipt.ANALYSIS_CONFIG_SCHEMAS_WITH_FAST_PATH)
    path = tmp_path / "run_manifest.txt"
    path.write_text("".join(f"{k}={v}\n" for k, v in _manifest().items()), encoding="utf-8")
    mode = soundness_gate.resolve_run_mode(path)

    assert mode.mode == soundness_gate.MODE_ON
    assert mode.detail == "analysis_config_v4"


def test_the_ledger_row_says_which_deadline_a_run_had():
    from scripts.function_tracer_pcode.reporting import verification_ledger

    for key in policy.MANIFEST_KEYS:
        assert key in verification_ledger.SETTING_KEYS


# --------------------------------------------------------------------------
# the CI workflow resolves once with the same rule and passes the result on
# --------------------------------------------------------------------------


WORKFLOW = REPO_ROOT / ".github" / "workflows" / "eqbench-subset.yml"


def _workflow_steps() -> dict:
    import yaml

    document = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))
    if True in document:
        document["on"] = document.pop(True)
    return document


def test_the_workflow_offers_the_deadline_without_a_default_of_its_own():
    inputs = _workflow_steps()["on"]["workflow_dispatch"]["inputs"]

    # empty = the subset manifest's value / the runner default: no second copy here
    assert inputs["analysis_timeout"]["default"] == ""
    assert inputs["analysis_timeout_margin"]["default"] == ""


def test_the_workflow_normalises_with_the_runners_rule_before_anything_runs():
    steps = _workflow_steps()["jobs"]["subset"]["steps"]
    names = [step.get("name", "") for step in steps]
    normalise = steps[names.index("Normalise the inputs")]["run"]

    assert "scripts.function_tracer_pcode.reporting.runner_timeout_policy" in normalise
    assert '"run_settings"]["ANALYSIS_TIMEOUT"]' in normalise
    assert names.index("Normalise the inputs") < names.index("Build the analysis container")


def test_every_container_run_and_every_verification_gets_the_effective_values():
    source = WORKFLOW.read_text(encoding="utf-8")
    runs = source.count('EQBENCH_IDENTICAL_FAST_PATH="$EQBENCH_IDENTICAL_FAST_PATH" \\')
    verifies = source.count("scripts.eqbench.ci_subset verify")

    assert runs == 3  # round trip, dry run, the run itself
    assert source.count('ANALYSIS_TIMEOUT="$ANALYSIS_TIMEOUT" \\') == runs
    assert source.count('ANALYSIS_TIMEOUT_MARGIN="$ANALYSIS_TIMEOUT_MARGIN" \\') == runs
    assert verifies == 2
    assert source.count('--analysis-timeout "$ANALYSIS_TIMEOUT" \\') == verifies
    assert source.count('--analysis-timeout-margin "$ANALYSIS_TIMEOUT_MARGIN" \\') == verifies


def test_the_runner_variables_stay_at_the_entry_points():
    """The deadline reaches a pair only as ``--analysis-timeout``; no deep layer
    reads the runner's variables (the analysis takes its ``DeadlinePolicy`` from
    the CLI, ``core/deadline.py`` owns what the deadline means)."""

    package = REPO_ROOT / "scripts" / "function_tracer_pcode"
    offenders = []
    for layer in ("core", "smt", "config", "ghidra", "analysis", "semantics", "proof",
                  "authority", "checker", "cli"):
        for path in (package / layer).rglob("*.py"):
            tree = ast.parse(path.read_text(encoding="utf-8"))
            docstrings = {
                id(node.body[0].value) for node in ast.walk(tree)
                if isinstance(node, (ast.Module, ast.FunctionDef, ast.ClassDef,
                                     ast.AsyncFunctionDef))
                and node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
            }
            for node in ast.walk(tree):
                named = (
                    isinstance(node, ast.Constant) and isinstance(node.value, str)
                    and id(node) not in docstrings
                    and re.search(r"\bANALYSIS_TIMEOUT", node.value)
                ) or (
                    isinstance(node, ast.ImportFrom)
                    and "runner_timeout_policy" in (node.module or "")
                )
                if named:
                    offenders.append(str(path.relative_to(package)))
    assert offenders == []
