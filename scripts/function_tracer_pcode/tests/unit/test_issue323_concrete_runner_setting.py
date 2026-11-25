# -*- coding: utf-8 -*-
"""Issue #323 (C4): the runners' concrete-execution setting, its identity and its per-pair record.

The rule (stage names, defaults, the analysis-deadline interplay) is tested on
``reporting/runner_concrete_policy.py``; its wiring is tested by driving the real
shell scripts -- ``run_pair`` with a stubbed pair entry point, and the scripts
themselves in ``DRY_RUN=1`` -- as the deadline tests of PR-106-B do.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
from decimal import Decimal
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.checker.concrete_replay import (
    CONCRETE_SETTING_SCHEMA,
    CONCRETE_STAGES,
    INACTIVE_NO_ANALYSIS_DEADLINE,
    INACTIVE_NOT_REQUESTED,
    STAGE_WITNESS_REPLAY,
    ConcreteReplayOptions,
    concrete_execution_setting,
)
from scripts.function_tracer_pcode.reporting import execution_receipt as er
from scripts.function_tracer_pcode.reporting import runner_concrete_policy as policy
from scripts.function_tracer_pcode.tests.unit.test_issue106b_runner_wiring import (
    COMMON,
    REPO_ROOT,
    RUNNERS,
    SCRIPTS,
    _pair_command,
    _script_env,
)
from scripts.function_tracer_pcode.tests.unit.test_issue124c_runner_and_supervisor import (
    _HARNESS,
    _extract_shell_function,
)


# --------------------------------------------------------------------------
# the rule
# --------------------------------------------------------------------------


def _resolve(stages="", budget="", deadline=True):
    return policy.resolve_runner_concrete_policy(
        stages=stages, budget=budget, analysis_timeout_enabled=deadline,
    )


def test_the_default_is_the_checkers_default():
    resolved, warning = _resolve()

    assert warning is None
    assert resolved.stages == (STAGE_WITNESS_REPLAY,)
    assert resolved.budget == Decimal(60)
    assert resolved.cli_args() == ("--concrete-replay-budget", "60")
    assert resolved.manifest_fields() == {
        "concrete_stages_requested": "witness_replay",
        "concrete_budget_requested": "60",
        "concrete_stages": "witness_replay",
        "concrete_budget": "60",
        "concrete_inactive_reason": "active",
    }
    assert tuple(resolved.manifest_fields()) == policy.MANIFEST_KEYS


def test_none_turns_every_stage_off_and_records_no_budget():
    resolved, warning = _resolve(stages="none", budget="30")

    assert warning is None
    assert resolved.stages == ()
    assert resolved.cli_args() == ("--no-concrete-replay",)
    fields = resolved.manifest_fields()
    assert fields["concrete_stages"] == "none"
    assert fields["concrete_budget"] == "0"
    assert fields["concrete_budget_requested"] == "30"
    assert fields["concrete_inactive_reason"] == INACTIVE_NOT_REQUESTED


def test_an_explicit_stage_without_an_analysis_deadline_is_refused():
    with pytest.raises(policy.ConcretePolicyError, match="needs the analysis deadline"):
        _resolve(stages="witness_replay", deadline=False)


def test_the_default_without_an_analysis_deadline_runs_no_stage_and_says_so():
    resolved, warning = _resolve(deadline=False)

    assert warning and "ANALYSIS_TIMEOUT is 0" in warning
    assert resolved.stages == ()
    assert resolved.requested_stages == (STAGE_WITNESS_REPLAY,)
    assert resolved.cli_args() == ("--no-concrete-replay",)
    fields = resolved.manifest_fields()
    assert fields["concrete_stages"] == "none"
    assert fields["concrete_budget"] == "0"
    assert fields["concrete_inactive_reason"] == INACTIVE_NO_ANALYSIS_DEADLINE


def test_explicit_none_without_a_deadline_is_not_refused():
    resolved, warning = _resolve(stages="none", deadline=False)

    assert warning is None and resolved.stages == ()


@pytest.mark.parametrize("raw", [
    "witness", "witness_replay,", ",witness_replay", "witness_replay,witness_replay",
    "none,witness_replay", " witness_replay", "WITNESS_REPLAY", "off", "0",
])
def test_a_misspelt_stage_list_is_refused(raw):
    with pytest.raises(policy.ConcretePolicyError):
        _resolve(stages=raw)


@pytest.mark.parametrize("raw", ["0", "-1", "1m", "inf", "nan", " 60"])
def test_a_bad_budget_is_refused(raw):
    with pytest.raises(policy.ConcretePolicyError):
        _resolve(budget=raw)


def test_the_budget_is_spelt_as_the_cli_reads_it():
    resolved, _ = _resolve(budget="12.50s")

    assert resolved.cli_args() == ("--concrete-replay-budget", "12.5")


def test_every_registered_stage_round_trips():
    for stage in CONCRETE_STAGES:
        assert policy.parse_stages(stage) == (stage,)
        assert policy.stages_text(policy.parse_stages(stage)) == stage


def test_the_module_cli_prints_the_values_then_the_arguments(capsys):
    assert policy.main(["resolve", "--analysis-timeout-enabled", "1"]) == 0
    out = capsys.readouterr().out.splitlines()

    assert out[: len(policy.MANIFEST_KEYS)] == [
        f"{key}={value}" for key, value in _resolve()[0].manifest_fields().items()
    ]
    assert out[len(policy.MANIFEST_KEYS):] == ["cli_arg=--concrete-replay-budget", "cli_arg=60"]


def test_the_module_cli_exits_1_on_refusal(capsys):
    code = policy.main([
        "resolve", "--stages", "witness_replay", "--analysis-timeout-enabled", "0",
    ])

    assert code == 1
    assert "needs the analysis deadline" in capsys.readouterr().err


# --------------------------------------------------------------------------
# the identity
# --------------------------------------------------------------------------


def _run_manifest(**overrides):
    run = {
        "run_scope": "REPRESENTATIVE", "build_policy": "REUSE_OR_COMPILE", "max_samples": "0",
        "sample_filter": "", "pair_filter": "", "debug": "0", "dry_run": "0",
        "parallel_jobs": "4", "validation_summary_level": "compact", "equiv_timeout": "10",
        "decompile_timeout": "60", "pairwise_timeout": "5", "pairwise_timeout_hard": "30",
        "pair_process_timeout_seconds": "600", "pair_process_kill_after_seconds": "30",
        "prefilter_source_census_digest": "0" * 64, "identical_fast_path": "1",
        "analysis_timeout": "410", "analysis_timeout_margin": "190",
        "expander_dedup_case_limit_effective": "16", "callee_unbound_reuse": "1",
        "callee_unbound_reuse_shadow": "0",
        "analysis_config_schema": er.ANALYSIS_CONFIG_V6_SCHEMA,
        "concrete_stages": "witness_replay", "concrete_budget": "60",
    }
    run.update(overrides)
    return run


def _digest(config):
    return hashlib.sha256(json.dumps(config, sort_keys=True).encode()).hexdigest()


def test_v6_carries_the_effective_concrete_setting():
    config = er.analysis_config_from_run(_run_manifest())

    assert config["schema"] == er.ANALYSIS_CONFIG_V6_SCHEMA
    assert config["concrete_stages"] == "witness_replay"
    assert config["concrete_budget_seconds"] == "60"
    assert set(config) == er.ANALYSIS_CONFIG_V6_FIELDS
    assert er.ANALYSIS_CONFIG_CONCRETE_FIELDS == {"concrete_stages", "concrete_budget_seconds"}


def test_on_and_off_and_another_budget_are_different_identities():
    on = er.normalize_semantic_analysis_config(er.analysis_config_from_run(_run_manifest()))
    off = er.normalize_semantic_analysis_config(er.analysis_config_from_run(
        _run_manifest(concrete_stages="none", concrete_budget="0")))
    budget = er.normalize_semantic_analysis_config(er.analysis_config_from_run(
        _run_manifest(concrete_budget="30")))

    assert len({_digest(on), _digest(off), _digest(budget)}) == 3


def test_v6_is_never_projected_onto_v5():
    """A v5 run did not record the concrete setting, so no v6 run matches it."""

    v6 = er.normalize_semantic_analysis_config(er.analysis_config_from_run(_run_manifest()))
    v5 = er.normalize_semantic_analysis_config(er.analysis_config_from_run(
        _run_manifest(analysis_config_schema=er.ANALYSIS_CONFIG_V5_SCHEMA)))

    assert v6["schema"] == er.ANALYSIS_CONFIG_V6_SCHEMA
    assert v5["schema"] == er.ANALYSIS_CONFIG_V5_SCHEMA
    assert "concrete_stages" not in v5
    assert _digest(v5) != _digest(v6)


@pytest.mark.parametrize("stages,budget", [
    ("none", "60"), ("witness_replay", "0"), ("unknown_stage", "60"), ("", "60"),
    ("witness_replay", "1m"), ("witness_replay", ""),
])
def test_an_inconsistent_v6_setting_is_refused(stages, budget):
    with pytest.raises(ValueError):
        er.analysis_config_from_run(_run_manifest(concrete_stages=stages, concrete_budget=budget))


def test_a_v6_manifest_without_the_concrete_rows_is_refused():
    run = _run_manifest()
    del run["concrete_stages"]

    with pytest.raises(ValueError):
        er.analysis_config_from_run(run)


def test_the_soundness_gate_knows_v6():
    from scripts.function_tracer_pcode.reporting import soundness_gate

    assert er.ANALYSIS_CONFIG_V6_SCHEMA in soundness_gate.ANALYSIS_CONFIG_SCHEMAS_WITH_FAST_PATH


def test_the_ledger_records_the_concrete_setting():
    from scripts.function_tracer_pcode.reporting.verification_ledger import SETTING_KEYS

    assert set(policy.MANIFEST_KEYS) <= set(SETTING_KEYS)


# --------------------------------------------------------------------------
# the per-pair record
# --------------------------------------------------------------------------


def test_the_record_of_an_on_pair_with_a_deadline():
    record = concrete_execution_setting(ConcreteReplayOptions(budget_seconds=45.0), 410.0)

    assert record == {
        "schema": CONCRETE_SETTING_SCHEMA,
        "stages": ["witness_replay"], "effective_stages": ["witness_replay"],
        "inactive_reason": None, "budget_seconds": 45.0, "run_time_limit_seconds": 20.0,
        "step_limit": 300000, "analysis_deadline_seconds": 410.0,
    }


def test_the_record_of_an_on_pair_without_a_deadline_has_no_effective_stage():
    record = concrete_execution_setting(ConcreteReplayOptions(), None)

    assert record["stages"] == ["witness_replay"]
    assert record["effective_stages"] == []
    assert record["inactive_reason"] == INACTIVE_NO_ANALYSIS_DEADLINE


def test_the_record_of_an_off_pair():
    record = concrete_execution_setting(None, 410.0)

    assert record["stages"] == [] and record["effective_stages"] == []
    assert record["inactive_reason"] == INACTIVE_NOT_REQUESTED
    assert record["budget_seconds"] is None


@pytest.mark.parametrize("argv,deadline,effective", [
    (["--analysis-timeout", "410"], 410.0, ["witness_replay"]),
    (["--analysis-timeout", "410", "--no-concrete-replay"], 410.0, []),
    (["--analysis-timeout", "410", "--concrete-replay-budget", "0"], 410.0, []),
    ([], None, []),
])
def test_the_cli_attaches_the_setting_it_parsed(argv, deadline, effective):
    from scripts.function_tracer_pcode.cli.args import build_parser
    from scripts.function_tracer_pcode.cli.commands.equivalence import (
        _attach_concrete_execution_setting,
    )

    args = build_parser().parse_args(["--equiv", "a", "b", "-f", "f", *argv])
    result = argparse.Namespace(diagnostics={"stages": {"kept": True}})
    _attach_concrete_execution_setting(result, args)

    record = result.diagnostics["concrete_execution_setting"]
    assert result.diagnostics["stages"] == {"kept": True}
    assert record["analysis_deadline_seconds"] == deadline
    assert record["effective_stages"] == effective


# --------------------------------------------------------------------------
# the wiring (real scripts)
# --------------------------------------------------------------------------

_ARGV_STUB = """#!/bin/sh
printf '%s\\n' "$*" >> "$ARGV_FILE"
echo stub
exit 0
"""


def _run_pair_argv(tmp_path: Path, runner: str, timeout: str, stages: str = "") -> str:
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
        f'ANALYSIS_TIMEOUT="{timeout}"\n'
        f'EQBENCH_CONCRETE_STAGES="{stages}"\n'
        f'validation_resolve_analysis_timeout_policy "{sys.executable}" "" "{REPO_ROOT}" || true\n'
        f'validation_resolve_concrete_policy "{sys.executable}" "{REPO_ROOT}" || true\n'
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
    for key in ("ANALYSIS_TIMEOUT_MARGIN", "EQBENCH_CONCRETE_BUDGET"):
        env.pop(key, None)
    env["ARGV_FILE"] = str(tmp_path / "argv.txt")
    env["ORDER_FILE"] = str(tmp_path / "order.txt")
    subprocess.run(["bash", "-c", script], env=env, capture_output=True, timeout=180)
    argv = tmp_path / "argv.txt"
    return argv.read_text(encoding="utf-8") if argv.is_file() else ""


@pytest.mark.parametrize("runner", RUNNERS)
@pytest.mark.parametrize("timeout,stages,expected", [
    ("40", "", "--concrete-replay-budget 60"),
    ("40", "none", "--no-concrete-replay"),
    ("0", "", "--no-concrete-replay"),
])
def test_the_setting_reaches_the_pair_command(tmp_path, runner, timeout, stages, expected):
    command = _pair_command(_run_pair_argv(tmp_path, runner, timeout, stages))

    assert expected in command, command
    assert command.count("concrete-replay") == 1, command


@pytest.mark.parametrize("runner", RUNNERS)
def test_the_runners_record_the_setting_before_the_config_digest(runner):
    source = (REPO_ROOT / runner).read_text(encoding="utf-8")

    assert "analysis_config_schema=eqbench-analysis-config-v6" in source
    assert source.index("$CONCRETE_MANIFEST_LINES") < source.index("--print-analysis-config-digest")
    resolve = source.index('validation_resolve_concrete_policy "$PYTHON_BIN"')
    assert source.index('validation_resolve_analysis_timeout_policy "$PYTHON_BIN"') < resolve
    assert source.count('validation_resolve_concrete_policy "$PYTHON_BIN"') == 1
    assert '"EQBENCH_CONCRETE_STAGES=${EQBENCH_CONCRETE_STAGES-}"' in source


def test_the_subset_records_what_the_halves_recorded():
    source = (REPO_ROOT / "eqbench_run_subset.sh").read_text(encoding="utf-8")

    assert '<<< "$CONCRETE_MANIFEST_LINES"' in source
    assert source.index("validation_resolve_analysis_timeout_policy") < source.index(
        "validation_resolve_concrete_policy")


@pytest.mark.parametrize("script", SCRIPTS)
def test_an_explicit_stage_without_a_deadline_exits_1_before_the_run_starts(tmp_path, script):
    env = _script_env(tmp_path, ANALYSIS_TIMEOUT="0", PAIR_PROCESS_TIMEOUT="600s",
                      EQBENCH_CONCRETE_STAGES="witness_replay")
    completed = subprocess.run(
        ["bash", str(REPO_ROOT / script)], cwd=REPO_ROOT, env=env,
        capture_output=True, text=True, timeout=120,
    )

    assert completed.returncode == 1, (completed.stdout, completed.stderr)
    assert "needs the analysis deadline" in completed.stderr, completed.stderr
    assert not (tmp_path / "out").exists()
    assert not (tmp_path / "tmpdir").exists()


@pytest.mark.parametrize("script", SCRIPTS)
def test_a_bad_stage_name_exits_1_before_the_run_starts(tmp_path, script):
    env = _script_env(tmp_path, PAIR_PROCESS_TIMEOUT="600s", EQBENCH_CONCRETE_STAGES="replay")
    completed = subprocess.run(
        ["bash", str(REPO_ROOT / script)], cwd=REPO_ROOT, env=env,
        capture_output=True, text=True, timeout=120,
    )

    assert completed.returncode == 1, (completed.stdout, completed.stderr)
    assert "EQBENCH_CONCRETE_STAGES must be" in completed.stderr, completed.stderr
    assert not (tmp_path / "out").exists()


@pytest.mark.parametrize("script", SCRIPTS)
def test_the_default_without_a_deadline_is_not_refused(tmp_path, script):
    """Control: ``ANALYSIS_TIMEOUT=0`` alone still runs (with a warning, no stage)."""

    env = _script_env(tmp_path, ANALYSIS_TIMEOUT="0", PAIR_PROCESS_TIMEOUT="60s")
    completed = subprocess.run(
        ["bash", str(REPO_ROOT / script)], cwd=REPO_ROOT, env=env,
        capture_output=True, text=True, timeout=180,
    )

    assert "needs the analysis deadline" not in completed.stderr, completed.stderr
    assert "EQBENCH_CONCRETE_STAGES must be" not in completed.stderr, completed.stderr


def test_the_eval_profiles_differ_only_in_the_concrete_stages():
    def rows(name):
        lines = (REPO_ROOT / "eval" / name).read_text(encoding="utf-8").splitlines()
        return dict(line.split("=", 1) for line in lines if line and not line.startswith("#"))

    on, off = rows("profile.env"), rows("profile.concrete-off.env")

    assert on["EQBENCH_CONCRETE_STAGES"] == "witness_replay"
    assert off["EQBENCH_CONCRETE_STAGES"] == "none"
    assert {k: v for k, v in on.items() if k != "EQBENCH_CONCRETE_STAGES"} == {
        k: v for k, v in off.items() if k != "EQBENCH_CONCRETE_STAGES"
    }


def test_the_setting_record_reaches_the_serialized_result():
    """記録は結果 JSON の ``diagnostics`` に出る（固定の形の view が落とさない）。

    `result.diagnostics` に付けただけでは足りない: 結果 JSON は
    `result_diagnostics_payload` の固定の形の view から作られる。
    """
    from scripts.function_tracer_pcode.checker.diagnostics import result_diagnostics_payload
    from scripts.function_tracer_pcode.cli.args import build_parser
    from scripts.function_tracer_pcode.cli.commands.equivalence import (
        _attach_concrete_execution_setting,
    )

    args = build_parser().parse_args(["--equiv", "a", "b", "-f", "f", "--analysis-timeout", "410"])
    result = type("_R", (), {})()
    result.diagnostics = {}
    _attach_concrete_execution_setting(result, args)
    payload = result_diagnostics_payload(result)
    assert payload["concrete_execution_setting"] == result.diagnostics["concrete_execution_setting"]
    assert payload["concrete_execution_setting"]["effective_stages"] == ["witness_replay"]
    lazy = dict(result_diagnostics_payload(result, lazy=True).json_items())
    assert "concrete_execution_setting" in lazy
    # 記録の無い結果では key を出さない（CLI を経ない結果 JSON の形は変えない）
    bare = type("_R", (), {})()
    bare.diagnostics = {}
    assert "concrete_execution_setting" not in result_diagnostics_payload(bare)
