"""scripts.eqbench.ci_subset (Issue #109 PR-109-C: the real-binary subset CI).

The workflow's verdict lives in this module, so the rules it encodes are
checked here against synthetic run trees: scope awareness (an ``eq`` run must
not be asked for ``neq`` evidence, and a half the scope *does* ask for must not
go missing unnoticed), the separation of the shared soundness gate from the
per-half benchmark validation gate, and the propagation of the settings the
workflow normalised.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts.eqbench import ci_subset


WORKING_ROOT = "/workspace/tmp/eqbench-work/benchmarks"
TIMEOUT = "240s"
FAST_PATH = "1"


def _run_manifest_text(half: str, **overrides: str) -> str:
    values = {
        ci_subset.ROOT_KEY_BY_HALF[half]: WORKING_ROOT,
        "pair_process_timeout": TIMEOUT,
        "identical_fast_path": FAST_PATH,
        "analysis_config_schema": ci_subset.DEFAULT_ANALYSIS_CONFIG_SCHEMA,
        "benchmark_gate_status": "PASS",
    }
    values.update(overrides)
    return "".join(f"{key}={value}\n" for key, value in values.items())


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _binary_manifest_text(rows: int = 2) -> str:
    lines = [ci_subset.BINARY_MANIFEST_HEADER, "sample_identity\tbinary_id\tpath\tsha256"]
    for index in range(rows):
        lines.append(f"s/{index}\tB{index}\ttmp/eqbench-work/benchmarks/b{index}\t" + "0" * 64)
    return "\n".join(lines) + "\n"


def make_run(tmp_path: Path, scope: str, **kwargs: object) -> Path:
    """A run tree that passes every check, for the halves ``scope`` asks for."""

    run_dir = tmp_path / "ci_subset"
    halves = ci_subset.halves_for_scope(scope)
    _write(
        run_dir / ci_subset.SUBSET_MANIFEST_FILE,
        f"scope={scope}\nexit_status=0\nparallel_jobs=2\nissue=109\npr=none\n",
    )
    _write(
        run_dir / ci_subset.SOUNDNESS_GATE_JSON,
        json.dumps(
            {
                "schema": kwargs.get("soundness_schema", ci_subset.SOUNDNESS_GATE_SCHEMA),
                "passed": kwargs.get("soundness_passed", True),
                "pairs": 144,
            }
        ),
    )
    _write(run_dir / ci_subset.SOUNDNESS_GATE_TEXT, "GATE: PASS\n")
    for half in halves:
        _write(run_dir / half / ci_subset.RUN_MANIFEST_FILE, _run_manifest_text(half))
        _write(
            run_dir / half / ci_subset.BENCHMARK_GATE_JSON,
            json.dumps({"gate": "PASS", "pairs": 64}),
        )
        _write(run_dir / half / ci_subset.BENCHMARK_GATE_TEXT, "GATE: PASS\n")
        _write(run_dir / half / "function_diff_manifest.json", "{}\n")
        _write(run_dir / half / "overall_summary.txt", "summary\n")
        _write(run_dir / half / "run_health_summary.json", "{}\n")
        _write(run_dir / half / "run_health_summary.txt", "health\n")
        _write(run_dir / f"{half}.log", "console\n")
        _write(run_dir / f"binary_manifest_{half}.txt", _binary_manifest_text())
    return run_dir


def run_verify(run_dir: Path, scope: str, **kwargs: object) -> ci_subset.Report:
    params = {
        "working_root": WORKING_ROOT,
        "pair_process_timeout": TIMEOUT,
        "identical_fast_path": FAST_PATH,
        "runner_exit_status": 0,
    }
    params.update(kwargs)
    return ci_subset.verify(run_dir=run_dir, scope=scope, **params)  # type: ignore[arg-type]


def failed_checks(report: ci_subset.Report) -> list:
    return [check.name for check in report.checks if not check.passed]


# --------------------------------------------------------------------------
# scope awareness
# --------------------------------------------------------------------------


@pytest.mark.parametrize("scope", ["eq", "neq", "all"])
def test_a_complete_run_passes_for_every_scope(tmp_path, scope):
    report = run_verify(make_run(tmp_path, scope), scope)
    assert report.passed, failed_checks(report)
    assert report.halves == ci_subset.HALVES_BY_SCOPE[scope]


@pytest.mark.parametrize("scope,absent", [("eq", "neq"), ("neq", "eq")])
def test_the_other_half_is_not_required(tmp_path, scope, absent):
    """A single-half run has no evidence for the other half, and needs none."""

    run_dir = make_run(tmp_path, scope)
    assert not (run_dir / absent).exists()
    report = run_verify(run_dir, scope)
    assert report.passed, failed_checks(report)
    # Nothing in the report may even mention the other half's root key.
    assert ci_subset.ROOT_KEY_BY_HALF[absent] not in report.as_text()
    assert absent not in report.as_dict()["root_key_by_half"]


@pytest.mark.parametrize("scope,missing", [("all", "neq"), ("all", "eq"), ("eq", "eq")])
def test_a_half_the_scope_asks_for_must_not_be_missing(tmp_path, scope, missing):
    import shutil

    run_dir = make_run(tmp_path, scope)
    shutil.rmtree(run_dir / missing)
    report = run_verify(run_dir, scope)
    assert not report.passed
    assert f"scope.{missing}.half_present" in failed_checks(report)


def test_an_out_of_scope_half_that_exists_anyway_fails(tmp_path):
    """The workflow runs into a fresh directory, so a stray half is not ours."""

    run_dir = make_run(tmp_path, "eq")
    _write(run_dir / "neq" / ci_subset.RUN_MANIFEST_FILE, _run_manifest_text("neq"))
    report = run_verify(run_dir, "eq")
    assert not report.passed
    assert "scope.neq.half_absent" in failed_checks(report)


def test_the_recorded_scope_must_match_the_requested_one(tmp_path):
    run_dir = make_run(tmp_path, "eq")
    _write(
        run_dir / ci_subset.SUBSET_MANIFEST_FILE, "scope=all\nexit_status=0\npr=none\n",
    )
    report = run_verify(run_dir, "eq")
    assert not report.passed
    assert "run.scope" in failed_checks(report)


def test_an_unknown_scope_is_an_error():
    with pytest.raises(ci_subset.SubsetCiError):
        ci_subset.halves_for_scope("both")


# --------------------------------------------------------------------------
# root keys: each half is verified through its own
# --------------------------------------------------------------------------


@pytest.mark.parametrize("half", ["eq", "neq"])
def test_each_half_is_verified_through_its_own_root_key(tmp_path, half):
    run_dir = make_run(tmp_path, half)
    _write(
        run_dir / half / ci_subset.RUN_MANIFEST_FILE,
        _run_manifest_text(half, **{ci_subset.ROOT_KEY_BY_HALF[half]: "/elsewhere"}),
    )
    report = run_verify(run_dir, half)
    assert not report.passed
    assert f"env.{half}.working_root" in failed_checks(report)
    check = next(c for c in report.checks if c.name == f"env.{half}.working_root")
    assert ci_subset.ROOT_KEY_BY_HALF[half] in check.detail


def test_the_eq_half_is_not_checked_against_the_neq_root_key(tmp_path):
    """An ``eq`` half carrying only ``eqbench_root`` is complete, not partial."""

    run_dir = make_run(tmp_path, "eq")
    manifest = (run_dir / "eq" / ci_subset.RUN_MANIFEST_FILE).read_text(encoding="utf-8")
    assert "neq_root=" not in manifest
    assert run_verify(run_dir, "eq").passed


# --------------------------------------------------------------------------
# env propagation
# --------------------------------------------------------------------------


@pytest.mark.parametrize(
    "key,name",
    [
        ("pair_process_timeout", "pair_process_timeout"),
        ("identical_fast_path", "identical_fast_path"),
        ("analysis_config_schema", "analysis_config_schema"),
    ],
)
def test_a_setting_that_did_not_reach_the_child_runner_fails(tmp_path, key, name):
    run_dir = make_run(tmp_path, "all")
    _write(
        run_dir / "eq" / ci_subset.RUN_MANIFEST_FILE,
        _run_manifest_text("eq", **{key: "something-else"}),
    )
    report = run_verify(run_dir, "all")
    assert not report.passed
    assert f"env.eq.{name}" in failed_checks(report)


def test_identical_fast_path_off_is_a_value_not_an_absence(tmp_path):
    """``0`` is a setting that must arrive as ``0``, never fall back to ``1``."""

    run_dir = make_run(tmp_path, "all")
    for half in ("eq", "neq"):
        _write(
            run_dir / half / ci_subset.RUN_MANIFEST_FILE,
            _run_manifest_text(half, identical_fast_path="0"),
        )
    assert run_verify(run_dir, "all", identical_fast_path="0").passed
    off_expected = run_verify(run_dir, "all", identical_fast_path="1")
    assert not off_expected.passed
    assert "env.eq.identical_fast_path" in failed_checks(off_expected)


def test_a_missing_run_manifest_key_fails_rather_than_being_skipped(tmp_path):
    run_dir = make_run(tmp_path, "eq")
    _write(run_dir / "eq" / ci_subset.RUN_MANIFEST_FILE, "pair_process_timeout=240s\n")
    report = run_verify(run_dir, "eq")
    assert not report.passed
    assert "env.eq.working_root" in failed_checks(report)


def _dry_run_sources_text(half: str, root: str = WORKING_ROOT, count: int = 2) -> str:
    return "".join(
        f"s/{index}/{half}\t{root}/s/{index}/newV.c\t{root}/s/{index}/oldV.c\n"
        for index in range(count)
    )


def make_dry_run(tmp_path: Path, scope: str, with_manifest=("eq", "neq")) -> Path:
    """What a ``DRY_RUN=1`` pass leaves behind: a census, maybe a manifest."""

    run_dir = tmp_path / "dryrun"
    # No `pr` field at all: a dry run records no measurement to attribute, and
    # the propagation profile must not ask for one.
    _write(run_dir / ci_subset.SUBSET_MANIFEST_FILE, f"scope={scope}\nexit_status=0\n")
    for half in ci_subset.halves_for_scope(scope):
        _write(run_dir / half / ci_subset.DRY_RUN_SOURCES_FILE, _dry_run_sources_text(half))
        if half in with_manifest:
            _write(run_dir / half / ci_subset.RUN_MANIFEST_FILE, _run_manifest_text(half))
    return run_dir


def test_the_propagation_profile_needs_no_gates_or_binaries(tmp_path):
    """After ``DRY_RUN=1`` there are run manifests but no pairs and no gates."""

    run_dir = make_dry_run(tmp_path, "all")
    report = run_verify(run_dir, "all", profile=ci_subset.PROFILE_PROPAGATION)
    assert report.passed, failed_checks(report)
    gates = report.as_dict()["gates"]
    assert ci_subset.GATE_SHARED_SOUNDNESS not in gates
    assert ci_subset.GATE_BENCHMARK_VALIDATION not in gates
    assert ci_subset.GATE_ARTIFACTS not in gates
    # ... while the full profile on the same tree fails, because it is not one.
    assert not run_verify(run_dir, "all").passed


def test_the_dry_run_census_proves_which_tree_the_half_walked(tmp_path):
    """The census carries absolute source paths, so the root is observable."""

    run_dir = make_dry_run(tmp_path, "all")
    _write(
        run_dir / "neq" / ci_subset.DRY_RUN_SOURCES_FILE,
        _dry_run_sources_text("neq", root="/workspace/targets/EqBench/benchmarks"),
    )
    report = run_verify(run_dir, "all", profile=ci_subset.PROFILE_PROPAGATION)
    assert not report.passed
    assert "env.neq.dry_run_sources" in failed_checks(report)


def test_a_half_that_selected_nothing_fails_the_dry_run(tmp_path):
    run_dir = make_dry_run(tmp_path, "eq")
    _write(run_dir / "eq" / ci_subset.DRY_RUN_SOURCES_FILE, "")
    report = run_verify(run_dir, "eq", profile=ci_subset.PROFILE_PROPAGATION)
    assert not report.passed
    assert "env.eq.dry_run_sources" in failed_checks(report)


def test_the_neq_half_may_have_no_dry_run_manifest_but_the_eq_half_may_not(tmp_path):
    """The two runners differ in dry-run mode; only the known gap is allowed."""

    assert ci_subset.DRY_RUN_MANIFEST_OPTIONAL == ("neq",)
    neq_only = make_dry_run(tmp_path / "a", "all", with_manifest=("eq",))
    report = run_verify(neq_only, "all", profile=ci_subset.PROFILE_PROPAGATION)
    assert report.passed, failed_checks(report)

    eq_missing = make_dry_run(tmp_path / "b", "all", with_manifest=("neq",))
    report = run_verify(eq_missing, "all", profile=ci_subset.PROFILE_PROPAGATION)
    assert not report.passed
    assert "env.eq.run_manifest" in failed_checks(report)


def test_a_dry_run_manifest_that_is_there_is_always_checked(tmp_path):
    """The allowance is for an absent manifest, never for a wrong one."""

    run_dir = make_dry_run(tmp_path, "neq")
    _write(
        run_dir / "neq" / ci_subset.RUN_MANIFEST_FILE,
        _run_manifest_text("neq", pair_process_timeout="600s"),
    )
    report = run_verify(run_dir, "neq", profile=ci_subset.PROFILE_PROPAGATION)
    assert not report.passed
    assert "env.neq.pair_process_timeout" in failed_checks(report)


def test_the_full_profile_never_allows_a_missing_run_manifest(tmp_path):
    run_dir = make_run(tmp_path, "all")
    (run_dir / "neq" / ci_subset.RUN_MANIFEST_FILE).unlink()
    report = run_verify(run_dir, "all")
    assert not report.passed
    assert "env.neq.run_manifest" in failed_checks(report)


# --------------------------------------------------------------------------
# the two gates are different contracts
# --------------------------------------------------------------------------


def test_the_shared_soundness_gate_is_read_only_from_its_own_file(tmp_path):
    run_dir = make_run(tmp_path, "all")
    soundness = [c for c in run_verify(run_dir, "all").checks
                 if c.gate == ci_subset.GATE_SHARED_SOUNDNESS]
    assert soundness
    assert {check.source for check in soundness} == {ci_subset.SOUNDNESS_GATE_JSON}


def test_the_benchmark_gate_is_read_only_from_per_half_files(tmp_path):
    run_dir = make_run(tmp_path, "all")
    benchmark = [c for c in run_verify(run_dir, "all").checks
                 if c.gate == ci_subset.GATE_BENCHMARK_VALIDATION]
    assert benchmark
    sources = {check.source for check in benchmark}
    assert sources == {
        f"{half}/{name}"
        for half in ("eq", "neq")
        for name in (ci_subset.RUN_MANIFEST_FILE, ci_subset.BENCHMARK_GATE_JSON)
    }
    assert ci_subset.SOUNDNESS_GATE_JSON not in sources


def test_a_failing_soundness_gate_is_not_covered_by_passing_benchmark_gates(tmp_path):
    run_dir = make_run(tmp_path, "all", soundness_passed=False)
    report = run_verify(run_dir, "all")
    assert not report.passed
    gates = report.as_dict()["gates"]
    assert gates[ci_subset.GATE_SHARED_SOUNDNESS]["passed"] is False
    assert gates[ci_subset.GATE_BENCHMARK_VALIDATION]["passed"] is True
    assert "soundness.passed" in failed_checks(report)


def test_a_failing_benchmark_gate_is_not_covered_by_a_passing_soundness_gate(tmp_path):
    run_dir = make_run(tmp_path, "all")
    _write(
        run_dir / "neq" / ci_subset.RUN_MANIFEST_FILE,
        _run_manifest_text("neq", benchmark_gate_status="FAIL"),
    )
    _write(
        run_dir / "neq" / ci_subset.BENCHMARK_GATE_JSON,
        json.dumps({"gate": "FAIL", "pairs": 80}),
    )
    report = run_verify(run_dir, "all")
    assert not report.passed
    gates = report.as_dict()["gates"]
    assert gates[ci_subset.GATE_SHARED_SOUNDNESS]["passed"] is True
    assert gates[ci_subset.GATE_BENCHMARK_VALIDATION]["passed"] is False
    assert failed_checks(report) == [
        "benchmark.neq.recorded_status", "benchmark.neq.report",
    ]


def test_the_soundness_gate_must_carry_the_v2_schema(tmp_path):
    run_dir = make_run(tmp_path, "all", soundness_schema="soundness-gate-v1")
    report = run_verify(run_dir, "all")
    assert not report.passed
    assert "soundness.schema" in failed_checks(report)


def test_a_truthy_passed_value_is_not_a_pass(tmp_path):
    run_dir = make_run(tmp_path, "all", soundness_passed="true")
    report = run_verify(run_dir, "all")
    assert not report.passed
    assert "soundness.passed" in failed_checks(report)


def test_a_missing_soundness_gate_fails_rather_than_being_skipped(tmp_path):
    run_dir = make_run(tmp_path, "all")
    (run_dir / ci_subset.SOUNDNESS_GATE_JSON).unlink()
    report = run_verify(run_dir, "all")
    assert not report.passed
    assert "soundness.report" in failed_checks(report)


# --------------------------------------------------------------------------
# run status and artifacts
# --------------------------------------------------------------------------


def test_the_runner_exit_status_is_a_success_condition(tmp_path):
    run_dir = make_run(tmp_path, "all")
    report = run_verify(run_dir, "all", runner_exit_status=1)
    assert not report.passed
    assert "run.runner_exit_status" in failed_checks(report)


def test_the_recorded_exit_status_is_a_success_condition(tmp_path):
    run_dir = make_run(tmp_path, "all")
    _write(
        run_dir / ci_subset.SUBSET_MANIFEST_FILE, "scope=all\nexit_status=2\npr=none\n",
    )
    report = run_verify(run_dir, "all")
    assert not report.passed
    assert "run.exit_status" in failed_checks(report)


def test_a_missing_run_directory_fails(tmp_path):
    report = run_verify(tmp_path / "nothing-here", "all")
    assert not report.passed
    assert failed_checks(report) == ["run.directory"]


@pytest.mark.parametrize(
    "name", ["soundness_gate.txt", "eq/overall_summary.txt", "binary_manifest_neq.txt"],
)
def test_a_required_artifact_must_be_present_and_non_empty(tmp_path, name):
    run_dir = make_run(tmp_path, "all")
    (run_dir / name).write_text("", encoding="utf-8")
    report = run_verify(run_dir, "all")
    assert not report.passed
    assert f"artifact.{name}" in failed_checks(report)


def test_the_required_artifacts_follow_the_scope(tmp_path):
    eq_only = ci_subset.required_artifacts(("eq",))
    assert "binary_manifest_eq.txt" in eq_only
    assert not [name for name in eq_only if name.startswith("neq")]
    assert "binary_manifest_neq.txt" in ci_subset.required_artifacts(("eq", "neq"))


def test_an_empty_binary_manifest_is_not_a_binary_manifest(tmp_path):
    """A manifest built before the run would have a header and no binaries."""

    run_dir = make_run(tmp_path, "eq")
    _write(
        run_dir / "binary_manifest_eq.txt",
        ci_subset.BINARY_MANIFEST_HEADER + "\nsample_identity\tbinary_id\tpath\tsha256\n",
    )
    report = run_verify(run_dir, "eq")
    assert not report.passed
    assert "binary_manifest.eq" in failed_checks(report)


def test_a_binary_manifest_with_the_wrong_header_fails(tmp_path):
    run_dir = make_run(tmp_path, "eq")
    _write(run_dir / "binary_manifest_eq.txt", "sample\tid\tpath\tsha\nrow\n")
    report = run_verify(run_dir, "eq")
    assert not report.passed
    assert "binary_manifest.eq" in failed_checks(report)


# --------------------------------------------------------------------------
# report shape
# --------------------------------------------------------------------------


def test_the_report_names_the_file_behind_every_check(tmp_path):
    report = run_verify(make_run(tmp_path, "all"), "all")
    for check in report.checks:
        assert check.source, check.name
        assert check.gate in ci_subset.GATE_ORDER


def test_the_json_report_is_serialisable_and_carries_the_verdict(tmp_path):
    report = run_verify(make_run(tmp_path, "all"), "all")
    payload = json.loads(json.dumps(report.as_dict()))
    assert payload["schema"] == ci_subset.VERIFICATION_SCHEMA
    assert payload["passed"] is True
    assert payload["scope"] == "all"
    assert payload["root_key_by_half"] == {"eq": "eqbench_root", "neq": "neq_root"}
    assert payload["expected"]["working_root"] == WORKING_ROOT


# --------------------------------------------------------------------------
# collect
# --------------------------------------------------------------------------


def _add_pair(run_dir: Path, half: str, sample: str, function: str, pair: str,
              outcome: str) -> Path:
    directory = run_dir / half / sample / function
    _write(
        directory / f"{function}_{pair}{ci_subset.PAIR_STATUS_SUFFIX}",
        json.dumps({"canonical_outcome": outcome}),
    )
    log = directory / f"{function}_{pair}.log"
    _write(log, f"{outcome} log\n")
    return log


def test_collect_keeps_the_evidence_but_not_every_pair_log(tmp_path):
    run_dir = make_run(tmp_path, "eq")
    _add_pair(run_dir, "eq", "s/a/Eq/new", "f", "B1_B2", "EQUIVALENT")
    _add_pair(run_dir, "eq", "s/a/Eq/new", "f", "B3_B11", "TIMEOUT")
    dest = tmp_path / "artifacts"
    summary = ci_subset.collect(run_dir, dest, "eq")

    assert (dest / ci_subset.SUBSET_MANIFEST_FILE).is_file()
    assert (dest / "eq" / ci_subset.RUN_MANIFEST_FILE).is_file()
    assert (dest / "eq.log").is_file()          # the half's console output
    assert (dest / "eq/s/a/Eq/new/f/f_B3_B11.log").is_file()   # TIMEOUT: kept
    assert not (dest / "eq/s/a/Eq/new/f/f_B1_B2.log").exists()  # ordinary: not
    assert summary["pair_logs_kept"] == ["eq/s/a/Eq/new/f/f_B3_B11.log"]
    assert summary["pair_logs_skipped"] == 2


def test_collect_keeps_the_logs_of_gate_violations(tmp_path):
    run_dir = make_run(tmp_path, "eq")
    _add_pair(run_dir, "eq", "s/a/Eq/new", "f", "B1_B2", "NOT_EQ")
    _write(
        run_dir / ci_subset.SOUNDNESS_GATE_JSON,
        json.dumps(
            {
                "schema": ci_subset.SOUNDNESS_GATE_SCHEMA,
                "passed": False,
                "verified_ground_truth": {
                    "unconditional_violations": [
                        {
                            "scope": "/workspace/logs/EqBench/ci_subset/eq",
                            "sample_identity": "s/a/Eq/new",
                            "function_name": "f",
                            "pair_id": "B1_B2",
                        }
                    ],
                },
            }
        ),
    )
    summary = ci_subset.collect(run_dir, tmp_path / "artifacts", "eq")
    assert summary["pair_logs_kept"] == ["eq/s/a/Eq/new/f/f_B1_B2.log"]


def test_collect_respects_the_pair_log_cap(tmp_path):
    run_dir = make_run(tmp_path, "eq")
    for index in range(5):
        _add_pair(run_dir, "eq", "s/a/Eq/new", "f", f"B{index}_B9", "ERROR")
    summary = ci_subset.collect(run_dir, tmp_path / "artifacts", "eq", max_pair_logs=2)
    assert len(summary["pair_logs_kept"]) == 2


def test_collect_only_walks_the_halves_in_scope(tmp_path):
    run_dir = make_run(tmp_path, "eq")
    _add_pair(run_dir, "eq", "s/a/Eq/new", "f", "B1_B2", "ERROR")
    summary = ci_subset.collect(run_dir, tmp_path / "artifacts", "eq")
    assert summary["halves"] == ["eq"]
    assert summary["pair_logs_kept"] == ["eq/s/a/Eq/new/f/f_B1_B2.log"]


def test_collect_on_a_missing_run_directory_is_an_error(tmp_path):
    with pytest.raises(ci_subset.SubsetCiError):
        ci_subset.collect(tmp_path / "nope", tmp_path / "dest", "all")


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


def test_cli_verify_writes_both_reports_and_returns_the_verdict(tmp_path, capsys):
    run_dir = make_run(tmp_path, "all")
    json_path = tmp_path / "out" / "verification.json"
    text_path = tmp_path / "out" / "verification.txt"
    code = ci_subset.main(
        [
            "verify", "--run-dir", str(run_dir), "--scope", "all",
            "--working-root", WORKING_ROOT,
            "--pair-process-timeout", TIMEOUT,
            "--identical-fast-path", FAST_PATH,
            "--runner-exit-status", "0",
            "--json", str(json_path), "--text", str(text_path),
        ]
    )
    assert code == ci_subset.EXIT_OK
    assert json.loads(json_path.read_text(encoding="utf-8"))["passed"] is True
    assert "VERIFICATION: PASS" in text_path.read_text(encoding="utf-8")
    assert "VERIFICATION: PASS" in capsys.readouterr().out


def test_cli_verify_fails_the_step_when_a_gate_did_not_pass(tmp_path, capsys):
    run_dir = make_run(tmp_path, "all", soundness_passed=False)
    code = ci_subset.main(
        [
            "verify", "--run-dir", str(run_dir), "--scope", "all",
            "--working-root", WORKING_ROOT,
            "--pair-process-timeout", TIMEOUT,
            "--identical-fast-path", FAST_PATH,
            "--runner-exit-status", "0",
        ]
    )
    assert code == ci_subset.EXIT_FAIL
    assert "VERIFICATION: FAIL" in capsys.readouterr().out


def test_cli_collect_reports_what_it_kept(tmp_path, capsys):
    run_dir = make_run(tmp_path, "eq")
    _add_pair(run_dir, "eq", "s/a/Eq/new", "f", "B1_B2", "ERROR")
    json_path = tmp_path / "collect.json"
    code = ci_subset.main(
        [
            "collect", "--run-dir", str(run_dir), "--dest", str(tmp_path / "art"),
            "--scope", "eq", "--json", str(json_path),
        ]
    )
    assert code == ci_subset.EXIT_OK
    assert json.loads(json_path.read_text(encoding="utf-8"))["pair_logs_kept"] == [
        "eq/s/a/Eq/new/f/f_B1_B2.log"
    ]
    assert "collected" in capsys.readouterr().out


# --------------------------------------------------------------------------
# provenance: a CI run identifier is not a PR number
# --------------------------------------------------------------------------


def test_a_ci_run_id_in_the_pr_field_is_a_provenance_failure(tmp_path):
    """``SUBSET_PR`` says which PR a measurement belongs to, nothing else."""

    run_dir = make_run(tmp_path, "all")
    _write(
        run_dir / ci_subset.SUBSET_MANIFEST_FILE,
        "scope=all\nexit_status=0\nissue=109\npr=17284455301\n",
    )
    report = run_verify(run_dir, "all")
    assert not report.passed
    assert "run.subset_pr" in failed_checks(report)


def test_the_pr_field_must_be_recorded_as_unset(tmp_path):
    run_dir = make_run(tmp_path, "all")
    _write(
        run_dir / ci_subset.SUBSET_MANIFEST_FILE,
        "scope=all\nexit_status=0\nissue=109\n",
    )
    report = run_verify(run_dir, "all")
    assert not report.passed
    assert "run.subset_pr" in failed_checks(report)


def test_the_propagation_profile_does_not_ask_for_a_pr_field(tmp_path):
    run_dir = make_dry_run(tmp_path, "eq")
    report = run_verify(run_dir, "eq", profile=ci_subset.PROFILE_PROPAGATION)
    assert report.passed, failed_checks(report)
    assert "run.subset_pr" not in [check.name for check in report.checks]


def test_the_full_profile_requires_the_runner_exit_status_to_be_supplied(tmp_path):
    """Omitting it must not turn a success condition into a skipped check."""

    run_dir = make_run(tmp_path, "all")
    report = ci_subset.verify(
        run_dir=run_dir, scope="all", working_root=WORKING_ROOT,
        pair_process_timeout=TIMEOUT, identical_fast_path=FAST_PATH,
    )
    assert not report.passed
    assert "run.runner_exit_status" in failed_checks(report)
