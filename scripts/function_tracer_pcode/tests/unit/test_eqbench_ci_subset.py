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
ANALYSIS_TIMEOUT = "120"
ANALYSIS_TIMEOUT_MARGIN = "100"

#: A miniature stand-in for scripts/function_tracer_pcode/reporting/
#: eqbench_subset.json: two sources and two pair ids per half, so the expected
#: pair set is small but derived the same way the real one is -- from the
#: definition, never from a number written into the test.
DEFINITION = {
    "schema": ci_subset.SUBSET_DEFINITION_SCHEMA,
    "eq": {
        "sources": ["fam/a/Eq/new", "fam/b/Eq/newV"],
        "pair_ids": ["B1_B2", "B3_B11"],
    },
    "neq": {
        "sources": ["fam/a/Neq/new-old", "fam/c/Neq/newV-oldV"],
        "pair_ids": ["N_B1_O_B1", "N_B2_O_B4"],
    },
}
FUNCTION = "fn"


def _run_manifest_text(half: str, **overrides: str) -> str:
    values = {
        ci_subset.ROOT_KEY_BY_HALF[half]: WORKING_ROOT,
        "pair_process_timeout": TIMEOUT,
        "identical_fast_path": FAST_PATH,
        "analysis_timeout": ANALYSIS_TIMEOUT,
        "analysis_timeout_margin": ANALYSIS_TIMEOUT_MARGIN,
        "analysis_config_schema": ci_subset.DEFAULT_ANALYSIS_CONFIG_SCHEMA,
        "benchmark_gate_status": "PASS",
    }
    values.update(overrides)
    return "".join(f"{key}={value}\n" for key, value in values.items())


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _binary_manifest_text(half: str = "eq") -> str:
    """A binary manifest naming exactly the half's samples, as a real one does."""

    lines = [ci_subset.BINARY_MANIFEST_HEADER, "sample_identity\tbinary_id\tpath\tsha256"]
    for index, source in enumerate(DEFINITION[half]["sources"]):
        lines.append(
            f"{source}\tB{index + 1}\ttmp/eqbench-work/benchmarks/{source}/b\t" + "0" * 64
        )
    return "\n".join(lines) + "\n"


def write_definition(tmp_path: Path, payload=None, name="eqbench_subset.json") -> Path:
    path = tmp_path / name
    _write(path, json.dumps(DEFINITION if payload is None else payload))
    return path


def expected_pair_paths(half: str) -> list:
    """The pair-status paths the definition implies, laid out as the runners do."""

    return [
        f"{source}/{FUNCTION}/{FUNCTION}_{pair_id}{ci_subset.PAIR_STATUS_SUFFIX}"
        for source in DEFINITION[half]["sources"]
        for pair_id in DEFINITION[half]["pair_ids"]
    ]


def write_half_workload(
    run_dir: Path,
    half: str,
    outcomes=None,
    expected_paths=None,
    written_paths=None,
    dry_run: int = 0,
    reused: list = (),
    skipped_jobs: int = 0,
    run_pair_failures: int = 0,
    schema: str = None,
) -> None:
    """A half's publication manifest plus the pair statuses it expected.

    ``outcomes`` maps a pair path to its canonical outcome; anything not named
    gets ``UNKNOWN``, which is a result the analysis produced.
    """

    paths = list(expected_pair_paths(half) if expected_paths is None else expected_paths)
    _write(
        run_dir / half / ci_subset.PUBLICATION_MANIFEST_FILE,
        json.dumps(
            {
                "schema": ci_subset.PUBLICATION_MANIFEST_SCHEMA if schema is None else schema,
                "dry_run": dry_run,
                "expected_pair_status_paths": paths,
                "verified_skipped_pair_status_paths": list(reused),
                "total_skipped_pair_jobs": skipped_jobs,
                "run_pair_failures": run_pair_failures,
            }
        ),
    )
    outcomes = dict(outcomes or {})
    for relative in (paths if written_paths is None else written_paths):
        outcome = outcomes.get(relative, outcomes.get("*", "UNKNOWN"))
        payload = {"canonical_outcome": outcome} if outcome is not None else {}
        _write(run_dir / half / relative, json.dumps(payload))


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
        _write(run_dir / f"binary_manifest_{half}.txt", _binary_manifest_text(half))
        write_half_workload(run_dir, half)
    return run_dir


def run_verify(run_dir: Path, scope: str, **kwargs: object) -> ci_subset.Report:
    params = {
        "working_root": WORKING_ROOT,
        "pair_process_timeout": TIMEOUT,
        "identical_fast_path": FAST_PATH,
        "analysis_timeout": ANALYSIS_TIMEOUT,
        "analysis_timeout_margin": ANALYSIS_TIMEOUT_MARGIN,
        "runner_exit_status": 0,
        "subset_definition": write_definition(run_dir.parent),
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
        ("analysis_timeout", "analysis_timeout"),
        ("analysis_timeout_margin", "analysis_timeout_margin"),
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


def test_analysis_timeout_off_is_a_value_not_an_absence(tmp_path):
    """Issue #106 PR-106-B: ``0`` (no deadline) must arrive as ``0``.

    A half that recorded no ``analysis_timeout`` at all -- a runner from before
    the deadline was wired -- is a failure, never read as "off".
    """

    run_dir = make_run(tmp_path, "all")
    for half in ("eq", "neq"):
        _write(
            run_dir / half / ci_subset.RUN_MANIFEST_FILE,
            _run_manifest_text(half, analysis_timeout="0"),
        )
    assert run_verify(run_dir, "all", analysis_timeout="0").passed
    on_expected = run_verify(run_dir, "all", analysis_timeout=ANALYSIS_TIMEOUT)
    assert "env.eq.analysis_timeout" in failed_checks(on_expected)

    text = _run_manifest_text("neq")
    _write(
        run_dir / "neq" / ci_subset.RUN_MANIFEST_FILE,
        "".join(line + "\n" for line in text.splitlines()
                if not line.startswith("analysis_timeout=")),
    )
    missing = run_verify(run_dir, "all", analysis_timeout="0")
    assert "env.neq.analysis_timeout" in failed_checks(missing)


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
            "--analysis-timeout", ANALYSIS_TIMEOUT,
            "--analysis-timeout-margin", ANALYSIS_TIMEOUT_MARGIN,
            "--runner-exit-status", "0",
            "--subset-definition", str(write_definition(tmp_path)),
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
            "--analysis-timeout", ANALYSIS_TIMEOUT,
            "--analysis-timeout-margin", ANALYSIS_TIMEOUT_MARGIN,
            "--runner-exit-status", "0",
            "--subset-definition", str(write_definition(tmp_path)),
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
        analysis_timeout=ANALYSIS_TIMEOUT, analysis_timeout_margin=ANALYSIS_TIMEOUT_MARGIN,
    )
    assert not report.passed
    assert "run.runner_exit_status" in failed_checks(report)


# --------------------------------------------------------------------------
# workload completeness and non-vacuity
#
# The two gates are about the pairs that were judged, so on their own they are
# content with a run that judged nothing: every pair killed at its deadline is
# a passing soundness gate, passing benchmark gates and exit_status=0. These
# are the checks that make such a run fail.
# --------------------------------------------------------------------------


def test_a_run_that_decided_something_passes(tmp_path):
    report = run_verify(make_run(tmp_path, "all"), "all")
    assert report.passed, failed_checks(report)
    decided = next(c for c in report.checks if c.name == "workload.eq.semantic_outcomes")
    assert "4 of 4" in decided.detail


@pytest.mark.parametrize("outcome", ["TIMEOUT", "ERROR"])
@pytest.mark.parametrize("scope", ["eq", "neq", "all"])
def test_a_run_where_no_pair_produced_a_result_fails(tmp_path, outcome, scope):
    """This is the `pair_process_timeout=1s` shape: nothing was decided."""

    run_dir = make_run(tmp_path, scope)
    for half in ci_subset.halves_for_scope(scope):
        write_half_workload(run_dir, half, outcomes={"*": outcome})
    report = run_verify(run_dir, scope)
    assert not report.passed
    for half in ci_subset.halves_for_scope(scope):
        assert f"workload.{half}.semantic_outcomes" in failed_checks(report)
    # ... and nothing else complained: the gates are happy with such a run.
    assert [name for name in failed_checks(report)
            if not name.endswith(".semantic_outcomes")] == []


def test_a_mix_of_timeouts_and_results_passes(tmp_path):
    """A few TIMEOUT pairs are normal; one of them must not fail the run."""

    run_dir = make_run(tmp_path, "all")
    eq_paths = expected_pair_paths("eq")
    write_half_workload(run_dir, "eq", outcomes={eq_paths[0]: "TIMEOUT"})
    neq_paths = expected_pair_paths("neq")
    write_half_workload(
        run_dir, "neq",
        outcomes={neq_paths[0]: "TIMEOUT", neq_paths[1]: "ERROR", neq_paths[2]: "NOT_EQ"},
    )
    report = run_verify(run_dir, "all")
    assert report.passed, failed_checks(report)


@pytest.mark.parametrize("outcome", ["EQUIVALENT", "NOT_EQ", "UNKNOWN"])
def test_every_outcome_the_authority_calls_a_result_counts(tmp_path, outcome):
    """UNKNOWN is a result the analysis produced -- the dominant one here."""

    assert outcome in ci_subset.semantic_outcomes()
    run_dir = make_run(tmp_path, "eq")
    write_half_workload(run_dir, "eq", outcomes={"*": outcome})
    assert run_verify(run_dir, "eq").passed


@pytest.mark.parametrize("outcome", ["TIMEOUT", "ERROR"])
def test_the_non_decisive_outcomes_come_from_the_authority_table(outcome):
    assert outcome not in ci_subset.semantic_outcomes()


def test_a_missing_expected_pair_status_fails(tmp_path):
    run_dir = make_run(tmp_path, "all")
    (run_dir / "neq" / expected_pair_paths("neq")[0]).unlink()
    report = run_verify(run_dir, "all")
    assert not report.passed
    assert "workload.neq.pair_statuses" in failed_checks(report)
    check = next(c for c in report.checks if c.name == "workload.neq.pair_statuses")
    assert "1 missing" in check.detail


def test_a_pair_status_the_run_never_expected_fails(tmp_path):
    run_dir = make_run(tmp_path, "eq")
    _write(
        run_dir / "eq" / "fam/a/Eq/new" / FUNCTION / f"{FUNCTION}_B9_B10.pair-status.json",
        json.dumps({"canonical_outcome": "UNKNOWN"}),
    )
    report = run_verify(run_dir, "eq")
    assert not report.passed
    assert "workload.eq.pair_statuses" in failed_checks(report)


def test_a_pair_status_without_an_outcome_is_not_a_result(tmp_path):
    run_dir = make_run(tmp_path, "eq")
    write_half_workload(run_dir, "eq", outcomes={"*": None})
    report = run_verify(run_dir, "eq")
    assert not report.passed
    assert "workload.eq.readable_outcomes" in failed_checks(report)
    assert "workload.eq.semantic_outcomes" in failed_checks(report)


def test_reused_pair_statuses_are_not_this_run_executing_the_subset(tmp_path):
    run_dir = make_run(tmp_path, "eq")
    write_half_workload(
        run_dir, "eq", reused=[expected_pair_paths("eq")[0]], skipped_jobs=1,
    )
    report = run_verify(run_dir, "eq")
    assert not report.passed
    assert "workload.eq.executed_not_reused" in failed_checks(report)


def test_a_pair_the_harness_failed_to_run_fails(tmp_path):
    run_dir = make_run(tmp_path, "eq")
    write_half_workload(run_dir, "eq", run_pair_failures=2)
    report = run_verify(run_dir, "eq")
    assert not report.passed
    assert "workload.eq.run_pair_failures" in failed_checks(report)


def test_a_dry_run_tree_is_not_a_real_run(tmp_path):
    run_dir = make_run(tmp_path, "eq")
    write_half_workload(run_dir, "eq", dry_run=1)
    report = run_verify(run_dir, "eq")
    assert not report.passed
    assert "workload.eq.publication_manifest" in failed_checks(report)


@pytest.mark.parametrize(
    "mutate,expected",
    [
        (lambda p: p.unlink(), "publication_manifest"),
        (lambda p: p.write_text("{not json", encoding="utf-8"), "publication_manifest"),
        (lambda p: p.write_text("[]", encoding="utf-8"), "publication_manifest"),
    ],
)
def test_an_unusable_publication_manifest_fails_rather_than_being_skipped(
    tmp_path, mutate, expected,
):
    run_dir = make_run(tmp_path, "eq")
    mutate(run_dir / "eq" / ci_subset.PUBLICATION_MANIFEST_FILE)
    report = run_verify(run_dir, "eq")
    assert not report.passed
    assert f"workload.eq.{expected}" in failed_checks(report)


def test_a_publication_manifest_of_another_schema_fails(tmp_path):
    run_dir = make_run(tmp_path, "eq")
    write_half_workload(run_dir, "eq", schema="eqbench-matrix-publication-manifest-v2")
    report = run_verify(run_dir, "eq")
    assert not report.passed
    assert "workload.eq.publication_manifest" in failed_checks(report)


def test_a_run_that_expected_fewer_samples_than_the_subset_fails(tmp_path):
    """A filter that quietly selected less is not the fixed subset."""

    run_dir = make_run(tmp_path, "eq")
    write_half_workload(run_dir, "eq", expected_paths=expected_pair_paths("eq")[:2])
    report = run_verify(run_dir, "eq")
    assert not report.passed
    assert "workload.eq.subset_coverage" in failed_checks(report)


def test_a_run_that_expected_a_sample_outside_the_subset_fails(tmp_path):
    run_dir = make_run(tmp_path, "eq")
    extra = f"other/x/Eq/new/{FUNCTION}/{FUNCTION}_B1_B2{ci_subset.PAIR_STATUS_SUFFIX}"
    write_half_workload(
        run_dir, "eq", expected_paths=expected_pair_paths("eq") + [extra],
    )
    report = run_verify(run_dir, "eq")
    assert not report.passed
    assert "workload.eq.subset_coverage" in failed_checks(report)


def test_the_coverage_check_is_robust_to_several_functions_per_sample(tmp_path):
    """Two functions of one sample still cover the same (sample, pair) set."""

    run_dir = make_run(tmp_path, "eq")
    sources = DEFINITION["eq"]["sources"]
    pair_ids = DEFINITION["eq"]["pair_ids"]
    paths = [
        f"{source}/{fn}/{fn}_{pair_id}{ci_subset.PAIR_STATUS_SUFFIX}"
        for source in sources for fn in ("fn", "helper") for pair_id in pair_ids
    ]
    write_half_workload(run_dir, "eq", expected_paths=paths)
    report = run_verify(run_dir, "eq")
    assert report.passed, failed_checks(report)


def test_an_unusable_subset_definition_fails(tmp_path):
    run_dir = make_run(tmp_path, "eq")
    broken = write_definition(tmp_path, {"schema": "something-else"}, name="broken.json")
    report = run_verify(run_dir, "eq", subset_definition=broken)
    assert not report.passed
    assert "workload.eq.subset_coverage" in failed_checks(report)


def test_a_missing_subset_definition_fails(tmp_path):
    run_dir = make_run(tmp_path, "eq")
    report = run_verify(run_dir, "eq", subset_definition=tmp_path / "absent.json")
    assert not report.passed
    assert "workload.eq.subset_coverage" in failed_checks(report)


def test_the_repository_subset_definition_is_the_one_shipped(tmp_path):
    """The default points at the file that defines the subset, and it parses."""

    assert ci_subset.SUBSET_DEFINITION_FILE.name == "eqbench_subset.json"
    for half, sources, pairs in (("eq", 8, 8), ("neq", 10, 8)):
        identities, source_count, pair_count = ci_subset.subset_definition_pairs(
            half, ci_subset.SUBSET_DEFINITION_FILE,
        )
        assert (source_count, pair_count) == (sources, pairs)
        assert len(identities) == sources * pairs


@pytest.mark.parametrize("scope,absent", [("eq", "neq"), ("neq", "eq")])
def test_the_workload_gate_only_asks_about_halves_in_scope(tmp_path, scope, absent):
    run_dir = make_run(tmp_path, scope)
    report = run_verify(run_dir, scope)
    assert report.passed, failed_checks(report)
    workload = [c.name for c in report.checks if c.gate == ci_subset.GATE_WORKLOAD]
    assert workload and all(f".{absent}." not in name for name in workload)


def test_the_workload_gate_asks_about_both_halves_for_scope_all(tmp_path):
    report = run_verify(make_run(tmp_path, "all"), "all")
    workload = [c.name for c in report.checks if c.gate == ci_subset.GATE_WORKLOAD]
    assert [n for n in workload if ".eq." in n]
    assert [n for n in workload if ".neq." in n]


def test_the_propagation_profile_has_no_workload_gate(tmp_path):
    """A dry run runs no pairs, so there is no workload to be complete."""

    report = run_verify(
        make_dry_run(tmp_path, "all"), "all", profile=ci_subset.PROFILE_PROPAGATION,
    )
    assert report.passed, failed_checks(report)
    assert ci_subset.GATE_WORKLOAD not in report.as_dict()["gates"]


def test_pair_identity_from_status_path_reads_both_halves_layouts():
    assert ci_subset.pair_identity_from_status_path(
        "CLEVER/LoopSub/Eq/new/foo/foo_B1_B2.pair-status.json"
    ) == ("CLEVER/LoopSub/Eq/new", "B1_B2")
    assert ci_subset.pair_identity_from_status_path(
        "CLEVER/LoopSub/Neq/new-old/foo/foo_N_B1_O_B1.pair-status.json"
    ) == ("CLEVER/LoopSub/Neq/new-old", "N_B1_O_B1")


@pytest.mark.parametrize(
    "path",
    [
        "foo_B1_B2.pair-status.json",             # no sample, no function
        "sample/foo/bar_B1_B2.pair-status.json",  # the file is not this function's
        "sample/foo/foo_.pair-status.json",       # no pair id
        "sample/foo/foo_B1_B2.log",               # not a pair status at all
    ],
)
def test_a_path_that_is_not_a_pair_status_identity_is_not_guessed(path):
    assert ci_subset.pair_identity_from_status_path(path) is None


def test_the_binary_manifest_must_name_this_half_s_samples(tmp_path):
    """A well-formed manifest of another run's samples is not this run's."""

    run_dir = make_run(tmp_path, "eq")
    _write(
        run_dir / "binary_manifest_eq.txt",
        ci_subset.BINARY_MANIFEST_HEADER
        + "\nsample_identity\tbinary_id\tpath\tsha256\n"
        + "somewhere/else/Eq/new\tB1\ttmp/x\t" + "0" * 64 + "\n",
    )
    report = run_verify(run_dir, "eq")
    assert not report.passed
    assert "workload.eq.binary_manifest_samples" in failed_checks(report)


def test_a_binary_manifest_missing_a_subset_sample_fails(tmp_path):
    run_dir = make_run(tmp_path, "eq")
    rows = "".join(
        f"{source}\tB1\ttmp/{index}\t{'0' * 64}\n"
        for index, source in enumerate(DEFINITION["eq"]["sources"][:1])
    )
    _write(
        run_dir / "binary_manifest_eq.txt",
        ci_subset.BINARY_MANIFEST_HEADER
        + "\nsample_identity\tbinary_id\tpath\tsha256\n" + rows,
    )
    report = run_verify(run_dir, "eq")
    assert not report.passed
    check = next(
        c for c in report.checks if c.name == "workload.eq.binary_manifest_samples"
    )
    assert not check.passed and "1 subset sample(s) absent" in check.detail


def test_binary_manifest_samples_refuses_to_read_a_foreign_format(tmp_path):
    path = tmp_path / "m.txt"
    _write(path, "sample\tid\tpath\tsha\nrow\n")
    with pytest.raises(ci_subset.SubsetCiError):
        ci_subset.binary_manifest_samples(path)
    _write(path, ci_subset.BINARY_MANIFEST_HEADER + "\ncols\n")
    with pytest.raises(ci_subset.SubsetCiError):
        ci_subset.binary_manifest_samples(path)
    with pytest.raises(ci_subset.SubsetCiError):
        ci_subset.binary_manifest_samples(tmp_path / "absent.txt")


def test_a_run_attributed_to_nothing_fails(tmp_path):
    run_dir = make_run(tmp_path, "eq")
    _write(
        run_dir / ci_subset.SUBSET_MANIFEST_FILE,
        "scope=eq\nexit_status=0\nissue=none\npr=none\n",
    )
    report = run_verify(run_dir, "eq")
    assert not report.passed
    assert "run.subset_issue" in failed_checks(report)


def test_the_publication_manifest_is_required_evidence(tmp_path):
    assert "eq/matrix-publication-manifest.json" in ci_subset.required_artifacts(("eq",))
    assert "neq/matrix-publication-manifest.json" not in ci_subset.required_artifacts(
        ("eq",)
    )


# --------------------------------------------------------------------------
# a repeated expected path must not be absorbed by a set
# --------------------------------------------------------------------------


def test_unique_expected_paths_still_pass(tmp_path):
    """The existing case is unchanged: distinct paths, nothing to complain of."""

    run_dir = make_run(tmp_path, "all")
    for half in ("eq", "neq"):
        paths = expected_pair_paths(half)
        assert len(paths) == len(set(paths))
    assert run_verify(run_dir, "all").passed


def test_a_repeated_expected_path_fails(tmp_path):
    """64 listed paths of which two are the same is not 64 expected pairs."""

    run_dir = make_run(tmp_path, "eq")
    paths = expected_pair_paths("eq")
    write_half_workload(run_dir, "eq", expected_paths=paths + [paths[0]])
    report = run_verify(run_dir, "eq")
    assert not report.passed
    check = next(
        c for c in report.checks if c.name == "workload.eq.publication_manifest"
    )
    assert not check.passed
    assert "repeat" in check.detail and paths[0] in check.detail


def test_a_repeat_fails_even_though_the_sets_would_agree(tmp_path):
    """The (sample, pair) set is unchanged by the repeat -- the count is not.

    This is the case a set comparison cannot see: coverage against the subset
    definition still matches, and every path on disk is still expected, so
    without the list-level check the run would pass.
    """

    run_dir = make_run(tmp_path, "eq")
    paths = expected_pair_paths("eq")
    duplicated = paths + [paths[-1]]
    write_half_workload(run_dir, "eq", expected_paths=duplicated)

    identities = {ci_subset.pair_identity_from_status_path(p) for p in duplicated}
    definition, _, _ = ci_subset.subset_definition_pairs(
        "eq", write_definition(tmp_path),
    )
    assert identities == set(definition)              # coverage would agree
    assert set(duplicated) == set(paths)              # the path set would agree

    report = run_verify(run_dir, "eq")
    assert not report.passed
    assert "workload.eq.publication_manifest" in failed_checks(report)


def test_the_repeat_check_names_how_many_and_which(tmp_path):
    run_dir = make_run(tmp_path, "neq")
    paths = expected_pair_paths("neq")
    write_half_workload(
        run_dir, "neq", expected_paths=paths + [paths[0], paths[1]],
    )
    check = next(
        c for c in run_verify(run_dir, "neq").checks
        if c.name == "workload.neq.publication_manifest"
    )
    assert not check.passed
    assert f"{len(paths) + 2} expected pair statuses" in check.detail
    assert f"only {len(paths)} distinct" in check.detail
    assert "2 path(s) repeat" in check.detail
