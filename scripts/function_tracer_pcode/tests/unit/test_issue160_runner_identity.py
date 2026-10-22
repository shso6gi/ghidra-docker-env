"""Issue #160: a FULL-scope evaluation tree holds only pairs of one identity.

Four things are pinned here, each through the code path the runners use:

* the narrowing guard: a FULL scope refuses every input that narrows the pairs
  it runs (sample limit, sample / pair filter, rerun manifest, ERROR-only), in
  both runners, before any pair and before the output directory is touched;
* the output admission (``execution_receipt.full_scope_output_admission``):
  FRESH or SAME_IDENTITY_RESUME, anything else is REFUSED and the directory is
  left byte-for-byte as it was;
* resume reuse: for a FULL scope the compatibility paths that let a pair status
  of another source / config digest through (and the function-summary
  shortcut derived from them) are closed;
* runtime receipts: one writer and schema for both runners, removed at the
  execution boundary, bound to the pair status by ``execution_nonce`` and
  refused by the consumer when they belong to another execution.
"""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
import uuid
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.authority.contracts import authority_digest
from scripts.function_tracer_pcode.authority.decision.pair_status_authority import (
    generate_pair_status_keypair,
    seal_pair_status,
)
from scripts.function_tracer_pcode.reporting import execution_receipt as er
from scripts.function_tracer_pcode.reporting import outcome_transition as ot
from scripts.function_tracer_pcode.reporting import pair_runtime_receipt as rr
from scripts.function_tracer_pcode.reporting.execution_identity import source_tree_digest


REPO_ROOT = Path(__file__).resolve().parents[4]
COMMON = REPO_ROOT / "scripts" / "validation_matrix_common.sh"
EQ_RUNNER = REPO_ROOT / "eqbench_run_all_32jobs.sh"
NEQ_RUNNER = REPO_ROOT / "neqbench_run_all_32jobs.sh"
FULL_SCOPE_EXPECTATION = (
    REPO_ROOT / "scripts" / "function_tracer_pcode" / "reporting" / "eqbench_full_scope.json"
)


@pytest.fixture(scope="module")
def current_source():
    return source_tree_digest(REPO_ROOT)


def _tree_state(root: Path):
    """Every entry under ``root`` with its type and content hash (the "SHA tree")."""
    if not root.exists():
        return None
    state = []
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root).as_posix()
        if path.is_symlink():
            state.append((relative, "link", os.readlink(path)))
        elif path.is_dir():
            state.append((relative, "dir", ""))
        else:
            state.append((relative, "file", hashlib.sha256(path.read_bytes()).hexdigest()))
    return state


# ---------------------------------------------------------------------------
# Output admission: the rule (execution_receipt)
# ---------------------------------------------------------------------------


def _manifest_fields(source, **overrides):
    fields = {
        "run_kind": "neqbench_all_same_isa_function_closure_current",
        "run_scope": "FULL_NEQ",
        "build_policy": "REUSE_OR_COMPILE",
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
        "pair_process_timeout_seconds": "600",
        "pair_process_kill_after_seconds": "30",
        "prefilter_source_census_digest": "c" * 64,
        "analysis_config_schema": "eqbench-analysis-config-v4",
        "identical_fast_path": "1",
        "analysis_timeout": "410",
        "analysis_timeout_margin": "190",
        "analysis_source_digest_start": source,
    }
    fields.update(overrides)
    config = er.analysis_config_from_run(fields)
    fields.setdefault("analysis_config_digest", authority_digest(config))
    return fields


def _write_manifest(path: Path, fields) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(f"{k}={v}\n" for k, v in fields.items()), encoding="utf-8")
    return path


def _admission(tmp_path, output, source, **candidate_overrides):
    candidate = _write_manifest(
        tmp_path / "candidate" / "run_manifest.txt",
        _manifest_fields(source, **candidate_overrides),
    )
    return er.full_scope_output_admission(
        output, candidate_manifest=candidate, repo_root=REPO_ROOT,
    )


def test_admission_is_fresh_only_for_a_missing_or_empty_directory(tmp_path, current_source):
    assert _admission(tmp_path, tmp_path / "missing", current_source)[0] == "FRESH"
    (tmp_path / "empty").mkdir()
    assert _admission(tmp_path, tmp_path / "empty", current_source)[0] == "FRESH"
    (tmp_path / "other").mkdir()
    (tmp_path / "other" / "notes.txt").write_text("x", encoding="utf-8")
    kind, reason = _admission(tmp_path, tmp_path / "other", current_source)
    assert kind == "REFUSE" and "run_manifest.txt" in reason


def test_admission_resumes_only_a_run_of_the_same_identity(tmp_path, current_source):
    same = tmp_path / "same"
    _write_manifest(same / "run_manifest.txt", {
        **_manifest_fields(current_source),
        "analysis_source_digest_end": current_source, "total_pair_jobs": "4",
    })
    assert _admission(tmp_path, same, current_source)[0] == "SAME_IDENTITY_RESUME"

    for name, overrides in (
        ("source", {"analysis_source_digest_start": "a" * 64}),
        ("source_end", {"analysis_source_digest_end": "a" * 64}),
        ("config", {"parallel_jobs": "8"}),
        ("deadline", {"analysis_timeout": "0"}),
        ("dry", {"dry_run": "1"}),
        ("scope", {"run_scope": "REPRESENTATIVE"}),
        ("kind", {"run_kind": "eqbench_all_eq_matrix_current"}),
        ("digest", {"analysis_config_digest": "f" * 64}),
    ):
        directory = tmp_path / name
        base = _manifest_fields(current_source)
        base.update(overrides)
        if name in {"config", "deadline", "dry", "scope"}:
            base = _manifest_fields(current_source, **overrides)
        _write_manifest(directory / "run_manifest.txt", base)
        kind, reason = _admission(tmp_path, directory, current_source)
        assert kind == "REFUSE", (name, reason)


def test_admission_refuses_a_manifest_it_cannot_read(tmp_path, current_source):
    broken = tmp_path / "broken"
    broken.mkdir()
    (broken / "run_manifest.txt").write_text("not a manifest\n", encoding="utf-8")
    assert _admission(tmp_path, broken, current_source)[0] == "REFUSE"
    untyped = tmp_path / "untyped"
    _write_manifest(untyped / "run_manifest.txt", {
        "run_kind": "neqbench_all_same_isa_function_closure_current",
        "run_scope": "FULL_NEQ", "dry_run": "0",
        "analysis_source_digest_start": current_source,
    })
    assert _admission(tmp_path, untyped, current_source)[0] == "REFUSE"


def test_admission_refuses_a_candidate_that_is_not_the_current_source(tmp_path, current_source):
    kind, reason = _admission(
        tmp_path, tmp_path / "missing", current_source,
        analysis_source_digest_start="b" * 64,
    )
    assert kind == "REFUSE" and "current source" in reason


def test_admission_applies_to_full_scopes_only(tmp_path, current_source):
    with pytest.raises(ValueError):
        _admission(tmp_path, tmp_path / "x", current_source, run_scope="REPRESENTATIVE")


def test_full_scope_gets_no_cross_identity_resume_compatibility(tmp_path, current_source):
    """The paths that accept another source / config digest are closed for FULL only.

    A REPRESENTATIVE run (an auxiliary rerun tree) keeps them; the control
    shows the same manifest is still accepted there.
    """
    previous_source = "a" * 64
    for scope in ("FULL_NEQ", "REPRESENTATIVE"):
        previous = _write_manifest(
            tmp_path / scope / "previous.txt",
            _manifest_fields(previous_source, run_scope=scope),
        )
        current = er.analysis_config_from_run(_manifest_fields(current_source, run_scope=scope))
        identity = er.compatible_previous_run_manifest_analysis_identity(
            previous, current_config=current,
        )
        if scope == "FULL_NEQ":
            assert identity is None
            assert er.cross_identity_resume_is_permitted(current) is False
        else:
            assert identity is not None and identity[1] == previous_source
            assert er.cross_identity_resume_is_permitted(current) is True
    assert er.compatible_published_analysis_identity(
        tmp_path / "nothing", current_config=er.analysis_config_from_run(
            _manifest_fields(current_source)),
        current_source_digest=current_source,
    ) is None


# ---------------------------------------------------------------------------
# Output admission and narrowing guard: the shell entry points
# ---------------------------------------------------------------------------


def _bash(script: str, *, env=None, timeout=300):
    return subprocess.run(
        ["bash", "-c", script], cwd=REPO_ROOT, capture_output=True, text=True,
        timeout=timeout, env={**os.environ, **(env or {})},
    )


@pytest.mark.parametrize("scope", ["FULL_EQBENCH", "FULL_NEQ"])
@pytest.mark.parametrize("narrowing", [
    ("1", "", "", "", "0"),
    ("0", "x", "", "", "0"),
    ("0", "", "B1_B2", "", "0"),
    ("0", "", "", "/m.tsv", "0"),
    ("0", "", "", "", "1"),
])
def test_narrowing_guard_refuses_every_narrowing_input_in_full_scope(scope, narrowing):
    args = " ".join(f"'{value}'" for value in narrowing)
    full = _bash(f'source "{COMMON}"; validation_refuse_narrowed_full_scope {scope} {args}')
    assert full.returncode == 1 and "refusing" in full.stderr
    representative = _bash(
        f'source "{COMMON}"; validation_refuse_narrowed_full_scope REPRESENTATIVE {args}'
    )
    assert representative.returncode == 0, representative.stderr


def test_narrowing_guard_accepts_an_unnarrowed_full_scope():
    result = _bash(f'source "{COMMON}"; validation_refuse_narrowed_full_scope FULL_NEQ 0 "" "" "" 0')
    assert result.returncode == 0 and not result.stderr


def test_shell_admission_reports_the_decision_and_leaves_a_refused_dir_alone(
    tmp_path, current_source,
):
    candidate = _write_manifest(tmp_path / "c" / "run_manifest.txt", _manifest_fields(current_source))
    same = tmp_path / "same"
    _write_manifest(same / "run_manifest.txt", _manifest_fields(current_source))
    other = tmp_path / "other"
    _write_manifest(other / "run_manifest.txt", _manifest_fields("a" * 64))
    (other / "f" / "f_N_B1_O_B1.pair-status.json").parent.mkdir()
    (other / "f" / "f_N_B1_O_B1.pair-status.json").write_text("{}", encoding="utf-8")
    script = (
        f'source "{COMMON}"; validation_admit_full_scope_output python3 "$1" "{candidate}" '
        '&& printf "decision=%s\\n" "$VALIDATION_OUTPUT_ADMISSION"'
    )
    for directory, expected in (
        (tmp_path / "fresh", "FRESH"), (same, "SAME_IDENTITY_RESUME"),
    ):
        result = subprocess.run(
            ["bash", "-c", script, "admit", str(directory)], cwd=REPO_ROOT,
            capture_output=True, text=True, timeout=120,
        )
        assert result.returncode == 0, result.stderr
        assert f"decision={expected}" in result.stdout
    before = _tree_state(other)
    result = subprocess.run(
        ["bash", "-c", script, "admit", str(other)], cwd=REPO_ROOT,
        capture_output=True, text=True, timeout=120,
    )
    assert result.returncode == 1
    assert "another source tree" in result.stderr
    assert _tree_state(other) == before


# ---------------------------------------------------------------------------
# The runners (DRY_RUN): guard and admission before anything is written
# ---------------------------------------------------------------------------


def _runner(runner: Path, tmp_path: Path, **env):
    base = {
        "EQBENCH_TMPDIR": str(tmp_path / "runner-tmp"),
        "EQBENCH_PRIVATE_AUTHORITY_ROOT": str(tmp_path / "authority"),
        "DRY_RUN": "1",
        "PARALLEL_JOBS": "2",
    }
    base.update(env)
    return subprocess.run(
        ["bash", str(runner)], cwd=REPO_ROOT, capture_output=True, text=True,
        timeout=600, env={**os.environ, **base},
    )


def _rerun_manifest(tmp_path: Path, lane: str) -> Path:
    path = tmp_path / "rerun.tsv"
    path.write_text(f"{lane}\tsample\tf\tB1_B2\n", encoding="utf-8")
    return path


@pytest.mark.parametrize("runner, scope_var, scope, manifest_var, lane, extra", [
    (EQ_RUNNER, "EQBENCH_RUN_SCOPE", "FULL_EQBENCH", "EQBENCH_RERUN_MANIFEST", "EQ", {}),
    (NEQ_RUNNER, "NEQ_RUN_SCOPE", "FULL_NEQ", "NEQ_RERUN_MANIFEST", "NEQ",
     {"NEQ_ROOT": str(REPO_ROOT / "scripts")}),
])
@pytest.mark.parametrize("how", ["rerun_manifest", "error_only"])
def test_full_scope_runner_refuses_a_narrowed_run_before_writing(
    tmp_path, runner, scope_var, scope, manifest_var, lane, extra, how,
):
    output = tmp_path / "out"
    env = {scope_var: scope, "OUTPUT_BASE_DIR": str(output), **extra}
    if how == "rerun_manifest":
        env.update({manifest_var: str(_rerun_manifest(tmp_path, lane)),
                    "ERROR_RERUN_RUN_ID": "t160", "ERROR_ONLY_RERUN": "1"})
    else:
        env["ERROR_ONLY_RERUN"] = "1"
    result = _runner(runner, tmp_path, **env)
    assert result.returncode == 1, result.stdout + result.stderr
    assert f"Error: {scope} runs every pair" in result.stderr
    assert not output.exists()


def _synthetic_eq_full_root(tmp_path: Path) -> Path:
    """An EqBench root whose source census is exactly the frozen FULL census."""
    root = tmp_path / "eqbench"
    expected = json.loads(FULL_SCOPE_EXPECTATION.read_text(encoding="utf-8"))
    for relative in expected["source_paths"]:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("int f(int x) { return x; }\n", encoding="utf-8")
    return root


def _seed(directory: Path, kind: str, source: str) -> None:
    directory.mkdir(parents=True)
    if kind == "other_source":
        _write_manifest(directory / "run_manifest.txt", _manifest_fields(
            "a" * 64, run_kind="eqbench_all_eq_matrix_current", run_scope="FULL_EQBENCH",
        ))
        (directory / "pair-status-verification-key.json").write_text("{}", encoding="utf-8")
    elif kind == "broken":
        (directory / "run_manifest.txt").write_text("garbage\n", encoding="utf-8")
    elif kind == "dry_run":
        _write_manifest(directory / "run_manifest.txt", _manifest_fields(
            source, run_kind="eqbench_all_eq_matrix_current", run_scope="FULL_EQBENCH",
            dry_run="1",
        ))
    elif kind == "no_manifest":
        (directory / "sample").mkdir()
        (directory / "sample" / "f_B1_B2.log").write_text("old\n", encoding="utf-8")
    else:
        raise AssertionError(kind)


@pytest.fixture(scope="module")
def eq_full_root(tmp_path_factory):
    return _synthetic_eq_full_root(tmp_path_factory.mktemp("eqroot"))


@pytest.mark.parametrize("kind", ["other_source", "broken", "dry_run", "no_manifest"])
def test_eq_full_runner_refuses_an_output_dir_and_leaves_it_unchanged(
    tmp_path, eq_full_root, current_source, kind,
):
    output = tmp_path / "out"
    _seed(output, kind, current_source)
    before = _tree_state(output)
    result = _runner(
        EQ_RUNNER, tmp_path, EQBENCH_RUN_SCOPE="FULL_EQBENCH",
        EQBENCH_ROOT=str(eq_full_root), OUTPUT_BASE_DIR=str(output),
    )
    assert result.returncode == 1, result.stdout + result.stderr
    assert "FULL-scope output directory refused" in result.stderr
    assert _tree_state(output) == before
    assert not (tmp_path / "authority").exists() or not any((tmp_path / "authority").iterdir())


def test_eq_full_runner_admits_a_fresh_directory(tmp_path, eq_full_root):
    output = tmp_path / "out"
    result = _runner(
        EQ_RUNNER, tmp_path, EQBENCH_RUN_SCOPE="FULL_EQBENCH",
        EQBENCH_ROOT=str(eq_full_root), OUTPUT_BASE_DIR=str(output),
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert "FULL-scope output admission: FRESH" in result.stdout
    manifest = (output / "run_manifest.txt").read_text(encoding="utf-8")
    assert "run_scope=FULL_EQBENCH" in manifest and "dry_run=1" in manifest
    assert "analysis_config_digest=" in manifest
    # The dry run leaves a dry-run manifest, so the same directory is refused next time.
    again = _runner(
        EQ_RUNNER, tmp_path, EQBENCH_RUN_SCOPE="FULL_EQBENCH",
        EQBENCH_ROOT=str(eq_full_root), OUTPUT_BASE_DIR=str(output),
    )
    assert again.returncode == 1 and "not from a real run" in again.stderr


@pytest.fixture
def neq_full_root():
    """A Neq root with exactly the FULL census size, inside the repository."""
    root = REPO_ROOT / "tmp" / f"issue160-neq-{uuid.uuid4().hex}"
    for index in range(125):
        directory = root / f"S{index:03d}" / "Neq"
        directory.mkdir(parents=True)
        (directory / "newV.c").write_text("int f(int x) { return x + 1; }\n", encoding="utf-8")
        (directory / "oldV.c").write_text("int f(int x) { return x; }\n", encoding="utf-8")
    yield root
    shutil.rmtree(root, ignore_errors=True)


def test_neq_full_runner_refuses_another_source_and_leaves_it_unchanged(
    tmp_path, neq_full_root,
):
    output = tmp_path / "out"
    output.mkdir()
    _write_manifest(output / "run_manifest.txt", _manifest_fields("a" * 64))
    before = _tree_state(output)
    result = _runner(
        NEQ_RUNNER, tmp_path, NEQ_RUN_SCOPE="FULL_NEQ", NEQ_ROOT=str(neq_full_root),
        OUTPUT_BASE_DIR=str(output),
    )
    assert result.returncode == 1, result.stdout + result.stderr
    assert "FULL-scope output directory refused" in result.stderr
    assert _tree_state(output) == before


def test_representative_runner_still_accepts_a_rerun_manifest(tmp_path):
    root = tmp_path / "eqbench"
    source = root / "X" / "Eq" / "newV.c"
    source.parent.mkdir(parents=True)
    source.write_text("int f(int x) { return x; }\n", encoding="utf-8")
    result = _runner(
        EQ_RUNNER, tmp_path, EQBENCH_RUN_SCOPE="REPRESENTATIVE", EQBENCH_ROOT=str(root),
        OUTPUT_BASE_DIR=str(tmp_path / "out"), EQBENCH_BUILD_POLICY="PREBUILT_ONLY",
        EQBENCH_RERUN_MANIFEST=str(_rerun_manifest(tmp_path, "EQ")),
        ERROR_RERUN_RUN_ID="t160", ERROR_ONLY_RERUN="1",
    )
    assert result.returncode == 0, result.stdout + result.stderr


# ---------------------------------------------------------------------------
# Runtime receipts: measurement, binding, acceptance (pair_runtime_receipt)
# ---------------------------------------------------------------------------


def _usage(path: Path, elapsed, rss, *, note=None) -> Path:
    lines = ([note] if note else []) + [f"elapsed_seconds={elapsed}", f"max_rss_kb={rss}"]
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return path


def test_the_runners_time_with_the_format_the_aggregator_reads():
    result = _bash(f'source "{COMMON}"; printf "%s\\n" "${{VALIDATION_SUPERVISOR_TIME[@]}}"')
    assert result.stdout.splitlines() == [
        "/usr/bin/time", "-f", rr.RUNTIME_USAGE_TIME_FORMAT,
    ]

    for runner in (EQ_RUNNER, NEQ_RUNNER):
        text = runner.read_text(encoding="utf-8")
        assert "/usr/bin/time" not in text and "elapsed_seconds" not in text, runner.name


def test_an_execution_is_measured_over_every_supervisor_invocation(tmp_path):
    """Wall clock adds up across invocations; peak RSS is the maximum, never a sum."""
    first = _usage(tmp_path / "1", "10.25", "800000", note="Command exited with non-zero status 1")
    recovery = _usage(tmp_path / "2", "3.5", "900000")
    assert rr.aggregate_resource_usage([first, recovery]) == {
        "supervisor_invocations": 2, "measurement_complete": True,
        "elapsed_seconds": 13.75, "max_rss_kb": 900000,
    }
    assert rr.aggregate_resource_usage([first])["elapsed_seconds"] == 10.25
    # A missing or malformed reading makes the whole measurement null: neither a
    # partial sum nor the recovery alone stands in for the execution.
    duplicated = tmp_path / "3"
    duplicated.write_text("elapsed_seconds=1\nelapsed_seconds=2\nmax_rss_kb=1\n")
    for paths in ([first, tmp_path / "missing"], [first, duplicated],
                  [_usage(tmp_path / "4", "-1", "5")], []):
        aggregate = rr.aggregate_resource_usage(paths)
        assert aggregate["measurement_complete"] is False
        assert aggregate["elapsed_seconds"] is None and aggregate["max_rss_kb"] is None


def _receipt(tmp_path=None, **override):
    usage = []
    if tmp_path is not None:
        usage = [_usage(tmp_path / "u1", "12.5", "1000")]
    payload = rr.build_receipt(
        state="COMPLETED", function_name="f", left_binary_id="N_B1",
        right_binary_id="O_B2", execution_nonce="n1", run_id="run-2",
        fields={"cpu_tokens": "16"}, usage_files=usage,
    )
    return {**payload, **override}


def test_receipt_acceptance_needs_both_the_status_and_the_run(tmp_path):
    status = {"execution_nonce": "n1"}
    bound = dict(function_name="f", left_binary_id="N_B1", right_binary_id="O_B2")
    good = _receipt(tmp_path)
    assert rr.classify_receipt(good, pair_status=status, run_id="run-2", **bound) == (
        "measured", 12.5)
    # Bound to its status but written by an earlier run: the pair was reused.
    assert rr.classify_receipt(good, pair_status=status, run_id="run-3", **bound) == (
        "retained", 12.5)
    assert rr.classify_receipt(good, pair_status=status, run_id=None, **bound)[0] == "retained"
    for receipt, pair_status in (
        (good, {"execution_nonce": "n2"}),                 # another execution
        (good, {"classification_valid": False}),           # unsigned diagnostic
        (good, None),                                      # no status
        ({k: v for k, v in good.items() if k != "execution_nonce"}, status),
        ({k: v for k, v in good.items() if k != "run_id"}, status),
        (_receipt(), status),                              # no usage: incomplete
        ({**good, "measurement_complete": False}, status),
        ({**good, "schema": "eqbench-pair-progress-receipt-v1"}, status),
        ({**good, "state": "RUNNING"}, status),
        ({**good, "function_name": "g"}, status),
        ({**good, "right_binary_id": "O_B3"}, status),
        ({**good, "elapsed_seconds": True}, status),
    ):
        assert rr.classify_receipt(
            receipt, pair_status=pair_status, run_id="run-2", **bound) == ("unusable", None)


def test_writer_publishes_the_runtime_receipt_only_when_completed(tmp_path):
    common = [
        "--metrics-dir", str(tmp_path), "--stem", "f_B1_B2", "--function-name", "f",
        "--left-binary-id", "B1", "--right-binary-id", "B2", "--execution-nonce", "n1",
        "--run-id", "run-1", "--started-at-epoch", "100.5", "--cpu-tokens", "16",
        "--parallel-jobs-requested", "-",
    ]
    progress, runtime = rr.receipt_paths(tmp_path, "f_B1_B2")
    assert rr.main(["write", "--state", "RUNNING", *common]) == 0
    assert json.loads(progress.read_text())["state"] == "RUNNING"
    assert not runtime.exists()
    usage = [_usage(tmp_path / "a", "3.25", "10"), _usage(tmp_path / "b", "1", "20")]
    assert rr.main(["write", "--state", "COMPLETED", *common,
                    "--resource-usage", str(usage[0]), "--resource-usage", str(usage[1]),
                    "--status", "UNKNOWN", "--error-kind", "-"]) == 0
    payload = json.loads(runtime.read_text())
    assert payload == json.loads(progress.read_text())
    assert payload["schema"] == rr.RUNTIME_RECEIPT_SCHEMA
    assert (payload["execution_nonce"], payload["run_id"]) == ("n1", "run-1")
    assert (payload["elapsed_seconds"], payload["max_rss_kb"]) == (4.25, 20)
    assert payload["supervisor_invocations"] == 2 and payload["measurement_complete"] is True
    assert payload["started_at_epoch"] == 100.5 and payload["cpu_tokens"] == 16
    assert payload["parallel_jobs_requested"] is None and payload["error_kind"] is None


SAMPLE = "S/Neq/new-old"


def _tree_pair(tree: Path, pair: str, *, receipt_run: str, seconds: float,
               status_nonce="same", tree_run: str = "run-after") -> None:
    """One pair of a tree: status, receipt and the tree's run manifest."""
    directory = tree / SAMPLE / "f"
    (directory / rr.RUNTIME_METRICS_DIR).mkdir(parents=True, exist_ok=True)
    nonce = f"nonce-{pair}"
    status = {"canonical_outcome": "UNKNOWN", "pair_execution_target": {
        "sample_identity": SAMPLE, "function_name": "f",
        "left_binary_id": pair.split("_O_")[0], "right_binary_id": "O_" + pair.split("_O_")[1],
    }}
    if status_nonce is not None:
        status["execution_nonce"] = nonce if status_nonce == "same" else status_nonce
    (directory / f"f_{pair}.pair-status.json").write_text(json.dumps(status))
    # Written as plain JSON (the shape the writer produces) so the same fixture
    # also runs against a consumer that predates the run binding.
    receipt = {
        "schema": "eqbench-pair-progress-receipt-v2", "state": "COMPLETED",
        "function_name": "f", "left_binary_id": pair.split("_O_")[0],
        "right_binary_id": "O_" + pair.split("_O_")[1], "execution_nonce": nonce,
        "run_id": receipt_run, "elapsed_seconds": float(seconds), "max_rss_kb": 100,
        "supervisor_invocations": 1, "measurement_complete": True,
    }
    (directory / rr.RUNTIME_METRICS_DIR / f"f_{pair}.runtime.json").write_text(json.dumps(receipt))
    (tree / "run_manifest.txt").write_text(f"runtime_run_id={tree_run}\n")


PAIRS = ("N_B1_O_B1", "N_B2_O_B2", "N_B9_O_B9")


def _keys():
    return sorted((SAMPLE, "f", pair.split("_O_")[0], "O_" + pair.split("_O_")[1])
                  for pair in PAIRS)


def test_a_rerun_that_reused_every_pair_measures_nothing(tmp_path):
    """The second run skipped every pair: its tree holds receipts, but it measured none."""
    before, after = tmp_path / "before", tmp_path / "after"
    for pair in PAIRS:
        _tree_pair(before, pair, receipt_run="run-before", seconds=10, tree_run="run-before")
        # the receipts were written by the first run into this tree, then reused
        _tree_pair(after, pair, receipt_run="run-after-1", seconds=10, tree_run="run-after-2")
    report = ot.build_runtime_metrics(before, after, _keys())
    assert report.complete is False
    assert report.deltas == ()
    assert (report.after_measured, report.after_retained, report.after_unusable) == (0, 3, 0)
    assert report.median_delta() is None
    assert ot.load_runtime_metrics(after) == ({}, 0)


def test_only_pairs_the_latest_run_executed_are_compared(tmp_path):
    before, after = tmp_path / "before", tmp_path / "after"
    for pair in PAIRS:
        _tree_pair(before, pair, receipt_run="run-before", seconds=10, tree_run="run-before")
    _tree_pair(after, PAIRS[0], receipt_run="run-after", seconds=4)                # executed
    _tree_pair(after, PAIRS[1], receipt_run="run-earlier", seconds=10)             # reused
    _tree_pair(after, PAIRS[2], receipt_run="run-after", seconds=4, status_nonce="other")
    report = ot.build_runtime_metrics(before, after, _keys())
    assert [key[2] for key, _b, _a in report.deltas] == ["N_B1"]
    assert (report.after_measured, report.after_retained, report.after_unusable) == (1, 1, 1)
    assert report.complete is False and report.faster == 1
    payload = report.as_dict()
    assert payload["pairs_measured_on_both_sides"] == 1
    assert payload["after_retained_from_earlier_runs"] == 1
    # The control: every pair executed by both runs is a complete comparison.
    fresh = tmp_path / "fresh"
    for pair in PAIRS:
        _tree_pair(fresh, pair, receipt_run="run-after", seconds=4)
    full = ot.build_runtime_metrics(before, fresh, _keys())
    assert full.complete is True and len(full.deltas) == 3 and full.faster == 3


def test_a_pair_the_latest_publication_lists_as_reused_is_never_its_measurement(tmp_path):
    """The run's own publication and the receipt must agree on what the run executed."""
    from scripts.function_tracer_pcode.tests.unit.test_verification_ledger import (
        build_formal_publication_manifest,
    )
    tree = tmp_path / "tree"
    reused = f"{SAMPLE}/f/f_{PAIRS[0]}.pair-status.json"
    build_formal_publication_manifest(
        tree, [f"{SAMPLE}/f/f_{pair}.pair-status.json" for pair in PAIRS],
        run_scope="REPRESENTATIVE", census_overrides={
            "verified_skipped_pair_status_paths.txt": [reused]},
    )
    manifest = (tree / "run_manifest.txt").read_text()
    for pair in PAIRS:
        _tree_pair(tree, pair, receipt_run="run-after", seconds=4)
    # _tree_pair rewrote the run manifest; restore it with the run id appended,
    # so the stored publication is still the one the tree rebuilds.
    (tree / "run_manifest.txt").write_text(manifest + "runtime_run_id=run-after\n")
    measurements = rr.load_tree_measurements(tree)
    assert sorted(key[2] for key in measurements.measured) == ["N_B2", "N_B9"]
    assert measurements.unusable == 1
    # A stale publication (it does not rebuild from the current manifest) is ignored.
    (tree / "run_manifest.txt").write_text(
        manifest.replace("parallel_jobs=20", "parallel_jobs=8") + "runtime_run_id=run-after\n")
    assert len(rr.load_tree_measurements(tree).measured) == 3


def test_a_failing_receipt_writer_never_fails_the_pair(tmp_path):
    """``set -e`` in a runner must not turn a diagnostic write failure into a pair failure."""
    script = (
        f'set -euo pipefail; source "{COMMON}"; '
        'validation_write_pair_runtime_receipt false --state RUNNING; '
        f'validation_write_pair_runtime_receipt python3 --state BOGUS --metrics-dir "{tmp_path}"; '
        'echo reached'
    )
    result = _bash(script)
    assert result.returncode == 0 and "reached" in result.stdout
    assert "Warning: pair runtime receipt was not written" in result.stderr


# ---------------------------------------------------------------------------
# The execution boundary: both runners' real run_pair drop the previous
# execution's receipts before anything of the new execution runs.
# ---------------------------------------------------------------------------


def _extract_shell_function(source: str, name: str) -> str:
    lines = source.splitlines()
    start = next(i for i, line in enumerate(lines) if line.startswith(f"{name}() {{"))
    end = next(i for i in range(start + 1, len(lines)) if lines[i] == "}")
    return "\n".join(lines[start:end + 1])


_BOUNDARY_HARNESS = """
set -u
source "__COMMON__"
EQBENCH_RUN_TMPDIR="__TMP__/runtmp"; RUN_TMP="__TMP__/runtmp"; EQBENCH_TMPDIR="__TMP__/runtmp"
SCRIPT_DIR="__TMP__"; OUTPUT_BASE_DIR="__TMP__/out"
PYTHON_BIN="__TMP__/python-probe"
EQUIV_TIMEOUT=10; DECOMPILE_TIMEOUT=60; PAIRWISE_TIMEOUT=5; PAIRWISE_TIMEOUT_HARD=30
PAIR_PROCESS_TIMEOUT_SECONDS=240; PAIR_PROCESS_KILL_AFTER_SECONDS=30
PAIR_PROCESS_TIMEOUT=240s; PAIR_PROCESS_KILL_AFTER=30s; PAIR_STACK_DUMP_LEAD_SECONDS=1
PAIR_PROCESS_DEADLINE_POLICY_DIGEST=deadbeef
PROCESS_SUPERVISOR_KEY_ID=k; PROCESS_SUPERVISOR_KEY_FILE=/dev/null
PROCESS_WORKER_KEY_ID=k; PROCESS_WORKER_KEY_FILE=/dev/null
SUPERVISOR_KEY_ID=k; SUPERVISOR_KEY=/dev/null; WORKER_KEY_ID=k; WORKER_KEY=/dev/null
PAIR_STATUS_SIGNING_PRIVATE_KEY_FILE=/dev/null; PAIR_STATUS_VERIFICATION_KEY_FILE=/dev/null
PAIR_PRIVATE_KEY=/dev/null; PAIR_PUBLIC_KEY=/dev/null
EQBENCH_DEBUG=0; EQBENCH_PROGRESS_INTERVAL_SECONDS=1; EQBENCH_IDENTICAL_FAST_PATH=1
EQBENCH_CPU_TOKENS=16; EQBENCH_PAIR_CPU_TOKENS=8; PARALLEL_JOBS=2; PARALLEL_JOBS_REQUESTED=2
RUNTIME_RUN_ID=harness-run
FT_EXPANDER_DEDUP_CASE_LIMIT=0; FT_CALLEE_UNBOUND_REUSE=0; FT_CALLEE_UNBOUND_REUSE_SHADOW=0
PROCESS_CLEANUP_FAILURES="__TMP__/cleanup-failures"; SOURCE_PAIR_COUNT=1
STACK_DUMP_ARTIFACT_STATE_FILE="__TMP__/state.tsv"
supervisor_projection_is_terminal() {
    # NONTERMINAL_ONCE: the first look finds a non-terminal projection, so the
    # runner resumes the supervisor once (the recovery path).
    if [[ -n "${NONTERMINAL_ONCE:-}" && ! -e "__TMP__/looked" ]]; then
        : > "__TMP__/looked"; return 1
    fi
    return 0
}
validate_current_pair_status() { printf 'UNKNOWN'; }
cleanup_pair_process_authority_with_run_health() { return 0; }
progress_update() { :; }
__FUNCTION__
run_pair __ARGS__ || true
"""

_PROBE = """#!/bin/sh
# Record, at the first interpreter call of the new execution, whether the
# previous execution's receipts were still there.
if [ ! -f "$PROBE_MARKER" ]; then
  state=""
  for f in "$PROBE_PROGRESS" "$PROBE_RUNTIME"; do
    if [ -f "$f" ] && grep -q previous-execution "$f"; then state="$state stale"; else state="$state clean"; fi
  done
  echo "$state" > "$PROBE_MARKER"
fi
echo stub
exit 0
"""


@pytest.mark.parametrize("runner", [EQ_RUNNER, NEQ_RUNNER])
def test_run_pair_drops_the_previous_receipts_before_the_new_execution(tmp_path, runner):
    out = tmp_path / "out" / "sample" / "f"
    metrics = out / rr.RUNTIME_METRICS_DIR
    metrics.mkdir(parents=True)
    (tmp_path / "runtmp").mkdir()
    stem = "f_B1_B2" if runner == EQ_RUNNER else "f_N_B1_O_B2"
    progress, runtime = rr.receipt_paths(metrics, stem)
    for path in (progress, runtime):
        path.write_text('{"state": "COMPLETED", "note": "previous-execution"}\n')
    probe = tmp_path / "python-probe"
    probe.write_text(_PROBE)
    probe.chmod(0o755)
    function = _extract_shell_function(runner.read_text(encoding="utf-8"), "run_pair")
    if runner == EQ_RUNNER:
        args = f'"sample" "f" "B1" "B2" "/left" "/right" "{out}" 1 1 "/target"'
    else:
        args = f'"sample" "f" "N_B1" "O_B2" "/left" "/right" "{out}" 1 1 "/target" 1 1 1'
    script = (
        _BOUNDARY_HARNESS.replace("__COMMON__", str(COMMON))
        .replace("__TMP__", str(tmp_path)).replace("__FUNCTION__", function)
        .replace("__ARGS__", args)
    )
    marker = tmp_path / "marker"
    subprocess.run(
        ["bash", "-c", script], capture_output=True, timeout=120,
        env={**os.environ, "PROBE_MARKER": str(marker), "PROBE_PROGRESS": str(progress),
             "PROBE_RUNTIME": str(runtime)},
    )
    assert marker.read_text().split() == ["clean", "clean"], (
        f"{runner.name}: the previous execution's receipts survived into the new execution"
    )
    assert not runtime.exists()


_TIMED_PROBE = """#!/bin/sh
# The receipt writer runs for real; each supervisor invocation sleeps a known
# time (1 s, then 2 s), and everything else is a no-op.
case "$*" in
  *pair_runtime_receipt*) exec "$REAL_PYTHON" "$@" ;;
  *supervisor_command*)
    n=$(cat "$COUNTER" 2>/dev/null || echo 0); n=$((n + 1)); echo "$n" > "$COUNTER"
    sleep "$n"; exit 0 ;;
esac
echo stub
exit 0
"""


@pytest.mark.parametrize("runner", [EQ_RUNNER, NEQ_RUNNER])
@pytest.mark.parametrize("recovery", [False, True])
def test_the_receipt_measures_the_execution_including_its_recovery(
    tmp_path, runner, recovery,
):
    """Elapsed time covers the first supervisor call and its recovery, not one of them."""
    out = tmp_path / "out" / "sample" / "f"
    out.mkdir(parents=True)
    (tmp_path / "runtmp").mkdir()
    probe = tmp_path / "python-probe"
    probe.write_text(_TIMED_PROBE)
    probe.chmod(0o755)
    function = _extract_shell_function(runner.read_text(encoding="utf-8"), "run_pair")
    if runner == EQ_RUNNER:
        args, stem = f'"sample" "f" "B1" "B2" "/left" "/right" "{out}" 1 1 "/target"', "f_B1_B2"
    else:
        args = f'"sample" "f" "N_B1" "O_B2" "/left" "/right" "{out}" 1 1 "/target" 1 1 1'
        stem = "f_N_B1_O_B2"
    script = (
        _BOUNDARY_HARNESS.replace("__COMMON__", str(COMMON))
        .replace("__TMP__", str(tmp_path)).replace("__FUNCTION__", function)
        .replace("__ARGS__", args)
    )
    env = {**os.environ, "REAL_PYTHON": sys.executable, "COUNTER": str(tmp_path / "count")}
    if recovery:
        env["NONTERMINAL_ONCE"] = "1"
    subprocess.run(["bash", "-c", script], capture_output=True, timeout=120, env=env)
    _progress, runtime = rr.receipt_paths(out / rr.RUNTIME_METRICS_DIR, stem)
    receipt = json.loads(runtime.read_text())
    expected = 3.0 if recovery else 1.0     # 1 s, plus 2 s for the recovery
    assert expected - 0.05 <= receipt["elapsed_seconds"] < expected + 1.5, receipt
    assert receipt["supervisor_invocations"] == (2 if recovery else 1)
    assert receipt["measurement_complete"] is True and receipt["run_id"] == "harness-run"


# ---------------------------------------------------------------------------
# Post-run audit
# ---------------------------------------------------------------------------


def _signed_status(tree: Path, private_key: Path, public_key: Path, relative: str,
                   *, source: str, config: str) -> None:
    from scripts.function_tracer_pcode.tests.unit.test_outcome_transition_axes_and_reason_sets import (  # noqa: E501
        _status_body,
    )
    body = _status_body("sample", "f", "B1", "B2", "UNKNOWN", "RESOLVED")
    target = {k: v for k, v in body["pair_execution_target"].items() if k != "target_digest"}
    target.update(analysis_source_digest=source, analysis_config_digest=config)
    body["pair_execution_target"] = {**target, "target_digest": authority_digest(target)}
    sealed = seal_pair_status(body, private_key_path=private_key, public_key_path=public_key)
    path = tree / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(sealed), encoding="utf-8")


def test_audit_flags_a_pair_status_of_another_identity(tmp_path):
    from scripts.function_tracer_pcode.tests.unit.test_verification_ledger import (
        build_formal_publication_manifest,
    )
    expected = ["sample/f/f_B1_B2.pair-status.json", "sample/f/f_B1_B3.pair-status.json",
                "sample/f/f_B1_B4.pair-status.json"]
    tree = tmp_path / "tree"
    private_key = tree / "pair-status-signing-key.bin"
    public_key = tree / "pair-status-verification-key.json"
    tree.mkdir()
    generate_pair_status_keypair(private_key, public_key)
    publication = build_formal_publication_manifest(tree, expected, run_scope="FULL_NEQ")
    source = publication["analysis_source_digest_start"]
    config = publication["analysis_config_digest"]
    _signed_status(tree, private_key, public_key, expected[0], source=source, config=config)
    _signed_status(tree, private_key, public_key, expected[1], source="a" * 64, config=config)
    report = er.audit_matrix_pair_identity(tree)
    assert report["passed"] is False
    assert report["matching_pairs"] == 1
    assert report["foreign_identity_pair_status_paths"] == [expected[1]]
    assert report["missing_pair_status_paths"] == [expected[2]]
    _signed_status(tree, private_key, public_key, expected[1], source=source, config=config)
    _signed_status(tree, private_key, public_key, expected[2], source=source, config=config)
    assert er.audit_matrix_pair_identity(tree)["passed"] is True
    # A classification failure's unsigned diagnostic has no identity to compare;
    # it is listed, not counted as matching, and does not fail the audit.
    (tree / expected[2]).write_text(json.dumps({
        "classification_valid": False, "error_kind": "PAIR_STATUS_AUTHORITY_INVALID",
        "detail": "classification failed",
    }), encoding="utf-8")
    report = er.audit_matrix_pair_identity(tree)
    assert report["passed"] is True and report["matching_pairs"] == 2
    assert report["unsigned_diagnostic_pair_status_paths"] == [expected[2]]
    # A tampered status is invalid, not a diagnostic.
    (tree / expected[2]).write_text('{"canonical_outcome": "EQUIVALENT"}', encoding="utf-8")
    report = er.audit_matrix_pair_identity(tree)
    assert report["passed"] is False and report["invalid_pair_status_paths"] == [expected[2]]


# ---------------------------------------------------------------------------
# Pair-level reuse: what a FULL resume relies on once the compatibility paths
# are closed (pair_status_authority.pair_status_file_skip_decision).
# ---------------------------------------------------------------------------


def test_a_pair_is_reused_only_for_the_exact_target(tmp_path):
    from scripts.function_tracer_pcode.authority.decision.pair_status_authority import (
        pair_status_file_skip_decision,
    )
    from scripts.function_tracer_pcode.tests.unit.test_outcome_transition_axes_and_reason_sets import (  # noqa: E501
        _status_body,
    )

    private_key, public_key = tmp_path / "k", tmp_path / "pair-status-verification-key.json"
    generate_pair_status_keypair(private_key, public_key)
    body = _status_body("sample", "f", "B1", "B2", "UNKNOWN", "RESOLVED")
    target = {k: v for k, v in body["pair_execution_target"].items() if k != "target_digest"}
    target.update(analysis_source_digest="1" * 64, analysis_config_digest="2" * 64)

    def sealed_target(**changes):
        fields = {**target, **changes}
        return {**fields, "target_digest": authority_digest(fields)}

    body["pair_execution_target"] = sealed_target()
    status = tmp_path / "f_B1_B2.pair-status.json"
    status.write_text(json.dumps(seal_pair_status(
        body, private_key_path=private_key, public_key_path=public_key)))
    log = tmp_path / "f_B1_B2.log"
    log.write_text("log\n")

    def decide(expected, **compat):
        path = tmp_path / "expected.json"
        path.write_text(json.dumps(expected))
        return pair_status_file_skip_decision(
            status, log_path=log, public_key_path=public_key,
            expected_pair_target_path=path, mode="NORMAL_RESUME", **compat,
        )

    assert decide(sealed_target()) == "SKIP"
    for changes in (
        {"analysis_source_digest": "3" * 64}, {"analysis_config_digest": "3" * 64},
        {"source_sha256": "3" * 64}, {"left_binary_sha256": "3" * 64},
        {"right_binary_sha256": "3" * 64},
    ):
        assert decide(sealed_target(**changes)) == "SCHEDULE", changes
    # What a FULL run no longer passes: the compatibility digests relax only the
    # analysis digests, never the inputs.
    compat = {"compatible_analysis_config_digest": "2" * 64,
              "compatible_analysis_source_digest": "1" * 64}
    assert decide(sealed_target(analysis_source_digest="3" * 64), **compat) == "SKIP"
    assert decide(sealed_target(analysis_source_digest="3" * 64,
                                left_binary_sha256="3" * 64), **compat) == "SCHEDULE"
