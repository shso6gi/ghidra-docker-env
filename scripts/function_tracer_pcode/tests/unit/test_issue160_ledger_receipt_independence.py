"""Issue #160 AC5: the verification ledger does not depend on runtime receipts.

Runtime receipts (``.runtime-metrics/<pair>.{progress,runtime}.json``) are
diagnostic.  The ledger's verdict -- coverage, completed scope, scope health
and the full-scope evidence -- is built from the formal publication, the
signed execution receipt, the run manifest and the pair statuses only.  This
module pins that as behaviour on the ledger's public entry points
(``build_row`` / ``full_scope_evidence`` / ``format_listing``) over the same
formal fixtures the ledger's own tests use:

* for one run, every receipt state a runner can leave behind (present, absent,
  values changed, nonce / run id changed, an older schema, broken JSON, only a
  RUNNING progress file) yields the identical row and verdict;
* the authority artifacts are byte-for-byte unchanged while the receipts vary;
* the control: breaking evidence the ledger does depend on changes the
  verdict, so the comparison above is not vacuous.
"""

from __future__ import annotations

import hashlib
import json
import shutil
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.reporting import pair_runtime_receipt as rr
from scripts.function_tracer_pcode.reporting import verification_ledger
from scripts.function_tracer_pcode.tests.unit.test_verification_ledger import (  # noqa: F401
    EQ_SAMPLE,
    _head_state,
    full_run,
    subset_run,
)

VOLATILE_ROW_KEYS = ("recorded_at_utc", "recorded_on_host")


def _status_paths(run_dir: Path):
    return sorted(run_dir.rglob("*.pair-status.json"))


def _with_run_id(run_dir: Path, run_id: str = "run-1") -> None:
    """Record a ``runtime_run_id`` in every tree's run manifest, as the runners do."""
    for manifest in run_dir.rglob("run_manifest.txt"):
        text = manifest.read_text(encoding="utf-8")
        if "runtime_run_id=" not in text:
            manifest.write_text(text + f"runtime_run_id={run_id}\n", encoding="utf-8")


def _authority_state(run_dir: Path):
    """Every file of the run except the runtime receipts, with its content hash."""
    return sorted(
        (path.relative_to(run_dir).as_posix(), hashlib.sha256(path.read_bytes()).hexdigest())
        for path in run_dir.rglob("*")
        if path.is_file() and rr.RUNTIME_METRICS_DIR not in path.parts
    )


def _write_receipts(run_dir: Path, tmp_path: Path, **overrides) -> None:
    """A real COMPLETED receipt (through the writer) next to every pair status."""
    usage = tmp_path / "usage.txt"
    usage.write_text("elapsed_seconds=12.5\nmax_rss_kb=4096\n", encoding="utf-8")
    for status_path in _status_paths(run_dir):
        stem = status_path.name[: -len(".pair-status.json")]
        status = json.loads(status_path.read_text(encoding="utf-8"))
        target = status["pair_execution_target"]
        args = [
            "write", "--state", "COMPLETED",
            "--metrics-dir", str(status_path.parent / rr.RUNTIME_METRICS_DIR),
            "--stem", stem, "--function-name", target["function_name"],
            "--left-binary-id", target["left_binary_id"],
            "--right-binary-id", target["right_binary_id"],
            "--execution-nonce", status.get("execution_nonce") or "nonce",
            "--run-id", "run-1", "--resource-usage", str(usage),
            "--status", status.get("canonical_outcome", "UNKNOWN"),
        ]
        assert rr.main(args) == 0
        if overrides:
            for path in rr.receipt_paths(status_path.parent / rr.RUNTIME_METRICS_DIR, stem):
                payload = json.loads(path.read_text(encoding="utf-8"))
                payload.update(overrides)
                path.write_text(json.dumps(payload), encoding="utf-8")


def _receipt_files(run_dir: Path):
    return [path for path in run_dir.rglob("*") if path.is_file()
            and rr.RUNTIME_METRICS_DIR in path.parts]


def _drop_receipts(run_dir: Path) -> None:
    for directory in list(run_dir.rglob(rr.RUNTIME_METRICS_DIR)):
        shutil.rmtree(directory)


def _variant(name, run_dir: Path, tmp_path: Path) -> None:
    """Put ``run_dir``'s receipts into one of the states a runner can leave."""
    _drop_receipts(run_dir)
    if name == "absent":
        return
    if name == "present":
        _write_receipts(run_dir, tmp_path)
    elif name == "measured_values_changed":
        _write_receipts(run_dir, tmp_path, elapsed_seconds=99999.0, max_rss_kb=1,
                        supervisor_invocations=7)
    elif name == "nonce_changed":
        _write_receipts(run_dir, tmp_path, execution_nonce="another-execution")
    elif name == "run_id_changed":
        _write_receipts(run_dir, tmp_path, run_id="an-earlier-run")
    elif name == "older_schema":
        _write_receipts(run_dir, tmp_path, schema="eqbench-pair-progress-receipt-v1")
    elif name == "incomplete_measurement":
        _write_receipts(run_dir, tmp_path, measurement_complete=False,
                        elapsed_seconds=None)
    elif name == "broken_json":
        _write_receipts(run_dir, tmp_path)
        for path in _receipt_files(run_dir):
            path.write_text("{not json", encoding="utf-8")
    elif name == "running_progress_only":
        _write_receipts(run_dir, tmp_path)
        for path in _receipt_files(run_dir):
            if path.name.endswith(rr.RUNTIME_SUFFIX):
                path.unlink()
            else:
                payload = json.loads(path.read_text(encoding="utf-8"))
                payload.update(state="RUNNING", elapsed_seconds=None)
                path.write_text(json.dumps(payload), encoding="utf-8")
    else:
        raise AssertionError(name)
    if name != "absent":
        assert _receipt_files(run_dir), name


VARIANTS = (
    "present", "absent", "measured_values_changed", "nonce_changed",
    "run_id_changed", "older_schema", "incomplete_measurement", "broken_json",
    "running_progress_only",
)


def _verdict(run_dir: Path, requested_scope: str, ledger: Path):
    """The ledger's whole judgement of ``run_dir`` through its public entry points."""
    row = verification_ledger.build_row(run_dir, requested_scope=requested_scope)
    row = {key: value for key, value in row.items() if key not in VOLATILE_ROW_KEYS}
    evidence = verification_ledger.full_scope_evidence(row)
    listing = verification_ledger.format_listing(
        ({**row, "recorded_at_utc": "fixed", "recorded_on_host": "fixed"},),
        _head_state(), ledger_path=ledger,
    )
    return json.loads(json.dumps(row, sort_keys=True, default=str)), evidence, listing


def _assert_independent(run_dir: Path, requested_scope: str, tmp_path: Path):
    _with_run_id(run_dir)
    authority = _authority_state(run_dir)
    ledger = tmp_path / "ledger.jsonl"
    _variant("present", run_dir, tmp_path)
    reference = _verdict(run_dir, requested_scope, ledger)
    for name in VARIANTS:
        _variant(name, run_dir, tmp_path)
        assert _verdict(run_dir, requested_scope, ledger) == reference, name
        assert _authority_state(run_dir) == authority, name
    return reference


@pytest.mark.parametrize("scope", ["full_eq", "full_neq"])
def test_a_full_verdict_does_not_depend_on_runtime_receipts(tmp_path, full_run, scope):
    run_dir = full_run(f"run_{scope}", scope=scope)
    row, evidence, listing = _assert_independent(run_dir, scope, tmp_path)
    # The reference is the real thing: a formally published, complete full run.
    assert row["completed_scope"] == "complete"
    assert evidence[0] is not None, evidence
    assert f"{scope}: YES" in listing


def test_a_subset_row_does_not_depend_on_runtime_receipts(tmp_path, subset_run):
    run_dir = subset_run("subset")
    row, _evidence, _listing = _assert_independent(run_dir, "subset", tmp_path)
    assert row["coverage"], row


def test_a_full_run_that_is_not_evidence_stays_not_evidence_whatever_its_receipts(
    tmp_path, full_run,
):
    """The negative verdict is just as independent (here: the run reused its only pair)."""
    reused = f"{EQ_SAMPLE}/f/f_B1_B2.pair-status.json"
    run_dir = full_run("reused", scope="full_eq", census_overrides={
        "verified_skipped_pair_status_paths.txt": [reused],
    })
    row, evidence, listing = _assert_independent(run_dir, "full_eq", tmp_path)
    assert row["completed_scope"] != "complete"
    assert evidence[0] is None and "full_eq: YES" not in listing


# ---------------------------------------------------------------------------
# Control: evidence the ledger does depend on changes the verdict.
# ---------------------------------------------------------------------------


def _break_pair_status(run_dir: Path) -> None:
    _status_paths(run_dir)[0].unlink()


def _break_publication(run_dir: Path) -> None:
    path = run_dir / verification_ledger.PUBLICATION_MANIFEST_FILE
    payload = json.loads(path.read_text(encoding="utf-8"))
    payload["total_pair_jobs"] += 1          # body no longer matches its digest
    path.write_text(json.dumps(payload), encoding="utf-8")


def _break_execution_receipt(run_dir: Path) -> None:
    path = run_dir / verification_ledger.EXECUTION_RECEIPT_FILE
    payload = json.loads(path.read_text(encoding="utf-8"))
    payload["exit_status"] = 2               # the signature no longer covers the body
    path.write_text(json.dumps(payload), encoding="utf-8")


@pytest.mark.parametrize("breaker", [
    _break_pair_status, _break_publication, _break_execution_receipt,
])
def test_the_ledger_does_react_to_the_evidence_it_depends_on(tmp_path, full_run, breaker):
    run_dir = full_run("control", scope="full_eq")
    _with_run_id(run_dir)
    _variant("present", run_dir, tmp_path)
    ledger = tmp_path / "ledger.jsonl"
    before_row, before_evidence, before_listing = _verdict(run_dir, "full_eq", ledger)
    assert before_evidence[0] is not None and "full_eq: YES" in before_listing
    broken = tmp_path / "broken"
    shutil.copytree(run_dir, broken)
    breaker(broken)
    row, evidence, listing = _verdict(broken, "full_eq", ledger)
    assert evidence[0] is None, breaker.__name__
    assert "full_eq: YES" not in listing
    assert (row["coverage"], row["completed_scope"], row["scope_evidence"]) != (
        before_row["coverage"], before_row["completed_scope"], before_row["scope_evidence"],
    ) or evidence != before_evidence
