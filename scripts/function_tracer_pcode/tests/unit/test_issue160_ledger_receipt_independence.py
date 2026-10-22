"""Issue #160 AC5: the verification ledger does not depend on runtime receipts.

Runtime receipts (``.runtime-metrics/<pair>.{progress,runtime}.json``) are
diagnostic.  The ledger's verdict -- the row with its coverage, completed scope
and scope health, the full-scope evidence and the listing -- comes from the
formal publication, the signed execution receipt, the run manifest and the
pair statuses only.  This module pins that as behaviour on the ledger's public
entry points (``build_row`` / ``full_scope_evidence`` / ``format_listing``).

It keeps four responsibilities apart, because a receipt that only *looks*
valid would make the comparison vacuous:

1. **Fixture preparation** -- the ledger's own formal fixtures, built with the
   identities a real run has: every pair status carries its
   ``execution_nonce`` and every tree's run manifest its ``runtime_run_id``,
   both before the publication is built and the execution receipt sealed.
   The authority snapshot is taken only after that.
2. **Receipt operations** -- receipts are written by the production writer
   from the prepared identity (a status without a nonce is a fixture contract
   violation and fails at once; nothing is filled in), and every variant
   touches ``.runtime-metrics`` only.
3. **Precondition** -- before the ledger is compared, the formal consumer
   (``pair_runtime_receipt.load_tree_measurements``) must classify each
   variant as intended: *measured* for a receipt of the tree's latest run,
   *retained* for one an earlier run left on a reused pair, *unusable* or
   *missing* for the broken states.  So the variants really cover usable,
   reused and unusable receipts.
4. **Ledger comparison** -- for every variant the ledger's whole judgement is
   identical to the baseline's, and the authority artifacts are unchanged.
   The control breaks evidence the ledger does use and sees the verdict move.
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
    NEQ_SAMPLE,
    _head_state,
    full_run,
    subset_run,
)

CURRENT_RUN = "run-current"
EARLIER_RUN = "run-earlier"
VOLATILE_ROW_KEYS = ("recorded_at_utc", "recorded_on_host")
FRESH, REUSED = "fresh", "reused"


# ---------------------------------------------------------------------------
# 1. Fixture preparation (authority first, then the snapshot)
# ---------------------------------------------------------------------------


def _prepare_full(full_run, scope, mode):
    """A formal full run of one pair whose identities a receipt can bind to.

    ``reused``: the run's own publication lists the pair as reused, as a resumed
    run that skipped it would; the ledger then does not count it as executed.
    """
    sample = EQ_SAMPLE if scope == "full_eq" else NEQ_SAMPLE
    census = {}
    if mode == REUSED:
        census = {"verified_skipped_pair_status_paths.txt": [f"{sample}/f/f_B1_B2.pair-status.json"]}
    run_dir = full_run(
        f"{scope}_{mode}", scope=scope, execution_nonces=True,
        run_manifest_overrides={"runtime_run_id": CURRENT_RUN}, census_overrides=census,
    )
    return run_dir, [run_dir]


def _prepare_subset(subset_run, mode):
    """A subset run whose eq and neq halves are separate trees."""
    skipped = ()
    if mode == REUSED:
        skipped = {
            "eq": [f"{EQ_SAMPLE}/f/f_B1_B2.pair-status.json"],
            "neq": [f"{NEQ_SAMPLE}/g/g_N_B1_O_B1.pair-status.json"],
        }
    run_dir = subset_run(
        f"subset_{mode}", execution_nonces=True, runtime_run_id=CURRENT_RUN, skipped=skipped,
    )
    return run_dir, [run_dir / "eq", run_dir / "neq"]


def _authority_state(run_dir: Path):
    """Every file of the run except the runtime receipts, with its content hash."""
    return sorted(
        (path.relative_to(run_dir).as_posix(), hashlib.sha256(path.read_bytes()).hexdigest())
        for path in run_dir.rglob("*")
        if path.is_file() and rr.RUNTIME_METRICS_DIR not in path.parts
    )


# ---------------------------------------------------------------------------
# 2. Receipt operations (``.runtime-metrics`` only)
# ---------------------------------------------------------------------------


def _status_paths(tree: Path):
    return sorted(tree.rglob("*.pair-status.json"))


def _write_receipt(status_path: Path, usage: Path, *, run_id: str) -> None:
    """The production writer's COMPLETED receipt for the execution behind ``status_path``.

    The nonce comes from the status, never from here: a status without one is
    a fixture that does not describe a real execution, and the test stops.
    """
    status = json.loads(status_path.read_text(encoding="utf-8"))
    assert status.get("execution_nonce"), (
        f"fixture contract: {status_path.name} has no execution_nonce to bind a receipt to"
    )
    target = status["pair_execution_target"]
    assert rr.main([
        "write", "--state", "COMPLETED",
        "--metrics-dir", str(status_path.parent / rr.RUNTIME_METRICS_DIR),
        "--stem", status_path.name[: -len(".pair-status.json")],
        "--function-name", target["function_name"],
        "--left-binary-id", target["left_binary_id"],
        "--right-binary-id", target["right_binary_id"],
        "--execution-nonce", status["execution_nonce"],
        "--run-id", run_id, "--resource-usage", str(usage),
        "--status", status["canonical_outcome"],
    ]) == 0


def _receipts(trees):
    for tree in trees:
        yield from (path for path in tree.rglob("*")
                    if path.is_file() and rr.RUNTIME_METRICS_DIR in path.parts)


def _write_baseline(trees, tmp_path: Path, mode: str) -> None:
    """Fresh: written by the tree's latest run.  Reused: left by an earlier run."""
    usage = tmp_path / "usage.txt"
    usage.write_text("elapsed_seconds=12.5\nmax_rss_kb=4096\n", encoding="utf-8")
    for tree in trees:
        for directory in list(tree.rglob(rr.RUNTIME_METRICS_DIR)):
            shutil.rmtree(directory)
        for status_path in _status_paths(tree):
            _write_receipt(status_path, usage,
                           run_id=CURRENT_RUN if mode == FRESH else EARLIER_RUN)


def _edit(trees, **changes):
    for path in _receipts(trees):
        payload = json.loads(path.read_text(encoding="utf-8"))
        payload.update(changes)
        path.write_text(json.dumps(payload), encoding="utf-8")


def _other_run(mode):
    return EARLIER_RUN if mode == FRESH else CURRENT_RUN


def _apply(variant, trees, mode):
    if variant == "baseline":
        return
    if variant == "absent":
        for path in list(_receipts(trees)):
            path.unlink()
    elif variant == "measured_values_changed":
        _edit(trees, elapsed_seconds=99999.0, max_rss_kb=1, supervisor_invocations=7)
    elif variant == "nonce_changed":
        _edit(trees, execution_nonce="another-execution")
    elif variant == "run_id_changed":
        _edit(trees, run_id=_other_run(mode))
    elif variant == "older_schema":
        _edit(trees, schema="eqbench-pair-progress-receipt-v1")
    elif variant == "incomplete_measurement":
        _edit(trees, measurement_complete=False, elapsed_seconds=None)
    elif variant == "broken_json":
        for path in _receipts(trees):
            path.write_text("{not json", encoding="utf-8")
    elif variant == "running_progress_only":
        for path in list(_receipts(trees)):
            if path.name.endswith(rr.RUNTIME_SUFFIX):
                path.unlink()
        _edit(trees, state="RUNNING", elapsed_seconds=None)
    else:
        raise AssertionError(variant)


# ---------------------------------------------------------------------------
# 3. Precondition: what the formal consumer makes of each variant
# ---------------------------------------------------------------------------

VARIANTS = (
    "baseline", "absent", "measured_values_changed", "nonce_changed",
    "run_id_changed", "older_schema", "incomplete_measurement", "broken_json",
    "running_progress_only",
)


def _expected_kind(variant, mode, *, formal_publication):
    """The class every pair's receipt must have under ``variant``."""
    baseline = "measured" if mode == FRESH else "retained"
    if variant in ("baseline", "measured_values_changed"):
        return baseline
    if variant in ("absent", "running_progress_only"):
        return "missing"
    if variant == "run_id_changed":
        if mode == FRESH:
            return "retained"
        # The receipt now claims the latest run measured the pair.  A formal
        # publication of that run says it reused it, so the claim is refused;
        # without one the consumer has nothing to contradict it with.
        return "unusable" if formal_publication else "measured"
    return "unusable"


def _observed(tree: Path):
    measurements = rr.load_tree_measurements(tree)
    statuses = _status_paths(tree)
    missing = sum(
        1 for path in statuses
        if not (path.parent / rr.RUNTIME_METRICS_DIR
                / (path.name[: -len(".pair-status.json")] + rr.RUNTIME_SUFFIX)).is_file()
    )
    return {
        "measured": len(measurements.measured), "retained": len(measurements.retained),
        "unusable": measurements.unusable, "missing": missing,
    }, len(statuses)


def _assert_precondition(trees, variant, mode, *, formal_publication):
    kind = _expected_kind(variant, mode, formal_publication=formal_publication)
    for tree in trees:
        observed, pairs = _observed(tree)
        expected = {name: 0 for name in observed}
        expected[kind] = pairs
        assert pairs > 0 and observed == expected, (
            f"FIXTURE PRECONDITION ({mode}/{variant}, {tree.name}): the receipts are not "
            f"in the state the variant names: {observed} != {expected}"
        )


# ---------------------------------------------------------------------------
# 4. Ledger comparison
# ---------------------------------------------------------------------------


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


def _assert_independent(run_dir, trees, requested_scope, mode, tmp_path, *, formal_publication):
    authority = _authority_state(run_dir)
    ledger = tmp_path / "ledger.jsonl"
    _write_baseline(trees, tmp_path, mode)
    _assert_precondition(trees, "baseline", mode, formal_publication=formal_publication)
    reference = _verdict(run_dir, requested_scope, ledger)
    for variant in VARIANTS:
        _write_baseline(trees, tmp_path, mode)
        _apply(variant, trees, mode)
        _assert_precondition(trees, variant, mode, formal_publication=formal_publication)
        assert _verdict(run_dir, requested_scope, ledger) == reference, (
            f"LEDGER DEPENDS ON RUNTIME RECEIPTS ({mode}/{variant})"
        )
        assert _authority_state(run_dir) == authority, f"authority changed ({mode}/{variant})"
    return reference


@pytest.mark.parametrize("scope", ["full_eq", "full_neq"])
def test_a_full_yes_does_not_depend_on_runtime_receipts(tmp_path, full_run, scope):
    run_dir, trees = _prepare_full(full_run, scope, FRESH)
    row, evidence, listing = _assert_independent(
        run_dir, trees, scope, FRESH, tmp_path, formal_publication=True)
    assert row["completed_scope"] == "complete"
    assert evidence[0] is not None, evidence
    assert f"{scope}: YES" in listing


@pytest.mark.parametrize("scope", ["full_eq", "full_neq"])
def test_a_full_no_does_not_depend_on_runtime_receipts(tmp_path, full_run, scope):
    """A run that reused its pair is not evidence, whatever its retained receipts say."""
    run_dir, trees = _prepare_full(full_run, scope, REUSED)
    row, evidence, listing = _assert_independent(
        run_dir, trees, scope, REUSED, tmp_path, formal_publication=True)
    assert row["completed_scope"] != "complete"
    assert evidence[0] is None and f"{scope}: YES" not in listing


@pytest.mark.parametrize("mode", [FRESH, REUSED])
def test_a_subset_row_does_not_depend_on_runtime_receipts(tmp_path, subset_run, mode):
    run_dir, trees = _prepare_subset(subset_run, mode)
    row, _evidence, _listing = _assert_independent(
        run_dir, trees, "subset", mode, tmp_path, formal_publication=False)
    assert row["coverage"], row
    if mode == FRESH:
        assert row["completed_scope"] == "complete"
    else:
        assert row["completed_scope"] != "complete"


def test_a_receipt_needs_the_identity_the_fixture_prepared(tmp_path, full_run):
    """No fallback: a status without an execution nonce cannot get a receipt."""
    run_dir = full_run("no_nonce", scope="full_eq")
    with pytest.raises(AssertionError, match="fixture contract"):
        _write_baseline([run_dir], tmp_path, FRESH)


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
    run_dir, trees = _prepare_full(full_run, "full_eq", FRESH)
    _write_baseline(trees, tmp_path, FRESH)
    _assert_precondition(trees, "baseline", FRESH, formal_publication=True)
    ledger = tmp_path / "ledger.jsonl"
    _before_row, before_evidence, before_listing = _verdict(run_dir, "full_eq", ledger)
    assert before_evidence[0] is not None and "full_eq: YES" in before_listing
    broken = tmp_path / "broken"
    shutil.copytree(run_dir, broken)
    breaker(broken)
    _row, evidence, listing = _verdict(broken, "full_eq", ledger)
    assert evidence[0] is None, breaker.__name__
    assert "full_eq: YES" not in listing
