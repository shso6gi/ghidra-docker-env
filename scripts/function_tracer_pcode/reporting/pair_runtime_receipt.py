"""Per-pair runtime receipts: the one contract both matrix runners and the consumers share.

A runner keeps two files per pair under ``<sample>/<function>/.runtime-metrics``:

``<function>_<left>_<right>.progress.json``
    ``RUNNING`` while the pair executes, ``COMPLETED`` once it is classified.
``<function>_<left>_<right>.runtime.json``
    the ``COMPLETED`` receipt only; this is the file consumers read.

A receipt is diagnostic.  It never feeds a pair status, a canonical result, a
signed artifact or the verification ledger, and failing to write one never
changes a pair's or a run's exit status.

This module owns four things, so the runners and the consumers cannot drift:

**Measurement.**  One execution of a pair is every supervisor invocation the
runner makes for it: the first one and each recovery of a non-terminal
projection.  The runner times each invocation with GNU time into its own usage
file (``RUNTIME_USAGE_TIME_FORMAT``) and hands all of them to the writer.
``aggregate_resource_usage`` sums the wall clock and takes the maximum of the
peak RSS (a peak is not additive), and reports the measurement complete only
if every invocation's file parses; otherwise both values are null.  A recovery
therefore never replaces the first invocation's numbers, and a partial sum is
never presented as the execution's time.

**Binding to the pair status.**  The receipt repeats the ``execution_nonce`` of
the pair status written by the same execution.

**Binding to the run.**  The receipt repeats the ``runtime_run_id`` the runner
wrote into ``run_manifest.txt`` when it started.  A pair the run reused keeps
the status and the receipt of the run that executed it, so its receipt carries
that earlier run's id.

**Acceptance for comparison** (``load_tree_measurements``).  A tree's receipt
is *measured* -- a measurement taken by the run that last wrote the tree -- only
if it is a complete ``COMPLETED`` receipt of this schema for its pair, bound to
the pair status next to it and to the tree's current ``runtime_run_id``, and the
pair is not one that run's own publication lists as reused.  A receipt bound to
its status but to an earlier run is *retained*: a valid measurement of the
result the tree holds, but not of the latest run.  Anything else is
*unusable*.  Comparisons use measured receipts only and report the other two
as counts, so a run that executed nothing never looks like a complete,
zero-delta measurement.

**Chain view** (``load_chain_measurements``, eval plan v2 PR-B).  A tree
finished over several executions holds, for each decided pair, the receipt of
the execution that produced it.  The chain view takes every receipt bound to
its pair status and made by an execution the tree records (its
``.executions`` start record), and reports per execution how many pairs it
measured and how many expected pairs have no such receipt.  A missing
measurement is counted, never read as 0 seconds.  The executions may have run
under different load (another parallel job count is impossible -- it is in the
identity -- but the host was not otherwise controlled), so the chain's times
are a sum of separately taken measurements.  ``load_tree_measurements`` (the
latest run's delta) is unchanged.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import json
import os
from pathlib import Path
import secrets
from typing import Any, Dict, Mapping, Optional, Sequence, Tuple


RUNTIME_RECEIPT_SCHEMA = "eqbench-pair-progress-receipt-v2"
RUNTIME_METRICS_DIR = ".runtime-metrics"
PROGRESS_SUFFIX = ".progress.json"
RUNTIME_SUFFIX = ".runtime.json"
PAIR_STATUS_SUFFIX = ".pair-status.json"
RUN_MANIFEST_FILE = "run_manifest.txt"
RUN_ID_KEY = "runtime_run_id"
STATE_RUNNING = "RUNNING"
STATE_COMPLETED = "COMPLETED"
STATES = (STATE_RUNNING, STATE_COMPLETED)
# The GNU time format the runners use for each supervisor invocation.
RUNTIME_USAGE_TIME_FORMAT = "elapsed_seconds=%e\\nmax_rss_kb=%M"
_USAGE_KEYS = ("elapsed_seconds", "max_rss_kb")

RECEIPT_MEASURED = "measured"
RECEIPT_RETAINED = "retained"
RECEIPT_UNUSABLE = "unusable"

_NUMBER_FIELDS = ("started_at_epoch", "finished_at_epoch", "child_returncode", "timed_command_pid")
_INTEGER_FIELDS = (
    "cpu_tokens", "pair_cpu_tokens", "parallel_jobs_requested",
    "parallel_jobs_effective",
)
_TEXT_FIELDS = ("status", "error_kind")

PairKey = Tuple[str, str, str, str]


def new_run_id() -> str:
    return secrets.token_hex(16)


def receipt_paths(metrics_dir: Path, stem: str) -> tuple[Path, Path]:
    """``(progress, runtime)`` receipt paths of the pair named ``stem``."""
    metrics_dir = Path(metrics_dir)
    return (
        metrics_dir / f"{stem}{PROGRESS_SUFFIX}",
        metrics_dir / f"{stem}{RUNTIME_SUFFIX}",
    )


def _number(value: str) -> Optional[float | int]:
    """Runner placeholders (``""``, ``-``, ``None``) and garbage become null."""
    if value in {"", "-", "None"}:
        return None
    try:
        return float(value) if "." in value else int(value)
    except ValueError:
        return None


def _parse_usage(path: Path) -> Optional[Mapping[str, float]]:
    """One GNU time usage file, or ``None`` if it is missing or not exactly one reading."""
    try:
        lines = Path(path).read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeError):
        return None
    values: Dict[str, float] = {}
    for line in lines:
        key, separator, raw = line.partition("=")
        if not separator or key not in _USAGE_KEYS:
            # GNU time prefixes notes such as "Command exited with non-zero status 1".
            continue
        number = _number(raw.strip())
        if key in values or number is None or number < 0:
            return None
        values[key] = float(number)
    return values if set(values) == set(_USAGE_KEYS) else None


def aggregate_resource_usage(paths: Sequence[Path]) -> Mapping[str, Any]:
    """The execution's measurement from every supervisor invocation's usage file."""
    readings = [_parse_usage(path) for path in paths]
    complete = bool(readings) and all(reading is not None for reading in readings)
    return {
        "supervisor_invocations": len(readings),
        "measurement_complete": complete,
        "elapsed_seconds": (
            round(sum(r["elapsed_seconds"] for r in readings), 6) if complete else None
        ),
        "max_rss_kb": (
            int(max(r["max_rss_kb"] for r in readings)) if complete else None
        ),
    }


def build_receipt(
    *, state: str, function_name: str, left_binary_id: str,
    right_binary_id: str, execution_nonce: str, run_id: str,
    fields: Mapping[str, str], usage_files: Sequence[Path] = (),
) -> Mapping[str, Any]:
    """The receipt body.  ``fields`` holds the runner's raw string values."""
    if state not in STATES:
        raise ValueError(f"runtime receipt state must be one of {STATES}")
    if not all(isinstance(value, str) and value for value in (
        function_name, left_binary_id, right_binary_id, execution_nonce, run_id,
    )):
        raise ValueError("runtime receipt identity fields must be non-empty")
    payload: dict[str, Any] = {
        "schema": RUNTIME_RECEIPT_SCHEMA,
        "state": state,
        "function_name": function_name,
        "left_binary_id": left_binary_id,
        "right_binary_id": right_binary_id,
        "execution_nonce": execution_nonce,
        "run_id": run_id,
        "writer_pid": os.getpid(),
    }
    for name in _NUMBER_FIELDS:
        payload[name] = _number(fields.get(name, "-"))
    for name in _INTEGER_FIELDS:
        value = _number(fields.get(name, "-"))
        payload[name] = value if isinstance(value, int) else None
    for name in _TEXT_FIELDS:
        value = fields.get(name, "-")
        payload[name] = None if value in {"", "-"} else value
    if state == STATE_COMPLETED:
        payload.update(aggregate_resource_usage(usage_files))
    else:
        payload.update({
            "supervisor_invocations": None, "measurement_complete": False,
            "elapsed_seconds": None, "max_rss_kb": None,
        })
    return payload


def _atomic_write_json(path: Path, payload: Mapping[str, Any]) -> None:
    temporary = path.with_name(f"{path.name}.tmp.{os.getpid()}")
    with open(temporary, "w", encoding="utf-8") as handle:
        json.dump(payload, handle, sort_keys=True, separators=(",", ":"))
        handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)


def write_receipt(metrics_dir: Path, stem: str, payload: Mapping[str, Any]) -> None:
    """Write ``progress``; a ``COMPLETED`` receipt is also published as ``runtime``."""
    progress, runtime = receipt_paths(metrics_dir, stem)
    progress.parent.mkdir(parents=True, exist_ok=True)
    _atomic_write_json(progress, payload)
    if payload["state"] == STATE_COMPLETED:
        _atomic_write_json(runtime, payload)


def classify_receipt(
    receipt: Any, *, function_name: str, left_binary_id: str,
    right_binary_id: str, pair_status: Any, run_id: Optional[str],
) -> Tuple[str, Optional[float]]:
    """``(measured | retained | unusable, elapsed seconds)`` of one receipt.

    Bound to the pair status = same pair, ``execution_nonce`` equal to the
    status's (an unsigned classification diagnostic carries none), and a
    complete measurement.  Bound to the run = ``run_id`` equal to the tree's
    current ``runtime_run_id``.  Both make it *measured*; the first alone makes
    it *retained*; anything less is *unusable*.
    """
    if not isinstance(receipt, Mapping) or not isinstance(pair_status, Mapping):
        return RECEIPT_UNUSABLE, None
    nonce = receipt.get("execution_nonce")
    seconds = receipt.get("elapsed_seconds")
    receipt_run = receipt.get("run_id")
    if (
        receipt.get("schema") != RUNTIME_RECEIPT_SCHEMA
        or receipt.get("state") != STATE_COMPLETED
        or receipt.get("measurement_complete") is not True
        or receipt.get("function_name") != function_name
        or receipt.get("left_binary_id") != left_binary_id
        or receipt.get("right_binary_id") != right_binary_id
        or not isinstance(nonce, str) or not nonce
        or pair_status.get("execution_nonce") != nonce
        or not isinstance(receipt_run, str) or not receipt_run
        or isinstance(seconds, bool) or not isinstance(seconds, (int, float))
    ):
        return RECEIPT_UNUSABLE, None
    if run_id is not None and receipt_run == run_id:
        return RECEIPT_MEASURED, float(seconds)
    return RECEIPT_RETAINED, float(seconds)


@dataclass(frozen=True)
class TreeMeasurements:
    """How a result tree's receipts were accepted (see the module docstring)."""

    run_id: Optional[str]
    measured: Dict[PairKey, float] = field(default_factory=dict)
    retained: Tuple[PairKey, ...] = ()
    unusable: int = 0


def _read_json_object(path: Path) -> Optional[Mapping[str, Any]]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    return payload if isinstance(payload, Mapping) else None


def tree_run_id(root: Path) -> Optional[str]:
    """The ``runtime_run_id`` of the run that last wrote ``root``, if it recorded one."""
    try:
        for line in (Path(root) / RUN_MANIFEST_FILE).read_text(encoding="utf-8").splitlines():
            key, separator, value = line.partition("=")
            if separator and key == RUN_ID_KEY and value:
                return value
    except (OSError, UnicodeError):
        return None
    return None


def _latest_run_reused_paths(root: Path) -> frozenset[str]:
    """Pairs the latest run's own publication lists as reused, if it published one.

    The publication is the latest run's only when rebuilding it from the
    tree's current run manifest and censuses reproduces it exactly; a stale
    publication (left by an earlier run, the latest one cut short) says
    nothing about the latest run and is ignored.
    """
    from scripts.function_tracer_pcode.reporting.execution_receipt import (
        MATRIX_PUBLICATION_MANIFEST_FILE,
        build_matrix_publication_manifest,
    )

    stored = _read_json_object(Path(root) / MATRIX_PUBLICATION_MANIFEST_FILE)
    if stored is None:
        return frozenset()
    try:
        rebuilt = build_matrix_publication_manifest(Path(root))
    except (OSError, UnicodeError, KeyError, ValueError):
        return frozenset()
    if rebuilt.get("artifact_digest") != stored.get("artifact_digest"):
        return frozenset()
    return frozenset(rebuilt["verified_skipped_pair_status_paths"])


def load_tree_measurements(root: Path) -> TreeMeasurements:
    """Classify every ``.runtime.json`` under ``root`` against its status and the run."""
    from scripts.function_tracer_pcode.reporting.pair_outcomes import (
        identity_from_status_path,
    )

    root = Path(root)
    run_id = tree_run_id(root)
    reused = _latest_run_reused_paths(root)
    measured: Dict[PairKey, float] = {}
    retained: list[PairKey] = []
    unusable = 0
    for path in sorted(root.rglob(f"*{RUNTIME_SUFFIX}")):
        relative = path.relative_to(root)
        if len(relative.parts) < 4 or relative.parts[-2] != RUNTIME_METRICS_DIR:
            unusable += 1
            continue
        status_path = path.parent.parent / (
            path.name[: -len(RUNTIME_SUFFIX)] + PAIR_STATUS_SUFFIX
        )
        try:
            key = identity_from_status_path(root, status_path)
        except ValueError:
            unusable += 1
            continue
        kind, seconds = classify_receipt(
            _read_json_object(path), function_name=key[1], left_binary_id=key[2],
            right_binary_id=key[3], pair_status=_read_json_object(status_path),
            run_id=run_id,
        )
        if kind == RECEIPT_MEASURED and status_path.relative_to(root).as_posix() in reused:
            # The latest run says it reused this pair, yet the receipt claims
            # that run measured it: the two records disagree, so neither wins.
            kind = RECEIPT_UNUSABLE
        if kind == RECEIPT_MEASURED:
            measured[key] = seconds
        elif kind == RECEIPT_RETAINED:
            retained.append(key)
        else:
            unusable += 1
    return TreeMeasurements(
        run_id=run_id, measured=measured, retained=tuple(retained), unusable=unusable,
    )


@dataclass(frozen=True)
class ChainMeasurements:
    """The chain view of a tree's receipts (see the module docstring)."""

    executions: Tuple[str, ...]
    measured: Dict[PairKey, float] = field(default_factory=dict)
    measured_by_execution: Dict[str, int] = field(default_factory=dict)
    #: Receipts bound to their status but made by an execution the tree does not record.
    unrecorded_execution: int = 0
    unusable: int = 0
    #: Expected pairs (by the tree's publication) with no accepted receipt.
    pairs_without_measurement: Optional[int] = None

    def as_dict(self) -> Dict[str, Any]:
        return {
            "executions": list(self.executions),
            "pairs_measured": len(self.measured),
            "measured_by_execution": dict(sorted(self.measured_by_execution.items())),
            "measured_seconds_total": round(sum(self.measured.values()), 3),
            "receipts_from_unrecorded_execution": self.unrecorded_execution,
            "receipts_unusable": self.unusable,
            "pairs_without_measurement": self.pairs_without_measurement,
        }


def load_chain_measurements(root: Path) -> ChainMeasurements:
    """Every pair's measurement by the execution that produced it, with coverage."""
    from scripts.function_tracer_pcode.reporting import execution_chain
    from scripts.function_tracer_pcode.reporting.pair_outcomes import (
        identity_from_status_path,
    )

    root = Path(root)
    executions, _unrecognised = execution_chain.execution_ids(root)
    recorded = {
        run_id for run_id in executions
        if (root / execution_chain.EXECUTIONS_DIR / run_id / execution_chain.START_RECORD).is_file()
    }
    measured: Dict[PairKey, float] = {}
    by_execution: Dict[str, int] = {run_id: 0 for run_id in sorted(recorded)}
    unrecorded = unusable = 0
    for path in sorted(root.rglob(f"*{RUNTIME_SUFFIX}")):
        relative = path.relative_to(root)
        if len(relative.parts) < 4 or relative.parts[-2] != RUNTIME_METRICS_DIR:
            unusable += 1
            continue
        status_path = path.parent.parent / (
            path.name[: -len(RUNTIME_SUFFIX)] + PAIR_STATUS_SUFFIX
        )
        try:
            key = identity_from_status_path(root, status_path)
        except ValueError:
            unusable += 1
            continue
        receipt = _read_json_object(path)
        kind, seconds = classify_receipt(
            receipt, function_name=key[1], left_binary_id=key[2], right_binary_id=key[3],
            pair_status=_read_json_object(status_path), run_id=None,
        )
        if kind == RECEIPT_UNUSABLE or seconds is None:
            unusable += 1
            continue
        producer = str((receipt or {}).get("run_id"))
        if producer not in recorded:
            unrecorded += 1
            continue
        measured[key] = seconds
        by_execution[producer] += 1
    expected_count: Optional[int] = None
    publication = _read_json_object(root / execution_chain.PUBLICATION_FILE)
    rows = (publication or {}).get("expected_pair_status_paths")
    if isinstance(rows, list):
        expected_count = len(rows) - len(measured)
    return ChainMeasurements(
        executions=tuple(sorted(recorded)), measured=measured,
        measured_by_execution=by_execution, unrecorded_execution=unrecorded,
        unusable=unusable, pairs_without_measurement=expected_count,
    )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    write = sub.add_parser("write", help="write one receipt (runner use)")
    write.add_argument("--metrics-dir", required=True)
    write.add_argument("--stem", required=True)
    write.add_argument("--state", required=True, choices=STATES)
    write.add_argument("--function-name", required=True)
    write.add_argument("--left-binary-id", required=True)
    write.add_argument("--right-binary-id", required=True)
    write.add_argument("--execution-nonce", required=True)
    write.add_argument("--run-id", required=True)
    write.add_argument(
        "--resource-usage", action="append", default=[], type=Path,
        help="GNU time usage file of one supervisor invocation (repeat for each)",
    )
    for name in (*_NUMBER_FIELDS, *_INTEGER_FIELDS, *_TEXT_FIELDS):
        write.add_argument("--" + name.replace("_", "-"), dest=name, default="-")
    sub.add_parser("new-run-id", help="print a fresh runtime_run_id (runner use)")
    chain = sub.add_parser(
        "chain-coverage", help="per-execution measurement coverage of a resumed tree",
    )
    chain.add_argument("--root", required=True)
    args = parser.parse_args(argv)
    if args.command == "new-run-id":
        print(new_run_id())
        return 0
    if args.command == "chain-coverage":
        print(json.dumps(load_chain_measurements(Path(args.root)).as_dict(), indent=2))
        return 0
    fields = {
        name: getattr(args, name)
        for name in (*_NUMBER_FIELDS, *_INTEGER_FIELDS, *_TEXT_FIELDS)
    }
    payload = build_receipt(
        state=args.state, function_name=args.function_name,
        left_binary_id=args.left_binary_id, right_binary_id=args.right_binary_id,
        execution_nonce=args.execution_nonce, run_id=args.run_id, fields=fields,
        usage_files=args.resource_usage,
    )
    write_receipt(Path(args.metrics_dir), args.stem, payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
