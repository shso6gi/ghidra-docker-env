"""Per-pair runtime receipts: the one schema both matrix runners write.

A runner keeps two files per pair under ``<sample>/<function>/.runtime-metrics``:

``<function>_<left>_<right>.progress.json``
    ``RUNNING`` while the pair executes, ``COMPLETED`` once it is classified.
``<function>_<left>_<right>.runtime.json``
    the ``COMPLETED`` receipt only; this is the file consumers read.

A receipt is diagnostic.  It never feeds a pair status, a canonical result, a
signed artifact or the verification ledger.  What makes it usable as a
measurement is that it belongs to the execution that produced the pair status
next to it: the receipt repeats that status's ``execution_nonce``.  A receipt
left by an earlier execution of the same pair (the runner deletes both files
at the execution boundary, but a run can be cut before it writes again) or one
written before the nonce existed therefore cannot be mistaken for the current
pair's wall clock; ``bound_elapsed_seconds`` refuses it.

The writer, the boundary that removes stale receipts, and the binding check
all live here so the two runners and the consumers share one contract.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
from typing import Any, Mapping, Optional, Sequence


RUNTIME_RECEIPT_SCHEMA = "eqbench-pair-progress-receipt-v2"
RUNTIME_METRICS_DIR = ".runtime-metrics"
PROGRESS_SUFFIX = ".progress.json"
RUNTIME_SUFFIX = ".runtime.json"
STATE_RUNNING = "RUNNING"
STATE_COMPLETED = "COMPLETED"
STATES = (STATE_RUNNING, STATE_COMPLETED)

_NUMBER_FIELDS = (
    "started_at_epoch", "finished_at_epoch", "elapsed_seconds", "max_rss_kb",
    "child_returncode", "timed_command_pid",
)
_INTEGER_FIELDS = (
    "cpu_tokens", "pair_cpu_tokens", "parallel_jobs_requested",
    "parallel_jobs_effective",
)
_TEXT_FIELDS = ("status", "error_kind")


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


def build_receipt(
    *, state: str, function_name: str, left_binary_id: str,
    right_binary_id: str, execution_nonce: str, fields: Mapping[str, str],
) -> Mapping[str, Any]:
    """The receipt body.  ``fields`` holds the runner's raw string values."""
    if state not in STATES:
        raise ValueError(f"runtime receipt state must be one of {STATES}")
    if not all(isinstance(value, str) and value for value in (
        function_name, left_binary_id, right_binary_id, execution_nonce,
    )):
        raise ValueError("runtime receipt identity fields must be non-empty")
    payload: dict[str, Any] = {
        "schema": RUNTIME_RECEIPT_SCHEMA,
        "state": state,
        "function_name": function_name,
        "left_binary_id": left_binary_id,
        "right_binary_id": right_binary_id,
        "execution_nonce": execution_nonce,
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


def bound_elapsed_seconds(
    receipt: Any, *, function_name: str, left_binary_id: str,
    right_binary_id: str, pair_status: Any,
) -> Optional[float]:
    """The receipt's wall clock, or ``None`` when it is not this pair's measurement.

    Usable only when the receipt is a ``COMPLETED`` receipt of this schema for
    this pair (function and both binary ids) and repeats the ``execution_nonce``
    of the pair status it sits next to.  A receipt from another execution, one
    without a nonce, or one next to a status that carries none (an unsigned
    classification diagnostic) is not bound to anything and is refused.
    """
    if not isinstance(receipt, Mapping) or not isinstance(pair_status, Mapping):
        return None
    nonce = receipt.get("execution_nonce")
    seconds = receipt.get("elapsed_seconds")
    if (
        receipt.get("schema") != RUNTIME_RECEIPT_SCHEMA
        or receipt.get("state") != STATE_COMPLETED
        or receipt.get("function_name") != function_name
        or receipt.get("left_binary_id") != left_binary_id
        or receipt.get("right_binary_id") != right_binary_id
        or not isinstance(nonce, str) or not nonce
        or pair_status.get("execution_nonce") != nonce
        or isinstance(seconds, bool) or not isinstance(seconds, (int, float))
    ):
        return None
    return float(seconds)


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
    for name in (*_NUMBER_FIELDS, *_INTEGER_FIELDS, *_TEXT_FIELDS):
        write.add_argument("--" + name.replace("_", "-"), dest=name, default="-")
    args = parser.parse_args(argv)
    fields = {
        name: getattr(args, name)
        for name in (*_NUMBER_FIELDS, *_INTEGER_FIELDS, *_TEXT_FIELDS)
    }
    payload = build_receipt(
        state=args.state, function_name=args.function_name,
        left_binary_id=args.left_binary_id, right_binary_id=args.right_binary_id,
        execution_nonce=args.execution_nonce, fields=fields,
    )
    write_receipt(Path(args.metrics_dir), args.stem, payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
