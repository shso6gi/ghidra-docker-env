#!/usr/bin/env python3
"""Build and verify exact EqBench/NeqBench ERROR-only rerun manifests."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

from scripts.function_tracer_pcode.equivalence.v2.pair_status_authority import (
    find_pair_status_public_key,
    validate_signed_pair_status,
)
from scripts.function_tracer_pcode.validation.result_summary import (
    classify_canonical_log_text,
    classify_log_text,
)
from scripts.function_tracer_pcode.validation.execution_receipt import (
    MATRIX_EXECUTION_RECEIPT_FILE,
    MATRIX_PUBLICATION_MANIFEST_FILE,
    validate_execution_receipt,
    validate_matrix_publication_manifest,
)


FATAL_ERROR_MARKERS = (
    "SolverQueryExecutionReceipt is not JSON serializable",
    "inconclusive comparison authority is not canonical",
    "SAT model does not completely bind declared replay inputs",
    "supervisor projection is not a terminal authority",
)
OPERATIONAL_LOG_NAMES = frozenset({"compile_all.log", "run_stdout.log"})


def _is_operational_log(path: Path) -> bool:
    return path.name in OPERATIONAL_LOG_NAMES or path.name.startswith("compile_")


def _target(root: Path, log: Path, lane: str) -> tuple[str, str, str, str]:
    relative = log.relative_to(root)
    if len(relative.parts) < 3:
        raise ValueError(f"log path has no sample/function hierarchy: {log}")
    function = relative.parent.name
    sample = relative.parent.parent.as_posix()
    stem = log.stem
    prefix = function + "_"
    if not stem.startswith(prefix):
        raise ValueError(f"log name does not join its function directory: {log}")
    pair = stem[len(prefix):]
    if lane == "EQ":
        parts = pair.split("_")
        if len(parts) != 2 or any(not item.startswith("B") for item in parts):
            raise ValueError(f"invalid EqBench pair ID: {pair}")
    elif not pair.startswith("N_B") or "_O_B" not in pair:
        raise ValueError(f"invalid NeqBench pair ID: {pair}")
    return lane, sample, function, pair


def _pair_target_or_none(
    root: Path, log: Path, lane: str,
) -> tuple[str, str, str, str] | None:
    """Distinguish schedulable pair logs from root/compile diagnostics."""

    try:
        return _target(root, log, lane)
    except ValueError:
        return None


def collect(root: Path, lane: str) -> set[tuple[str, str, str, str]]:
    if not root.is_dir():
        return set()
    targets = set()
    for summary in sorted(root.rglob("results_summary.txt")):
        in_error_section = False
        for line in summary.read_text(encoding="utf-8", errors="replace").splitlines():
            stripped = line.strip()
            if stripped == "ERROR pairs:":
                in_error_section = True
                continue
            if in_error_section and stripped.endswith("pairs:"):
                in_error_section = False
                continue
            if not in_error_section:
                continue
            match = re.fullmatch(r"- (B[0-9]+) ↔ (B[0-9]+)", stripped)
            if match is None:
                if stripped.startswith("-"):
                    raise ValueError(f"invalid ERROR pair in {summary}: {stripped}")
                if stripped:
                    in_error_section = False
                continue
            function = summary.parent.name
            pair = (
                f"{match.group(1)}_{match.group(2)}"
                if lane == "EQ"
                else f"N_{match.group(1)}_O_{match.group(2)}"
            )
            log = summary.parent / f"{function}_{pair}.log"
            if not log.is_file():
                raise ValueError(f"ERROR summary points to missing log: {log}")
            targets.add(_target(root, log, lane))
    try:
        result = subprocess.run(
            ["rg", "-l", "-g", "*.log", *sum((["-e", marker] for marker in FATAL_ERROR_MARKERS), []), str(root)],
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        if result.returncode not in {0, 1}:
            raise OSError(result.stderr.strip() or f"rg exited {result.returncode}")
        fatal_logs = {
            Path(line) for line in result.stdout.splitlines()
            if line and not _is_operational_log(Path(line))
        }
    except (FileNotFoundError, OSError):
        fatal_logs = set()
        for log in root.rglob("*.log"):
            if _is_operational_log(log):
                continue
            text = log.read_text(encoding="utf-8", errors="replace")
            if any(marker in text for marker in FATAL_ERROR_MARKERS):
                fatal_logs.add(log)
    for log in fatal_logs:
        target = _pair_target_or_none(root, log, lane)
        if target is not None:
            targets.add(target)
    for log in sorted(root.rglob("*.log")):
        if _is_operational_log(log):
            continue
        if log in fatal_logs:
            continue
        text = log.read_text(encoding="utf-8", errors="replace")
        if classify_log_text(text, matrix_context=True) == "ERROR":
            target = _pair_target_or_none(root, log, lane)
            if target is not None:
                targets.add(target)
    return targets


def read_manifest(path: Path) -> list[tuple[str, str, str, str]]:
    rows = []
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line or line.startswith("#"):
            continue
        fields = tuple(line.split("\t"))
        if len(fields) != 4:
            raise ValueError(f"manifest line {number} does not have four fields")
        rows.append(fields)  # type: ignore[arg-type]
    if len(rows) != len(set(rows)):
        raise ValueError("rerun manifest contains duplicate targets")
    return rows


def sample_filter_regex(
    rows: list[tuple[str, str, str, str]], lane: str,
) -> str:
    """Translate manifest sample identities to each production runner's input."""

    values = sorted({sample for row_lane, sample, _function, _pair in rows
                     if row_lane == lane})
    if not values:
        raise ValueError(f"rerun manifest has no {lane} sample identities")
    alternatives = "|".join(re.escape(value) for value in values)
    if lane == "EQ":
        # EqBench applies its filter to an absolute source path ending in .c.
        return rf"(^|/)({alternatives})[.]c$"
    if lane == "NEQ":
        # NeqBench applies its filter directly to the normalized sample identity.
        return rf"^({alternatives})$"
    raise ValueError(f"unsupported rerun lane: {lane}")


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _expected_status_path(row: tuple[str, str, str, str]) -> str:
    _lane, sample, function, pair = row
    return f"{sample}/{function}/{function}_{pair}.pair-status.json"


def validate_rerun_publication_contract(
    *, rows: list[tuple[str, str, str, str]], publication: dict,
    execution: dict, manifest_digest: str, run_id: str,
) -> tuple[str, str]:
    expected_paths = sorted(_expected_status_path(row) for row in rows)
    expected_command_rows = {
        f"ERROR_RERUN_MANIFEST_SHA256={manifest_digest}",
        f"ERROR_RERUN_RUN_ID={run_id}",
    }
    command = set(execution["command"])
    error_only = "ERROR_ONLY_RERUN=1" in command
    expected_command_rows.add(
        "SKIP_COMPLETED_RESULTS=1" if error_only
        else "SKIP_COMPLETED_RESULTS=0"
    )
    if error_only:
        expected_command_rows.add("ERROR_ONLY_RERUN=1")
    skipped_paths = sorted(publication["verified_skipped_pair_status_paths"])
    if (
        execution["execution_kind"] != "EQBENCH_MATRIX"
        or execution["exit_status"] != 0
        or not expected_command_rows.issubset(command)
        or execution["source_tree_digest_start"]
        != publication["analysis_source_digest_start"]
        or execution["source_tree_digest_end"]
        != publication["analysis_source_digest_end"]
        or execution["analysis_config_digest"]
        != publication["analysis_config_digest"]
        or publication["analysis_source_digest_start"]
        != publication["analysis_source_digest_end"]
        or publication["total_pair_jobs"] != len(rows)
        or publication["total_scheduled_pair_jobs"]
        + publication["total_skipped_pair_jobs"] != len(rows)
        or publication["total_skipped_pair_jobs"] != len(skipped_paths)
        or sorted(publication["expected_pair_status_paths"]) != expected_paths
        or not set(skipped_paths).issubset(expected_paths)
    ):
        raise ValueError("rerun execution receipt does not bind the exact scheduled target set")
    return (
        publication["analysis_source_digest_start"],
        publication["analysis_config_digest"],
    )


def _validate_lane_run(
    root: Path, rows: list[tuple[str, str, str, str]], *,
    manifest_digest: str, run_id: str,
) -> tuple[str, str]:
    public_key = root / "pair-status-verification-key.json"
    receipt_path = root / MATRIX_EXECUTION_RECEIPT_FILE
    publication_path = root / MATRIX_PUBLICATION_MANIFEST_FILE
    execution = validate_execution_receipt(
        json.loads(receipt_path.read_text(encoding="utf-8")),
        public_key_path=public_key,
    )
    publication = json.loads(publication_path.read_text(encoding="utf-8"))
    validate_matrix_publication_manifest(publication)
    if execution["artifact_sha256"].get(MATRIX_PUBLICATION_MANIFEST_FILE) != _sha256(
        publication_path
    ):
        raise ValueError("execution receipt does not seal the matrix publication manifest")
    return validate_rerun_publication_contract(
        rows=rows, publication=publication, execution=execution,
        manifest_digest=manifest_digest, run_id=run_id,
    )


def validate_rerun_pair_outcome(log_text: str, body: dict) -> str:
    """Use signed status as authority and logs only for contradiction checks."""

    signed_outcome = body["canonical_outcome"]
    if signed_outcome == "ERROR":
        raise ValueError("rerun signed outcome remains ERROR")
    if any(marker in log_text for marker in FATAL_ERROR_MARKERS):
        raise ValueError("rerun log retains a known fatal ERROR signature")
    classification = classify_canonical_log_text(log_text, matrix_context=True)
    if classification == "INCOMPLETE" and body["supervisor_status"] == "TIMEOUT":
        # A supervisor can terminate the child before it emits any result JSON or
        # even a plain Result line.  The durable signed TIMEOUT bundle is the
        # terminal authority; any available log result remains a contradiction
        # check only.
        diagnostic = classify_log_text(log_text, matrix_context=True)
        if diagnostic not in {"INCOMPLETE", signed_outcome}:
            raise ValueError(
                "log and signed pair-status outcomes differ: "
                f"{diagnostic} != {signed_outcome}"
            )
        return signed_outcome
    if classification in {"ERROR", "INCOMPLETE"}:
        raise ValueError(f"rerun classification remains {classification}")
    if signed_outcome != classification:
        raise ValueError(
            "log and signed pair-status outcomes differ: "
            f"{classification} != {signed_outcome}"
        )
    return signed_outcome


def expected_pair_execution_identity(
    row: tuple[str, str, str, str],
) -> dict[str, str]:
    """Derive the signed target identity required by one rerun manifest row."""

    lane, sample, function, pair = row
    if lane == "EQ":
        match = re.fullmatch(r"(B[0-9]+)_(B[0-9]+)", pair)
    elif lane == "NEQ":
        match = re.fullmatch(r"(N_B[0-9]+)_(O_B[0-9]+)", pair)
    else:
        raise ValueError(f"unsupported rerun lane: {lane}")
    if match is None:
        raise ValueError(f"invalid {lane} rerun pair identity: {pair}")
    return {
        "sample_identity": sample,
        "output_sample_relative_path": sample,
        "function_name": function,
        "left_binary_id": match.group(1),
        "right_binary_id": match.group(2),
    }


def validate_rerun_pair_target(
    row: tuple[str, str, str, str], body: dict, *,
    source_digest: str, config_digest: str,
) -> None:
    """Join a signed pair target to its exact manifest row and matrix run."""

    target = body["pair_execution_target"]
    expected_identity = expected_pair_execution_identity(row)
    actual_identity = {field: target[field] for field in expected_identity}
    if actual_identity != expected_identity:
        raise ValueError("signed pair execution identity differs from rerun manifest")
    if (
        target["analysis_source_digest"] != source_digest
        or target["analysis_config_digest"] != config_digest
    ):
        raise ValueError("pair status does not join the current rerun receipt")


def verify(path: Path, roots: dict[str, Path], *, run_id: str) -> None:
    failures = []
    rows = read_manifest(path)
    manifest_digest = _sha256(path)
    run_bindings = {}
    for lane in roots:
        lane_rows = [row for row in rows if row[0] == lane]
        if not lane_rows:
            continue
        try:
            run_bindings[lane] = _validate_lane_run(
                roots[lane], lane_rows,
                manifest_digest=manifest_digest, run_id=run_id,
            )
        except Exception as exc:
            failures.append(
                f"{lane}\tRUN_RECEIPT\t{type(exc).__name__}: {exc}"
            )
    for row in rows:
        lane, sample, function, pair = row
        if lane not in run_bindings:
            continue
        root = roots[lane]
        log = root / sample / function / f"{function}_{pair}.log"
        status_path = log.with_suffix(".pair-status.json")
        try:
            log_text = log.read_text(encoding="utf-8", errors="replace")
            payload = json.loads(status_path.read_text(encoding="utf-8"))
            body = validate_signed_pair_status(
                payload,
                public_key_path=find_pair_status_public_key(status_path),
            )
            if body["classification_valid"] is not True:
                raise ValueError("signed classification_valid is not true")
            validate_rerun_pair_outcome(log_text, body)
            source_digest, config_digest = run_bindings[lane]
            validate_rerun_pair_target(
                row, body,
                source_digest=source_digest,
                config_digest=config_digest,
            )
        except Exception as exc:
            failures.append(f"{lane}\t{sample}\t{function}\t{pair}\t{type(exc).__name__}: {exc}")
    if failures:
        raise SystemExit("ERROR-only rerun verification failed:\n" + "\n".join(failures))
    print(f"verified_targets={len(rows)}")
    print("error=0")
    print("incomplete=0")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--eq-root", type=Path, required=True)
    parser.add_argument("--neq-root", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify", type=Path)
    parser.add_argument("--run-id")
    args = parser.parse_args()
    roots = {"EQ": args.eq_root.resolve(), "NEQ": args.neq_root.resolve()}
    if args.verify:
        if not args.run_id:
            parser.error("--run-id is required with --verify")
        verify(args.verify.resolve(), roots, run_id=args.run_id)
        return 0
    if args.output is None:
        parser.error("--output is required when --verify is not used")
    targets = collect(roots["EQ"], "EQ") | collect(roots["NEQ"], "NEQ")
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        "# lane\tsample\tfunction\tpair\n"
        + "".join("\t".join(row) + "\n" for row in sorted(targets)),
        encoding="utf-8",
    )
    print(f"manifest={output}")
    print(f"targets={len(targets)}")
    print(f"eq_targets={sum(row[0] == 'EQ' for row in targets)}")
    print(f"neq_targets={sum(row[0] == 'NEQ' for row in targets)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
