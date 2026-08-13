"""Signed, current-source-bound validation execution receipts."""

from __future__ import annotations

import argparse
import base64
import json
from pathlib import Path
import re
import subprocess
from typing import Any, Mapping, Sequence

from ..equivalence.v2.contracts import authority_digest
from ..equivalence.v2.pair_status_authority import (
    load_pair_status_public_key,
    validate_pair_status_keypair,
)
from .execution_identity import sha256_file, source_tree_digest


EXECUTION_RECEIPT_SCHEMA = "phase10-validation-execution-receipt-v1"
EXECUTION_RECEIPT_KIND = "Phase10ValidationExecutionReceipt"
MATRIX_EXECUTION_RECEIPT_FILE = "validation-execution-receipt.json"
MATRIX_PUBLICATION_MANIFEST_FILE = "matrix-publication-manifest.json"
MATRIX_PUBLICATION_SCHEMA = "eqbench-matrix-publication-manifest-v3"
SEAL_FIELDS = frozenset({"body_digest", "signature"})
BODY_FIELDS = frozenset({
    "schema", "authority_kind", "execution_kind", "command",
    "source_tree_digest_start", "source_tree_digest_end",
    "analysis_config_digest", "exit_status", "artifact_sha256",
    "signing_key_id",
})
MATRIX_PUBLICATION_FIELDS = frozenset({
    "schema", "authority_kind", "run_scope", "analysis_config",
    "prefilter_source_count",
    "prefilter_source_census_digest", "prefilter_source_paths",
    "target_sources", "completed_samples",
    "skipped_samples", "dry_run", "total_functions", "total_pair_jobs",
    "total_scheduled_pair_jobs", "total_skipped_pair_jobs",
    "expected_pairs_per_function", "expected_binary_count",
    "compiled_binary_count", "compile_failure_count",
    "missing_binary_count", "compile_failure_samples",
    "missing_binary_axes", "function_census_failure_count",
    "function_census_failures", "run_pair_failures", "analysis_source_digest_start",
    "analysis_source_digest_end", "analysis_config_digest",
    "build_receipts", "expected_pair_status_paths",
    "verified_skipped_pair_status_paths", "artifact_digest",
})
ANALYSIS_CONFIG_V1_FIELDS = frozenset({
    "schema", "authority_kind", "run_scope", "build_policy", "max_samples",
    "sample_filter", "pair_filter", "debug", "skip_completed_results",
    "dry_run",
    "parallel_jobs", "validation_summary_level", "equiv_timeout_seconds",
    "decompile_timeout_seconds", "pairwise_timeout_seconds",
    "pairwise_timeout_hard_seconds", "pair_process_timeout_seconds",
    "pair_process_kill_after_seconds", "prefilter_source_census_digest",
})
ANALYSIS_CONFIG_V2_FIELDS = ANALYSIS_CONFIG_V1_FIELDS - {"skip_completed_results"}
MATRIX_RUN_SCOPES = frozenset({"REPRESENTATIVE", "FULL_EQBENCH", "FULL_NEQ"})


def analysis_config_from_run(run: Mapping[str, str]) -> Mapping[str, Any]:
    try:
        config = {
            "schema": "eqbench-analysis-config-v2",
            "authority_kind": "EqBenchAnalysisConfig",
            "run_scope": run["run_scope"],
            "build_policy": run["build_policy"],
            "max_samples": int(run["max_samples"]),
            "sample_filter": run["sample_filter"],
            "pair_filter": run["pair_filter"],
            "debug": bool(int(run["debug"])),
            "dry_run": bool(int(run["dry_run"])),
            "parallel_jobs": int(run["parallel_jobs"]),
            "validation_summary_level": run["validation_summary_level"],
            "equiv_timeout_seconds": run["equiv_timeout"],
            "decompile_timeout_seconds": run["decompile_timeout"],
            "pairwise_timeout_seconds": run["pairwise_timeout"],
            "pairwise_timeout_hard_seconds": run["pairwise_timeout_hard"],
            "pair_process_timeout_seconds": run["pair_process_timeout_seconds"],
            "pair_process_kill_after_seconds": run["pair_process_kill_after_seconds"],
            "prefilter_source_census_digest": run["prefilter_source_census_digest"],
        }
    except (KeyError, ValueError) as exc:
        raise ValueError("matrix run manifest lacks typed analysis config") from exc
    validate_analysis_config(config)
    return config


def validate_analysis_config(config: Mapping[str, Any]) -> None:
    timeout_fields = (
        "equiv_timeout_seconds", "decompile_timeout_seconds",
        "pairwise_timeout_seconds", "pairwise_timeout_hard_seconds",
        "pair_process_timeout_seconds", "pair_process_kill_after_seconds",
    )
    if not isinstance(config, Mapping):
        raise ValueError("EqBench typed analysis config is invalid")
    expected_fields = {
        "eqbench-analysis-config-v1": ANALYSIS_CONFIG_V1_FIELDS,
        "eqbench-analysis-config-v2": ANALYSIS_CONFIG_V2_FIELDS,
    }.get(config.get("schema"))
    bool_fields = {"debug", "dry_run"}
    if config.get("schema") == "eqbench-analysis-config-v1":
        bool_fields.add("skip_completed_results")
    if (
        expected_fields is None or set(config) != expected_fields
        or config["authority_kind"] != "EqBenchAnalysisConfig"
        or config["run_scope"] not in MATRIX_RUN_SCOPES
        or config["build_policy"] not in {
            "REUSE_OR_COMPILE", "PREBUILT_ONLY", "FRESH_ONLY",
        }
        or type(config["max_samples"]) is not int or config["max_samples"] < 0
        or type(config["parallel_jobs"]) is not int or config["parallel_jobs"] < 1
        or any(type(config[field]) is not bool for field in bool_fields)
        or any(type(config[field]) is not str for field in expected_fields - {
            "max_samples", "parallel_jobs", *bool_fields,
        })
        or any(not re.fullmatch(r"[0-9]+(?:\.[0-9]+)?", config[field])
               for field in timeout_fields)
    ):
        raise ValueError("EqBench typed analysis config is invalid")


def normalize_semantic_analysis_config(config: Mapping[str, Any]) -> Mapping[str, Any]:
    """Project historical v1 config onto the scheduling-free v2 authority."""

    validate_analysis_config(config)
    if config["schema"] == "eqbench-analysis-config-v2":
        return dict(config)
    normalized = {
        key: value for key, value in config.items()
        if key != "skip_completed_results"
    }
    normalized["schema"] = "eqbench-analysis-config-v2"
    validate_analysis_config(normalized)
    return normalized


def _legacy_analysis_config_from_run(run: Mapping[str, str]) -> Mapping[str, Any]:
    """Reconstruct the v1 config sealed by pre-v2 matrix runs.

    ``skip_completed_results`` was part of the v1 digest even though it is a
    scheduling policy rather than semantic analysis configuration.  Keep this
    parser private so new runs continue to use the v2 identity while old
    manifests can still be published and then normalized by resume checks.
    """

    config = dict(analysis_config_from_run(run))
    try:
        config["schema"] = "eqbench-analysis-config-v1"
        config["skip_completed_results"] = bool(int(run["skip_completed_results"]))
    except (KeyError, ValueError) as exc:
        raise ValueError("legacy matrix run manifest lacks typed analysis config") from exc
    validate_analysis_config(config)
    return config


def _read_key_values(path: Path) -> Mapping[str, str]:
    values: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line or "=" not in line:
            raise ValueError("matrix run manifest contains a malformed row")
        key, value = line.split("=", 1)
        if not key or key in values:
            raise ValueError("matrix run manifest fields differ")
        values[key] = value
    return values


def _read_census(path: Path) -> list[str]:
    rows = path.read_text(encoding="utf-8").splitlines()
    if len(rows) != len(set(rows)) or any(
        not row.endswith(".pair-status.json")
        or Path(row).is_absolute() or ".." in Path(row).parts
        for row in rows
    ):
        raise ValueError(f"matrix pair-status census is invalid: {path}")
    return rows


def _read_unique_rows(path: Path) -> list[str]:
    rows = path.read_text(encoding="utf-8").splitlines()
    if len(rows) != len(set(rows)) or any(not row for row in rows):
        raise ValueError(f"matrix authority census is invalid: {path}")
    return rows


def _source_census_digest(rows: Sequence[str]) -> str:
    import hashlib
    return hashlib.sha256(("\n".join(rows) + "\n").encode("utf-8")).hexdigest()


def build_matrix_publication_manifest(matrix_root: Path) -> Mapping[str, Any]:
    """Replace diagnostic TXT/log inputs with one exact canonical JSON body."""
    run = _read_key_values(matrix_root / "run_manifest.txt")
    integer_fields = (
        "prefilter_source_count", "target_sources",
        "completed_samples", "skipped_samples", "dry_run",
        "total_functions", "total_pair_jobs", "total_scheduled_pair_jobs",
        "total_skipped_pair_jobs", "expected_pairs_per_function",
        "expected_binary_count", "compiled_binary_count",
        "compile_failure_count", "missing_binary_count",
        "function_census_failure_count", "run_pair_failures",
    )
    try:
        integers = {field: int(run[field]) for field in integer_fields}
        strings = {field: run[field] for field in (
            "analysis_source_digest_start", "analysis_source_digest_end",
            "analysis_config_digest", "run_scope", "prefilter_source_census_digest",
        )}
    except (KeyError, ValueError) as exc:
        raise ValueError("matrix run manifest lacks canonical publication fields") from exc
    analysis_config = analysis_config_from_run(run)
    if run["analysis_config_digest"] != authority_digest(analysis_config):
        # A v1 publication is still a valid authority artifact.  Accept it
        # only when the stored digest exactly matches the reconstructed v1
        # object; never silently replace a mismatched digest.
        analysis_config = _legacy_analysis_config_from_run(run)
        if run["analysis_config_digest"] != authority_digest(analysis_config):
            raise ValueError("matrix analysis config digest differs")
    build_receipts = [
        json.loads(line) for line in
        (matrix_root / "used_build_receipts.jsonl").read_text(encoding="utf-8").splitlines()
    ]
    body = {
        "schema": MATRIX_PUBLICATION_SCHEMA,
        "authority_kind": "EqBenchMatrixPublicationManifest",
        **integers,
        **strings,
        "analysis_config": analysis_config,
        "build_receipts": build_receipts,
        "prefilter_source_paths": _read_unique_rows(
            matrix_root / "prefilter_source_paths.txt"
        ),
        "compile_failure_samples": _read_unique_rows(
            matrix_root / "compile_failure_samples.txt"
        ),
        "missing_binary_axes": _read_unique_rows(
            matrix_root / "missing_binary_axes.txt"
        ),
        "function_census_failures": _read_unique_rows(
            matrix_root / "function_census_failures.txt"
        ),
        "expected_pair_status_paths": _read_census(
            matrix_root / "expected_pair_status_paths.txt"
        ),
        "verified_skipped_pair_status_paths": _read_census(
            matrix_root / "verified_skipped_pair_status_paths.txt"
        ),
    }
    if body["prefilter_source_count"] != len(body["prefilter_source_paths"]):
        raise ValueError("matrix prefilter source count differs")
    if body["prefilter_source_census_digest"] != _source_census_digest(
        body["prefilter_source_paths"]
    ):
        raise ValueError("matrix prefilter source census digest differs")
    return {**body, "artifact_digest": authority_digest(body)}


def validate_matrix_publication_manifest(payload: Mapping[str, Any]) -> Mapping[str, Any]:
    if not isinstance(payload, Mapping) or set(payload) != MATRIX_PUBLICATION_FIELDS:
        raise ValueError("matrix publication manifest schema differs")
    body = {key: payload[key] for key in MATRIX_PUBLICATION_FIELDS - {"artifact_digest"}}
    integer_fields = (
        "prefilter_source_count", "target_sources",
        "completed_samples", "skipped_samples", "dry_run",
        "total_functions", "total_pair_jobs", "total_scheduled_pair_jobs",
        "total_skipped_pair_jobs", "expected_pairs_per_function",
        "expected_binary_count", "compiled_binary_count",
        "compile_failure_count", "missing_binary_count",
        "function_census_failure_count", "run_pair_failures",
    )
    census_fields = (
        "prefilter_source_paths", "compile_failure_samples",
        "missing_binary_axes", "function_census_failures",
        "expected_pair_status_paths",
        "verified_skipped_pair_status_paths",
    )
    if (
        payload["schema"] != MATRIX_PUBLICATION_SCHEMA
        or payload["authority_kind"] != "EqBenchMatrixPublicationManifest"
        or any(type(payload[field]) is not int or payload[field] < 0 for field in integer_fields)
        or any(type(payload[field]) is not str for field in (
            "analysis_source_digest_start", "analysis_source_digest_end",
            "analysis_config_digest", "run_scope", "prefilter_source_census_digest",
        ))
        or any(type(payload[field]) is not list for field in census_fields)
        or any(len(payload[field]) != len(set(payload[field])) for field in census_fields)
        or payload["run_scope"] not in MATRIX_RUN_SCOPES
        or type(payload["build_receipts"]) is not list
        or not isinstance(payload["analysis_config"], Mapping)
        or payload["prefilter_source_count"] != len(payload["prefilter_source_paths"])
        or payload["prefilter_source_census_digest"] != _source_census_digest(
            payload["prefilter_source_paths"]
        )
        or payload["compile_failure_count"] != len(payload["compile_failure_samples"])
        or payload["missing_binary_count"] != len(payload["missing_binary_axes"])
        or payload["function_census_failure_count"]
        != len(payload["function_census_failures"])
        or payload["run_scope"] != payload["analysis_config"].get("run_scope")
        or payload["analysis_config_digest"] != authority_digest(payload["analysis_config"])
        or payload["artifact_digest"] != authority_digest(body)
    ):
        raise ValueError("matrix publication manifest body is invalid")
    validate_analysis_config(payload["analysis_config"])
    return body


def _sign(body: Mapping[str, Any], private_key_path: Path) -> str:
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
    key = Ed25519PrivateKey.from_private_bytes(private_key_path.read_bytes())
    return base64.b64encode(
        key.sign(bytes.fromhex(authority_digest(body)))
    ).decode("ascii")


def seal_execution_receipt(
    *, execution_kind: str, command: Sequence[str], source_digest_start: str,
    source_digest_end: str, analysis_config_digest: str, exit_status: int,
    artifacts: Mapping[str, str], private_key_path: Path, public_key_path: Path,
) -> Mapping[str, Any]:
    public, _ = load_pair_status_public_key(public_key_path)
    validate_pair_status_keypair(private_key_path, public_key_path)
    body = {
        "schema": EXECUTION_RECEIPT_SCHEMA,
        "authority_kind": EXECUTION_RECEIPT_KIND,
        "execution_kind": execution_kind,
        "command": list(command),
        "source_tree_digest_start": source_digest_start,
        "source_tree_digest_end": source_digest_end,
        "analysis_config_digest": analysis_config_digest,
        "exit_status": exit_status,
        "artifact_sha256": dict(sorted(artifacts.items())),
        "signing_key_id": public["key_id"],
    }
    if source_digest_start != source_digest_end:
        raise ValueError("validation source changed during execution")
    digest = authority_digest(body)
    return {**body, "body_digest": digest, "signature": _sign(body, private_key_path)}


def validate_execution_receipt(
    payload: Mapping[str, Any], *, public_key_path: Path,
) -> Mapping[str, Any]:
    if not isinstance(payload, Mapping) or set(payload) != BODY_FIELDS | SEAL_FIELDS:
        raise ValueError("validation execution receipt schema differs")
    body = {key: payload[key] for key in BODY_FIELDS}
    if (
        body["schema"] != EXECUTION_RECEIPT_SCHEMA
        or body["authority_kind"] != EXECUTION_RECEIPT_KIND
        or type(body["command"]) is not list
        or not body["command"]
        or any(type(item) is not str or not item for item in body["command"])
        or type(body["artifact_sha256"]) is not dict
        or type(body["exit_status"]) is not int
        or body["source_tree_digest_start"] != body["source_tree_digest_end"]
        or payload["body_digest"] != authority_digest(body)
    ):
        raise ValueError("validation execution receipt body is invalid")
    public, key = load_pair_status_public_key(public_key_path)
    if body["signing_key_id"] != public["key_id"]:
        raise ValueError("validation execution receipt key differs")
    try:
        signature = base64.b64decode(payload["signature"], validate=True)
        key.verify(signature, bytes.fromhex(payload["body_digest"]))
    except Exception as exc:
        raise ValueError("validation execution receipt signature is invalid") from exc
    return body


def compatible_published_analysis_identity(
    matrix_root: Path, *, current_config: Mapping[str, Any],
    current_source_digest: str,
) -> tuple[str, str] | None:
    """Authorize a signed prior run for pair-level cross-checkout reuse.

    The publication/receipt authenticates the historical config and source
    digests.  Pair-level validation still compares every concrete source and
    binary hash, so changing the checkout does not authorize reusing a result
    for different benchmark inputs.  ``current_source_digest`` is retained in
    the API for callers that want to report the migration boundary; it is not
    required to equal the historical digest for this explicitly signed resume
    compatibility path.
    """

    publication_path = matrix_root / MATRIX_PUBLICATION_MANIFEST_FILE
    receipt_path = matrix_root / MATRIX_EXECUTION_RECEIPT_FILE
    public_key_path = matrix_root / "pair-status-verification-key.json"
    if not all(path.is_file() for path in (
        publication_path, receipt_path, public_key_path,
    )):
        return None
    try:
        publication = validate_matrix_publication_manifest(json.loads(
            publication_path.read_text(encoding="utf-8")
        ))
        receipt = validate_execution_receipt(
            json.loads(receipt_path.read_text(encoding="utf-8")),
            public_key_path=public_key_path,
        )
        legacy_config = publication["analysis_config"]
        config_schema = legacy_config["schema"]
        if (
            config_schema not in {
                "eqbench-analysis-config-v1", "eqbench-analysis-config-v2",
            }
            or normalize_semantic_analysis_config(legacy_config) != current_config
            or receipt["execution_kind"] != "EQBENCH_MATRIX"
            or receipt["exit_status"] not in {0, 1}
            or receipt["analysis_config_digest"]
            != publication["analysis_config_digest"]
            or receipt["artifact_sha256"].get(MATRIX_PUBLICATION_MANIFEST_FILE)
            != sha256_file(publication_path)
            or receipt["source_tree_digest_start"]
            != publication["analysis_source_digest_start"]
            or receipt["source_tree_digest_end"]
            != publication["analysis_source_digest_end"]
        ):
            return None
        return (
            str(publication["analysis_config_digest"]),
            str(publication["analysis_source_digest_start"]),
        )
    except (OSError, UnicodeError, json.JSONDecodeError, KeyError, ValueError):
        return None


# Kept as a compatibility alias for callers and stored validation scripts
# created before cross-checkout resume was generalized.
compatible_legacy_analysis_identity = compatible_published_analysis_identity


def _write(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--private-key")
    parser.add_argument("--public-key")
    parser.add_argument("--output")
    parser.add_argument("--run-manifest")
    parser.add_argument("--print-analysis-config-digest", action="store_true")
    parser.add_argument("--resume-compatibility-root")
    parser.add_argument("--current-source-digest")
    parser.add_argument(
        "--print-compatible-analysis-config-digest", action="store_true"
    )
    parser.add_argument("--matrix-root")
    parser.add_argument("--source-digest-start")
    parser.add_argument("--analysis-config-digest", default="full-unit-default")
    parser.add_argument("--exit-status", type=int)
    parser.add_argument("--run-junit", action="store_true")
    parser.add_argument("--junit")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    repo_root = Path(args.repo_root).resolve()
    if args.print_compatible_analysis_config_digest:
        if (
            not args.run_manifest or not args.resume_compatibility_root
            or not args.current_source_digest
        ):
            parser.error(
                "resume compatibility requires matrix root, run manifest and source digest"
            )
        current = analysis_config_from_run(
            _read_key_values(Path(args.run_manifest))
        )
        identity = compatible_published_analysis_identity(
            Path(args.resume_compatibility_root), current_config=current,
            current_source_digest=args.current_source_digest,
        )
        if identity is None:
            return 1
        print("\t".join(identity))
        return 0
    if args.print_analysis_config_digest:
        if not args.run_manifest:
            parser.error("analysis config digest requires --run-manifest")
        config = analysis_config_from_run(_read_key_values(Path(args.run_manifest)))
        print(authority_digest(config))
        return 0
    if not args.private_key or not args.public_key or not args.output:
        parser.error("receipt issuance requires private/public keys and output")
    private = Path(args.private_key)
    public = Path(args.public_key)
    output = Path(args.output)
    if args.matrix_root:
        root = Path(args.matrix_root)
        if args.exit_status is None:
            parser.error("matrix receipt requires --exit-status")
        publication = build_matrix_publication_manifest(root)
        _write(root / MATRIX_PUBLICATION_MANIFEST_FILE, publication)
        names = (MATRIX_PUBLICATION_MANIFEST_FILE, "run_health_summary.json")
        artifacts = {
            name: sha256_file(root / name) for name in names
            if (root / name).is_file()
        }
        end = source_tree_digest(repo_root)
        command = list(args.command)
        if command and command[0] == "--":
            command = command[1:]
        if not command:
            parser.error("matrix receipt requires an exact command after --")
        payload = seal_execution_receipt(
            execution_kind="EQBENCH_MATRIX", command=command,
            source_digest_start=str(args.source_digest_start), source_digest_end=end,
            analysis_config_digest=args.analysis_config_digest, exit_status=args.exit_status,
            artifacts=artifacts, private_key_path=private, public_key_path=public,
        )
        _write(output, payload)
        return 0
    if args.run_junit:
        if not args.junit or not args.command or args.command[0] != "--":
            parser.error("JUnit execution requires --junit and a command after --")
        command = args.command[1:]
        start = source_tree_digest(repo_root)
        completed = subprocess.run(command, cwd=repo_root, check=False)
        end = source_tree_digest(repo_root)
        junit = Path(args.junit)
        junit_absolute = junit if junit.is_absolute() else repo_root / junit
        artifacts = {junit.as_posix(): sha256_file(junit_absolute)} if junit_absolute.is_file() else {}
        payload = seal_execution_receipt(
            execution_kind="FULL_UNIT_JUNIT", command=command,
            source_digest_start=start, source_digest_end=end,
            analysis_config_digest=args.analysis_config_digest,
            exit_status=completed.returncode, artifacts=artifacts,
            private_key_path=private, public_key_path=public,
        )
        _write(output, payload)
        return completed.returncode
    parser.error("choose matrix receipt or JUnit execution")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
