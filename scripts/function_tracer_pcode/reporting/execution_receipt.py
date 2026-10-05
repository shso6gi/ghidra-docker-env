"""Signed, current-source-bound validation execution receipts."""

from __future__ import annotations

import argparse
import base64
from decimal import Decimal
import json
from pathlib import Path
import re
import subprocess
from typing import Any, Mapping, Sequence

from scripts.function_tracer_pcode.authority.contracts import authority_digest
from scripts.function_tracer_pcode.authority.decision.pair_status_authority import (
    load_pair_status_public_key,
    validate_pair_status_keypair,
)
from scripts.function_tracer_pcode.reporting.execution_identity import (
    sha256_file,
    source_tree_digest,
)
from scripts.function_tracer_pcode.reporting.runner_timeout_policy import (
    KEY_ANALYSIS_TIMEOUT,
    KEY_ANALYSIS_TIMEOUT_MARGIN,
)


EXECUTION_RECEIPT_SCHEMA = "phase10-validation-execution-receipt-v1"
EXECUTION_RECEIPT_KIND = "Phase10ValidationExecutionReceipt"
MATRIX_EXECUTION_RECEIPT_FILE = "validation-execution-receipt.json"
MATRIX_PUBLICATION_MANIFEST_FILE = "matrix-publication-manifest.json"
BENCHMARK_GATE_REPORT_FILE = "benchmark_validation_gate.json"
FUNCTION_DIFF_MANIFEST_FILE = "function_diff_manifest.json"
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
# Issue #15 PR-15-B.  The identical-input fast path changes what a pair's
# result means, so it belongs to the analysis identity: an ON run and an OFF
# run get different ``analysis_config_digest`` values and a pair status from
# one is never reused for the other.  A run manifest opts in by naming the
# schema; one that does not name it is read as v2 exactly as before.
ANALYSIS_CONFIG_V3_FIELDS = ANALYSIS_CONFIG_V2_FIELDS | {"identical_fast_path"}
ANALYSIS_CONFIG_V3_SCHEMA = "eqbench-analysis-config-v3"
# Issue #106 PR-106-B.  The runner's analysis deadline changes what a pair's
# result is (a pair cut at the deadline is an UNKNOWN it would not otherwise
# be), so the deadline and its margin join the identity: runs with different
# deadlines never reuse each other's pair statuses, and the publication
# manifest's ``analysis_config`` records the values a run used.  A v4 run with
# the deadline off (``analysis_timeout`` = 0) ran exactly what a v3 run ran, so
# ``normalize_semantic_analysis_config`` projects it onto v3 -- the margin means
# nothing without a deadline -- and an OFF run can resume a tree written before
# the deadline existed.
ANALYSIS_CONFIG_V4_FIELDS = ANALYSIS_CONFIG_V3_FIELDS | {
    "analysis_timeout_seconds", "analysis_timeout_margin_seconds",
}
ANALYSIS_CONFIG_V4_SCHEMA = "eqbench-analysis-config-v4"
ANALYSIS_CONFIG_SCHEMAS_WITH_FAST_PATH = frozenset({
    ANALYSIS_CONFIG_V3_SCHEMA, ANALYSIS_CONFIG_V4_SCHEMA,
})
ANALYSIS_CONFIG_SCHEMA_KEY = "analysis_config_schema"
MATRIX_RUN_SCOPES = frozenset({"REPRESENTATIVE", "FULL_EQBENCH", "FULL_NEQ"})


def analysis_config_from_run(run: Mapping[str, str]) -> Mapping[str, Any]:
    """The typed analysis config a run manifest describes.

    A manifest that names ``analysis_config_schema`` must name one this reader
    knows and must carry every field that schema requires; anything else is a
    ``ValueError`` rather than a silent fall back to the older identity, which
    would let an ON run and an OFF run share a digest.
    """
    schema = run.get(ANALYSIS_CONFIG_SCHEMA_KEY)
    if schema is not None and schema not in ANALYSIS_CONFIG_SCHEMAS_WITH_FAST_PATH:
        raise ValueError("matrix run manifest names an unknown analysis config schema")
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
        if schema in ANALYSIS_CONFIG_SCHEMAS_WITH_FAST_PATH:
            config["schema"] = schema
            config["identical_fast_path"] = _exact_flag(run["identical_fast_path"])
        if schema == ANALYSIS_CONFIG_V4_SCHEMA:
            config["analysis_timeout_seconds"] = run[KEY_ANALYSIS_TIMEOUT]
            config["analysis_timeout_margin_seconds"] = run[KEY_ANALYSIS_TIMEOUT_MARGIN]
    except (KeyError, ValueError) as exc:
        raise ValueError("matrix run manifest lacks typed analysis config") from exc
    validate_analysis_config(config)
    return config


def _exact_flag(value: str) -> bool:
    """``0``/``1`` only: a runner flag is never inferred from another spelling."""
    if value not in ("0", "1"):
        raise ValueError("matrix run manifest flag is not 0 or 1")
    return value == "1"


def validate_analysis_config(config: Mapping[str, Any]) -> None:
    timeout_fields = [
        "equiv_timeout_seconds", "decompile_timeout_seconds",
        "pairwise_timeout_seconds", "pairwise_timeout_hard_seconds",
        "pair_process_timeout_seconds", "pair_process_kill_after_seconds",
    ]
    if not isinstance(config, Mapping):
        raise ValueError("EqBench typed analysis config is invalid")
    expected_fields = {
        "eqbench-analysis-config-v1": ANALYSIS_CONFIG_V1_FIELDS,
        "eqbench-analysis-config-v2": ANALYSIS_CONFIG_V2_FIELDS,
        ANALYSIS_CONFIG_V3_SCHEMA: ANALYSIS_CONFIG_V3_FIELDS,
        ANALYSIS_CONFIG_V4_SCHEMA: ANALYSIS_CONFIG_V4_FIELDS,
    }.get(config.get("schema"))
    bool_fields = {"debug", "dry_run"}
    if config.get("schema") == "eqbench-analysis-config-v1":
        bool_fields.add("skip_completed_results")
    if config.get("schema") in ANALYSIS_CONFIG_SCHEMAS_WITH_FAST_PATH:
        bool_fields.add("identical_fast_path")
    if config.get("schema") == ANALYSIS_CONFIG_V4_SCHEMA:
        timeout_fields += ["analysis_timeout_seconds", "analysis_timeout_margin_seconds"]
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
    """Project historical v1 config onto the scheduling-free v2 authority.

    A v4 config whose analysis deadline is off is projected onto v3 (see
    ``ANALYSIS_CONFIG_V4_SCHEMA``); a v4 config with the deadline on stays v4,
    so it never compares equal to a run made without the deadline.
    """

    validate_analysis_config(config)
    if (
        config["schema"] == ANALYSIS_CONFIG_V4_SCHEMA
        and Decimal(config["analysis_timeout_seconds"]) == 0
    ):
        projected = {
            key: value for key, value in config.items()
            if key not in ANALYSIS_CONFIG_V4_FIELDS - ANALYSIS_CONFIG_V3_FIELDS
        }
        projected["schema"] = ANALYSIS_CONFIG_V3_SCHEMA
        validate_analysis_config(projected)
        return projected
    if config["schema"] in (
        "eqbench-analysis-config-v2", ANALYSIS_CONFIG_V3_SCHEMA, ANALYSIS_CONFIG_V4_SCHEMA,
    ):
        # A v3 config is *not* projected onto v2: dropping the fast-path field
        # would make an ON run and an OFF run compare equal, which is exactly
        # the confusion the field exists to prevent.
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
    if config["schema"] != "eqbench-analysis-config-v2":
        # v1 predates both later schemas; a manifest that declares one of them
        # has no v1 reading at all.
        raise ValueError("this matrix run manifest has no legacy v1 analysis config")
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


def compatible_previous_run_manifest_analysis_identity(
    previous_manifest: Path, *, current_config: Mapping[str, Any],
) -> tuple[str, str] | None:
    """Return a prior run's config/source identity without publication JSON.

    A matrix runner writes ``run_manifest.txt`` before scheduling pairs and
    appends its completion counters before issuing the publication receipt.
    Therefore a receipt-generation failure can leave a complete prior
    manifest while the signed pair-status files remain usable.  Treat that
    manifest only as a compatibility hint: the caller still validates every
    signed pair status against the concrete current target (including source
    and binary hashes).  Accept both the scheduling-free v2 digest and the
    historical v1 digest, but require the stored digest to match the
    reconstructed typed config exactly.
    """

    try:
        run = _read_key_values(previous_manifest)
        stored_digest = run["analysis_config_digest"]
        source_start = run["analysis_source_digest_start"]
        source_end = run.get("analysis_source_digest_end")
        if (
            not re.fullmatch(r"[0-9a-f]{64}", stored_digest)
            or not re.fullmatch(r"[0-9a-f]{64}", source_start)
            or (
                source_end is not None
                and (
                    not re.fullmatch(r"[0-9a-f]{64}", source_end)
                    or source_start != source_end
                )
            )
        ):
            return None
        current_semantic = normalize_semantic_analysis_config(current_config)
        candidates: list[Mapping[str, Any]] = [analysis_config_from_run(run)]
        try:
            candidates.append(_legacy_analysis_config_from_run(run))
        except (KeyError, ValueError):
            pass
        for candidate in candidates:
            if (
                authority_digest(candidate) == stored_digest
                and normalize_semantic_analysis_config(candidate)
                == current_semantic
            ):
                return stored_digest, source_start
    except (OSError, UnicodeError, KeyError, ValueError):
        return None
    return None


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
        # object; never silently replace a mismatched digest.  A manifest that
        # declares a later schema has no v1 reading, so its digest must match
        # the config it declared.
        if analysis_config["schema"] != "eqbench-analysis-config-v2":
            raise ValueError("matrix analysis config digest differs")
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


MATRIX_EXECUTION_BINDING_CHECKS = (
    "execution_kind", "publication_sha256", "analysis_config_digest",
    "source_tree_digest_start", "source_tree_digest_end",
)


def matrix_execution_binding_mismatch(
    publication_path: Path,
    publication: Mapping[str, Any],
    receipt: Mapping[str, Any],
) -> str | None:
    """Why a validated receipt does not bind to its publication, or ``None``.

    The two artifacts must describe the *same* execution: the receipt names the
    matrix execution kind, hashes the exact publication file on disk, and
    repeats that publication's analysis config and source-tree digests.  Left
    unchecked, a directory reused across runs can end up holding one run's
    publication next to another run's manifests.

    Extracted from ``compatible_published_analysis_identity`` so the resume
    path and any other caller share one implementation of the binding rather
    than each carrying a copy.  Deliberately says nothing about
    ``exit_status``: whether a run's exit code matters is the caller's policy,
    not part of "are these artifacts from the same execution".
    """
    if receipt["execution_kind"] != "EQBENCH_MATRIX":
        return (
            f"the receipt records execution_kind={receipt['execution_kind']}, "
            "not EQBENCH_MATRIX"
        )
    published_sha256 = receipt["artifact_sha256"].get(MATRIX_PUBLICATION_MANIFEST_FILE)
    actual_sha256 = sha256_file(publication_path)
    if published_sha256 != actual_sha256:
        return (
            f"the receipt signs a different {MATRIX_PUBLICATION_MANIFEST_FILE} "
            f"({published_sha256} vs {actual_sha256} on disk)"
        )
    for receipt_key, publication_key in (
        ("analysis_config_digest", "analysis_config_digest"),
        ("source_tree_digest_start", "analysis_source_digest_start"),
        ("source_tree_digest_end", "analysis_source_digest_end"),
    ):
        if receipt[receipt_key] != publication[publication_key]:
            return (
                f"the receipt's {receipt_key} ({receipt[receipt_key]}) differs from "
                f"the publication's {publication_key} ({publication[publication_key]})"
            )
    return None


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
            or receipt["exit_status"] not in {0, 1}
            or matrix_execution_binding_mismatch(
                publication_path, publication, receipt
            ) is not None
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
    parser.add_argument("--resume-compatibility-manifest")
    parser.add_argument(
        "--print-compatible-manifest-analysis-identity", action="store_true"
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
    if args.print_compatible_manifest_analysis_identity:
        if not args.run_manifest or not args.resume_compatibility_manifest:
            parser.error(
                "manifest resume compatibility requires current and previous manifests"
            )
        current = analysis_config_from_run(
            _read_key_values(Path(args.run_manifest))
        )
        identity = compatible_previous_run_manifest_analysis_identity(
            Path(args.resume_compatibility_manifest), current_config=current,
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
        names = (
            MATRIX_PUBLICATION_MANIFEST_FILE,
            "run_health_summary.json",
            # Issue #104 runner benchmark gate artifacts (present when the gate ran).
            BENCHMARK_GATE_REPORT_FILE,
            FUNCTION_DIFF_MANIFEST_FILE,
        )
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
