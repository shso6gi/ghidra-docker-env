"""Materialize and validate the source-bound Phase-10 validation root."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
from typing import Any, Iterable, Mapping, Sequence
import xml.etree.ElementTree as ET

from ..equivalence.v2.contracts import authority_digest
from ..equivalence.v2.pair_status_authority import (
    PAIR_STATUS_PUBLIC_KEY_FILE,
    validate_signed_pair_status,
    pair_status_resume_disposition,
)
from .execution_identity import (
    SOURCE_ROOTS, sha256_file, source_files, source_tree_digest,
    validate_pair_execution_target,
)
from .execution_receipt import (
    MATRIX_EXECUTION_RECEIPT_FILE, MATRIX_PUBLICATION_MANIFEST_FILE,
    validate_execution_receipt, validate_matrix_publication_manifest,
)
from .eqbench_build_receipt import BINARY_IDS, validate_receipt as validate_build_receipt


MANIFEST_SCHEMA = "unknown-taxonomy-v2-phase10-validation-root-v3"
ROOT_PURPOSES = frozenset({"REPRESENTATIVE_EVIDENCE", "PHASE10_COMPLETION"})
FULL_SCOPE_EXPECTATION_FILE = Path(
    "scripts/function_tracer_pcode/validation/eqbench_full_scope.json"
)


def _full_scope_expectation(repo_root: Path) -> Mapping[str, Any]:
    payload = json.loads((repo_root / FULL_SCOPE_EXPECTATION_FILE).read_text(encoding="utf-8"))
    required = {
        "schema", "authority_kind", "expected_source_count",
        "expected_binary_ids", "expected_pairs_per_function", "source_paths",
        "expected_functions",
    }
    if (
        not isinstance(payload, Mapping) or set(payload) != required
        or payload["schema"] != "eqbench-full-scope-v1"
        or payload["authority_kind"] != "EqBenchFullScopeExpectation"
        or payload["expected_source_count"] != 147
        or payload["expected_pairs_per_function"] != 120
        or payload["expected_binary_ids"] != [f"B{index}" for index in range(1, 17)]
        or type(payload["source_paths"]) is not list
        or len(payload["source_paths"]) != payload["expected_source_count"]
        or len(set(payload["source_paths"])) != len(payload["source_paths"])
        or payload["source_paths"] != sorted(payload["source_paths"])
        or type(payload["expected_functions"]) is not dict
        or set(payload["expected_functions"]) != set(payload["source_paths"])
        or any(
            type(functions) is not list or not functions
            or functions != sorted(set(functions))
            or any(type(function) is not str or not function for function in functions)
            for functions in payload["expected_functions"].values()
        )
    ):
        raise ValueError("EqBench full-scope expectation is invalid")
    return payload


def validate_full_eqbench_scope(
    publication: Mapping[str, Any], expectation: Mapping[str, Any],
) -> None:
    expected_pair_paths = []
    binary_ids = expectation["expected_binary_ids"]
    for source_path in expectation["source_paths"]:
        sample_path = source_path[:-2] if source_path.endswith(".c") else source_path
        for function_name in expectation["expected_functions"][source_path]:
            for left_index, left_id in enumerate(binary_ids[:-1]):
                for right_id in binary_ids[left_index + 1:]:
                    expected_pair_paths.append(
                        f"{sample_path}/{function_name}/"
                        f"{function_name}_{left_id}_{right_id}.pair-status.json"
                    )
    if (
        publication["run_scope"] != "FULL_EQBENCH"
        or publication["analysis_config"]["max_samples"] != 0
        or publication["analysis_config"]["sample_filter"] != ""
        or publication["analysis_config"]["pair_filter"] != ""
        or publication["prefilter_source_count"] != expectation["expected_source_count"]
        or publication["prefilter_source_paths"] != expectation["source_paths"]
        or publication["target_sources"] != expectation["expected_source_count"]
        or publication["expected_binary_count"]
        != expectation["expected_source_count"] * len(expectation["expected_binary_ids"])
        or publication["total_functions"]
        != sum(len(row) for row in expectation["expected_functions"].values())
        or publication["expected_pairs_per_function"] != expectation["expected_pairs_per_function"]
        or publication["total_pair_jobs"]
        != publication["total_functions"] * expectation["expected_pairs_per_function"]
        or publication["expected_pair_status_paths"] != expected_pair_paths
    ):
        raise ValueError("FULL_EQBENCH scope authority is incomplete")


def _sha256(path: Path) -> str:
    return sha256_file(path)


def _git(repo_root: Path, *arguments: str) -> bytes:
    return subprocess.run(
        ("git", *arguments), cwd=repo_root, check=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    ).stdout


def _source_files(repo_root: Path) -> tuple[Mapping[str, str], ...]:
    return source_files(repo_root)


def _junit_entry(repo_root: Path, path: Path) -> Mapping[str, Any]:
    absolute = repo_root / path
    root = ET.parse(absolute).getroot()
    suite = root.find("testsuite") if root.tag == "testsuites" else root
    if suite is None:
        raise ValueError("full-unit JUnit has no testsuite")
    return {
        "path": path.as_posix(),
        "sha256": _sha256(absolute),
        "tests": int(suite.attrib["tests"]),
        "failures": int(suite.attrib["failures"]),
        "errors": int(suite.attrib["errors"]),
        "skipped": int(suite.attrib["skipped"]),
        "time_seconds": suite.attrib["time"],
    }


def _pair_status_root(
    repo_root: Path, matrix_root: Path, current_source_digest: str,
) -> tuple[int, str, frozenset[str], Mapping[str, Mapping[str, int]], Mapping[str, Mapping[str, Any]]]:
    public_key_path = matrix_root / PAIR_STATUS_PUBLIC_KEY_FILE
    rows = []
    bodies: dict[str, Mapping[str, Any]] = {}
    occurrence_ids: set[str] = set()
    body_digests: set[str] = set()
    target_digests: set[str] = set()
    axes: dict[str, dict[str, int]] = {
        "error_kind_counts": {},
        "child_returncode_counts": {},
        "supervisor_status_counts": {},
    }
    for path in sorted(matrix_root.rglob("*.pair-status.json")):
        payload = json.loads(path.read_text(encoding="utf-8"))
        body = validate_signed_pair_status(payload, public_key_path=public_key_path)
        target = body["pair_execution_target"]
        validate_pair_execution_target(
            target, repo_root=repo_root,
            expected_source_digest=current_source_digest,
        )
        relative = path.relative_to(matrix_root).as_posix()
        expected_relative = (
            f'{target["output_sample_relative_path"]}/'
            f'{target["function_name"]}/'
            f'{target["function_name"]}_{target["left_binary_id"]}_'
            f'{target["right_binary_id"]}.pair-status.json'
        )
        if relative != expected_relative or target["sample_identity"] != target["output_sample_relative_path"]:
            raise ValueError("signed pair target differs from census path")
        identities = (
            (occurrence_ids, body["result_occurrence_id"], "result occurrence"),
            (body_digests, payload["pair_status_body_digest"], "pair-status body"),
            (target_digests, target["target_digest"], "pair target"),
        )
        for seen, value, label in identities:
            if value in seen:
                raise ValueError(f"duplicate signed {label} identity")
            seen.add(value)
        values = {
            "error_kind_counts": (
                "<none>" if body["error_kind"] is None else str(body["error_kind"])
            ),
            "child_returncode_counts": (
                "null" if body["child_returncode"] is None
                else str(body["child_returncode"])
            ),
            "supervisor_status_counts": str(body["supervisor_status"]),
        }
        for field, value in values.items():
            axes[field][value] = axes[field].get(value, 0) + 1
        rows.append({
            "path": relative,
            "sha256": _sha256(path),
            "body_digest": payload["pair_status_body_digest"],
        })
        bodies[relative] = body
    if not rows:
        raise ValueError(f"matrix has no signed pair-status authority: {matrix_root}")
    return (
        len(rows), authority_digest({"pair_status_rows": rows}),
        frozenset(row["path"] for row in rows), axes, bodies,
    )


def _matrix_entry(repo_root: Path, path: Path) -> Mapping[str, Any]:
    matrix_root = repo_root / path
    required = (
        MATRIX_PUBLICATION_MANIFEST_FILE, "run_health_summary.json",
        PAIR_STATUS_PUBLIC_KEY_FILE, MATRIX_EXECUTION_RECEIPT_FILE,
    )
    files = {}
    for name in required:
        artifact = matrix_root / name
        if not artifact.is_file():
            raise ValueError(f"matrix validation artifact is missing: {artifact}")
        files[name] = _sha256(artifact)
    current_source_digest = source_tree_digest(repo_root)
    count, pair_status_root_digest, actual_paths, axes, bodies = _pair_status_root(
        repo_root, matrix_root, current_source_digest
    )
    health = json.loads((matrix_root / "run_health_summary.json").read_text())
    publication = validate_matrix_publication_manifest(json.loads(
        (matrix_root / MATRIX_PUBLICATION_MANIFEST_FILE).read_text(encoding="utf-8")
    ))
    expected_rows = publication["expected_pair_status_paths"]
    if (
        not expected_rows
        or len(expected_rows) != len(set(expected_rows))
        or any(
            not row.endswith(".pair-status.json")
            or Path(row).is_absolute() or ".." in Path(row).parts
            for row in expected_rows
        )
        or frozenset(expected_rows) != actual_paths
    ):
        raise ValueError("matrix expected pair identity census differs")
    skipped_rows = publication["verified_skipped_pair_status_paths"]
    if len(skipped_rows) != len(set(skipped_rows)) or not set(skipped_rows) <= set(expected_rows):
        raise ValueError("matrix verified skip census differs")
    if any(not pair_status_resume_disposition(bodies[row]).startswith("COMPLETE_") for row in skipped_rows):
        raise ValueError("matrix skip census contains resumable or failed outcome")
    receipt_by_sample = {}
    required_ids_by_sample: dict[str, set[str]] = {}
    for body in bodies.values():
        target = body["pair_execution_target"]
        sample = target["sample_identity"]
        required_ids_by_sample.setdefault(sample, set()).update((
            target["left_binary_id"], target["right_binary_id"],
        ))
    for build_receipt in publication["build_receipts"]:
        if not isinstance(build_receipt, Mapping):
            raise ValueError("matrix build receipt schema differs")
        sample = build_receipt.get("sample_identity")
        if sample in receipt_by_sample or sample not in required_ids_by_sample:
            raise ValueError("matrix build receipt sample census differs")
        validate_build_receipt(
            build_receipt, repo_root=repo_root,
            required_binary_ids=tuple(required_ids_by_sample[sample]),
            require_fresh=publication["run_scope"] == "FULL_EQBENCH",
        )
        receipt_by_sample[sample] = build_receipt
    if set(receipt_by_sample) != set(required_ids_by_sample):
        raise ValueError("matrix build receipts do not cover pair samples")
    for body in bodies.values():
        target = body["pair_execution_target"]
        sample_receipt = receipt_by_sample[target["sample_identity"]]
        if (
            sample_receipt["source_path"] != target["source_path"]
            or sample_receipt["source_sha256"] != target["source_sha256"]
        ):
            raise ValueError("pair target does not join build receipt source")
        build_axes = {
            row["binary_id"]: row
            for row in sample_receipt["binary_axes"]
        }
        for side in ("left", "right"):
            binary_id = target[f"{side}_binary_id"]
            if (
                build_axes[binary_id]["binary_path"] != target[f"{side}_binary_path"]
                or build_axes[binary_id]["binary_sha256"] != target[f"{side}_binary_sha256"]
            ):
                raise ValueError("pair target does not join build receipt axis")
    counts = health.get("final_result_counts")
    if not isinstance(counts, Mapping):
        raise ValueError("matrix health final-result counts are invalid")
    function_total = sum(
        int(row.get("total", -1))
        for row in health.get("functions", {}).values()
        if isinstance(row, Mapping)
    )
    if (
        publication["dry_run"] != 0
        or publication["run_pair_failures"] != 0
        or publication["compile_failure_count"] != 0
        or publication["missing_binary_count"] != 0
        or publication["function_census_failure_count"] != 0
        or publication["compile_failure_samples"]
        or publication["missing_binary_axes"]
        or publication["function_census_failures"]
        or publication["compiled_binary_count"] != publication["expected_binary_count"]
        or publication["skipped_samples"] != 0
        or publication["target_sources"] != publication["completed_samples"]
        or publication["total_pair_jobs"] != count
        or publication["total_skipped_pair_jobs"] != len(skipped_rows)
        or publication["total_scheduled_pair_jobs"] + len(skipped_rows) != count
        or int(health.get("total_results", -1)) != count
        or sum(int(value) for value in counts.values()) != count
        or function_total != count
        or int(counts.get("ERROR", -1)) != 0
        or int(counts.get("INCOMPLETE", -1)) != 0
    ):
        raise ValueError("matrix completion counters do not join")
    if any(health.get(field) != value for field, value in axes.items()):
        raise ValueError("matrix verified pair-status metadata counts differ")
    if publication["run_scope"] == "FULL_EQBENCH":
        expectation = _full_scope_expectation(repo_root)
        validate_full_eqbench_scope(publication, expectation)
    elif publication["run_scope"] != "REPRESENTATIVE":
        raise ValueError("matrix run scope is invalid")
    receipt_payload = json.loads((matrix_root / MATRIX_EXECUTION_RECEIPT_FILE).read_text())
    receipt = validate_execution_receipt(
        receipt_payload, public_key_path=matrix_root / PAIR_STATUS_PUBLIC_KEY_FILE,
    )
    receipt_artifacts = {
        name: files[name] for name in (
            MATRIX_PUBLICATION_MANIFEST_FILE, "run_health_summary.json",
        )
    }
    if (
        receipt["execution_kind"] != "EQBENCH_MATRIX"
        or receipt["exit_status"] != 0
        or receipt["source_tree_digest_start"] != current_source_digest
        or receipt["analysis_config_digest"] != publication["analysis_config_digest"]
        or receipt["artifact_sha256"] != receipt_artifacts
    ):
        raise ValueError("matrix execution receipt does not join current artifacts")
    return {
        "path": path.as_posix(),
        "artifact_sha256": files,
        "pair_status_count": count,
        "pair_status_root_digest": pair_status_root_digest,
        "final_result_counts": health["final_result_counts"],
        "total_results": health["total_results"],
        "verified_pair_status_metadata_counts": axes,
        "execution_receipt_digest": receipt_payload["body_digest"],
        "run_scope": publication["run_scope"],
        "analysis_config": publication["analysis_config"],
        "build_receipt_root_digest": authority_digest({
            "build_receipts": publication["build_receipts"],
        }),
        "prefilter_source_census_digest": publication["prefilter_source_census_digest"],
        "completion_counters": {
            field: publication[field]
            for field in (
                "target_sources", "completed_samples", "skipped_samples",
                "total_pair_jobs", "total_scheduled_pair_jobs",
                "total_skipped_pair_jobs", "run_pair_failures", "dry_run",
                "expected_binary_count", "compiled_binary_count",
                "compile_failure_count", "missing_binary_count",
                "function_census_failure_count",
            )
        },
    }


def build_manifest(
    repo_root: Path, *, junit_path: Path, matrix_paths: Sequence[Path],
    commands: Sequence[str], junit_receipt_path: Path,
    root_purpose: str = "REPRESENTATIVE_EVIDENCE",
) -> Mapping[str, Any]:
    repo_root = repo_root.resolve()
    source_files = _source_files(repo_root)
    secret_keys = sorted(
        path.relative_to(repo_root).as_posix()
        for path in (repo_root / "artifacts/unknown_taxonomy_v2/phase10").rglob("*.key")
    )
    if secret_keys:
        raise ValueError(f"publishable Phase-10 artifact contains secret keys: {secret_keys}")
    junit = _junit_entry(repo_root, junit_path)
    if junit["failures"] != 0 or junit["errors"] != 0:
        raise ValueError("full-unit JUnit is not green")
    junit_receipt_payload = json.loads((repo_root / junit_receipt_path).read_text())
    junit_receipt = validate_execution_receipt(
        junit_receipt_payload,
        public_key_path=repo_root / "artifacts/unknown_taxonomy_v2/phase10/validation-verification-key.json",
    )
    current_source_digest = source_tree_digest(repo_root)
    if root_purpose not in ROOT_PURPOSES:
        raise ValueError("Phase-10 validation root purpose is invalid")
    if (
        junit_receipt["execution_kind"] != "FULL_UNIT_JUNIT"
        or junit_receipt["exit_status"] != 0
        or junit_receipt["source_tree_digest_start"] != current_source_digest
        or junit_receipt["artifact_sha256"] != {junit_path.as_posix(): junit["sha256"]}
    ):
        raise ValueError("full-unit execution receipt source digest or JUnit join differs")
    matrices = [_matrix_entry(repo_root, path) for path in matrix_paths]
    completion_eligible = any(
        matrix["run_scope"] == "FULL_EQBENCH" for matrix in matrices
    )
    if root_purpose == "PHASE10_COMPLETION" and not completion_eligible:
        raise ValueError("Phase-10 completion requires FULL_EQBENCH authority")
    body = {
        "schema": MANIFEST_SCHEMA,
        "authority_kind": "Phase10CurrentSourceValidationRoot",
        "root_purpose": root_purpose,
        "completion_eligible": completion_eligible,
        "source_roots": list(SOURCE_ROOTS),
        "source_file_count": len(source_files),
        "source_tree_digest": authority_digest({"source_files": source_files}),
        "commands": list(commands),
        "full_unit_junit": junit,
        "full_unit_execution_receipt": {
            "path": junit_receipt_path.as_posix(),
            "body_digest": junit_receipt_payload["body_digest"],
            "command": junit_receipt["command"],
        },
        "matrices": matrices,
        "publishable_secret_key_count": 0,
    }
    return {**body, "manifest_digest": authority_digest(body)}


def validate_manifest(repo_root: Path, payload: Mapping[str, Any]) -> None:
    required = {
        "schema", "authority_kind", "source_roots",
        "root_purpose", "completion_eligible",
        "source_file_count", "source_tree_digest", "commands", "full_unit_junit",
        "full_unit_execution_receipt",
        "matrices", "publishable_secret_key_count", "manifest_digest",
    }
    if not isinstance(payload, Mapping) or set(payload) != required:
        raise ValueError("Phase-10 validation manifest schema differs")
    rebuilt = build_manifest(
        repo_root,
        junit_path=Path(payload["full_unit_junit"]["path"]),
        junit_receipt_path=Path(payload["full_unit_execution_receipt"]["path"]),
        matrix_paths=tuple(Path(row["path"]) for row in payload["matrices"]),
        commands=tuple(payload["commands"]),
        root_purpose=payload["root_purpose"],
    )
    if dict(payload) != rebuilt:
        raise ValueError("Phase-10 validation manifest drifted from current source")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--output", required=True)
    parser.add_argument("--junit", required=True)
    parser.add_argument("--junit-receipt", required=True)
    parser.add_argument("--matrix", action="append", default=[])
    parser.add_argument("--command", action="append", default=[])
    parser.add_argument("--root-purpose", choices=sorted(ROOT_PURPOSES),
                        default="REPRESENTATIVE_EVIDENCE")
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args(argv)
    repo_root = Path(args.repo_root)
    output = Path(args.output)
    if args.validate:
        validate_manifest(repo_root, json.loads(output.read_text(encoding="utf-8")))
    else:
        payload = build_manifest(
            repo_root, junit_path=Path(args.junit),
            junit_receipt_path=Path(args.junit_receipt),
            matrix_paths=tuple(Path(path) for path in args.matrix),
            commands=tuple(args.command),
            root_purpose=args.root_purpose,
        )
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
