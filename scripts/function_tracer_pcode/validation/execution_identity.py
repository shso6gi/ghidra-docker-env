"""Current-source and concrete EqBench pair execution identity contracts."""

from __future__ import annotations

import hashlib
import argparse
import json
from pathlib import Path
import subprocess
from typing import Any, Mapping

from ..equivalence.v2.contracts import authority_digest


SOURCE_ROOTS = (
    "eqbench_run_all_32jobs.sh",
    "requirements-test.txt",
    "scripts/validation_matrix_common.sh",
    "scripts/eqbench",
    "scripts/function_tracer_pcode",
)
PAIR_EXECUTION_TARGET_SCHEMA = "eqbench-pair-execution-target-v1"
PAIR_EXECUTION_TARGET_KIND = "PairExecutionTargetReceipt"


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _git(repo_root: Path, *arguments: str) -> bytes:
    return subprocess.run(
        ("git", *arguments), cwd=repo_root, check=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    ).stdout


def source_files(repo_root: Path) -> tuple[Mapping[str, str], ...]:
    repo_root = repo_root.resolve()
    tracked = _git(repo_root, "ls-files", "--", *SOURCE_ROOTS).decode().splitlines()
    untracked = _git(
        repo_root, "ls-files", "--others", "--exclude-standard", "--",
        *SOURCE_ROOTS,
    ).decode().splitlines()
    return tuple(
        {"path": path, "sha256": sha256_file(repo_root / path)}
        for path in sorted(set(tracked) | set(untracked))
    )


def source_tree_digest(repo_root: Path) -> str:
    return authority_digest({"source_files": source_files(repo_root)})


def _relative_file(repo_root: Path, path: Path) -> tuple[str, str]:
    absolute = path.resolve(strict=True)
    try:
        relative = absolute.relative_to(repo_root.resolve()).as_posix()
    except ValueError as exc:
        raise ValueError(f"execution input is outside repository: {absolute}") from exc
    if not absolute.is_file():
        raise ValueError(f"execution input is not a file: {absolute}")
    return relative, sha256_file(absolute)


def build_pair_execution_target(
    repo_root: Path, *, sample_identity: str, output_sample_relative_path: str,
    function_name: str, left_binary_id: str, right_binary_id: str,
    source_path: Path, left_binary_path: Path, right_binary_path: Path,
    analysis_source_digest: str, analysis_config_digest: str,
) -> Mapping[str, Any]:
    source_relative, source_sha256 = _relative_file(repo_root, source_path)
    left_relative, left_sha256 = _relative_file(repo_root, left_binary_path)
    right_relative, right_sha256 = _relative_file(repo_root, right_binary_path)
    body = {
        "schema": PAIR_EXECUTION_TARGET_SCHEMA,
        "authority_kind": PAIR_EXECUTION_TARGET_KIND,
        "sample_identity": sample_identity,
        "output_sample_relative_path": output_sample_relative_path,
        "function_name": function_name,
        "left_binary_id": left_binary_id,
        "right_binary_id": right_binary_id,
        "source_path": source_relative,
        "source_sha256": source_sha256,
        "left_binary_path": left_relative,
        "left_binary_sha256": left_sha256,
        "right_binary_path": right_relative,
        "right_binary_sha256": right_sha256,
        "analysis_source_digest": analysis_source_digest,
        "analysis_config_digest": analysis_config_digest,
    }
    return {**body, "target_digest": authority_digest(body)}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--print-source-digest", action="store_true")
    parser.add_argument("--build-pair-target", action="store_true")
    parser.add_argument("--sample-identity")
    parser.add_argument("--output-sample-relative-path")
    parser.add_argument("--function-name")
    parser.add_argument("--left-binary-id")
    parser.add_argument("--right-binary-id")
    parser.add_argument("--source-path")
    parser.add_argument("--left-binary-path")
    parser.add_argument("--right-binary-path")
    parser.add_argument("--analysis-source-digest")
    parser.add_argument("--analysis-config-digest")
    args = parser.parse_args(argv)
    repo_root = Path(args.repo_root)
    if args.print_source_digest:
        print(source_tree_digest(repo_root))
        return 0
    if args.build_pair_target:
        names = (
            "sample_identity", "output_sample_relative_path", "function_name",
            "left_binary_id", "right_binary_id", "source_path",
            "left_binary_path", "right_binary_path", "analysis_source_digest",
            "analysis_config_digest",
        )
        if any(not getattr(args, name) for name in names):
            parser.error("pair target construction requires every identity input")
        payload = build_pair_execution_target(
            repo_root,
            sample_identity=args.sample_identity,
            output_sample_relative_path=args.output_sample_relative_path,
            function_name=args.function_name,
            left_binary_id=args.left_binary_id,
            right_binary_id=args.right_binary_id,
            source_path=Path(args.source_path),
            left_binary_path=Path(args.left_binary_path),
            right_binary_path=Path(args.right_binary_path),
            analysis_source_digest=args.analysis_source_digest,
            analysis_config_digest=args.analysis_config_digest,
        )
        print(json.dumps(payload, sort_keys=True))
        return 0
    parser.error("one execution identity operation is required")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
