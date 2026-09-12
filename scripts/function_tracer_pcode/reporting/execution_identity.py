"""Current-source and concrete EqBench pair execution identity contracts."""

from __future__ import annotations

import hashlib
import argparse
import json
from pathlib import Path
import subprocess
from typing import Any, Mapping

from scripts.function_tracer_pcode.authority.contracts import authority_digest


SOURCE_ROOTS = (
    "eqbench_run_all_32jobs.sh",
    "eqbench_run_subset.sh",
    "neqbench_run_all_32jobs.sh",
    "requirements-test.txt",
    "scripts/validation_matrix_common.sh",
    "scripts/eqbench",
    "scripts/function_tracer_pcode",
)
PAIR_EXECUTION_TARGET_SCHEMA = "eqbench-pair-execution-target-v1"
PAIR_EXECUTION_TARGET_KIND = "PairExecutionTargetReceipt"
GIT_STATE_UNAVAILABLE = "unavailable"
GIT_DIRTY_UNKNOWN = "unknown"
GIT_DIRTY_YES = "1"
GIT_DIRTY_NO = "0"


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


def _porcelain_entries(repo_root: Path, status: bytes) -> tuple[Mapping[str, str], ...]:
    """``git status --porcelain=v1 -z`` のレコードを内容 sha256 付きで並べる。

    NUL 区切りを使うのは、空白を含む path が引用されて曖昧になるのを避けるため。
    rename / copy は「新 path のレコード」の直後に旧 path が 1 レコードとして続く。
    """
    fields = status.split(b"\0")
    entries: list[Mapping[str, str]] = []
    index = 0
    while index < len(fields):
        record = fields[index]
        index += 1
        if not record:
            continue
        code = record[:2].decode()
        path = record[3:].decode()
        renamed_from = ""
        if code[:1] in {"R", "C"} and index < len(fields):
            renamed_from = fields[index].decode()
            index += 1
        absolute = repo_root / path
        entries.append({
            "status": code,
            "path": path,
            "renamed_from": renamed_from,
            # 削除された path は "absent"。作業ツリーの内容そのものを digest に
            # 含めるので、同じ file 集合でも中身が違えば digest が変わる。
            "sha256": sha256_file(absolute) if absolute.is_file() else "absent",
        })
    return tuple(sorted(
        entries, key=lambda entry: (entry["path"], entry["status"], entry["renamed_from"])
    ))


def git_state(repo_root: Path) -> Mapping[str, Any]:
    """run を出した作業ツリーの git 素性（commit と SOURCE_ROOTS の汚れ）。

    ``dirty`` は ``SOURCE_ROOTS`` に限定した ``git status`` の結果で、解析結果に
    影響しうる未コミット変更だけを見る（`docs/issues/` のような範囲外の untracked
    は clean のまま）。git が使えない場合は欄を空にせず ``unavailable`` /
    ``unknown`` を返す: 「汚れていない」と読み違えられないようにするため。
    """
    repo_root = repo_root.resolve()
    try:
        commit = _git(repo_root, "rev-parse", "HEAD").decode().strip()
        status = _git(
            repo_root, "status", "--porcelain=v1", "-z", "--untracked-files=all",
            "--", *SOURCE_ROOTS,
        )
    except (OSError, subprocess.SubprocessError):
        return {
            "commit": GIT_STATE_UNAVAILABLE,
            "dirty": GIT_DIRTY_UNKNOWN,
            "dirty_files": (),
            "dirty_files_digest": GIT_STATE_UNAVAILABLE,
        }
    dirty_files = _porcelain_entries(repo_root, status)
    return {
        "commit": commit,
        "dirty": GIT_DIRTY_YES if dirty_files else GIT_DIRTY_NO,
        "dirty_files": dirty_files,
        "dirty_files_digest": authority_digest({"dirty_files": dirty_files}),
    }


def format_git_state(state: Mapping[str, Any]) -> str:
    """runner の manifest 行そのままの形（`key=value` 3 行）で返す。"""
    return "\n".join((
        f"git_commit={state['commit']}",
        f"git_dirty={state['dirty']}",
        f"git_dirty_files_digest={state['dirty_files_digest']}",
    ))


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
    parser.add_argument("--print-git-state", action="store_true")
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
    if args.print_git_state:
        print(format_git_state(git_state(repo_root)))
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
