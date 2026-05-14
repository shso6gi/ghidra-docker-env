# -*- coding: utf-8 -*-
"""Freeze existing validation logs as an immutable observed-baseline artifact."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence, Tuple

from .result_summary import aggregate_validation_logs_by_function
from .unknown_reason_summary import summarize_validation_unknowns


MANIFEST_VERSION = 1
RAW_EVIDENCE_GIT_POLICY = "external_not_committed"


def freeze_observed_baseline(
    *,
    baseline_id: str,
    git_head: str,
    output_root: Path,
    source_roots: Mapping[str, Path],
    runner_commands: Sequence[str] = (),
    workspace_root: Optional[Path] = None,
) -> Path:
    workspace = Path(workspace_root or Path.cwd()).resolve()
    output = Path(output_root).resolve()
    raw_dir = output / "raw"
    if raw_dir.exists() and any(raw_dir.iterdir()):
        raise FileExistsError(f"baseline raw artifact already exists: {raw_dir}")
    raw_dir.mkdir(parents=True, exist_ok=True)

    workspace_state = _collect_workspace_state(workspace, raw_dir)
    source_entries = []
    file_hashes: Dict[str, str] = {}
    recovered_manifests = {}
    copied_log_roots = []

    for category, source_root in sorted(source_roots.items()):
        src = Path(source_root).resolve()
        if not src.is_dir():
            raise FileNotFoundError(f"source root does not exist: {src}")
        dest = raw_dir / "logs" / category
        shutil.copytree(src, dest)
        copied_log_roots.append(dest)
        category_hashes = _hash_files_under(dest, raw_dir)
        file_hashes.update(category_hashes)
        source_entries.append(
            {
                "category": category,
                "source_path": str(src),
                "raw_copy_path": str(dest.relative_to(raw_dir)),
                "file_count": len(category_hashes),
                "content_hash": _content_hash_from_file_hashes(category_hashes),
            }
        )
        recovered = _recover_category_manifest(category, dest)
        recovered_manifests[category] = recovered
        manifest_name = _recovered_manifest_filename(category, recovered["function_count"])
        _write_json(raw_dir / manifest_name, recovered)

    validation_summary = _summarize_copied_logs(copied_log_roots)
    recovered_manifest_paths = {
        category: _recovered_manifest_filename(
            category,
            int(manifest_data.get("function_count", 0) or 0),
        )
        for category, manifest_data in sorted(recovered_manifests.items())
    }
    _write_raw_readme(raw_dir)
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "baseline_id": baseline_id,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "git_head": _resolve_git_ref(workspace, git_head) or git_head,
        "git_head_input": git_head,
        "capture_workspace_git_head": _git_output(workspace, "rev-parse", "HEAD"),
        "dirty_state": workspace_state,
        "source_paths": source_entries,
        "file_content_hashes": dict(sorted(file_hashes.items())),
        "raw_logs_root": "logs",
        "artifact_storage": _artifact_storage_policy(recovered_manifest_paths, workspace_state),
        "recovered_manifests": recovered_manifest_paths,
        "execution": {
            "runner_commands": list(runner_commands),
            "environment": {
                key: os.environ.get(key)
                for key in (
                    "PARALLEL_JOBS",
                    "VALIDATION_BEFORE_DIR",
                    "VALIDATION_AUTO_BEFORE_SNAPSHOT",
                    "VALIDATION_REQUIRE_BEFORE_DELTA",
                    "VALIDATION_REQUIRE_BASELINE_MATCH",
                )
                if os.environ.get(key) is not None
            },
        },
        "tooling": {
            "python": sys.version,
            "platform": platform.platform(),
            "executable": sys.executable,
        },
        "validation_summary": validation_summary,
    }
    manifest_path = raw_dir / "artifact_manifest.json"
    _write_json(manifest_path, manifest)
    _write_json(raw_dir / "file_hashes.json", dict(sorted(file_hashes.items())))
    return manifest_path


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Freeze existing validation logs as observed baseline raw artifact.",
    )
    parser.add_argument("--baseline-id", required=True)
    parser.add_argument("--git-head", required=True)
    parser.add_argument("--output-root", required=True)
    parser.add_argument(
        "--source",
        action="append",
        required=True,
        help="category=path; may be repeated, e.g. function_call=logs/...",
    )
    parser.add_argument(
        "--runner-command",
        action="append",
        default=None,
        help="runner command or env snippet to record in the manifest",
    )
    args = parser.parse_args(argv)

    manifest_path = freeze_observed_baseline(
        baseline_id=args.baseline_id,
        git_head=args.git_head,
        output_root=Path(args.output_root),
        source_roots=_parse_source_args(args.source),
        runner_commands=tuple(args.runner_command or ()),
        workspace_root=Path.cwd(),
    )
    print(manifest_path)
    return 0


def _parse_source_args(values: Iterable[str]) -> Dict[str, Path]:
    parsed: Dict[str, Path] = {}
    for value in values:
        if "=" not in value:
            raise ValueError(f"--source must be category=path, got {value!r}")
        category, raw_path = value.split("=", 1)
        category = category.strip()
        if not category:
            raise ValueError(f"--source category is empty in {value!r}")
        parsed[category] = Path(raw_path)
    return parsed


def _collect_workspace_state(workspace: Path, raw_dir: Path) -> Dict[str, Any]:
    status_short = _git_output(workspace, "status", "--short") or ""
    diff_stat = _git_output(workspace, "diff", "--stat") or ""
    cached_diff_stat = _git_output(workspace, "diff", "--cached", "--stat") or ""
    dirty_patch = _git_output(workspace, "diff", "--binary") or ""
    cached_dirty_patch = _git_output(workspace, "diff", "--cached", "--binary") or ""
    untracked = _list_untracked_files(workspace)
    untracked_hashes = {
        path: _sha256_file(workspace / path)
        for path in sorted(untracked)
        if (workspace / path).is_file() and not _is_relative_to(workspace / path, raw_dir)
    }
    dirty_payload = json.dumps(
        {
            "status_short": status_short,
            "diff_stat": diff_stat,
            "cached_diff_stat": cached_diff_stat,
            "dirty_patch": dirty_patch,
            "cached_dirty_patch": cached_dirty_patch,
            "untracked_hashes": untracked_hashes,
        },
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    state_dir = raw_dir / "workspace_state"
    state_dir.mkdir(parents=True, exist_ok=True)
    (state_dir / "git_status_short.txt").write_text(status_short)
    (state_dir / "git_diff_stat.txt").write_text(diff_stat)
    if dirty_patch:
        (state_dir / "dirty_diff.patch").write_text(dirty_patch)
    if cached_dirty_patch:
        (state_dir / "cached_dirty_diff.patch").write_text(cached_dirty_patch)
    _write_json(state_dir / "untracked_file_hashes.json", dict(sorted(untracked_hashes.items())))
    return {
        "is_dirty": bool(status_short.strip()),
        "status_short_path": "workspace_state/git_status_short.txt",
        "diff_stat_path": "workspace_state/git_diff_stat.txt",
        "untracked_file_hashes_path": "workspace_state/untracked_file_hashes.json",
        "untracked_file_hash_count": len(untracked_hashes),
        "dirty_diff_path": "workspace_state/dirty_diff.patch" if dirty_patch else None,
        "cached_dirty_diff_path": (
            "workspace_state/cached_dirty_diff.patch" if cached_dirty_patch else None
        ),
        "dirty_snapshot_hash": hashlib.sha256(dirty_payload).hexdigest(),
    }


def _artifact_storage_policy(
    recovered_manifest_paths: Mapping[str, str],
    workspace_state: Mapping[str, Any],
) -> Dict[str, Any]:
    tracked_metadata_paths = [
        "README.md",
        "artifact_manifest.json",
        "file_hashes.json",
        "workspace_state/git_status_short.txt",
        "workspace_state/git_diff_stat.txt",
        "workspace_state/untracked_file_hashes.json",
        *sorted(recovered_manifest_paths.values()),
    ]
    for key in ("dirty_diff_path", "cached_dirty_diff_path"):
        path = workspace_state.get(key)
        if path:
            tracked_metadata_paths.append(str(path))
    return {
        "raw_evidence_git_policy": RAW_EVIDENCE_GIT_POLICY,
        "raw_evidence_root": "logs",
        "raw_evidence_hash_index_path": "file_hashes.json",
        "raw_evidence_complete_in_freeze_dir": True,
        "raw_evidence_commit_exclusion": "artifacts/baselines/*/raw/logs/",
        "tracked_metadata_paths": tracked_metadata_paths,
        "external_artifact_requirement": (
            "Publish or preserve raw/logs outside ordinary Git when this baseline "
            "must be independently replayable; file_hashes.json is the content index."
        ),
    }


def _write_raw_readme(raw_dir: Path) -> None:
    lines = [
        "# Observed Baseline Raw Artifact",
        "",
        "This directory freezes observed validation evidence for comparison only.",
        "The `logs/` tree can be multi-gigabyte raw evidence and is intentionally",
        "kept out of ordinary Git commits by the repository ignore policy.",
        "",
        "Commit the metadata files in this directory, including `artifact_manifest.json`,",
        "`file_hashes.json`, recovered manifests, and `workspace_state/` provenance.",
        "Preserve or publish `logs/` as an external artifact or Git LFS object when",
        "independent replay of the exact raw evidence is required.",
    ]
    (raw_dir / "README.md").write_text(
        "\n".join(lines) + "\n"
    )


def _summarize_copied_logs(log_roots: Sequence[Path]) -> Dict[str, Any]:
    log_paths = []
    for root in log_roots:
        log_paths.extend(root.glob("*/*.log"))
    summary = aggregate_validation_logs_by_function(sorted(log_paths))
    payloads = []
    for record in summary.overall.records:
        payloads.extend(record.payloads)
    unknown_summary = summarize_validation_unknowns(payloads)
    return {
        "overall": summary.overall.to_dict(),
        "functions": {
            function: aggregate.to_dict()
            for function, aggregate in summary.function_summaries.items()
        },
        "unknown_summary": unknown_summary.to_dict(),
    }


def _recover_category_manifest(category: str, raw_category_root: Path) -> Dict[str, Any]:
    functions = []
    binary_ids = set()
    for function_dir in sorted(path for path in raw_category_root.iterdir() if path.is_dir()):
        pairs = []
        for log_path in sorted(function_dir.glob("*.log")):
            pair = _pair_from_log_name(log_path, function_dir.name)
            if pair is None:
                continue
            left, right = pair
            binary_ids.update((left, right))
            ordered_pair = "_".join(sorted((left, right), key=_binary_sort_key))
            pairs.append(ordered_pair)
        functions.append(
            {
                "function": function_dir.name,
                "log_count": len(tuple(function_dir.glob("*.log"))),
                "binary_pairs": sorted(set(pairs), key=_pair_sort_key),
            }
        )
    return {
        "manifest_version": MANIFEST_VERSION,
        "category": category,
        "function_count": len(functions),
        "binary_ids": sorted(binary_ids, key=_binary_sort_key),
        "functions": functions,
    }


def _pair_from_log_name(log_path: Path, function_name: str) -> Optional[Tuple[str, str]]:
    stem = log_path.stem
    prefix = f"{function_name}_"
    if not stem.startswith(prefix):
        return None
    tail = stem[len(prefix):]
    parts = tail.rsplit("_", 1)
    if len(parts) != 2:
        return None
    return parts[0], parts[1]


def _binary_sort_key(binary_id: str) -> Tuple[str, int, str]:
    text = str(binary_id)
    if len(text) > 1 and text[0].isalpha() and text[1:].isdigit():
        return text[0], int(text[1:]), text
    return text, -1, text


def _pair_sort_key(pair: str) -> Tuple[Tuple[str, int, str], Tuple[str, int, str], str]:
    left, right = pair.split("_", 1)
    return _binary_sort_key(left), _binary_sort_key(right), pair


def _recovered_manifest_filename(category: str, function_count: int) -> str:
    return f"{category}_{function_count}_manifest.json"


def _hash_files_under(root: Path, raw_dir: Path) -> Dict[str, str]:
    hashes = {}
    for path in sorted(p for p in root.rglob("*") if p.is_file()):
        hashes[str(path.relative_to(raw_dir))] = _sha256_file(path)
    return hashes


def _content_hash_from_file_hashes(file_hashes: Mapping[str, str]) -> str:
    payload = json.dumps(
        dict(sorted(file_hashes.items())),
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _git_output(workspace: Path, *args: str) -> Optional[str]:
    try:
        result = subprocess.run(
            ["git", *args],
            cwd=workspace,
            check=False,
            capture_output=True,
            text=True,
        )
    except OSError:
        return None
    if result.returncode != 0:
        return None
    return result.stdout


def _git_output_bytes(workspace: Path, *args: str) -> Optional[bytes]:
    try:
        result = subprocess.run(
            ["git", *args],
            cwd=workspace,
            check=False,
            capture_output=True,
        )
    except OSError:
        return None
    if result.returncode != 0:
        return None
    return result.stdout


def _list_untracked_files(workspace: Path) -> Tuple[str, ...]:
    output = _git_output_bytes(workspace, "ls-files", "--others", "--exclude-standard", "-z")
    if output is None:
        return ()
    return tuple(
        path
        for path in output.decode("utf-8", "surrogateescape").split("\0")
        if path
    )


def _resolve_git_ref(workspace: Path, ref: str) -> Optional[str]:
    output = _git_output(workspace, "rev-parse", ref)
    return output.strip() if output else None


def _is_relative_to(path: Path, base: Path) -> bool:
    try:
        path.resolve().relative_to(base.resolve())
    except ValueError:
        return False
    return True


if __name__ == "__main__":
    raise SystemExit(main())
