# -*- coding: utf-8 -*-
"""Run one Phase 0 real-evidence command and seal its provenance receipt."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping, Optional, Sequence

from .result_summary import classify_result_payload
from .unknown_reason_summary import extract_result_payloads_from_text


RECEIPT_SCHEMA_VERSION = 1
RECEIPT_KIND = "phase0_current_head_run_receipt"


def _json_digest(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _git(root: Path, *args: str) -> str:
    completed = subprocess.run(
        ["git", *args], cwd=root, check=True, capture_output=True, text=True
    )
    return completed.stdout.strip()


def _tracked_worktree_digest(root: Path) -> str:
    paths = tuple(
        line for line in _git(root, "ls-files").splitlines() if line
    )
    digest = hashlib.sha256()
    for rel in paths:
        path = root / rel
        digest.update(rel.encode("utf-8"))
        digest.update(b"\0")
        if path.is_file():
            digest.update(bytes.fromhex(_sha256_file(path)))
        else:
            digest.update(b"MISSING")
        digest.update(b"\0")
    return digest.hexdigest()


def run_selection(
    *, repo_root: Path, selection: Mapping[str, Any], receipt_path: Path
) -> Mapping[str, Any]:
    root = repo_root.resolve()
    if selection.get("evidence_mode") != "CURRENT_HEAD_REAL_RERUN":
        raise ValueError("run receipts are only valid for current-HEAD real reruns")
    command = selection.get("analysis_command")
    config = selection.get("analysis_config")
    if not isinstance(command, list) or not command or not isinstance(config, Mapping):
        raise ValueError("selection requires an argv array and an analysis_config object")
    head_before = _git(root, "rev-parse", "HEAD")
    expected_head = str(selection.get("repository_commit") or "")
    if head_before != expected_head:
        raise ValueError(f"selection HEAD mismatch: expected {expected_head}, found {head_before}")
    head_tree_before = _git(root, "rev-parse", "HEAD^{tree}")
    tracked_before = _tracked_worktree_digest(root)
    raw_log_path = Path(str(selection.get("source_artifact_path") or ""))
    if not raw_log_path.as_posix():
        raise ValueError("selection lacks source_artifact_path")
    log_path = raw_log_path if raw_log_path.is_absolute() else root / raw_log_path
    log_path.parent.mkdir(parents=True, exist_ok=True)
    started = datetime.now(timezone.utc).isoformat()
    with log_path.open("wb") as output:
        completed = subprocess.run(
            [str(item) for item in command],
            cwd=root,
            stdout=output,
            stderr=subprocess.STDOUT,
            check=False,
        )
    finished = datetime.now(timezone.utc).isoformat()
    head_after = _git(root, "rev-parse", "HEAD")
    head_tree_after = _git(root, "rev-parse", "HEAD^{tree}")
    tracked_after = _tracked_worktree_digest(root)
    if (head_before, head_tree_before, tracked_before) != (
        head_after,
        head_tree_after,
        tracked_after,
    ):
        raise ValueError("repository provenance changed while evidence command was running")
    text = log_path.read_text(encoding="utf-8", errors="replace")
    payloads = extract_result_payloads_from_text(text)
    if not payloads:
        raise ValueError("evidence command produced no result payload")
    payload_index = len(payloads) - 1
    payload = payloads[payload_index]
    receipt = {
        "schema_version": RECEIPT_SCHEMA_VERSION,
        "receipt_kind": RECEIPT_KIND,
        "repository_commit": head_after,
        "head_tree_digest": head_tree_after,
        "tracked_worktree_digest": tracked_after,
        "analysis_command": list(command),
        "analysis_command_digest": _json_digest(list(command)),
        "analysis_config": dict(config),
        "analysis_config_digest": _json_digest(dict(config)),
        "binary_content_identities": selection.get("binary_content_identities") or {},
        "started_at_utc": started,
        "finished_at_utc": finished,
        "exit_code": completed.returncode,
        "source_artifact_path": raw_log_path.as_posix(),
        "source_artifact_digest": _sha256_file(log_path),
        "payload_index": payload_index,
        "payload_digest": _json_digest(payload),
        "decision": classify_result_payload(payload),
        "observed_binary_content_identities": {
            "left": payload.get("binary1_content_identity"),
            "right": payload.get("binary2_content_identity"),
        },
    }
    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    receipt_path.write_text(
        json.dumps(receipt, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return receipt


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--selection-input", required=True)
    parser.add_argument("--selection-index", required=True, type=int)
    parser.add_argument("--receipt", required=True)
    args = parser.parse_args(argv)
    document = json.loads(Path(args.selection_input).read_text(encoding="utf-8"))
    selections = document.get("selections") or ()
    try:
        selection = selections[args.selection_index]
    except IndexError as exc:
        raise ValueError("selection index is out of range") from exc
    receipt = run_selection(
        repo_root=Path(args.repo_root),
        selection=selection,
        receipt_path=Path(args.receipt),
    )
    print(json.dumps({
        "receipt": args.receipt,
        "decision": receipt["decision"],
        "exit_code": receipt["exit_code"],
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
