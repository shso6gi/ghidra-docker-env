"""Build the exact, secret-free Phase-10 publication staging allowlist."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
from typing import Any, Mapping, Sequence

from ..equivalence.v2.contracts import authority_digest
from ..equivalence.v2.pair_status_authority import PAIR_STATUS_PUBLIC_KEY_FILE
from .execution_identity import sha256_file
from .execution_receipt import (
    MATRIX_EXECUTION_RECEIPT_FILE, MATRIX_PUBLICATION_MANIFEST_FILE,
)
from .phase10_validation_manifest import validate_manifest


SCHEMA = "phase10-publication-allowlist-v2"
FORBIDDEN_PARTS = frozenset({".process-authority", ".process-authority-keys", "keys"})
FORBIDDEN_SUFFIXES = frozenset({".key", ".log", ".txt"})


def _safe_relative(repo_root: Path, value: str | Path) -> Path:
    path = Path(value)
    if path.is_absolute() or ".." in path.parts or not path.parts:
        raise ValueError(f"publication path is not repository-relative: {path}")
    absolute = (repo_root / path).resolve()
    try:
        absolute.relative_to(repo_root.resolve())
    except ValueError as exc:
        raise ValueError(f"publication path escapes repository: {path}") from exc
    if FORBIDDEN_PARTS.intersection(path.parts) or path.suffix in FORBIDDEN_SUFFIXES:
        raise ValueError(f"diagnostic, internal, or secret path is not publishable: {path}")
    if not absolute.is_file():
        raise ValueError(f"publication artifact is missing: {path}")
    return path


def build_publication_allowlist(
    repo_root: Path, *, validation_root_path: Path, allowlist_path: Path,
    extras: Sequence[Path] = (),
) -> Mapping[str, Any]:
    repo_root = repo_root.resolve()
    root_path = _safe_relative(repo_root, validation_root_path)
    self_path = Path(allowlist_path)
    if self_path.is_absolute() or ".." in self_path.parts or not self_path.parts:
        raise ValueError("publication allowlist path is not repository-relative")
    root = json.loads((repo_root / root_path).read_text(encoding="utf-8"))
    validate_manifest(repo_root, root)
    paths: set[Path] = {
        root_path,
        _safe_relative(repo_root, root["full_unit_junit"]["path"]),
        _safe_relative(repo_root, root["full_unit_execution_receipt"]["path"]),
        _safe_relative(
            repo_root,
            "artifacts/unknown_taxonomy_v2/phase10/validation-verification-key.json",
        ),
    }
    for extra in extras:
        paths.add(_safe_relative(repo_root, extra))
    for matrix in root["matrices"]:
        matrix_path = _safe_relative(repo_root, matrix["path"] + "/" + MATRIX_PUBLICATION_MANIFEST_FILE).parent
        for name in (
            MATRIX_PUBLICATION_MANIFEST_FILE, "run_health_summary.json",
            PAIR_STATUS_PUBLIC_KEY_FILE, MATRIX_EXECUTION_RECEIPT_FILE,
        ):
            paths.add(_safe_relative(repo_root, matrix_path / name))
        publication = json.loads(
            (repo_root / matrix_path / MATRIX_PUBLICATION_MANIFEST_FILE).read_text(encoding="utf-8")
        )
        for relative in publication["expected_pair_status_paths"]:
            status_path = _safe_relative(repo_root, matrix_path / relative)
            paths.add(status_path)
            status = json.loads((repo_root / status_path).read_text(encoding="utf-8"))
            target = status["pair_execution_target"]
            for field in ("source_path", "left_binary_path", "right_binary_path"):
                paths.add(_safe_relative(repo_root, target[field]))
    rows = [
        {"path": path.as_posix(), "sha256": sha256_file(repo_root / path)}
        for path in sorted(paths)
    ]
    force_add_paths = [
        row["path"] for row in rows
        if subprocess.run(
            ("git", "check-ignore", "--no-index", "-q", "--", row["path"]),
            cwd=repo_root, check=False,
        ).returncode == 0
    ]
    regular_add_paths = sorted(
        {row["path"] for row in rows} - set(force_add_paths) | {self_path.as_posix()}
    )
    body = {
        "schema": SCHEMA,
        "authority_kind": "Phase10PublicationAllowlist",
        "validation_root_path": root_path.as_posix(),
        "self_path": self_path.as_posix(),
        "artifacts": rows,
        "force_add_paths": force_add_paths,
        "regular_add_paths": regular_add_paths,
    }
    return {**body, "artifact_digest": authority_digest(body)}


def validate_publication_allowlist(repo_root: Path, payload: Mapping[str, Any]) -> None:
    required = {
        "schema", "authority_kind", "validation_root_path", "self_path",
        "artifacts", "force_add_paths", "regular_add_paths", "artifact_digest",
    }
    if not isinstance(payload, Mapping) or set(payload) != required:
        raise ValueError("Phase-10 publication allowlist schema differs")
    body = {key: payload[key] for key in required - {"artifact_digest"}}
    if (
        payload["schema"] != SCHEMA
        or payload["authority_kind"] != "Phase10PublicationAllowlist"
        or payload["artifact_digest"] != authority_digest(body)
        or type(payload["artifacts"]) is not list
        or type(payload["force_add_paths"]) is not list
        or type(payload["regular_add_paths"]) is not list
    ):
        raise ValueError("Phase-10 publication allowlist body is invalid")
    actual = build_publication_allowlist(
        repo_root, validation_root_path=Path(payload["validation_root_path"]),
        allowlist_path=Path(payload["self_path"]),
        extras=tuple(
            Path(row["path"]) for row in payload["artifacts"]
            if str(row["path"]).endswith((".md",))
        ),
    )
    if actual != payload:
        raise ValueError("Phase-10 publication allowlist drifted")


def validate_staged_index(repo_root: Path, payload: Mapping[str, Any]) -> None:
    """Require a publication-only index with exact paths and content hashes."""
    validate_publication_allowlist(repo_root, payload)
    expected = {row["path"]: row["sha256"] for row in payload["artifacts"]}
    expected[payload["self_path"]] = sha256_file(repo_root / payload["self_path"])
    staged = subprocess.run(
        ("git", "diff", "--cached", "--name-only", "--diff-filter=ACMR"),
        cwd=repo_root, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True,
    ).stdout.splitlines()
    if set(staged) != set(expected) or len(staged) != len(expected):
        raise ValueError("staged publication paths differ from exact allowlist scope")
    for path, digest in expected.items():
        blob = subprocess.run(
            ("git", "show", f":{path}"), cwd=repo_root, check=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        ).stdout
        if hashlib.sha256(blob).hexdigest() != digest:
            raise ValueError(f"staged publication blob differs: {path}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--validation-root", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--extra", action="append", default=[])
    parser.add_argument("--validate", action="store_true")
    parser.add_argument("--validate-staged-index", action="store_true")
    args = parser.parse_args(argv)
    repo_root = Path(args.repo_root).resolve()
    output = Path(args.output)
    if args.validate or args.validate_staged_index:
        loaded = json.loads(output.read_text(encoding="utf-8"))
        if args.validate_staged_index:
            validate_staged_index(repo_root, loaded)
        else:
            validate_publication_allowlist(repo_root, loaded)
    else:
        payload = build_publication_allowlist(
            repo_root, validation_root_path=Path(args.validation_root),
            allowlist_path=output.relative_to(repo_root) if output.is_absolute() else output,
            extras=tuple(Path(value) for value in args.extra),
        )
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
