# -*- coding: utf-8 -*-
"""Create a compact validation artifact bundle for remote triage.

The bundle intentionally avoids large pair logs by default. It captures the
artifacts that are most useful for UNKNOWN/NOT_EQ triage after a dedicated-PC
matrix run: health summaries, overall summaries, gate/index JSON, and tails of
top-level stdout logs. Gate/index JSON files larger than the configured direct
file limit are represented by ``oversized/*.skipped.txt`` markers.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import tarfile
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Optional, Sequence


DEFAULT_INCLUDE_GLOBS: Sequence[str] = (
    "**/run_health_summary.json",
    "**/run_health_summary.txt",
    "**/overall_summary.txt",
    "**/*_gate/*.json",
    "**/*_index/*.json",
    "phase*_stdout.log",
    "*_stdout.log",
)


@dataclass(frozen=True)
class BundleEntry:
    source_path: Path
    archive_path: str
    kind: str
    size_bytes: int
    sha256: str
    truncated: bool = False

    def to_dict(self) -> Dict[str, Any]:
        return {
            "source_path": str(self.source_path),
            "archive_path": self.archive_path,
            "kind": self.kind,
            "size_bytes": self.size_bytes,
            "sha256": self.sha256,
            "truncated": self.truncated,
        }


def build_validation_transfer_bundle(
    *,
    source_root: Path,
    output_path: Path,
    include_globs: Sequence[str] = DEFAULT_INCLUDE_GLOBS,
    stdout_roots: Sequence[Path] = (),
    max_stdout_tail_lines: int = 200,
    max_direct_file_bytes: int = 2_000_000,
) -> Path:
    source_root = source_root.resolve()
    stdout_roots = tuple(Path(root).resolve() for root in stdout_roots)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    candidates = _collect_candidates(source_root, include_globs)
    stdout_candidates = _collect_stdout_candidates(stdout_roots)
    entries: list[BundleEntry] = []
    with tarfile.open(output_path, "w:gz") as archive:
        for path in candidates:
            if not path.is_file():
                continue
            rel = path.relative_to(source_root).as_posix()
            if path.name.endswith("_stdout.log") and max_stdout_tail_lines >= 0:
                data = _tail_bytes(path, max_stdout_tail_lines)
                archive_path = f"stdout_tail/{rel}.tail.txt"
                _add_bytes(archive, archive_path, data)
                entries.append(
                    BundleEntry(
                        source_path=path,
                        archive_path=archive_path,
                        kind="stdout_tail",
                        size_bytes=len(data),
                        sha256=_sha256_bytes(data),
                        truncated=True,
                    )
                )
                continue
            size = path.stat().st_size
            if size > max_direct_file_bytes:
                data = (
                    f"Skipped oversized artifact: {rel}\n"
                    f"size_bytes={size}\n"
                    f"max_direct_file_bytes={max_direct_file_bytes}\n"
                ).encode("utf-8")
                archive_path = f"oversized/{rel}.skipped.txt"
                _add_bytes(archive, archive_path, data)
                entries.append(
                    BundleEntry(
                        source_path=path,
                        archive_path=archive_path,
                        kind="oversized_skip",
                        size_bytes=len(data),
                        sha256=_sha256_bytes(data),
                        truncated=True,
                    )
                )
                continue
            archive_path = f"artifacts/{rel}"
            archive.add(path, arcname=archive_path)
            entries.append(
                BundleEntry(
                    source_path=path,
                    archive_path=archive_path,
                    kind=_classify_artifact(path),
                    size_bytes=size,
                    sha256=_sha256_file(path),
                )
            )

        for stdout_root, path in stdout_candidates:
            if not path.is_file() or max_stdout_tail_lines < 0:
                continue
            rel = path.relative_to(stdout_root).as_posix()
            data = _tail_bytes(path, max_stdout_tail_lines)
            archive_path = f"stdout_tail/{rel}.tail.txt"
            _add_bytes(archive, archive_path, data)
            entries.append(
                BundleEntry(
                    source_path=path,
                    archive_path=archive_path,
                    kind="stdout_tail",
                    size_bytes=len(data),
                    sha256=_sha256_bytes(data),
                    truncated=True,
                )
            )

        manifest = {
            "manifest_kind": "validation_transfer_bundle",
            "created_at": datetime.now(timezone.utc).isoformat(),
            "source_root": str(source_root),
            "stdout_roots": [str(root) for root in stdout_roots],
            "entry_count": len(entries),
            "entries": [entry.to_dict() for entry in entries],
            "include_globs": list(include_globs),
            "max_stdout_tail_lines": max_stdout_tail_lines,
            "max_direct_file_bytes": max_direct_file_bytes,
        }
        _add_bytes(
            archive,
            "bundle_manifest.json",
            json.dumps(manifest, indent=2, sort_keys=True).encode("utf-8") + b"\n",
        )
        _add_bytes(
            archive,
            "README.txt",
            (
                "Compact validation transfer bundle.\n"
                "Large pair logs are intentionally excluded by default.\n"
                "Oversized gate/index JSON files are represented by oversized/*.skipped.txt markers.\n"
                "Use bundle_manifest.json to see included artifacts and truncation.\n"
            ).encode("utf-8"),
        )
    return output_path


def _collect_candidates(source_root: Path, include_globs: Sequence[str]) -> tuple[Path, ...]:
    seen: set[Path] = set()
    paths: list[Path] = []
    for pattern in include_globs:
        for path in sorted(source_root.glob(pattern)):
            resolved = path.resolve()
            if resolved in seen or not path.is_file():
                continue
            seen.add(resolved)
            paths.append(path)
    return tuple(paths)


def _collect_stdout_candidates(stdout_roots: Sequence[Path]) -> tuple[tuple[Path, Path], ...]:
    seen: set[Path] = set()
    paths: list[tuple[Path, Path]] = []
    for root in stdout_roots:
        for pattern in ("phase*_stdout.log", "*_stdout.log"):
            for path in sorted(root.glob(pattern)):
                resolved = path.resolve()
                if resolved in seen or not path.is_file():
                    continue
                seen.add(resolved)
                paths.append((root, path))
    return tuple(paths)


def _classify_artifact(path: Path) -> str:
    name = path.name
    if name == "overall_summary.txt":
        return "overall_summary"
    if name.startswith("run_health_summary."):
        return "run_health_summary"
    if name.endswith(".json"):
        return "gate_or_index_json"
    return "artifact"


def _tail_bytes(path: Path, line_count: int) -> bytes:
    lines = path.read_text(errors="replace").splitlines()
    tail = lines[-line_count:] if line_count > 0 else []
    return ("\n".join(tail) + ("\n" if tail else "")).encode("utf-8")


def _add_bytes(archive: tarfile.TarFile, arcname: str, data: bytes) -> None:
    import io

    info = tarfile.TarInfo(arcname)
    info.size = len(data)
    info.mtime = 0
    archive.addfile(info, io.BytesIO(data))


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Create a compact validation transfer bundle.")
    parser.add_argument("--source-root", default="logs/equivalence_all")
    parser.add_argument(
        "--stdout-root",
        action="append",
        default=None,
        help="additional root containing top-level *_stdout.log files; may be repeated",
    )
    parser.add_argument("--output", required=True)
    parser.add_argument("--include-glob", action="append", default=None)
    parser.add_argument("--max-stdout-tail-lines", type=int, default=200)
    parser.add_argument("--max-direct-file-bytes", type=int, default=2_000_000)
    args = parser.parse_args(argv)
    output = build_validation_transfer_bundle(
        source_root=Path(args.source_root),
        output_path=Path(args.output),
        include_globs=tuple(args.include_glob or DEFAULT_INCLUDE_GLOBS),
        stdout_roots=tuple(Path(root) for root in (args.stdout_root or ())),
        max_stdout_tail_lines=args.max_stdout_tail_lines,
        max_direct_file_bytes=args.max_direct_file_bytes,
    )
    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
