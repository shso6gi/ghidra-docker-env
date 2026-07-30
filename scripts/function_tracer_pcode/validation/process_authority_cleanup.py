"""Remove one ephemeral process-authority tree without following symlinks."""

from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path
from typing import Optional, Sequence


_RUN_DIRECTORY_PATTERN = re.compile(r"eqbench-run\.[A-Za-z0-9]+")
_EXECUTION_NONCE_PATTERN = re.compile(r"[0-9a-f]{24}")
_DIRECTORY_OPEN_FLAGS = (
    os.O_RDONLY
    | os.O_DIRECTORY
    | getattr(os, "O_CLOEXEC", 0)
    | getattr(os, "O_NOFOLLOW", 0)
)


class ProcessAuthorityCleanupError(RuntimeError):
    """The requested cleanup is outside the no-follow deletion boundary."""


def _open_directory(name: str, *, dir_fd: Optional[int] = None) -> int:
    return os.open(name, _DIRECTORY_OPEN_FLAGS, dir_fd=dir_fd)


def _remove_directory_contents(directory_fd: int) -> None:
    with os.scandir(directory_fd) as entries:
        for entry in entries:
            if entry.is_dir(follow_symlinks=False):
                child_fd = _open_directory(entry.name, dir_fd=directory_fd)
                try:
                    _remove_directory_contents(child_fd)
                finally:
                    os.close(child_fd)
                os.rmdir(entry.name, dir_fd=directory_fd)
            else:
                os.unlink(entry.name, dir_fd=directory_fd)


def remove_process_authority_nonce(
    *,
    tmp_root: Path,
    run_tmpdir: Path,
    checkpoint_root: Path,
    execution_nonce: str,
) -> bool:
    """Remove the exact nonce directory and return whether it existed."""

    tmp_root = Path(os.path.abspath(tmp_root))
    run_tmpdir = Path(os.path.abspath(run_tmpdir))
    checkpoint_root = Path(os.path.abspath(checkpoint_root))
    if (
        run_tmpdir.parent != tmp_root
        or _RUN_DIRECTORY_PATTERN.fullmatch(run_tmpdir.name) is None
        or checkpoint_root != run_tmpdir / "process-authority"
        or _EXECUTION_NONCE_PATTERN.fullmatch(execution_nonce) is None
    ):
        raise ProcessAuthorityCleanupError(
            "process-authority cleanup target is outside the EqBench run boundary"
        )

    tmp_root_fd = _open_directory(os.fspath(tmp_root))
    try:
        run_fd = _open_directory(run_tmpdir.name, dir_fd=tmp_root_fd)
        try:
            try:
                checkpoint_fd = _open_directory("process-authority", dir_fd=run_fd)
            except FileNotFoundError:
                return False
            try:
                try:
                    nonce_fd = _open_directory(
                        execution_nonce, dir_fd=checkpoint_fd
                    )
                except FileNotFoundError:
                    return False
                try:
                    _remove_directory_contents(nonce_fd)
                finally:
                    os.close(nonce_fd)
                os.rmdir(execution_nonce, dir_fd=checkpoint_fd)
                return True
            finally:
                os.close(checkpoint_fd)
        finally:
            os.close(run_fd)
    finally:
        os.close(tmp_root_fd)


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tmp-root", required=True)
    parser.add_argument("--run-tmpdir", required=True)
    parser.add_argument("--checkpoint-root", required=True)
    parser.add_argument("--execution-nonce", required=True)
    args = parser.parse_args(argv)
    try:
        remove_process_authority_nonce(
            tmp_root=Path(args.tmp_root),
            run_tmpdir=Path(args.run_tmpdir),
            checkpoint_root=Path(args.checkpoint_root),
            execution_nonce=args.execution_nonce,
        )
    except (OSError, ProcessAuthorityCleanupError) as exc:
        print(f"process-authority cleanup failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
