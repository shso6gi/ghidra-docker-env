from pathlib import Path

import pytest

from scripts.function_tracer_pcode.reporting.process_authority_cleanup import (
    ProcessAuthorityCleanupError,
    remove_process_authority_nonce,
)


EXECUTION_NONCE = "0123456789abcdef01234567"


def _run_paths(
    tmp_path: Path, prefix: str = "eqbench-run"
) -> tuple[Path, Path, Path]:
    tmp_root = tmp_path / "tmp"
    run_tmpdir = tmp_root / f"{prefix}.test"
    checkpoint_root = run_tmpdir / "process-authority"
    checkpoint_root.mkdir(parents=True)
    return tmp_root, run_tmpdir, checkpoint_root


def test_cleanup_removes_only_the_exact_nonce_tree_without_following_leaf_symlink(
    tmp_path,
):
    tmp_root, run_tmpdir, checkpoint_root = _run_paths(tmp_path)
    nonce_dir = checkpoint_root / EXECUTION_NONCE
    nested = nonce_dir / "checkpoint-history"
    nested.mkdir(parents=True)
    (nested / "checkpoint.json").write_text("authority")
    outside = tmp_path / "outside"
    outside.mkdir()
    (outside / "keep.txt").write_text("keep")
    (nonce_dir / "outside-link").symlink_to(outside, target_is_directory=True)

    removed = remove_process_authority_nonce(
        tmp_root=tmp_root,
        run_tmpdir=run_tmpdir,
        checkpoint_root=checkpoint_root,
        execution_nonce=EXECUTION_NONCE,
    )

    assert removed is True
    assert not nonce_dir.exists()
    assert (outside / "keep.txt").read_text() == "keep"


def test_cleanup_accepts_neqbench_run_directory(tmp_path):
    tmp_root, run_tmpdir, checkpoint_root = _run_paths(
        tmp_path, prefix="neqbench-run"
    )
    nonce_dir = checkpoint_root / EXECUTION_NONCE
    nonce_dir.mkdir()
    (nonce_dir / "checkpoint.json").write_text("authority")

    removed = remove_process_authority_nonce(
        tmp_root=tmp_root,
        run_tmpdir=run_tmpdir,
        checkpoint_root=checkpoint_root,
        execution_nonce=EXECUTION_NONCE,
    )

    assert removed is True
    assert not nonce_dir.exists()


def test_cleanup_rejects_symlinked_checkpoint_parent_without_touching_target(
    tmp_path,
):
    tmp_root = tmp_path / "tmp"
    run_tmpdir = tmp_root / "eqbench-run.test"
    run_tmpdir.mkdir(parents=True)
    outside_checkpoint = tmp_path / "outside-process-authority"
    outside_nonce = outside_checkpoint / EXECUTION_NONCE
    outside_nonce.mkdir(parents=True)
    (outside_nonce / "keep.txt").write_text("keep")
    checkpoint_root = run_tmpdir / "process-authority"
    checkpoint_root.symlink_to(outside_checkpoint, target_is_directory=True)

    with pytest.raises(OSError):
        remove_process_authority_nonce(
            tmp_root=tmp_root,
            run_tmpdir=run_tmpdir,
            checkpoint_root=checkpoint_root,
            execution_nonce=EXECUTION_NONCE,
        )

    assert (outside_nonce / "keep.txt").read_text() == "keep"


def test_cleanup_rejects_symlinked_run_directory_without_touching_target(tmp_path):
    tmp_root = tmp_path / "tmp"
    tmp_root.mkdir()
    outside_run = tmp_path / "outside-run"
    outside_nonce = outside_run / "process-authority" / EXECUTION_NONCE
    outside_nonce.mkdir(parents=True)
    (outside_nonce / "keep.txt").write_text("keep")
    run_tmpdir = tmp_root / "eqbench-run.test"
    run_tmpdir.symlink_to(outside_run, target_is_directory=True)

    with pytest.raises(OSError):
        remove_process_authority_nonce(
            tmp_root=tmp_root,
            run_tmpdir=run_tmpdir,
            checkpoint_root=run_tmpdir / "process-authority",
            execution_nonce=EXECUTION_NONCE,
        )

    assert (outside_nonce / "keep.txt").read_text() == "keep"


def test_cleanup_rejects_lexical_checkpoint_escape(tmp_path):
    tmp_root, run_tmpdir, _ = _run_paths(tmp_path)
    outside = tmp_path / "outside" / EXECUTION_NONCE
    outside.mkdir(parents=True)

    with pytest.raises(ProcessAuthorityCleanupError):
        remove_process_authority_nonce(
            tmp_root=tmp_root,
            run_tmpdir=run_tmpdir,
            checkpoint_root=outside.parent,
            execution_nonce=EXECUTION_NONCE,
        )

    assert outside.is_dir()
