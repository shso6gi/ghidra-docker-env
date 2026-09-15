# -*- coding: utf-8 -*-
"""Issue #15 PR-15-B: two runs are comparable only on identical binaries.

``binary_manifest`` answers "which bytes did this run actually compare?" from
the signed execution target of every pair, and ``compare`` requires the two
manifests to name the same key set *and* the same digest for every key.  A
binary that appeared, disappeared, moved or changed all fail the same way,
because any of them makes an outcome difference ambiguous.
"""
from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts.eqbench import binary_manifest

SHA_A = "a" * 64
SHA_B = "b" * 64


def write_pair_status(
    root: Path, sample: str, function: str, left: str, right: str,
    *, left_path: str, right_path: str, left_sha: str = SHA_A, right_sha: str = SHA_B,
    target=True,
) -> Path:
    path = root / sample / function / f"{function}_{left}_{right}.pair-status.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {"canonical_outcome": "UNKNOWN"}
    if target:
        payload["pair_execution_target"] = {
            "sample_identity": sample,
            "function_name": function,
            "left_binary_id": left,
            "right_binary_id": right,
            "left_binary_path": left_path,
            "right_binary_path": right_path,
            "left_binary_sha256": left_sha,
            "right_binary_sha256": right_sha,
        }
    path.write_text(json.dumps(payload), encoding="utf-8")
    return path


def run_tree(root: Path, **overrides) -> Path:
    write_pair_status(
        root, "a/b/Eq/newV", "f", "B1", "B2",
        left_path="work/a-O0", right_path="work/a-O1", **overrides,
    )
    return root


def manifest_of(root: Path, **kwargs):
    return dict(binary_manifest.build_manifest(root, **kwargs))


def test_one_row_per_binary_even_when_many_pairs_share_it(tmp_path):
    root = tmp_path / "run"
    write_pair_status(root, "a/b/Eq/newV", "f", "B1", "B2",
                      left_path="work/a-O0", right_path="work/a-O1")
    write_pair_status(root, "a/b/Eq/newV", "f", "B1", "B3",
                      left_path="work/a-O0", right_path="work/a-O2",
                      right_sha="c" * 64)

    rows = manifest_of(root)

    assert rows == {
        ("a/b/Eq/newV", "B1", "work/a-O0"): SHA_A,
        ("a/b/Eq/newV", "B2", "work/a-O1"): SHA_B,
        ("a/b/Eq/newV", "B3", "work/a-O2"): "c" * 64,
    }


def test_two_pairs_disagreeing_about_one_binary_is_an_error(tmp_path):
    root = tmp_path / "run"
    write_pair_status(root, "a/b/Eq/newV", "f", "B1", "B2",
                      left_path="work/a-O0", right_path="work/a-O1")
    write_pair_status(root, "a/b/Eq/newV", "f", "B1", "B3",
                      left_path="work/a-O0", right_path="work/a-O2",
                      left_sha="c" * 64)

    with pytest.raises(binary_manifest.ManifestError, match="disagree"):
        manifest_of(root)


@pytest.mark.parametrize("overrides,match", [
    pytest.param({"target": False}, "no execution target", id="no-target"),
    pytest.param({"left_sha": ""}, "usable left binary", id="empty-digest"),
])
def test_a_status_that_names_no_binary_fails_the_build(tmp_path, overrides, match):
    with pytest.raises(binary_manifest.ManifestError, match=match):
        manifest_of(run_tree(tmp_path / "run", **overrides))


def test_an_empty_tree_is_not_an_empty_manifest(tmp_path):
    (tmp_path / "run").mkdir()
    with pytest.raises(binary_manifest.ManifestError, match="no pair status"):
        manifest_of(tmp_path / "run")


def test_a_rebuilt_binary_on_disk_fails_the_build(tmp_path):
    root = run_tree(tmp_path / "run")
    binaries = tmp_path / "root"
    (binaries / "work").mkdir(parents=True)
    (binaries / "work" / "a-O0").write_bytes(b"rebuilt")

    with pytest.raises(binary_manifest.ManifestError, match="differs from the one"):
        manifest_of(root, binary_root=binaries)


def test_a_binary_that_is_gone_does_not_fail_the_build(tmp_path):
    """The manifest records what the run compared; a working root may be deleted."""

    root = run_tree(tmp_path / "run")
    assert len(manifest_of(root, binary_root=tmp_path / "absent")) == 2


def test_a_binary_still_on_disk_is_rehashed_and_accepted(tmp_path):
    import hashlib

    content = b"the exact binary"
    digest = hashlib.sha256(content).hexdigest()
    root = tmp_path / "run"
    write_pair_status(root, "a/b/Eq/newV", "f", "B1", "B2",
                      left_path="work/a-O0", right_path="work/a-O1",
                      left_sha=digest, right_sha=digest)
    binaries = tmp_path / "root"
    (binaries / "work").mkdir(parents=True)
    for name in ("a-O0", "a-O1"):
        (binaries / "work" / name).write_bytes(content)

    assert len(manifest_of(root, binary_root=binaries)) == 2


# ---------------------------------------------------------------------------
# compare
# ---------------------------------------------------------------------------


BASE = {
    ("a/b/Eq/newV", "B1", "work/a-O0"): SHA_A,
    ("a/b/Eq/newV", "B2", "work/a-O1"): SHA_B,
}


def test_identical_manifests_compare_equal():
    assert binary_manifest.compare_manifests(BASE, dict(BASE)) == []


@pytest.mark.parametrize("after,expected", [
    pytest.param(
        {key: value for key, value in BASE.items() if key[1] != "B2"},
        "missing in after", id="missing-key",
    ),
    pytest.param(
        {**BASE, ("a/b/Eq/newV", "B3", "work/a-O2"): SHA_A},
        "only in after", id="extra-key",
    ),
    pytest.param(
        {**BASE, ("a/b/Eq/newV", "B2", "work/a-O1"): "c" * 64},
        "sha256 differs", id="changed-digest",
    ),
    pytest.param(
        {("a/b/Eq/newV", "B1", "moved/a-O0"): SHA_A,
         ("a/b/Eq/newV", "B2", "work/a-O1"): SHA_B},
        "missing in after", id="moved-path",
    ),
    pytest.param(
        {("a/b/Eq/newV", "B9", "work/a-O0"): SHA_A,
         ("a/b/Eq/newV", "B2", "work/a-O1"): SHA_B},
        "missing in after", id="renamed-binary-id",
    ),
])
def test_any_difference_in_the_key_set_or_a_digest_fails(after, expected):
    problems = binary_manifest.compare_manifests(BASE, after)
    assert problems and any(problem.startswith(expected) for problem in problems)


# ---------------------------------------------------------------------------
# the file format and the CLI
# ---------------------------------------------------------------------------


def test_a_manifest_round_trips_through_its_file(tmp_path):
    path = tmp_path / "m.txt"
    path.write_text(binary_manifest.format_manifest(sorted(BASE.items())), encoding="utf-8")
    assert binary_manifest.parse_manifest(path) == BASE


@pytest.mark.parametrize("text,match", [
    pytest.param("nope\n", "not an eqbench binary manifest", id="header"),
    pytest.param(f"{binary_manifest.MANIFEST_HEADER}\na\tb\n", "unexpected columns",
                 id="columns"),
    pytest.param(
        binary_manifest.format_manifest(sorted(BASE.items())) + "short\trow\n",
        "malformed", id="short-row",
    ),
    pytest.param(
        binary_manifest.format_manifest(sorted(BASE.items()))
        + "a/b/Eq/newV\tB1\twork/a-O0\t" + "c" * 64 + "\n",
        "duplicate", id="duplicate-row",
    ),
    pytest.param(
        binary_manifest.MANIFEST_HEADER + "\n" + "\t".join(binary_manifest.COLUMNS) + "\n",
        "holds no binary", id="empty",
    ),
])
def test_a_manifest_file_that_cannot_be_trusted_is_refused(tmp_path, text, match):
    path = tmp_path / "m.txt"
    path.write_text(text, encoding="utf-8")
    with pytest.raises(binary_manifest.ManifestError, match=match):
        binary_manifest.parse_manifest(path)


def test_the_cli_builds_and_compares(tmp_path, capsys):
    before_run, after_run = tmp_path / "before", tmp_path / "after"
    run_tree(before_run)
    run_tree(after_run)
    before, after = tmp_path / "before.txt", tmp_path / "after.txt"

    for run, output in ((before_run, before), (after_run, after)):
        assert binary_manifest.main([
            "build", "--run-dir", str(run), "--output", str(output),
        ]) == binary_manifest.EXIT_OK
    capsys.readouterr()

    assert binary_manifest.main([
        "compare", "--before", str(before), "--after", str(after),
    ]) == binary_manifest.EXIT_OK
    assert "BINARY MANIFEST: IDENTICAL (2 binaries)" in capsys.readouterr().out

    write_pair_status(after_run, "a/b/Eq/newV", "f", "B1", "B3",
                      left_path="work/a-O0", right_path="work/a-O2")
    assert binary_manifest.main([
        "build", "--run-dir", str(after_run), "--output", str(after),
    ]) == binary_manifest.EXIT_OK
    capsys.readouterr()
    assert binary_manifest.main([
        "compare", "--before", str(before), "--after", str(after),
    ]) == binary_manifest.EXIT_FAIL
    assert "BINARY MANIFEST: DIFFERS" in capsys.readouterr().out


def test_the_cli_reports_a_broken_input_as_a_failure(tmp_path, capsys):
    missing = tmp_path / "missing.txt"
    assert binary_manifest.main([
        "compare", "--before", str(missing), "--after", str(missing),
    ]) == binary_manifest.EXIT_FAIL
    assert "error:" in capsys.readouterr().err
