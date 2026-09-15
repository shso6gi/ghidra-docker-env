# -*- coding: utf-8 -*-
"""Which binaries a finished run actually compared, and whether two runs agree.

Issue #15 PR-15-B.  A before/after comparison only means something when both
runs analysed the same bytes.  This tool answers that from the runs themselves:

``build``
    walk a result tree's signed ``*.pair-status.json`` files and collect, for
    each side of each pair, the ``pair_execution_target``'s binary path, binary
    id and sha256.  The digests are the ones the runner sealed into the target
    *before* the pair ran, so they describe the binary that was compared, not
    whatever happens to be on disk now.  With ``--binary-root`` every one of
    them is re-hashed there and a missing or differing file is an error --
    "I could not look" must not read as "they agree".

``compare``
    two manifests agree only when they name **the same set of keys** and every
    key carries the same digest.  A key present on one side only -- a binary
    that appeared, disappeared, moved or was renamed -- is a failure just like
    a changed digest, because either one makes "the outcome changed" ambiguous.

Exit 0 when the manifests agree, 1 when they do not (or an input is broken).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

# The soundness gate and this tool must agree on what counts as a digest, so
# there is one definition: a value that is not a full sha256 is not "a digest
# that happens to differ", it is one neither tool can compare.
from scripts.function_tracer_pcode.reporting.pair_outcomes import normalized_sha256

MANIFEST_HEADER = "# eqbench-binary-manifest-v1"
COLUMNS = ("sample_identity", "binary_id", "binary_relative_path", "sha256")

PAIR_STATUS_SUFFIX = ".pair-status.json"

EXIT_OK = 0
EXIT_FAIL = 1

Key = Tuple[str, str, str]


class ManifestError(Exception):
    """The run tree or a manifest file cannot be read as one."""


def _sha256_of(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def exact_sha256(value: object) -> str:
    """``value`` as a lower-case sha256, or ``ManifestError``."""

    digest = normalized_sha256(value)
    if digest is None:
        raise ManifestError(f"binary digest is not a sha256: {value!r}")
    return digest


def _sides(target: Mapping[str, object]) -> Iterable[Tuple[str, str, str]]:
    for side in ("left", "right"):
        binary_id = target.get(f"{side}_binary_id")
        path = target.get(f"{side}_binary_path")
        if not all(isinstance(value, str) and value for value in (binary_id, path)):
            raise ManifestError(
                f"pair execution target lacks a usable {side} binary: {target!r}"
            )
        yield str(binary_id), str(path), exact_sha256(target.get(f"{side}_binary_sha256"))


def build_manifest(
    run_dir: Path, *, binary_root: Optional[Path] = None,
) -> List[Tuple[Key, str]]:
    """Collect every binary this run's pairs named, one row per binary.

    A binary used by many pairs contributes one row; two pairs that disagree
    about its digest is an error, not a row that silently keeps one of them.
    """

    rows: Dict[Key, str] = {}
    statuses = sorted(Path(run_dir).rglob(f"*{PAIR_STATUS_SUFFIX}"))
    if not statuses:
        raise ManifestError(f"no pair status under: {run_dir}")
    for status_path in statuses:
        try:
            payload = json.loads(status_path.read_text(encoding="utf-8"))
        except (OSError, ValueError) as exc:
            raise ManifestError(f"unreadable pair status: {status_path}: {exc}") from exc
        target = payload.get("pair_execution_target") if isinstance(payload, dict) else None
        if not isinstance(target, dict):
            # A pair whose status carries no signed target (classification
            # failure) names no binary; it cannot contribute a row and it must
            # not be silently treated as "no binaries were used" either.
            raise ManifestError(
                f"pair status carries no execution target: {status_path}"
            )
        sample = target.get("sample_identity")
        if not isinstance(sample, str) or not sample:
            raise ManifestError(f"pair status carries no sample identity: {status_path}")
        for binary_id, path, sha256 in _sides(target):
            key: Key = (sample, binary_id, path)
            previous = rows.get(key)
            if previous is not None and previous != sha256:
                raise ManifestError(
                    f"two pairs disagree about {key}: {previous} != {sha256}"
                )
            rows[key] = sha256
    if binary_root is not None:
        _verify_against_disk(rows, Path(binary_root))
    return sorted(rows.items())


def _verify_against_disk(rows: Mapping[Key, str], binary_root: Path) -> None:
    """Re-hash every binary the run named; missing or different is an error.

    ``--binary-root`` is a claim: "the tree the run compared is still here".
    A file that is absent refutes that claim just as much as one that changed,
    and skipping it would turn an unverifiable manifest into a verified one --
    the exact failure this tool exists to prevent.  A caller that only wants
    the manifest (because the working root is gone) simply omits the option.
    """

    for (sample, binary_id, relative), sha256 in rows.items():
        candidate = binary_root / relative
        if not candidate.is_file():
            raise ManifestError(
                f"binary the run compared is not under the binary root: "
                f"{sample} {binary_id} {relative} (looked at {candidate})"
            )
        observed = _sha256_of(candidate)
        if observed != sha256:
            raise ManifestError(
                f"binary on disk differs from the one the run compared: "
                f"{sample} {binary_id} {relative}: {observed} != {sha256}"
            )


def format_manifest(rows: Sequence[Tuple[Key, str]]) -> str:
    lines = [MANIFEST_HEADER, "\t".join(COLUMNS)]
    for (sample, binary_id, relative), sha256 in rows:
        lines.append("\t".join((sample, binary_id, relative, sha256)))
    return "\n".join(lines) + "\n"


def parse_manifest(path: Path) -> Dict[Key, str]:
    text = Path(path).read_text(encoding="utf-8")
    lines = text.splitlines()
    if not lines or lines[0] != MANIFEST_HEADER:
        raise ManifestError(f"not an eqbench binary manifest: {path}")
    if len(lines) < 2 or lines[1].split("\t") != list(COLUMNS):
        raise ManifestError(f"binary manifest has unexpected columns: {path}")
    rows: Dict[Key, str] = {}
    for line in lines[2:]:
        if not line:
            continue
        fields = line.split("\t")
        if len(fields) != len(COLUMNS):
            raise ManifestError(f"binary manifest row is malformed: {path}: {line!r}")
        sample, binary_id, relative, sha256 = fields
        if not all((sample, binary_id, relative)):
            raise ManifestError(f"binary manifest row has an empty field: {path}: {line!r}")
        key: Key = (sample, binary_id, relative)
        if key in rows:
            raise ManifestError(f"duplicate binary manifest row: {path}: {key}")
        rows[key] = exact_sha256(sha256)
    if not rows:
        raise ManifestError(f"binary manifest holds no binary: {path}")
    return rows


def compare_manifests(
    before: Mapping[Key, str], after: Mapping[Key, str],
) -> List[str]:
    """Every difference, as report lines.  An empty list means the runs agree."""

    problems: List[str] = []
    for key in sorted(set(before) - set(after)):
        problems.append(f"missing in after: {' '.join(key)}")
    for key in sorted(set(after) - set(before)):
        problems.append(f"only in after: {' '.join(key)}")
    for key in sorted(set(before) & set(after)):
        if before[key] != after[key]:
            problems.append(
                f"sha256 differs: {' '.join(key)}: {before[key]} != {after[key]}"
            )
    return problems


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    commands = parser.add_subparsers(dest="command", required=True)

    build_command = commands.add_parser(
        "build", help="collect the binaries a run's pairs compared",
    )
    build_command.add_argument("--run-dir", type=Path, required=True)
    build_command.add_argument("--output", type=Path, default=None)
    build_command.add_argument(
        "--binary-root", type=Path, default=None,
        help=(
            "re-hash every binary under this root (the target paths are repo "
            "relative, so this is normally the repo root) and fail when one is "
            "missing or differs from what the run compared"
        ),
    )

    compare_command = commands.add_parser(
        "compare", help="require the same key set and the same digests",
    )
    compare_command.add_argument("--before", type=Path, required=True)
    compare_command.add_argument("--after", type=Path, required=True)
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        if args.command == "build":
            rows = build_manifest(args.run_dir, binary_root=args.binary_root)
            text = format_manifest(rows)
            if args.output is not None:
                args.output.parent.mkdir(parents=True, exist_ok=True)
                args.output.write_text(text, encoding="utf-8")
                print(f"binaries: {len(rows)} -> {args.output}")
            else:
                sys.stdout.write(text)
            return EXIT_OK
        before = parse_manifest(args.before)
        after = parse_manifest(args.after)
    except (ManifestError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return EXIT_FAIL
    problems = compare_manifests(before, after)
    for problem in problems:
        print(problem)
    if problems:
        print(f"BINARY MANIFEST: DIFFERS ({len(problems)})")
        return EXIT_FAIL
    print(f"BINARY MANIFEST: IDENTICAL ({len(before)} binaries)")
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
