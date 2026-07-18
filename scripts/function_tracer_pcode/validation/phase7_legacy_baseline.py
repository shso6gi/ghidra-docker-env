"""Build and validate the ordered Phase 7 legacy 411-summary manifest."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Optional, Sequence

from ..equivalence.v2.legacy_codec import (
    LegacyDiagnosticByteEnvelope,
    LosslessLegacyByteDecoder,
)


PHASE7_LEGACY_BASELINE_KIND = "phase7_saved_eqbench_411_raw_byte_diagnostic"
EXPECTED_LEGACY_SUMMARY_COUNT = 411
LEGACY_BASELINE_RELATIVE_ROOT = "logs/EqBench/all_eq_matrix_current"


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _json_digest(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return _sha256(encoded.encode("utf-8"))


def _relative(path: Path, root: Path) -> str:
    return path.resolve().relative_to(root.resolve()).as_posix()


def _discover_summary_paths(root: Path) -> tuple[Path, ...]:
    baseline_root = root / LEGACY_BASELINE_RELATIVE_ROOT
    paths = tuple(sorted(
        baseline_root.rglob("results_summary.txt"), key=lambda path: path.as_posix()
    ))
    if len(paths) != EXPECTED_LEGACY_SUMMARY_COUNT:
        raise ValueError(
            f"expected {EXPECTED_LEGACY_SUMMARY_COUNT} saved legacy summaries, found {len(paths)}"
        )
    return paths


def _entry_id(*, ordinal: int, source_path: str, raw_length: int, raw_sha256: str) -> str:
    return _json_digest({
        "ordinal": ordinal,
        "source_path": source_path,
        "raw_length": raw_length,
        "raw_sha256": raw_sha256,
    })


def build_phase7_legacy_baseline_manifest(repo_root: Path) -> Mapping[str, Any]:
    root = Path(repo_root).resolve()
    baseline_root = root / LEGACY_BASELINE_RELATIVE_ROOT
    # This tuple is the discovery authority.  Do not deduplicate it.
    paths = _discover_summary_paths(root)
    entries = []
    for ordinal, path in enumerate(paths):
        raw = path.read_bytes()
        source_path = _relative(path, root)
        raw_sha256 = _sha256(raw)
        entry_id = _entry_id(
            ordinal=ordinal, source_path=source_path,
            raw_length=len(raw), raw_sha256=raw_sha256,
        )
        entries.append({
            "entry_id": entry_id,
            "ordinal": ordinal,
            "source_path": source_path,
            "raw_length": len(raw),
            "raw_sha256": raw_sha256,
        })
    body = {
        "manifest_kind": PHASE7_LEGACY_BASELINE_KIND,
        "non_authoritative": True,
        "canonical_v2_metrics": False,
        "source_root": _relative(baseline_root, root),
        "entry_count": len(entries),
        "entries": entries,
    }
    return {**body, "manifest_digest": _json_digest(body)}


def decode_and_validate_phase7_legacy_baseline(
    repo_root: Path, manifest: Mapping[str, Any],
) -> tuple[LegacyDiagnosticByteEnvelope, ...]:
    root = Path(repo_root).resolve()
    if manifest.get("manifest_kind") != PHASE7_LEGACY_BASELINE_KIND:
        raise ValueError("legacy baseline manifest kind is invalid")
    if manifest.get("non_authoritative") is not True or manifest.get("canonical_v2_metrics") is not False:
        raise ValueError("legacy baseline manifest must remain diagnostic-only")
    if manifest.get("source_root") != LEGACY_BASELINE_RELATIVE_ROOT:
        raise ValueError("legacy baseline source root is invalid")
    body = {key: value for key, value in manifest.items() if key != "manifest_digest"}
    if manifest.get("manifest_digest") != _json_digest(body):
        raise ValueError("legacy baseline manifest digest mismatch")
    entries = tuple(manifest.get("entries") or ())
    if len(entries) != EXPECTED_LEGACY_SUMMARY_COUNT or manifest.get("entry_count") != len(entries):
        raise ValueError("legacy baseline manifest must contain exactly 411 entries")
    if tuple(row.get("ordinal") for row in entries) != tuple(range(len(entries))):
        raise ValueError("legacy baseline manifest ordinals are not exact and ordered")
    entry_ids = tuple(row.get("entry_id") for row in entries)
    if len(entry_ids) != len(set(entry_ids)):
        raise ValueError("legacy baseline entry IDs are duplicated")
    discovered_paths = tuple(_relative(path, root) for path in _discover_summary_paths(root))
    manifest_paths = tuple(str(row.get("source_path") or "") for row in entries)
    if manifest_paths != discovered_paths:
        raise ValueError("legacy baseline manifest differs from ordered discovered source set")

    envelopes = []
    for row in entries:
        source_path = str(row.get("source_path") or "")
        path = (root / source_path).resolve()
        try:
            path.relative_to(root)
        except ValueError as exc:
            raise ValueError("legacy baseline path escapes repository root") from exc
        raw = path.read_bytes()
        expected_entry_id = _entry_id(
            ordinal=int(row.get("ordinal")), source_path=source_path,
            raw_length=int(row.get("raw_length")),
            raw_sha256=str(row.get("raw_sha256") or ""),
        )
        if row.get("entry_id") != expected_entry_id:
            raise ValueError("legacy baseline entry ID is not derived from its bound fields")
        envelope = LosslessLegacyByteDecoder.decode(
            entry_id=str(row.get("entry_id") or ""),
            ordinal=int(row.get("ordinal")),
            source_path=source_path,
            raw_length=int(row.get("raw_length")),
            raw_sha256=str(row.get("raw_sha256") or ""),
            raw_payload=raw,
        )
        if envelope.encode_lossless() != raw:
            raise ValueError("legacy baseline byte round-trip is not lossless")
        envelopes.append(envelope)
    if tuple(item.entry_id for item in envelopes) != entry_ids:
        raise ValueError("legacy baseline decode dropped, duplicated, or reordered entries")
    return tuple(envelopes)


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--output", required=True)
    args = parser.parse_args(argv)
    manifest = build_phase7_legacy_baseline_manifest(Path(args.repo_root))
    decode_and_validate_phase7_legacy_baseline(Path(args.repo_root), manifest)
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
