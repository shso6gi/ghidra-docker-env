from __future__ import annotations

import copy
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.equivalence.v2.census_contract import (
    CensusManifest,
    CensusStatus,
    CoverageInputs,
    compute_canonical_census,
)
from scripts.function_tracer_pcode.equivalence.v2.contracts import CensusMode
from scripts.function_tracer_pcode.equivalence.v2.legacy_codec import (
    LegacyDiagnosticByteEnvelope,
    LosslessLegacyByteDecoder,
)
from scripts.function_tracer_pcode.validation.phase7_legacy_baseline import (
    EXPECTED_LEGACY_SUMMARY_COUNT,
    LEGACY_BASELINE_RELATIVE_ROOT,
    _entry_id,
    _json_digest,
    build_phase7_legacy_baseline_manifest,
    decode_and_validate_phase7_legacy_baseline,
)


REPO_ROOT = Path(__file__).resolve().parents[4]


def _redigest(manifest):
    body = {key: value for key, value in manifest.items() if key != "manifest_digest"}
    manifest["manifest_digest"] = _json_digest(body)


@pytest.fixture(scope="module")
def manifest():
    saved_summaries = tuple(
        (REPO_ROOT / LEGACY_BASELINE_RELATIVE_ROOT).rglob(
            "results_summary.txt"
        )
    )
    if len(saved_summaries) != EXPECTED_LEGACY_SUMMARY_COUNT:
        pytest.skip(
            "requires the external 411-summary legacy diagnostic fixture"
        )
    return build_phase7_legacy_baseline_manifest(REPO_ROOT)


def test_phase7_legacy_manifest_binds_exact_ordered_411_raw_files(manifest):
    assert manifest["entry_count"] == EXPECTED_LEGACY_SUMMARY_COUNT == 411
    entries = manifest["entries"]
    assert [row["ordinal"] for row in entries] == list(range(411))
    assert len({row["entry_id"] for row in entries}) == 411
    assert all(row["raw_length"] >= 0 and len(row["raw_sha256"]) == 64 for row in entries)

    envelopes = decode_and_validate_phase7_legacy_baseline(REPO_ROOT, manifest)
    assert len(envelopes) == 411
    assert [item.entry_id for item in envelopes] == [row["entry_id"] for row in entries]
    assert all(item.non_authoritative is True for item in envelopes)
    assert all(item.encode_lossless() == item.raw_payload for item in envelopes)


def test_phase7_legacy_manifest_rejects_drop_duplicate_reorder_and_digest_drift(manifest):
    dropped = copy.deepcopy(manifest)
    dropped["entries"].pop()
    _redigest(dropped)
    with pytest.raises(ValueError, match="exactly 411"):
        decode_and_validate_phase7_legacy_baseline(REPO_ROOT, dropped)

    reordered = copy.deepcopy(manifest)
    reordered["entries"][0], reordered["entries"][1] = (
        reordered["entries"][1], reordered["entries"][0]
    )
    _redigest(reordered)
    with pytest.raises(ValueError, match="ordinals"):
        decode_and_validate_phase7_legacy_baseline(REPO_ROOT, reordered)

    duplicated = copy.deepcopy(manifest)
    duplicated["entries"][1] = copy.deepcopy(duplicated["entries"][0])
    _redigest(duplicated)
    with pytest.raises(ValueError, match="ordinals|duplicated"):
        decode_and_validate_phase7_legacy_baseline(REPO_ROOT, duplicated)

    drifted = copy.deepcopy(manifest)
    drifted["entries"][0]["raw_sha256"] = "0" * 64
    _redigest(drifted)
    with pytest.raises(ValueError, match="entry ID|raw-byte"):
        decode_and_validate_phase7_legacy_baseline(REPO_ROOT, drifted)


def test_phase7_legacy_validator_rejects_self_consistent_source_and_id_substitution(manifest):
    wrong_root = copy.deepcopy(manifest)
    wrong_root["source_root"] = "logs"
    _redigest(wrong_root)
    with pytest.raises(ValueError, match="source root"):
        decode_and_validate_phase7_legacy_baseline(REPO_ROOT, wrong_root)

    substituted = copy.deepcopy(manifest)
    row = substituted["entries"][0]
    replacement = REPO_ROOT / "docs" / "implementation-plan.md"
    raw = replacement.read_bytes()
    import hashlib

    row["source_path"] = "docs/implementation-plan.md"
    row["raw_length"] = len(raw)
    row["raw_sha256"] = hashlib.sha256(raw).hexdigest()
    row["entry_id"] = _entry_id(
        ordinal=row["ordinal"], source_path=row["source_path"],
        raw_length=row["raw_length"], raw_sha256=row["raw_sha256"],
    )
    _redigest(substituted)
    with pytest.raises(ValueError, match="ordered discovered source set"):
        decode_and_validate_phase7_legacy_baseline(REPO_ROOT, substituted)

    forged_id = copy.deepcopy(manifest)
    forged_id["entries"][0]["entry_id"] = "f" * 64
    _redigest(forged_id)
    with pytest.raises(ValueError, match="entry ID"):
        decode_and_validate_phase7_legacy_baseline(REPO_ROOT, forged_id)


def test_phase7_lossless_decoder_is_factory_owned_and_byte_exact():
    raw = b"\xfflegacy\x00\r\n"
    import hashlib

    envelope = LosslessLegacyByteDecoder.decode(
        entry_id="entry",
        ordinal=0,
        source_path="legacy.bin",
        raw_length=len(raw),
        raw_sha256=hashlib.sha256(raw).hexdigest(),
        raw_payload=raw,
    )
    assert envelope.encode_lossless() == raw
    with pytest.raises(ValueError, match="lossless decoder"):
        LegacyDiagnosticByteEnvelope(
            "entry", 0, "legacy.bin", len(raw), hashlib.sha256(raw).hexdigest(), raw, True
        )
    with pytest.raises(ValueError, match="binding mismatch"):
        LosslessLegacyByteDecoder.decode(
            entry_id="entry", ordinal=0, source_path="legacy.bin",
            raw_length=len(raw) + 1, raw_sha256=hashlib.sha256(raw).hexdigest(),
            raw_payload=raw,
        )


def test_phase7_diagnostic_envelope_is_rejected_by_canonical_census():
    raw = b"legacy"
    import hashlib

    envelope = LosslessLegacyByteDecoder.decode(
        entry_id="entry", ordinal=0, source_path="legacy.bin",
        raw_length=len(raw), raw_sha256=hashlib.sha256(raw).hexdigest(), raw_payload=raw,
    )
    manifest = CensusManifest("m", CensusMode.V2_CANONICAL, "head", "config", ())
    result = compute_canonical_census(
        manifest, (envelope,), (), (), coverage_inputs=CoverageInputs(())
    )
    assert result.status is CensusStatus.INVALID
    assert "exact candidate authorities" in result.diagnostic_errors[0]
