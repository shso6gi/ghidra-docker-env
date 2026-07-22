import copy
import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.validation.phase7_producer_manifest import (
    build_phase7_producer_manifest,
    validate_phase7_producer_manifest,
)


def test_phase7_producer_manifest_is_current_complete_and_unique():
    root = Path(__file__).resolve().parents[4]
    path = root / "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
    stored = json.loads(path.read_text(encoding="utf-8"))
    validate_phase7_producer_manifest(root, stored)
    assert stored["site_count"] > 0
    ids = [row["producer_site_manifest_id"] for row in stored["sites"]]
    assert len(ids) == len(set(ids)) == stored["site_count"] == 26
    assert "pairwise-return-width-relation-blocker" not in ids
    assert "obligation-stage-final-eq-closure" not in ids
    assert "sat-safety-blocker-observed" in ids
    assert all("NOT_REACHED" not in row["allowed_dispositions"] for row in stored["sites"])
    assert all(row["branch_or_attempt_contract_id"] for row in stored["sites"])
    assert all(row["allowed_producer_ids"] for row in stored["sites"])
    assert all(
        row["expected_cause_slots"]
        for row in stored["sites"]
        if "ELIGIBLE" in row["allowed_dispositions"]
    )
    assert all(
        slot["allowed_reason_ids"]
        and len(slot["allowed_reason_ids"]) == 1
        and slot["expected_domain"] == row["domain"]
        and slot["expected_target_kind"]
        and slot["expected_identity_scope"] in {"UNARY", "RELATIONAL"}
        and slot["slot_semantics"] == "ALTERNATIVE_REASON_CHOICE"
        for row in stored["sites"]
        for slot in row["expected_cause_slots"]
    )


def test_phase7_producer_manifest_rejects_drift():
    root = Path(__file__).resolve().parents[4]
    payload = build_phase7_producer_manifest(root)
    tampered = copy.deepcopy(payload)
    tampered["sites"][0]["source_sha256"] = "0" * 64
    with pytest.raises(ValueError, match="drifted"):
        validate_phase7_producer_manifest(root, tampered)
