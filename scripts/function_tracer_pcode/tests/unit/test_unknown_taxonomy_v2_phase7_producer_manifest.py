import copy
import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.equivalence.v2.call_effect_sites import (
    CALL_EFFECT_PROOF_BATCH_SITE,
)
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
    assert len(ids) == len(set(ids)) == stored["site_count"] == 28
    assert "pairwise-return-width-relation-blocker" not in ids
    assert "obligation-stage-final-eq-closure" not in ids
    assert "sat-safety-blocker-observed" in ids
    call_effect_batch = next(
        row
        for row in stored["sites"]
        if row["producer_site_manifest_id"]
        == CALL_EFFECT_PROOF_BATCH_SITE.site_id
    )
    assert tuple(call_effect_batch["allowed_producer_ids"]) == (
        CALL_EFFECT_PROOF_BATCH_SITE.producer_id,
    )
    assert tuple(call_effect_batch["allowed_dispositions"]) == (
        CALL_EFFECT_PROOF_BATCH_SITE.disposition,
    )
    prerequisite_site = next(
        row
        for row in stored["sites"]
        if row["producer_site_manifest_id"]
        == "call-effect-producer-prerequisite"
    )
    assert {
        tuple(slot["allowed_reason_ids"])
        for slot in prerequisite_site["expected_cause_slots"]
    } == {
        ("abi_argument_relation_unproven",),
        ("callsite_correspondence_unproven",),
        ("memory_final_state_correspondence_unproven",),
        ("pure_call_semantics_unproven",),
    }
    sat_sites = {
        row["producer_site_manifest_id"]: (
            tuple(row["allowed_producer_ids"]),
            tuple(row["allowed_dispositions"]),
            row["emitter"],
        )
        for row in stored["sites"]
        if row["producer_site_manifest_id"].startswith("sat-safety-")
    }
    assert sat_sites == {
        "sat-safety-blocker-observed": (
            ("sat_unsafety_reason_producer",),
            ("ELIGIBLE",),
            "emit_sat_safety_signal",
        ),
        "sat-safety-blocker-completed": (
            ("sat_unsafety_resolution_producer",),
            ("DECISIVE",),
            "emit_sat_safety_completion_if_observed",
        ),
        "sat-safety-ambiguity-observed": (
            ("sat_counterexample_ambiguity_producer",),
            ("ELIGIBLE",),
            "emit_sat_safety_signal",
        ),
        "sat-safety-ambiguity-completed": (
            ("sat_counterexample_ambiguity_resolution_producer",),
            ("DECISIVE",),
            "emit_sat_safety_completion_if_observed",
        ),
    }
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
