from __future__ import annotations

import copy
import json
from pathlib import Path
from unittest.mock import patch

import pytest

from scripts.function_tracer_pcode.equivalence.v2.phase7_cutover import (
    RETIRED_UMBRELLA_REASON_IDS,
)
from scripts.function_tracer_pcode.validation.phase7_retired_inventory import (
    RetiredReferenceRelation,
    build_phase7_retired_inventory,
    build_review_template,
    discover_retired_reference_candidates,
)


REPO_ROOT = Path(__file__).resolve().parents[4]


@pytest.fixture(scope="module")
def template():
    return build_review_template(REPO_ROOT)


def _review_suggestions(template):
    reviewed = copy.deepcopy(template)
    for row in reviewed["entries"]:
        row["review_status"] = "reviewed"
        row["reviewed_in_scope"] = True
        row["reviewed_relation"] = row["suggested_relation"]
        row["reviewed_finite_reason_set"] = row["proposed_finite_reason_set"]
        row["reviewer_disposition"] = "synthetic unit-test partition fixture"
    return reviewed


def _candidates(template):
    return tuple({
        key: value for key, value in row.items()
        if key not in {
            "review_status", "reviewed_relation", "reviewed_finite_reason_set",
            "reviewed_in_scope", "reviewer_disposition",
        }
    } for row in template["entries"])


def _build(template, reviewed):
    with patch(
        "scripts.function_tracer_pcode.validation.phase7_retired_inventory."
        "discover_retired_reference_candidates",
        return_value=_candidates(template),
    ):
        return build_phase7_retired_inventory(REPO_ROOT, reviewed)


def test_phase7_candidate_universe_is_unique_source_bound_and_finite(template):
    candidates = _candidates(template)
    assert len(candidates) == len(template["entries"])
    assert len({row["candidate_id"] for row in candidates}) == len(candidates)
    assert {row["reason_id"] for row in candidates} == RETIRED_UMBRELLA_REASON_IDS
    assert all(row["reason_id"] in row["proposed_finite_reason_set"] for row in candidates)
    assert all(set(row["proposed_finite_reason_set"]) <= RETIRED_UMBRELLA_REASON_IDS for row in candidates)
    assert not any("/tests/" in row["path"] for row in candidates)
    assert not any(
        row["path"].endswith("control_recovery_1.py") and row["line"] == 1598
        for row in candidates
    )
    stored = json.loads((
        REPO_ROOT / "artifacts/unknown_taxonomy_v2/phase7/retired-reference-review-template.json"
    ).read_text(encoding="utf-8"))
    assert stored == template
    assert not any(
        row["ast_node_kind"] == "ShellToken" and "unknown_counts" in row["context_source"]
        for row in candidates
    )


def test_phase7_stored_review_closes_both_production_relations():
    manifest = json.loads((
        REPO_ROOT / "artifacts/unknown_taxonomy_v2/phase7/retired-reference-inventory.json"
    ).read_text(encoding="utf-8"))
    assert manifest["production_umbrella_generation"] == 0
    assert manifest["production_umbrella_routing"] == 0
    assert manifest["relation_counts"]["P_emit"] == 0
    assert manifest["relation_counts"]["P_route"] == 0


def test_phase7_representative_ambiguous_sites_have_explicit_expected_classification(template):
    rows = template["entries"]
    assert not any(
        row["reference_kind"] != "indirect_dynamic_site"
        and row["suggested_relation"] in {"P_emit", "P_route"}
        for row in rows
    )
    normalize = next(row for row in rows if (
        row["path"].endswith("equivalence/unknown_reason.py")
        and "normalize_unknown_reason_id" in row["symbol"]
    ))
    assert normalize["suggested_relation"] == "L_decode"
    constructor = next(row for row in rows if (
        row["path"].endswith("equivalence/unknown_reason.py")
        and "make_unknown_reason" in row["symbol"]
    ))
    assert constructor["suggested_relation"] == "D_legacy"
    registry_declaration = next(row for row in rows if (
        row["path"].endswith("equivalence/unknown_reason.py")
        and row["symbol"] == "_register_defaults"
    ))
    assert registry_declaration["suggested_relation"] == "L_decode"
    diagnostic_coercion = next(row for row in rows if (
        row["path"].endswith("equivalence/unknown_reason.py")
        and row["symbol"] == "coerce_unknown_recovery_action"
    ))
    assert diagnostic_coercion["suggested_relation"] == "D_legacy"
    dynamic = next(row for row in rows if (
        row["path"].endswith("equivalence/v2/loop_recurrence.py")
        and row["reference_kind"] == "indirect_dynamic_site"
        and row["line"] == 328
    ))
    assert dynamic["proposed_finite_reason_set"] == ["unknown"]
    assert dynamic["suggested_relation"] == "P_emit"


def test_phase7_inventory_requires_external_complete_review(template):
    with pytest.raises(ValueError, match="not independently reviewed"):
        _build(template, template)

    missing = _review_suggestions(template)
    missing["entries"].pop()
    with pytest.raises(ValueError, match="candidate and reviewed sets differ"):
        _build(template, missing)

    drifted = _review_suggestions(template)
    drifted["entries"][0]["source_fingerprint"] = "0" * 64
    with pytest.raises(ValueError, match="source field drifted"):
        _build(template, drifted)

    invalid_finite = _review_suggestions(template)
    dynamic = next(
        row for row in invalid_finite["entries"]
        if row["reference_kind"] == "indirect_dynamic_site"
    )
    dynamic["reviewed_finite_reason_set"] = []
    with pytest.raises(ValueError, match="reviewed finite set"):
        _build(template, invalid_finite)


def test_phase7_reviewed_partition_is_exact_disjoint_and_metric_owned(template):
    manifest = _build(template, _review_suggestions(template))
    relations = manifest["relations"]
    assert set(relations) == {item.value for item in RetiredReferenceRelation}
    rows = [row for relation_rows in relations.values() for row in relation_rows]
    assert manifest["candidate_count"] == manifest["classified_count"] == len(rows)
    assert manifest["discovered_probe_count"] == len(rows)
    assert sum(manifest["relation_counts"].values()) == len(rows)
    assert len({row["candidate_id"] for row in rows}) == len(rows)
    assert manifest["production_umbrella_generation"] == len(relations["P_emit"])
    assert manifest["production_umbrella_routing"] == len(relations["P_route"])
    assert manifest["production_umbrella_generation"] > 0
    assert manifest["production_umbrella_routing"] == 0
    assert all("/validation/" not in row["path"] for row in relations["P_emit"])
    assert all("/validation/" not in row["path"] for row in relations["P_route"])


def test_phase7_independent_review_can_narrow_function_wide_flow_proposal(template):
    reviewed = _review_suggestions(template)
    row = next(item for item in reviewed["entries"] if (
        item["path"].endswith("phase2_return_coverage_risk_preflight.py")
        and item["line"] == 736
        and item["reference_kind"] == "indirect_dynamic_site"
    ))
    assert len(row["proposed_finite_reason_set"]) > 1
    row["reviewed_finite_reason_set"] = ["sat_unsafety"]
    manifest = _build(template, reviewed)
    materialized = next(item for item in manifest["relations"]["D_legacy"] if (
        item["candidate_id"] == row["candidate_id"]
    ))
    assert materialized["finite_reason_set"] == ["sat_unsafety"]


def test_phase7_independent_review_can_exclude_false_dynamic_probe(template):
    reviewed = _review_suggestions(template)
    row = next(item for item in reviewed["entries"] if (
        item["path"].endswith("equivalence/v2/loop_recurrence.py")
        and item["line"] == 328
        and item["reference_kind"] == "indirect_dynamic_site"
    ))
    row["reviewed_in_scope"] = False
    row["reviewed_relation"] = None
    row["reviewed_finite_reason_set"] = []
    row["reviewer_disposition"] = (
        "sealed slice-4 mapping returns only non-retired typed reason IDs"
    )
    manifest = _build(template, reviewed)
    assert manifest["discovered_probe_count"] == manifest["candidate_count"] + 1
    assert manifest["excluded_flow_probe_count"] == 1
    assert manifest["excluded_flow_probes"][0]["candidate_id"] == row["candidate_id"]


def test_phase7_partition_rejects_unknown_or_duplicate_relation(template):
    unknown = _review_suggestions(template)
    unknown["entries"][0]["reviewed_relation"] = "OTHER"
    with pytest.raises(ValueError):
        _build(template, unknown)

    duplicate = _review_suggestions(template)
    duplicate["entries"].append(copy.deepcopy(duplicate["entries"][0]))
    with pytest.raises(ValueError, match="candidate and reviewed sets differ"):
        _build(template, duplicate)
