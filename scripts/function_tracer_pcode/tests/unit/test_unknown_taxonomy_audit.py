# -*- coding: utf-8 -*-

import copy
import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.equivalence.unknown_reason import UnknownReasonId
from scripts.function_tracer_pcode.validation.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
)
from scripts.function_tracer_pcode.validation.unknown_taxonomy_audit import (
    ARTIFACT_NAMES,
    PHASE0_MANIFEST_KIND,
    _build_census,
    _apply_inventory_review,
    _json_digest,
    _validate_run_artifact_accounting,
    _reason_site_posture,
    build_unknown_taxonomy_audit,
    discover_inventory_candidate_digest,
    validate_unknown_taxonomy_audit,
)


REPO_ROOT = Path(__file__).resolve().parents[4]
HEAD = "29376ea952073e52185cb1821eebb6d04a383ef3"
FROZEN_HEAD_TREE = "f17420710598e894eef246a8e34cfc3b525ab4be"
FROZEN_TRACKED_WORKTREE = "0258631b12ead771100bc747524c68caac17f5f319e11c7ab2aa5a8f40f81262"
FROZEN_VALIDATION = {
    "frozen_head_tree_digest": FROZEN_HEAD_TREE,
    "frozen_tracked_worktree_digest": FROZEN_TRACKED_WORKTREE,
}
SELECTION_INPUT_PATH = REPO_ROOT / "artifacts/unknown_reason_audit/current-head/selection-input.json"


@pytest.fixture(scope="module")
def built_audit(tmp_path_factory):
    tmp = tmp_path_factory.mktemp("unknown-taxonomy-audit")
    selection_input = json.loads(
        (
            SELECTION_INPUT_PATH
        ).read_text()
    )
    selections = copy.deepcopy(selection_input["selections"])
    inventory_review = json.loads(
        (
            REPO_ROOT
            / "artifacts/unknown_reason_audit/current-head/inventory-review.json"
        ).read_text()
    )
    frozen_dir = REPO_ROOT / "artifacts/unknown_reason_audit/current-head"
    payloads = {
        name: json.loads((frozen_dir / name).read_text())
        for name in ARTIFACT_NAMES
    }
    return tmp, payloads, selections, inventory_review, selection_input


def test_phase0_inventory_is_complete_reviewed_and_non_authoritative(built_audit):
    _, payloads, _, inventory_review, _ = built_audit

    validate_unknown_taxonomy_audit(payloads, repo_root=REPO_ROOT, **FROZEN_VALIDATION)
    registry = payloads["registry.json"]
    assert registry["reason_count"] == 37
    assert {row["reason_id"] for row in registry["reasons"]} == {
        item.value for item in UnknownReasonId
    }
    producers = payloads["producers.json"]
    assert set(producers["candidate_site_ids"]) == set(producers["classified_site_ids"])
    assert producers["inventory_candidate_set_digest"] == inventory_review["candidate_set_digest"]
    assert producers["unresolved_dynamic_site_count"] == 0
    initializer = next(
        row for row in producers["sites"]
        if row["path"].endswith("pairwise_models.py") and row["line"] == 192
    )
    assert initializer["authority_role"] == "derived_projection"
    assert initializer["reason_resolution"] == "not_applicable"
    assert initializer["resolved_reason_ids"] == []
    manifest = payloads["census_manifest.json"]
    assert manifest["manifest_kind"] == PHASE0_MANIFEST_KIND
    assert manifest["non_authoritative"] is True
    assert payloads["census.json"]["census_mode"] == "LEGACY_DIAGNOSTIC"
    allowed_postures = {
        "production",
        "derived_projection_only",
        "test_only",
        "legacy_only",
        "dead",
    }
    assert {row["lifecycle_posture"] for row in registry["reasons"]} <= allowed_postures
    assert all(
        {
            "production_site_count",
            "derived_projection_site_count",
            "legacy_reader_site_count",
            "legacy_readable",
        } <= set(row)
        for row in registry["reasons"]
    )
    migration_rows = payloads["migration_manifest.json"]["reason_status"]
    assert len({row["recommended_action"] for row in migration_rows}) == 37
    assert len({row["known_issue"] for row in migration_rows}) == 37


def test_phase0_validation_rejects_inventory_fingerprint_drift(built_audit):
    _, payloads, _, _, _ = built_audit
    tampered = copy.deepcopy(payloads)
    tampered["producers.json"]["inventory_candidates"][0][
        "inventory_source_fingerprint"
    ] = "0" * 64

    with pytest.raises(ValueError, match="source fingerprints"):
        validate_unknown_taxonomy_audit(tampered)


def test_phase0_validation_rejects_unclassified_or_dynamic_site(built_audit):
    _, payloads, _, _, _ = built_audit
    unclassified = copy.deepcopy(payloads)
    unclassified["producers.json"]["classified_site_ids"].pop()
    with pytest.raises(ValueError, match="site sets differ"):
        validate_unknown_taxonomy_audit(unclassified)

    dynamic = copy.deepcopy(payloads)
    site = next(
        row for row in dynamic["producers.json"]["sites"]
        if row["construct_kind"] == "reason_constructor"
    )
    site["reason_resolution"] = "dynamic"
    with pytest.raises(ValueError, match="unresolved dynamic"):
        validate_unknown_taxonomy_audit(dynamic)


def test_phase0_validation_rejects_manifest_escape_and_v2_digest(built_audit):
    _, payloads, _, _, _ = built_audit
    escaped = copy.deepcopy(payloads)
    escaped["census.json"]["results"][0]["result_entry_id"] = "outside"
    with pytest.raises(ValueError, match="outside its manifest"):
        validate_unknown_taxonomy_audit(escaped)

    fabricated = copy.deepcopy(payloads)
    fabricated["census_manifest.json"]["entries"][0][
        "decision_receipt_digest"
    ] = "f" * 64
    with pytest.raises(ValueError, match="fabricates v2 authority"):
        validate_unknown_taxonomy_audit(fabricated)


def test_phase0_validation_rematerializes_decision_branch_config_and_command(built_audit):
    _, payloads, _, _, _ = built_audit
    decision = copy.deepcopy(payloads)
    decision["census_manifest.json"]["entries"][0]["decision"] = "ERROR"
    decision["census.json"]["manifest_digest"] = _json_digest(decision["census_manifest.json"])
    with pytest.raises(ValueError, match="decision mismatch|selection branch"):
        validate_unknown_taxonomy_audit(decision, repo_root=REPO_ROOT, **FROZEN_VALIDATION)

    branch = copy.deepcopy(payloads)
    branch["census_manifest.json"]["entries"][0]["covered_consumer_branches"] = [
        "decision:ERROR"
    ]
    branch["census.json"]["manifest_digest"] = _json_digest(branch["census_manifest.json"])
    with pytest.raises(ValueError, match="selection branch"):
        validate_unknown_taxonomy_audit(branch)

    for field, expected in (
        ("analysis_config", "analysis config digest"),
        ("analysis_command", "analysis command digest"),
    ):
        tampered = copy.deepcopy(payloads)
        entry = next(
            row for row in tampered["census_manifest.json"]["entries"]
            if row["evidence_mode"] == "CURRENT_HEAD_REAL_RERUN"
        )
        entry[field] = {"tampered": True} if field == "analysis_config" else ["tampered"]
        tampered["census.json"]["manifest_digest"] = _json_digest(
            tampered["census_manifest.json"]
        )
        with pytest.raises(ValueError, match=expected):
            validate_unknown_taxonomy_audit(tampered)


def test_phase0_validation_joins_every_manifest_entry_to_selection_row(built_audit):
    _, payloads, _, _, _ = built_audit
    for field in ("selection_reason", "covered_consumer_branches"):
        tampered = copy.deepcopy(payloads)
        entry = tampered["census_manifest.json"]["entries"][0]
        if field == "selection_reason":
            entry[field] = "self-consistent manifest text not present in selection input"
        else:
            decision_branch = next(
                branch for branch in entry[field] if branch.startswith("decision:")
            )
            entry[field] = [decision_branch, "fabricated_nondecision_branch"]
        tampered["census.json"]["manifest_digest"] = _json_digest(
            tampered["census_manifest.json"]
        )
        with pytest.raises(ValueError, match=f"selection row field mismatch: {field}"):
            validate_unknown_taxonomy_audit(tampered, repo_root=REPO_ROOT, **FROZEN_VALIDATION)

    synthetic = copy.deepcopy(payloads)
    entry = next(
        row for row in synthetic["census_manifest.json"]["entries"]
        if row["evidence_mode"] == "SYNTHETIC_CONTRACT_FIXTURE"
    )
    entry["analysis_config"] = {"fixture_kind": "fabricated_but_self_consistent"}
    entry["analysis_config_digest"] = _json_digest(entry["analysis_config"])
    synthetic["census.json"]["manifest_digest"] = _json_digest(
        synthetic["census_manifest.json"]
    )
    with pytest.raises(ValueError, match="selection row field mismatch: analysis_config"):
        validate_unknown_taxonomy_audit(synthetic, repo_root=REPO_ROOT, **FROZEN_VALIDATION)


def test_phase0_validation_rejects_timeout_and_legacy_binding_tamper(built_audit):
    _, payloads, _, _, _ = built_audit
    timeout = copy.deepcopy(payloads)
    row = next(
        item for item in timeout["census.json"]["runtime_timeout_correspondence"]
        if item["final_outcome"] == "TIMEOUT"
    )
    assert row["correspondence"] == "reason_budget_mismatch"
    row["terminal_timeout_event_count"] = 0
    with pytest.raises(ValueError, match="exactly one terminal timeout"):
        validate_unknown_taxonomy_audit(timeout)

    legacy = copy.deepcopy(payloads)
    legacy["census.json"]["legacy_baseline_diagnostic"]["non_current_diagnostic"] = False
    with pytest.raises(ValueError, match="isolated from current canonical truth"):
        validate_unknown_taxonomy_audit(legacy)


def test_phase0_validation_rejects_selection_exclusion_and_allowlist_tamper(built_audit):
    _, payloads, _, _, _ = built_audit
    selected = copy.deepcopy(payloads)
    selected["census_manifest.json"]["entries"][0]["selection_input_digest"] = "0" * 64
    selected["census.json"]["manifest_digest"] = _json_digest(selected["census_manifest.json"])
    with pytest.raises(ValueError, match="selection input"):
        validate_unknown_taxonomy_audit(selected)

    excluded = copy.deepcopy(payloads)
    excluded["census_manifest.json"]["excluded_result_observations"][0][
        "source_artifact_digest"
    ] = "0" * 64
    excluded["census.json"]["manifest_digest"] = _json_digest(excluded["census_manifest.json"])
    with pytest.raises(ValueError, match="excluded result artifact digest"):
        validate_unknown_taxonomy_audit(excluded, repo_root=REPO_ROOT, **FROZEN_VALIDATION)

    allowlist = copy.deepcopy(payloads)
    allowlist["migration_manifest.json"]["phase0_gate"]["production_change_allowlist"] = [
        "scripts/function_tracer_pcode/equivalence/checker.py"
    ]
    with pytest.raises(ValueError, match="allowlist must be empty"):
        validate_unknown_taxonomy_audit(allowlist)


def test_inventory_review_must_be_separate_complete_and_reviewed():
    candidate = {
        "site_id": "site-1",
        "path": "producer.py",
        "line": 1,
        "symbol": "f",
        "construct_kind": "reason_constructor",
        "source": "make_unknown_reason('unknown')",
        "inventory_source_fingerprint": "fingerprint",
    }
    digest = _json_digest({
        "sites": [{
            key: candidate[key]
            for key in (
                "site_id", "path", "symbol", "construct_kind", "inventory_source_fingerprint"
            )
        }]
    })
    review = {
        "review_kind": "unknown_taxonomy_phase0_inventory_classification",
        "candidate_set_digest": digest,
        "reviewed_by": None,
        "review_status": "unreviewed_template",
        "entries": [],
    }
    with pytest.raises(ValueError, match="independently approved"):
        _apply_inventory_review((candidate,), review, ("unknown",), digest)


def test_run_artifact_accounting_rejects_unselected_log(tmp_path):
    output = tmp_path / "audit"
    runs = output / "runs"
    runs.mkdir(parents=True)
    (runs / "unselected.log").write_text("Result: UNKNOWN\n", encoding="utf-8")
    with pytest.raises(ValueError, match="run artifact accounting mismatch"):
        _validate_run_artifact_accounting(
            output=output,
            root=tmp_path,
            selected_entries=(),
            excluded_entries=(),
        )


def test_census_rejects_unknown_evidence_mode(tmp_path):
    result = tmp_path / "result.log"
    _write_result(result, {"is_equivalent": None, "unknown_reasons": []})
    with pytest.raises(ValueError, match="invalid Phase 0 evidence_mode"):
        _build_census(
            root=REPO_ROOT,
            head=HEAD,
            selections=({
                "evidence_mode": "UNLABELED_MIXED_MODE",
                "source_artifact_path": str(result),
            },),
            common={"schema_version": 1, "git_head": HEAD},
            selection_input_digest="fixture",
        )


def test_phase0_validation_rejects_selected_artifact_tamper(built_audit):
    tmp, payloads, _, _, _ = built_audit
    tampered = copy.deepcopy(payloads)
    entry = next(
        row for row in tampered["census_manifest.json"]["entries"]
        if row["evidence_mode"] == "SYNTHETIC_CONTRACT_FIXTURE"
    )
    source = REPO_ROOT / entry["source_artifact_path"]
    copied = tmp / "selected-tamper.log"
    copied.write_bytes(source.read_bytes())
    entry["source_artifact_path"] = str(copied)
    selection_document = json.loads(SELECTION_INPUT_PATH.read_text())
    selection_row = selection_document["selections"][entry["selection_row_index"]]
    selection_row["source_artifact_path"] = str(copied)
    entry["selection_row_digest"] = _json_digest(selection_row)
    copied_selection = tmp / "selection-tamper.json"
    copied_selection.write_text(json.dumps(selection_document), encoding="utf-8")
    selection_digest = _json_digest(selection_document)
    tampered["census_manifest.json"]["selection_input_path"] = str(copied_selection)
    tampered["census_manifest.json"]["selection_input_digest"] = selection_digest
    for manifest_entry in tampered["census_manifest.json"]["entries"]:
        manifest_entry["selection_input_digest"] = selection_digest
    copied.write_text(copied.read_text() + "\n# tampered\n", encoding="utf-8")
    tampered["census.json"]["manifest_digest"] = _json_digest(
        tampered["census_manifest.json"]
    )
    with pytest.raises(ValueError, match="artifact digest mismatch"):
        validate_unknown_taxonomy_audit(tampered, repo_root=REPO_ROOT, **FROZEN_VALIDATION)


def test_duplicate_stable_result_requires_explicit_policy(tmp_path):
    left = tmp_path / "a.log"
    right = tmp_path / "b.log"
    payload = {
        "is_equivalent": None,
        "function1_name": "f",
        "function2_name": "f",
        "binary1_name": "B1",
        "binary2_name": "B2",
        "unknown_reasons": [],
    }
    _write_result(left, payload)
    _write_result(right, payload)
    base = {
        "evidence_mode": "SYNTHETIC_CONTRACT_FIXTURE",
        "repository_commit": HEAD,
        "analysis_config": {},
        "selection_reason": "duplicate fixture",
        "covered_branches": ["duplicate_stable_result"],
    }

    with pytest.raises(ValueError, match="duplicate_policy"):
        _build_census(
            root=REPO_ROOT,
            head=HEAD,
            selections=(
                {**base, "source_artifact_path": str(left)},
                {**base, "source_artifact_path": str(right)},
            ),
            common={"schema_version": 1, "git_head": HEAD},
            selection_input_digest="fixture-selection-input",
        )


def test_current_real_not_eq_and_timeout_require_domain_model_and_timeout_event(tmp_path):
    not_eq = tmp_path / "not-eq.log"
    _write_result(not_eq, {
        "is_equivalent": False,
        "function1_name": "left",
        "function2_name": "right",
        "binary1_content_identity": ["sha256", "a"],
        "binary2_content_identity": ["sha256", "b"],
        "solver_results": {"all_results": []},
    })
    base = {
        "evidence_mode": "CURRENT_HEAD_REAL_RERUN",
        "repository_commit": HEAD,
        "analysis_command": ["fixture"],
        "analysis_config": {"domain_rationale": "manual witness"},
        "binary_content_identities": {
            "left": ["sha256", "a"], "right": ["sha256", "b"]
        },
        "source_artifact_path": str(not_eq),
        "selection_reason": "negative contract fixture",
        "covered_branches": ["decision:NOT_EQ"],
    }
    with pytest.raises(ValueError, match="solver model"):
        _build_census(
            root=REPO_ROOT, head=HEAD, selections=(base,),
            common={"schema_version": 1, "git_head": HEAD},
            selection_input_digest="fixture",
        )

    timeout = tmp_path / "timeout.log"
    _write_result(timeout, {
        "is_equivalent": None,
        "is_timeout": True,
        "function1_name": "left",
        "function2_name": "right",
        "binary1_content_identity": ["sha256", "a"],
        "binary2_content_identity": ["sha256", "b"],
        "solver_results": {"all_results": []},
    })
    timeout_selection = {
        **base,
        "source_artifact_path": str(timeout),
        "analysis_config": {},
        "covered_branches": ["decision:TIMEOUT"],
    }
    with pytest.raises(ValueError, match="terminal solver timeout evidence"):
        _build_census(
            root=REPO_ROOT, head=HEAD, selections=(timeout_selection,),
            common={"schema_version": 1, "git_head": HEAD},
            selection_input_digest="fixture",
        )


def test_new_candidate_changes_reviewed_inventory_digest(tmp_path):
    source = tmp_path / "scripts" / "function_tracer_pcode" / "equivalence"
    source.mkdir(parents=True)
    (source / "producer.py").write_text(
        "def f():\n    return make_unknown_reason('unknown')\n",
        encoding="utf-8",
    )
    first, first_count = discover_inventory_candidate_digest(tmp_path)
    (source / "producer.py").write_text(
        "def f():\n    return make_unknown_reason('unknown')\n"
        "def g():\n    return make_unknown_reason('strategy_exception')\n",
        encoding="utf-8",
    )
    second, second_count = discover_inventory_candidate_digest(tmp_path)

    assert second_count == first_count + 1
    assert second != first


def test_regeneration_is_deterministic(built_audit):
    _, payloads, _, _, _ = built_audit
    before = {
        name: json.dumps(payloads[name], sort_keys=True, separators=(",", ":"))
        for name in ARTIFACT_NAMES
    }
    frozen_dir = REPO_ROOT / "artifacts/unknown_reason_audit/current-head"
    after = {
        name: json.dumps(
            json.loads((frozen_dir / name).read_text()),
            sort_keys=True,
            separators=(",", ":"),
        )
        for name in ARTIFACT_NAMES
    }

    assert after == before


def test_phase0_snapshot_stays_frozen_after_phase6_migration_begins():
    review = json.loads(
        (REPO_ROOT / "artifacts/unknown_reason_audit/current-head/inventory-review.json").read_text()
    )
    current_digest, current_count = discover_inventory_candidate_digest(REPO_ROOT)
    assert current_digest != review["candidate_set_digest"]
    assert current_count > len(review["entries"])
    assert (
        REPO_ROOT
        / "artifacts/unknown_taxonomy_v2/phase6/slice1_sat_safety.json"
    ).is_file()


def test_reason_posture_distinguishes_production_projection_test_legacy_and_dead():
    production = _reason_site_posture(
        "r",
        ({"resolved_reason_ids": ["r"], "authority_role": "production"},),
        {},
    )
    projection = _reason_site_posture(
        "r",
        ({"resolved_reason_ids": ["r"], "authority_role": "derived_projection"},),
        {},
    )
    test_only = _reason_site_posture("r", (), {"r": ({"path": "test.py"},)})
    legacy_only = _reason_site_posture("r", (), {})
    dead = _reason_site_posture("r", (), {}, legacy_readable=False)

    assert production["lifecycle_posture"] == "production"
    assert projection["lifecycle_posture"] == "derived_projection_only"
    assert test_only["lifecycle_posture"] == "test_only"
    assert legacy_only["lifecycle_posture"] == "legacy_only"
    assert legacy_only["legacy_readable"] is True
    assert dead["lifecycle_posture"] == "dead"


def _write_result(path: Path, payload):
    path.write_text(
        "\n".join(
            (
                "Result: UNKNOWN",
                RESULT_JSON_BEGIN,
                json.dumps(payload, sort_keys=True),
                RESULT_JSON_END,
                "",
            )
        ),
        encoding="utf-8",
    )
