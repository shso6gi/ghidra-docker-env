# -*- coding: utf-8 -*-
"""Generate the read-only Phase 0 UNKNOWN taxonomy audit.

This module inventories the existing v1 implementation.  It deliberately does
not change normalization, reason production, lifecycle, or final decisions.
The generated files are evidence for the v2 migration, not v2 authority.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
import subprocess
from collections import Counter, defaultdict
from dataclasses import asdict
from pathlib import Path
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence, Tuple

from ..equivalence.unknown_reason import (
    UnknownReasonId,
    coerce_unknown_reason_records,
    unknown_reason_registry_snapshot,
    unknown_recovery_plan_registry_snapshot,
)
from .result_summary import classify_result_payload
from .unknown_reason_summary import extract_result_payloads_from_text


AUDIT_SCHEMA_VERSION = 1
EXPECTED_REASON_COUNT = 37
ARTIFACT_NAMES = (
    "registry.json",
    "producers.json",
    "consumers.json",
    "decision_projection.json",
    "legacy_aliases.json",
    "census_manifest.json",
    "census.json",
    "overlap_candidates.json",
    "migration_manifest.json",
)
PHASE0_MANIFEST_KIND = "phase0_legacy_diagnostic_selection"
PHASE0_EVIDENCE_MODES = frozenset(
    {
        "CURRENT_HEAD_REAL_RERUN",
        "SYNTHETIC_CONTRACT_FIXTURE",
        "LEGACY_BASELINE_DIAGNOSTIC",
    }
)
REQUIRED_SELECTION_BRANCHES = frozenset(
    {
        "decision:EQUIVALENT",
        "decision:NOT_EQ",
        "decision:UNKNOWN",
        "decision:TIMEOUT",
        "decision:ERROR",
        "fallback_retry",
        "multiple_reason",
        "root_blocker_candidates",
        "operational_unknown",
        "duplicate_stable_result",
    }
)
_TRACKED_WORKTREE_DIGEST_CACHE: Dict[Tuple[str, str], str] = {}


def build_unknown_taxonomy_audit(
    *,
    repo_root: Path,
    output_dir: Path,
    selections: Sequence[Mapping[str, Any]] = (),
    exclusions: Sequence[Mapping[str, Any]] = (),
    inventory_review: Optional[Mapping[str, Any]] = None,
    selection_input_digest: Optional[str] = None,
    selection_input_path: Optional[str] = None,
    git_head: Optional[str] = None,
    frozen_head_tree_digest: Optional[str] = None,
    frozen_tracked_worktree_digest: Optional[str] = None,
) -> Dict[str, Path]:
    """Build all Phase 0 artifacts and return their paths."""

    root = Path(repo_root).resolve()
    output = Path(output_dir).resolve()
    source_root = root / "scripts" / "function_tracer_pcode"
    if not source_root.is_dir():
        raise FileNotFoundError(f"function_tracer_pcode source root is missing: {source_root}")

    head = git_head or _git_head(root)
    source_files = tuple(sorted(source_root.rglob("*.py"), key=lambda path: path.as_posix()))
    scans = tuple(_scan_python_file(path, root) for path in source_files)
    shell_paths = tuple(root.glob("*.sh")) + tuple((root / "scripts").rglob("*.sh"))
    shell_scans = tuple(
        _scan_text_file(path, root)
        for path in sorted(set(shell_paths), key=lambda path: path.as_posix())
        if ".git" not in path.parts
    )
    definitions = unknown_reason_registry_snapshot()
    recovery_plans = unknown_recovery_plan_registry_snapshot()
    reason_ids = tuple(sorted(definitions))
    if len(reason_ids) != EXPECTED_REASON_COUNT:
        raise ValueError(
            f"expected {EXPECTED_REASON_COUNT} registered reasons, found {len(reason_ids)}"
        )
    if set(reason_ids) != {item.value for item in UnknownReasonId}:
        raise ValueError("UnknownReasonId and registry membership differ")

    common = {
        "schema_version": AUDIT_SCHEMA_VERSION,
        "audit_kind": "unknown_taxonomy_v1_current_head_inventory",
        "git_head": head,
    }
    inventory_candidates = _discover_inventory_candidates(scans, shell_scans)
    reason_resolution_index = _build_reason_resolution_index(scans, reason_ids)
    candidate_set_digest = _inventory_candidate_set_digest(inventory_candidates)
    if inventory_review is None:
        raise ValueError("Phase 0 inventory requires a separate reviewed classification input")
    classified_sites = _apply_inventory_review(
        inventory_candidates,
        inventory_review,
        reason_ids,
        candidate_set_digest,
    )
    producer_rows, _dynamic_constructor_rows = _producer_inventory(scans, reason_ids)
    indirect_constructor_rows = [
        row for row in classified_sites
        if row["construct_kind"] == "reason_constructor"
        and row["reason_resolution"] == "static_set"
    ]
    consumer_rows = [
        row for row in classified_sites
        if row["authority_role"] in {"derived_projection", "legacy_reader"}
        or row["construct_kind"] in {
            "reason_collection_read",
            "reason_collection_mutation",
            "shell_status_or_reason",
        }
    ]
    test_refs = _test_reference_inventory(scans, reason_ids)
    registry = {
        **common,
        "expected_reason_count": EXPECTED_REASON_COUNT,
        "reason_count": len(reason_ids),
        "recovery_plan_count": len(recovery_plans),
        "reasons": [
            {
                **asdict(definitions[reason_id]),
                "recovery_plan": (
                    recovery_plans[reason_id].to_dict()
                    if reason_id in recovery_plans
                    else None
                ),
                **_reason_site_posture(reason_id, classified_sites, test_refs),
                "consumer_status": _reason_consumer_status(reason_id, consumer_rows),
                "test_status": "referenced" if test_refs.get(reason_id) else "not_referenced",
                "legacy_status": _legacy_status(reason_id),
                "direct_static_producer_count": len(producer_rows.get(reason_id, ())),
                "test_reference_count": len(test_refs.get(reason_id, ())),
            }
            for reason_id in reason_ids
        ],
    }
    producers = {
        **common,
        "classification_contract": {
            "typed": "make_unknown_reason call with a statically resolvable registered ID",
            "dynamic": "make_unknown_reason call whose ID cannot be resolved statically",
            "test": "reference below the tests subtree; excluded from production producer counts",
        },
        "reason_producers": [
            {"reason_id": reason_id, "sites": list(producer_rows.get(reason_id, ())) }
            for reason_id in reason_ids
        ],
        "indirect_constructor_sites": indirect_constructor_rows,
        "indirect_constructor_site_count": len(indirect_constructor_rows),
        "unresolved_dynamic_sites": [],
        "unresolved_dynamic_site_count": 0,
        "inventory_candidate_set_digest": candidate_set_digest,
        "inventory_review_digest": _json_digest(inventory_review),
        "inventory_candidates": inventory_candidates,
        "candidate_site_ids": [row["site_id"] for row in inventory_candidates],
        "classified_site_ids": [row["site_id"] for row in classified_sites],
        "sites": [
            row for row in classified_sites
            if row["construct_kind"] in {
                "reason_constructor",
                "reason_selection_assignment",
                "reason_collection_mutation",
                "shell_status_or_reason",
            }
        ],
    }
    consumers = {
        **common,
        "consumer_classes": {
            "final_primary": "selects or summarizes final/primary UNKNOWN reasons",
            "fallback_retry": "uses reasons across fallback, retry, strategy, or attempt flow",
            "cli_batch_resume": "parses or reports reasons in CLI, batch, or resume flow",
            "proof_backlog": "turns reasons into recovery actions, blockers, or proof backlog",
            "general": "other production reads or coercions of unknown_reasons",
        },
        "sites": consumer_rows,
        "inventory_sites": [
            row for row in classified_sites
            if row["construct_kind"] in {
                "reason_collection_read",
                "legacy_deserialization",
                "reason_collection_mutation",
                "shell_status_or_reason",
            }
        ],
        "class_counts": dict(sorted(Counter(row["consumer_class"] for row in consumer_rows).items())),
        "test_references_by_reason": [
            {"reason_id": reason_id, "sites": list(test_refs.get(reason_id, ())) }
            for reason_id in reason_ids
        ],
    }
    decision_projection = {
        **common,
        "authority_note": (
            "This is a v1 location inventory only. Diagnostic reasons are not final outcome "
            "authority and solver_unknown_timeout does not imply a TIMEOUT decision."
        ),
        "sites": _decision_projection_inventory(scans),
    }
    legacy_aliases = {
        **common,
        "authoritative_for_v2": False,
        "normalization_definition": _source_reference(
            root / "scripts/function_tracer_pcode/equivalence/unknown_reason.py",
            root,
            "def normalize_unknown_reason_id",
        ),
        "suffix_normalization_enabled_in_v1": True,
        "unknown_fallback_enabled_in_v1": True,
        "exact_registered_ids": list(reason_ids),
        "legacy_status_by_reason": [
            {"reason_id": reason_id, "status": _legacy_status(reason_id)}
            for reason_id in reason_ids
        ],
        "string_literal_and_dynamic_sites": _legacy_site_inventory(scans, reason_ids),
    }

    manifest, census = _build_census(
        root=root,
        head=head,
        selections=selections,
        common=common,
        selection_input_digest=(
            selection_input_digest
            or _json_digest({"selections": list(selections), "excluded_observations": list(exclusions)})
        ),
        selection_input_path=selection_input_path,
        head_tree_digest_override=frozen_head_tree_digest,
        tracked_worktree_digest_override=frozen_tracked_worktree_digest,
    )
    decision_projection["runtime_timeout_correspondence"] = census[
        "runtime_timeout_correspondence"
    ]
    excluded_rows = _build_excluded_observations(root, exclusions)
    manifest["excluded_result_observations"] = excluded_rows
    manifest["excluded_result_observation_count"] = len(excluded_rows)
    legacy_baseline = _build_legacy_baseline(root)
    manifest["legacy_baseline_binding"] = {
        "baseline_kind": legacy_baseline["baseline_kind"],
        "non_current_diagnostic": True,
        "summary_file_count": legacy_baseline["summary_file_count"],
        "baseline_digest": legacy_baseline["baseline_digest"],
    }
    census["legacy_baseline_diagnostic"] = legacy_baseline
    _validate_run_artifact_accounting(
        output=output,
        root=root,
        selected_entries=manifest["entries"],
        excluded_entries=excluded_rows,
    )
    census["manifest_digest"] = _json_digest(manifest)
    overlap_candidates = {
        **common,
        "authority": "review_candidates_only",
        "candidates": _overlap_candidates(definitions),
    }
    migration_manifest = {
        **common,
        "source_artifacts": list(ARTIFACT_NAMES[:-1]),
        "reason_status": [
            {
                "reason_id": reason_id,
                "producer_status": next(
                    row["producer_status"] for row in registry["reasons"]
                    if row["reason_id"] == reason_id
                ),
                "consumer_status": _reason_consumer_status(reason_id, consumer_rows),
                "legacy_status": _legacy_status(reason_id),
                "test_status": "referenced" if test_refs.get(reason_id) else "not_referenced",
                **_migration_posture(reason_id, definitions[reason_id]),
            }
            for reason_id in reason_ids
        ],
        "phase0_gate": {
            "all_reasons_enumerated": len(reason_ids) == EXPECTED_REASON_COUNT,
            "all_reasons_have_status": True,
            "dynamic_producers_enumerated": True,
            "result_selection_manifest_bound": True,
            "current_head_representative_result_count": manifest["mode_counts"].get(
                "CURRENT_HEAD_REAL_RERUN", 0
            ),
            "production_behavior_changed": False,
            "production_change_allowlist": [],
        },
    }

    payloads = {
        "registry.json": registry,
        "producers.json": producers,
        "consumers.json": consumers,
        "decision_projection.json": decision_projection,
        "legacy_aliases.json": legacy_aliases,
        "census_manifest.json": manifest,
        "census.json": census,
        "overlap_candidates.json": overlap_candidates,
        "migration_manifest.json": migration_manifest,
    }
    validate_unknown_taxonomy_audit(
        payloads,
        repo_root=root,
        frozen_head_tree_digest=frozen_head_tree_digest,
        frozen_tracked_worktree_digest=frozen_tracked_worktree_digest,
    )
    output.mkdir(parents=True, exist_ok=True)
    paths: Dict[str, Path] = {}
    for name in ARTIFACT_NAMES:
        path = output / name
        _write_json(path, payloads[name])
        paths[name] = path
    return paths


def validate_unknown_taxonomy_audit(
    payloads: Mapping[str, Mapping[str, Any]], *, repo_root: Optional[Path] = None,
    frozen_head_tree_digest: Optional[str] = None,
    frozen_tracked_worktree_digest: Optional[str] = None,
) -> None:
    missing = sorted(set(ARTIFACT_NAMES) - set(payloads))
    if missing:
        raise ValueError(f"missing Phase 0 artifacts: {', '.join(missing)}")
    heads = {str(payloads[name].get("git_head") or "") for name in ARTIFACT_NAMES}
    if len(heads) != 1 or not next(iter(heads)):
        raise ValueError("Phase 0 artifacts do not share one non-empty git_head")

    registry = payloads["registry.json"]
    reasons = registry.get("reasons") or ()
    if int(registry.get("reason_count") or 0) != EXPECTED_REASON_COUNT or len(reasons) != EXPECTED_REASON_COUNT:
        raise ValueError("Phase 0 registry does not contain exactly 37 reasons")
    reason_ids = [str(row.get("reason_id") or "") for row in reasons]
    if len(set(reason_ids)) != EXPECTED_REASON_COUNT:
        raise ValueError("Phase 0 registry contains duplicate reason IDs")
    required_status = {"producer_status", "consumer_status", "test_status", "legacy_status"}
    for row in reasons:
        absent = sorted(required_status - set(row))
        if absent:
            raise ValueError(f"reason {row.get('reason_id')} lacks audit status: {absent}")

    producers = payloads["producers.json"]
    candidate_ids = producers.get("candidate_site_ids") or ()
    classified_ids = producers.get("classified_site_ids") or ()
    if len(candidate_ids) != len(set(candidate_ids)):
        raise ValueError("discovered inventory candidate IDs are not unique")
    if set(candidate_ids) != set(classified_ids):
        raise ValueError("discovered and classified inventory site sets differ")
    if not producers.get("inventory_review_digest"):
        raise ValueError("inventory review digest is missing")
    if _inventory_candidate_set_digest(producers.get("inventory_candidates") or ()) != producers.get(
        "inventory_candidate_set_digest"
    ):
        raise ValueError("inventory source fingerprints differ from the reviewed candidate set")
    all_inventory_sites = list(producers.get("sites") or ()) + list(
        payloads["consumers.json"].get("inventory_sites") or ()
    )
    by_id = {}
    for row in all_inventory_sites:
        site_id = str(row.get("site_id"))
        if site_id in by_id and by_id[site_id] != row:
            raise ValueError(f"conflicting inventory classifications: {site_id}")
        by_id[site_id] = row
    if set(by_id) != set(candidate_ids):
        raise ValueError("artifact inventory sites do not cover the discovered candidates")
    for site in by_id.values():
        if site.get("review_status") != "reviewed":
            raise ValueError(f"unreviewed inventory site: {site.get('site_id')}")
        if site.get("reason_resolution") == "dynamic":
            raise ValueError(f"unresolved dynamic inventory site: {site.get('site_id')}")
        if not site.get("inventory_source_fingerprint"):
            raise ValueError(f"inventory site lacks source fingerprint: {site.get('site_id')}")

    manifest = payloads["census_manifest.json"]
    if manifest.get("manifest_kind") != PHASE0_MANIFEST_KIND:
        raise ValueError("Phase 0 census manifest kind collides with v2 authority")
    if manifest.get("non_authoritative") is not True:
        raise ValueError("Phase 0 census manifest must be non-authoritative")
    entries = manifest.get("entries") or ()
    if int(manifest.get("entry_count") or 0) != len(entries):
        raise ValueError("census manifest entry_count mismatch")
    entry_ids = [str(entry.get("result_entry_id") or "") for entry in entries]
    if len(entry_ids) != len(set(entry_ids)):
        raise ValueError("census manifest result_entry_id is not unique")
    for entry in entries:
        if not entry.get("source_artifact_digest") or not entry.get("comparison_identity_digest"):
            raise ValueError("census manifest entry lacks bound digest")
        if entry.get("selection_input_digest") != manifest.get("selection_input_digest"):
            raise ValueError("census entry is not bound to the selection input")
        if _json_digest(entry.get("analysis_config") or {}) != entry.get("analysis_config_digest"):
            raise ValueError("census entry analysis config digest mismatch")
        if _json_digest(entry.get("analysis_command")) != entry.get("analysis_command_digest"):
            raise ValueError("census entry analysis command digest mismatch")
        if entry.get("evidence_mode") not in PHASE0_EVIDENCE_MODES:
            raise ValueError("census manifest entry has invalid evidence mode")
        if {
            "event_stream_authority_digest",
            "lifecycle_projection_digest",
            "decision_receipt_digest",
        }.intersection(entry):
            raise ValueError("Phase 0 manifest fabricates v2 authority digests")
        declared_decisions = {
            str(branch).split(":", 1)[1]
            for branch in entry.get("covered_consumer_branches") or ()
            if str(branch).startswith("decision:")
        }
        observed_decision = "EQUIVALENT" if entry.get("decision") == "EQ" else entry.get("decision")
        if declared_decisions and declared_decisions != {observed_decision}:
            raise ValueError("selection branch does not match observed decision")
    if manifest.get("missing_required_selection_branches"):
        raise ValueError("Phase 0 representative selection matrix is incomplete")
    covered = {
        str(branch)
        for entry in entries
        for branch in entry.get("covered_consumer_branches") or ()
    }
    if not REQUIRED_SELECTION_BRANCHES.issubset(covered):
        raise ValueError("Phase 0 manifest does not cover every required selection branch")

    census = payloads["census.json"]
    if census.get("manifest_digest") != _json_digest(manifest):
        raise ValueError("census is not bound to the supplied manifest")
    if int(census.get("result_count") or 0) != len(entries):
        raise ValueError("census result_count mismatch")
    census_ids = [str(row.get("result_entry_id") or "") for row in census.get("results") or ()]
    if set(census_ids) != set(entry_ids) or len(census_ids) != len(entry_ids):
        raise ValueError("census contains a result outside its manifest")
    timeout_rows = census.get("runtime_timeout_correspondence") or ()
    if {row.get("result_entry_id") for row in timeout_rows} != set(entry_ids):
        raise ValueError("timeout correspondence does not cover the manifest")
    for row in timeout_rows:
        if row.get("final_outcome") == "TIMEOUT":
            if int(row.get("terminal_timeout_event_count") or 0) != 1:
                raise ValueError("final TIMEOUT lacks exactly one terminal timeout event")
            if int(row.get("solver_unknown_timeout_reason_occurrence_count") or 0) < 1:
                raise ValueError("final TIMEOUT lacks its diagnostic timeout reason")
        elif int(row.get("terminal_timeout_event_count") or 0) != 0:
            raise ValueError("non-TIMEOUT result has a terminal timeout event")
    if repo_root is not None:
        root = Path(repo_root).resolve()
        current_head_tree = (
            frozen_head_tree_digest
            if frozen_head_tree_digest is not None
            else _git_value(root, "rev-parse", "HEAD^{tree}")
        )
        current_tracked_worktree = (
            frozen_tracked_worktree_digest
            if frozen_tracked_worktree_digest is not None
            else _tracked_worktree_digest(root)
        )
        raw_selection_path = manifest.get("selection_input_path")
        selection_document = None
        if raw_selection_path:
            selection_path = Path(str(raw_selection_path))
            if not selection_path.is_absolute():
                selection_path = root / selection_path
            selection_document = json.loads(selection_path.read_text(encoding="utf-8"))
            if _json_digest(selection_document) != manifest.get("selection_input_digest"):
                raise ValueError("selection input artifact digest mismatch")
            selection_rows = selection_document.get("selections") or ()
            exclusion_rows = selection_document.get("excluded_observations") or ()
            if len(selection_rows) != len(entries):
                raise ValueError("selection input row count does not match manifest entries")
            if len(exclusion_rows) != len(manifest.get("excluded_result_observations") or ()):
                raise ValueError("selection exclusion row count does not match manifest")
            if {int(entry.get("selection_row_index", -1)) for entry in entries} != set(
                range(len(selection_rows))
            ):
                raise ValueError("selection rows are not joined one-to-one with manifest entries")
            if {
                int(entry.get("selection_row_index", -1))
                for entry in manifest.get("excluded_result_observations") or ()
            } != set(range(len(exclusion_rows))):
                raise ValueError("exclusion rows are not joined one-to-one with manifest entries")
        for entry in entries:
            if selection_document is not None:
                _validate_selection_row_binding(
                    entry,
                    (selection_document.get("selections") or ()),
                    row_kind="selection",
                )
            source = Path(str(entry["source_artifact_path"]))
            if not source.is_absolute():
                source = root / source
            if _sha256_file(source) != entry["source_artifact_digest"]:
                raise ValueError("selected result artifact digest mismatch")
            source_payloads = extract_result_payloads_from_text(
                source.read_text(encoding="utf-8", errors="replace")
            )
            payload_index = int(entry.get("payload_index", -1))
            if payload_index < 0 or payload_index >= len(source_payloads):
                raise ValueError("selected result payload index cannot be rematerialized")
            payload = source_payloads[payload_index]
            identity = _result_identity(payload, source)
            if identity != entry.get("comparison_identity"):
                raise ValueError("selected result comparison identity mismatch")
            if _json_digest(identity) != entry.get("comparison_identity_digest"):
                raise ValueError("selected result comparison identity digest mismatch")
            if _json_digest(payload) != entry.get("legacy_projection_input_digest"):
                raise ValueError("selected result legacy projection digest mismatch")
            if classify_result_payload(payload) != entry.get("decision"):
                raise ValueError("selected result decision mismatch")
            observed_binary_identities = {
                "left": payload.get("binary1_content_identity"),
                "right": payload.get("binary2_content_identity"),
            }
            if entry.get("evidence_mode") == "CURRENT_HEAD_REAL_RERUN":
                if observed_binary_identities != entry.get("binary_content_identities"):
                    raise ValueError("selected result binary identities mismatch")
                _validate_bound_receipt_entry(
                    root,
                    entry,
                    payload,
                    head_tree_digest=current_head_tree,
                    tracked_worktree_digest=current_tracked_worktree,
                )
        for entry in manifest.get("excluded_result_observations") or ():
            if selection_document is not None:
                _validate_selection_row_binding(
                    entry,
                    (selection_document.get("excluded_observations") or ()),
                    row_kind="exclusion",
                )
            source = Path(str(entry["source_artifact_path"]))
            if not source.is_absolute():
                source = root / source
            if _sha256_file(source) != entry["source_artifact_digest"]:
                raise ValueError("excluded result artifact digest mismatch")
    migration = payloads["migration_manifest.json"]
    phase0_gate = migration.get("phase0_gate") or {}
    if phase0_gate.get("production_behavior_changed") is not False:
        raise ValueError("Phase 0 must not claim a production behavior change")
    if phase0_gate.get("production_change_allowlist") != []:
        raise ValueError("Phase 0 production change allowlist must be empty")
    migration_rows = migration.get("reason_status") or ()
    migration_ids = [str(row.get("reason_id") or "") for row in migration_rows]
    if migration_ids != sorted(reason_ids):
        raise ValueError("migration manifest does not cover the canonical reason set")
    for row in migration_rows:
        if not all(
            row.get(field)
            for field in (
                "recommended_action",
                "recommended_v2_kind",
                "classification_confidence",
                "known_issue",
            )
        ):
            raise ValueError(f"migration posture is incomplete: {row.get('reason_id')}")
    legacy = census.get("legacy_baseline_diagnostic") or {}
    binding = manifest.get("legacy_baseline_binding") or {}
    if legacy.get("non_current_diagnostic") is not True or legacy.get("canonical_v2_metrics") is not False:
        raise ValueError("legacy baseline is not isolated from current canonical truth")
    if int(legacy.get("summary_file_count") or 0) != 411:
        raise ValueError("legacy baseline does not bind all 411 saved summaries")
    if binding.get("baseline_digest") != legacy.get("baseline_digest"):
        raise ValueError("legacy baseline binding digest mismatch")
    if _json_digest({"entries": legacy.get("entries") or []}) != legacy.get("baseline_digest"):
        raise ValueError("legacy baseline entry manifest digest mismatch")


def _scan_python_file(path: Path, root: Path) -> Dict[str, Any]:
    text = path.read_text(encoding="utf-8", errors="replace")
    try:
        tree = ast.parse(text, filename=str(path))
    except SyntaxError as exc:
        return {
            "path": path.relative_to(root).as_posix(),
            "is_test": "/tests/" in f"/{path.relative_to(root).as_posix()}",
            "text": text,
            "lines": text.splitlines(),
            "tree": None,
            "syntax_error": str(exc),
        }
    rel = path.relative_to(root).as_posix()
    return {
        "path": rel,
        "is_test": "/tests/" in f"/{rel}",
        "text": text,
        "lines": text.splitlines(),
        "tree": tree,
        "syntax_error": None,
    }


def _scan_text_file(path: Path, root: Path) -> Dict[str, Any]:
    text = path.read_text(encoding="utf-8", errors="replace")
    rel = path.relative_to(root).as_posix()
    return {
        "path": rel,
        "is_test": "/tests/" in f"/{rel}",
        "text": text,
        "lines": text.splitlines(),
        "tree": None,
        "syntax_error": None,
    }


def discover_inventory_candidate_digest(repo_root: Path) -> Tuple[str, int]:
    """Return the current production candidate-set digest for review bootstrap."""

    root = Path(repo_root).resolve()
    source_root = root / "scripts" / "function_tracer_pcode"
    scans = tuple(
        _scan_python_file(path, root)
        for path in sorted(source_root.rglob("*.py"), key=lambda value: value.as_posix())
    )
    shell_paths = tuple(root.glob("*.sh")) + tuple((root / "scripts").rglob("*.sh"))
    shell_scans = tuple(
        _scan_text_file(path, root)
        for path in sorted(set(shell_paths), key=lambda value: value.as_posix())
        if ".git" not in path.parts
    )
    candidates = _discover_inventory_candidates(scans, shell_scans)
    return _inventory_candidate_set_digest(candidates), len(candidates)


def build_inventory_review_template(repo_root: Path) -> Dict[str, Any]:
    """Create an unapproved review table; the audit never accepts this directly."""

    root = Path(repo_root).resolve()
    source_root = root / "scripts" / "function_tracer_pcode"
    scans = tuple(
        _scan_python_file(path, root)
        for path in sorted(source_root.rglob("*.py"), key=lambda value: value.as_posix())
    )
    shell_paths = tuple(root.glob("*.sh")) + tuple((root / "scripts").rglob("*.sh"))
    shell_scans = tuple(
        _scan_text_file(path, root)
        for path in sorted(set(shell_paths), key=lambda value: value.as_posix())
        if ".git" not in path.parts
    )
    reason_ids = tuple(sorted(unknown_reason_registry_snapshot()))
    candidates = _discover_inventory_candidates(scans, shell_scans)
    resolution_index = _build_reason_resolution_index(scans, reason_ids)
    proposed = [
        _classify_inventory_candidate(candidate, reason_ids, resolution_index)
        for candidate in candidates
    ]
    return {
        "schema_version": 1,
        "review_kind": "unknown_taxonomy_phase0_inventory_classification",
        "candidate_set_digest": _inventory_candidate_set_digest(candidates),
        "reviewed_by": None,
        "review_status": "unreviewed_template",
        "entries": [
            {
                key: row[key]
                for key in (
                    "site_id",
                    "path",
                    "line",
                    "symbol",
                    "construct_kind",
                    "source",
                    "inventory_source_fingerprint",
                    "authority_role",
                    "reason_resolution",
                    "resolved_reason_ids",
                    "resolution_basis",
                    "consumer_class",
                    "shell_role",
                    "review_status",
                )
            }
            for row in proposed
        ],
    }


def _apply_inventory_review(
    candidates: Sequence[Mapping[str, Any]],
    review: Mapping[str, Any],
    reason_ids: Sequence[str],
    candidate_set_digest: str,
) -> list:
    if review.get("review_kind") != "unknown_taxonomy_phase0_inventory_classification":
        raise ValueError("inventory review kind mismatch")
    if review.get("candidate_set_digest") != candidate_set_digest:
        raise ValueError("inventory review is stale for the discovered candidate set")
    if review.get("review_status") != "reviewed" or not review.get("reviewed_by"):
        raise ValueError("inventory review has not been independently approved")
    candidates_by_id = {str(row["site_id"]): row for row in candidates}
    entries = review.get("entries") or ()
    review_by_id = {str(row.get("site_id")): row for row in entries}
    if len(review_by_id) != len(entries) or set(review_by_id) != set(candidates_by_id):
        raise ValueError("inventory review entries do not equal discovered candidates")
    known = set(reason_ids)
    classified = []
    for site_id in sorted(candidates_by_id):
        candidate = candidates_by_id[site_id]
        row = review_by_id[site_id]
        if row.get("review_status") != "reviewed":
            raise ValueError(f"inventory site is not reviewed: {site_id}")
        if row.get("inventory_source_fingerprint") != candidate.get("inventory_source_fingerprint"):
            raise ValueError(f"inventory review source fingerprint mismatch: {site_id}")
        resolution = str(row.get("reason_resolution") or "")
        resolved = tuple(str(value) for value in row.get("resolved_reason_ids") or ())
        if resolution == "dynamic_unresolved":
            raise ValueError(f"inventory dynamic site remains unresolved: {site_id}")
        if not set(resolved).issubset(known):
            raise ValueError(f"inventory review contains an unknown reason ID: {site_id}")
        classified.append(
            {
                **candidate,
                "authority_role": row.get("authority_role"),
                "reason_resolution": resolution,
                "resolved_reason_ids": list(resolved),
                "resolution_basis": row.get("resolution_basis") or {},
                "consumer_class": row.get("consumer_class"),
                "shell_role": row.get("shell_role"),
                "review_status": "reviewed",
            }
        )
    return sorted(classified, key=lambda row: (row["path"], row["line"], row["construct_kind"]))


def _discover_inventory_candidates(
    scans: Sequence[Mapping[str, Any]],
    shell_scans: Sequence[Mapping[str, Any]],
) -> list:
    candidates = []
    for scan in scans:
        if (
            scan["is_test"]
            or scan["path"].endswith("equivalence/unknown_reason.py")
            or scan["path"].endswith("validation/unknown_taxonomy_audit.py")
            or scan["path"].endswith("validation/unknown_taxonomy_evidence_runner.py")
        ):
            continue
        for line_no, line in enumerate(scan["lines"], 1):
            lowered = line.lower()
            stripped = line.strip()
            if not stripped or stripped.startswith("#"):
                continue
            construct_kind = None
            if "make_unknown_reason(" in line or "UnknownReasonRecord.create(" in line:
                construct_kind = "reason_constructor"
            elif _looks_like_reason_producer_assignment(line):
                construct_kind = "reason_selection_assignment"
            elif "unknown_reasons" in lowered and any(
                token in lowered for token in ("append(", "extend(", "=", "[*")
            ):
                construct_kind = "reason_collection_mutation"
            elif any(
                token in line
                for token in (
                    "coerce_unknown_reason_record",
                    "coerce_unknown_reason_records",
                    "UnknownReasonRecord.from_dict",
                )
            ):
                construct_kind = "legacy_deserialization"
            elif "unknown_reason" in lowered and not stripped.startswith(("from ", "import ")):
                construct_kind = "reason_collection_read"
            if construct_kind is None:
                continue
            candidates.append(_candidate_site(scan, line_no, construct_kind))
    for scan in shell_scans:
        if scan["is_test"]:
            continue
        for line_no, line in enumerate(scan["lines"], 1):
            lowered = line.lower()
            stripped = line.strip()
            if not stripped or stripped.startswith("#"):
                continue
            if any(token in lowered for token in ("unknown_reason", "unknown", "timeout")):
                candidates.append(_candidate_site(scan, line_no, "shell_status_or_reason"))
    unique = {row["site_id"]: row for row in candidates}
    return sorted(unique.values(), key=lambda row: (row["path"], row["line"], row["construct_kind"]))


def _looks_like_reason_producer_assignment(line: str) -> bool:
    if any(operator in line for operator in ("==", "!=", "<=", ">=")):
        return False
    if "=" not in line:
        return False
    left, right = line.split("=", 1)
    compact_left = left.replace(" ", "")
    if "blocking_reason" in compact_left:
        return True
    if "REASON" in left and ("{" in right or "dict(" in right):
        return True
    if compact_left.endswith("reason_id"):
        return any(
            token in right
            for token in ("UnknownReasonId.", "_unknown_reason_id_", "_REASON_BY_", ".get(")
        )
    return False


def _candidate_site(
    scan: Mapping[str, Any], line_no: int, construct_kind: str
) -> Dict[str, Any]:
    source = scan["lines"][line_no - 1].strip()
    symbol = _symbol_for_line(scan.get("tree"), line_no)
    fingerprint = hashlib.sha256(source.encode("utf-8")).hexdigest()
    # Identical one-line constructs can occur more than once in one function.
    # The line anchor is intentionally part of the reviewed discovery identity:
    # source movement invalidates the review instead of silently coalescing two
    # distinct producer/consumer occurrences.
    stable_key = (
        f"{scan['path']}\0{symbol}\0{line_no}\0{construct_kind}\0{fingerprint}"
    )
    return {
        "site_id": hashlib.sha256(stable_key.encode("utf-8")).hexdigest(),
        "path": scan["path"],
        "line": line_no,
        "symbol": symbol,
        "construct_kind": construct_kind,
        "source": source,
        "inventory_source_fingerprint": fingerprint,
    }


def _symbol_for_line(tree: Optional[ast.AST], line_no: int) -> str:
    if tree is None:
        return "<shell>"
    enclosing = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            end = int(getattr(node, "end_lineno", node.lineno))
            if node.lineno <= line_no <= end:
                enclosing.append((end - node.lineno, node.lineno, node.name))
    return min(enclosing)[2] if enclosing else "<module>"


def _inventory_candidate_set_digest(candidates: Sequence[Mapping[str, Any]]) -> str:
    authority_rows = [
        {
            "site_id": row["site_id"],
            "path": row["path"],
            "symbol": row["symbol"],
            "construct_kind": row["construct_kind"],
            "inventory_source_fingerprint": row["inventory_source_fingerprint"],
        }
        for row in candidates
    ]
    return _json_digest({"sites": authority_rows})


def _classify_inventory_candidate(
    candidate: Mapping[str, Any],
    reason_ids: Sequence[str],
    resolution_index: Optional[Mapping[Tuple[str, str], Sequence[str]]] = None,
) -> Dict[str, Any]:
    source = str(candidate.get("source") or "")
    resolved = sorted(
        reason_id
        for reason_id in reason_ids
        if f'"{reason_id}"' in source or f"'{reason_id}'" in source
    )
    if "UnknownReasonId." in source:
        for item in UnknownReasonId:
            if f"UnknownReasonId.{item.name}" in source:
                resolved.append(item.value)
        resolved = sorted(set(resolved))
    construct = str(candidate["construct_kind"])
    if construct == "reason_selection_assignment" and not _is_reason_producing_assignment(source):
        resolution = "not_applicable"
        resolved = []
        resolution_basis = {
            "kind": "field_initialization_or_nonproducing_transfer",
            "refs": [candidate["site_id"]],
        }
    elif resolved:
        resolution = "static_single" if len(resolved) == 1 else "static_set"
        resolution_basis = {"kind": "same_line_literal_or_enum", "refs": [candidate["site_id"]]}
    elif construct == "shell_status_or_reason":
        resolution = "not_applicable"
        resolution_basis = {"kind": "status_or_reporting_not_semantic_reason", "refs": [candidate["site_id"]]}
    elif construct in {
        "reason_constructor",
        "reason_selection_assignment",
    }:
        # The reviewed Phase 0 inventory conservatively over-approximates
        # indirect mappings and legacy strings with the complete v1 set.
        index = resolution_index or {}
        resolved = list(index.get((str(candidate["path"]), str(candidate["symbol"])), ()))
        if not resolved:
            resolved = list(index.get((str(candidate["path"]), "<file>"), ()))
        if not resolved:
            resolved = list(reason_ids)
        resolution = "static_set"
        resolution_basis = {
            "kind": "symbol_or_file_flow_proposal",
            "refs": [f"{candidate['path']}:{candidate['symbol']}"],
        }
    else:
        resolution = "not_applicable"
        resolution_basis = {"kind": "consumer_or_transfer", "refs": [candidate["site_id"]]}
    path = str(candidate["path"])
    if "/tests/" in f"/{path}":
        authority_role = "test_only"
    elif construct == "legacy_deserialization":
        authority_role = "legacy_reader"
    elif "/validation/" in f"/{path}" and construct in {
        "reason_constructor",
        "reason_selection_assignment",
    }:
        authority_role = "derived_projection"
    elif construct == "shell_status_or_reason":
        authority_role = "derived_projection"
    elif construct == "reason_selection_assignment" and not _is_reason_producing_assignment(source):
        authority_role = "derived_projection"
    elif ".reason_id" in source and construct == "reason_constructor":
        authority_role = "derived_projection"
    elif construct in {"reason_collection_read", "reason_collection_mutation"}:
        authority_role = "derived_projection"
    else:
        authority_role = "production"
    consumer_class = _review_consumer_class(path, construct, source)
    shell_role = _shell_review_role(source) if construct == "shell_status_or_reason" else None
    return {
        **candidate,
        "reason_resolution": resolution,
        "authority_role": authority_role,
        "resolved_reason_ids": resolved,
        "resolution_basis": resolution_basis,
        "consumer_class": consumer_class,
        "shell_role": shell_role,
        "review_status": "unreviewed",
    }


def _review_consumer_class(path: str, construct: str, source: str) -> str:
    lowered = f"{path} {source}".lower()
    if construct == "shell_status_or_reason" or any(
        token in lowered for token in ("/cli/", "batch", "resume", "matrix")
    ):
        return "cli_batch_resume"
    if any(token in lowered for token in ("root_blocker", "recovery", "proof_action", "backlog")):
        return "proof_backlog"
    if any(token in lowered for token in ("fallback", "retry", "attempt", "strategy")):
        return "fallback_retry"
    if any(token in lowered for token in ("primary", "final_unknown", "summarize", "summary")):
        return "final_primary"
    return "general"


def _shell_review_role(source: str) -> str:
    lowered = source.lower()
    if any(token in lowered for token in ("resume", "skip_completed", "skip_existing")):
        return "resume"
    if any(token in lowered for token in ("grep", "awk", "sed", "result_json", "classify")):
        return "parser"
    if any(token in lowered for token in ("echo", "printf", "tee")):
        return "reporting_only"
    if any(token in lowered for token in ("timeout=", "timeout ", "--timeout", "equiv_timeout")):
        return "execution_config"
    if any(token in lowered for token in ("status=", "result=", "exit_code", "return ")):
        return "status_authority"
    return "other_consumer"


def _is_reason_producing_assignment(source: str) -> bool:
    compact = source.replace(" ", "")
    if "failure_status" in compact:
        return False
    if ".blocking_reason=" in compact or compact.startswith("blocking_reason="):
        return True
    if "reason_id=" not in compact:
        return False
    right = compact.split("reason_id=", 1)[1]
    return any(
        token in right
        for token in (
            "UnknownReasonId.",
            "_unknown_reason_id_",
            "_REASON_BY_",
            ".get(",
            '"',
            "'",
        )
    )


def _build_reason_resolution_index(
    scans: Sequence[Mapping[str, Any]], reason_ids: Sequence[str]
) -> Dict[Tuple[str, str], Tuple[str, ...]]:
    known = set(reason_ids)
    index: Dict[Tuple[str, str], set] = defaultdict(set)
    for scan in scans:
        tree = scan.get("tree")
        if tree is None or scan["is_test"]:
            continue
        file_values = set()
        for node in ast.walk(tree):
            value = _static_reason_value(node)
            if value in known:
                file_values.add(value)
        index[(str(scan["path"]), "<file>")].update(file_values)
        for node in ast.walk(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            values = set()
            for child in ast.walk(node):
                value = _static_reason_value(child)
                if value in known:
                    values.add(value)
            index[(str(scan["path"]), node.name)].update(values)
    return {key: tuple(sorted(values)) for key, values in index.items()}


def _reason_site_posture(
    reason_id: str,
    sites: Sequence[Mapping[str, Any]],
    test_refs: Mapping[str, Sequence[Mapping[str, Any]]],
    *,
    legacy_readable: bool = True,
) -> Dict[str, Any]:
    relevant = [row for row in sites if reason_id in row.get("resolved_reason_ids", ())]
    production = [row for row in relevant if row.get("authority_role") == "production"]
    derived = [row for row in relevant if row.get("authority_role") == "derived_projection"]
    legacy = [row for row in relevant if row.get("authority_role") == "legacy_reader"]
    test_count = len(test_refs.get(reason_id, ()))
    if production:
        posture = "production"
    elif derived:
        posture = "derived_projection_only"
    elif test_count:
        posture = "test_only"
    elif legacy_readable:
        posture = "legacy_only"
    else:
        posture = "dead"
    return {
        "producer_status": posture,
        "lifecycle_posture": posture,
        "production_site_count": len(production),
        "derived_projection_site_count": len(derived),
        "legacy_reader_site_count": len(legacy),
        "legacy_readable": legacy_readable,
    }


def _producer_inventory(
    scans: Sequence[Mapping[str, Any]], reason_ids: Sequence[str]
) -> Tuple[Dict[str, list], list]:
    known = set(reason_ids)
    rows: Dict[str, list] = defaultdict(list)
    dynamic = []
    for scan in scans:
        tree = scan.get("tree")
        if tree is None or scan["is_test"] or scan["path"].endswith("equivalence/unknown_reason.py"):
            continue
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call) or _call_name(node.func) not in {
                "make_unknown_reason",
                "UnknownReasonRecord.create",
            }:
                continue
            value = _static_reason_value(node.args[0]) if node.args else None
            site = _site(scan, node.lineno, expression=value or "<dynamic>")
            if value in known:
                rows[value].append(site)
            else:
                site["raw_static_value"] = value
                site["classification"] = "unregistered_literal" if value is not None else "dynamic"
                dynamic.append(site)
    for value in rows.values():
        value.sort(key=lambda row: (row["path"], row["line"]))
    dynamic.sort(key=lambda row: (row["path"], row["line"]))
    return rows, dynamic


def _consumer_inventory(scans: Sequence[Mapping[str, Any]]) -> list:
    rows = []
    for scan in scans:
        if scan["is_test"] or scan["path"].endswith("equivalence/unknown_reason.py"):
            continue
        path_lower = scan["path"].lower()
        for line_no, line in enumerate(scan["lines"], 1):
            lowered = line.lower()
            if "unknown_reason" not in lowered:
                continue
            if "make_unknown_reason(" in line:
                continue
            if any(token in lowered for token in ("primary", "final_unknown", "summarize", "summary")):
                kind = "final_primary"
            elif any(token in lowered for token in ("fallback", "retry", "attempt", "strategy")):
                kind = "fallback_retry"
            elif any(token in path_lower or token in lowered for token in ("/cli/", "batch", "resume")):
                kind = "cli_batch_resume"
            elif any(token in path_lower or token in lowered for token in ("root_blocker", "recovery", "proof_action", "backlog")):
                kind = "proof_backlog"
            else:
                kind = "general"
            rows.append({**_site(scan, line_no), "consumer_class": kind})
    return sorted(rows, key=lambda row: (row["consumer_class"], row["path"], row["line"]))


def _test_reference_inventory(
    scans: Sequence[Mapping[str, Any]], reason_ids: Sequence[str]
) -> Dict[str, list]:
    by_enum = {item.name: item.value for item in UnknownReasonId}
    result: Dict[str, list] = defaultdict(list)
    known = set(reason_ids)
    for scan in scans:
        if not scan["is_test"]:
            continue
        for line_no, line in enumerate(scan["lines"], 1):
            found = set()
            for enum_name, reason_id in by_enum.items():
                if f"UnknownReasonId.{enum_name}" in line:
                    found.add(reason_id)
            for reason_id in known:
                if f'"{reason_id}"' in line or f"'{reason_id}'" in line:
                    found.add(reason_id)
            for reason_id in sorted(found):
                result[reason_id].append(_site(scan, line_no))
    return result


def _decision_projection_inventory(scans: Sequence[Mapping[str, Any]]) -> list:
    rows = []
    decision_tokens = (
        "is_equivalent",
        "status_timeout",
        '"timeout"',
        "'timeout'",
        "not_eq",
        "not equivalent",
        "result: unknown",
        "classify_result",
    )
    for scan in scans:
        if scan["is_test"]:
            continue
        for line_no, line in enumerate(scan["lines"], 1):
            lowered = line.lower()
            matched = sorted(token for token in decision_tokens if token in lowered)
            if matched:
                rows.append({**_site(scan, line_no), "matched_tokens": matched})
    return sorted(rows, key=lambda row: (row["path"], row["line"]))


def _legacy_site_inventory(scans: Sequence[Mapping[str, Any]], reason_ids: Sequence[str]) -> list:
    known = set(reason_ids)
    rows = []
    for scan in scans:
        if scan["is_test"]:
            continue
        for line_no, line in enumerate(scan["lines"], 1):
            lowered = line.lower()
            literals = sorted(reason for reason in known if reason in line)
            if (
                "normalize_unknown_reason_id" in line
                or "rsplit(" in line and "reason" in lowered
                or literals and "UnknownReasonId." not in line
            ):
                rows.append({**_site(scan, line_no), "registered_literals": literals})
    return sorted(rows, key=lambda row: (row["path"], row["line"]))


def _build_census(
    *,
    root: Path,
    head: str,
    selections: Sequence[Mapping[str, Any]],
    common: Mapping[str, Any],
    selection_input_digest: str,
    selection_input_path: Optional[str] = None,
    head_tree_digest_override: Optional[str] = None,
    tracked_worktree_digest_override: Optional[str] = None,
) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    entries = []
    payload_by_id = {}
    has_real_rerun = any(
        selection.get("evidence_mode") == "CURRENT_HEAD_REAL_RERUN"
        for selection in selections
    )
    current_head_tree = (
        head_tree_digest_override
        if has_real_rerun and head_tree_digest_override is not None
        else _git_value(root, "rev-parse", "HEAD^{tree}") if has_real_rerun else None
    )
    current_tracked_worktree = (
        tracked_worktree_digest_override
        if has_real_rerun and tracked_worktree_digest_override is not None
        else _tracked_worktree_digest(root) if has_real_rerun else None
    )
    for selection_index, selection in enumerate(selections):
        mode = str(selection.get("evidence_mode") or "")
        if mode not in PHASE0_EVIDENCE_MODES:
            raise ValueError(f"invalid Phase 0 evidence_mode: {mode!r}")
        raw_path = selection.get("source_artifact_path")
        if not raw_path:
            raise ValueError("selection is missing source_artifact_path")
        path = Path(str(raw_path))
        if not path.is_absolute():
            path = root / path
        path = path.resolve()
        if not path.is_file():
            raise FileNotFoundError(path)
        payloads = extract_result_payloads_from_text(path.read_text(errors="replace"))
        if not payloads:
            raise ValueError(f"no result payload found in {path}")
        payload = payloads[-1]
        identity = _result_identity(payload, path)
        sha256 = _sha256_file(path)
        identity_digest = _json_digest(identity)
        analysis_config = selection.get("analysis_config") or {}
        analysis_config_digest = _json_digest(analysis_config)
        analysis_command = selection.get("analysis_command")
        analysis_command_digest = _json_digest(analysis_command)
        selection_reason = str(selection.get("selection_reason") or "")
        covered_branches = tuple(str(item) for item in selection.get("covered_branches") or ())
        if not selection_reason or not covered_branches:
            raise ValueError("selection requires rationale and covered consumer branches")
        if mode == "CURRENT_HEAD_REAL_RERUN":
            if str(selection.get("repository_commit") or "") != head:
                raise ValueError("current-HEAD rerun selection is not bound to audit HEAD")
            if not analysis_command:
                raise ValueError("current-HEAD rerun selection lacks analysis command")
            if not selection.get("binary_content_identities"):
                raise ValueError("current-HEAD rerun selection lacks binary content identities")
            supplied_identities = selection["binary_content_identities"]
            observed_identities = {
                "left": payload.get("binary1_content_identity"),
                "right": payload.get("binary2_content_identity"),
            }
            if supplied_identities != observed_identities:
                raise ValueError("selected binary content identities do not match result payload")
            decision = classify_result_payload(payload)
            solver_results = (payload.get("solver_results") or {}).get("all_results") or ()
            if decision == "NOT_EQ":
                if not str(analysis_config.get("domain_rationale") or ""):
                    raise ValueError("NOT_EQ selection lacks domain rationale")
                if not any(
                    row.get("status") == "SAT" and row.get("model") is not None
                    for row in solver_results if isinstance(row, Mapping)
                ):
                    raise ValueError("NOT_EQ selection lacks a solver model")
            if decision == "TIMEOUT":
                if payload.get("is_timeout") is not True or not any(
                    row.get("status") == "TIMEOUT"
                    for row in solver_results if isinstance(row, Mapping)
                ):
                    raise ValueError("TIMEOUT selection lacks terminal solver timeout evidence")
            receipt_path, receipt_digest = _validate_run_receipt(
                root=root,
                selection=selection,
                source_path=path,
                source_digest=sha256,
                payload=payload,
                payload_index=len(payloads) - 1,
                head=head,
                head_tree_digest=current_head_tree,
                tracked_worktree_digest=current_tracked_worktree,
            )
        else:
            receipt_path, receipt_digest = None, None
        entry_id = hashlib.sha256(
            (
                f"{mode}\0{identity_digest}\0{sha256}\0{len(payloads) - 1}\0"
                f"{_relative_or_absolute(path, root)}"
            ).encode("utf-8")
        ).hexdigest()
        entry = {
            "result_occurrence_id": entry_id,
            "result_entry_id": entry_id,
            "evidence_mode": mode,
            "repository_commit": selection.get("repository_commit"),
            "analysis_command": analysis_command,
            "analysis_command_digest": analysis_command_digest,
            "analysis_config": analysis_config,
            "analysis_config_digest": analysis_config_digest,
            "binary_content_identities": selection.get("binary_content_identities") or {},
            "comparison_identity": identity,
            "comparison_identity_digest": identity_digest,
            "source_artifact_path": _relative_or_absolute(path, root),
            "source_artifact_digest": sha256,
            "payload_index": len(payloads) - 1,
            "legacy_projection_input_digest": _json_digest(payload),
            "selection_input_digest": selection_input_digest,
            "selection_row_index": selection_index,
            "selection_row_digest": _json_digest(selection),
            "run_receipt_path": receipt_path,
            "run_receipt_digest": receipt_digest,
            "selection_reason": selection_reason,
            "covered_consumer_branches": list(covered_branches),
            "duplicate_policy": selection.get("duplicate_policy"),
            "decision": classify_result_payload(payload),
        }
        entries.append(entry)
        payload_by_id[entry_id] = payload
    entries.sort(key=lambda row: row["result_entry_id"])
    mode_counts = dict(sorted(Counter(entry["evidence_mode"] for entry in entries).items()))
    manifest = {
        **common,
        "manifest_kind": PHASE0_MANIFEST_KIND,
        "non_authoritative": True,
        "incompatible_with": "v2_canonical_census_manifest",
        "selection_policy": "explicit_reviewed_entries_last_result_payload_no_implicit_duplicates",
        "selection_input_digest": selection_input_digest,
        "selection_input_path": selection_input_path,
        "entry_count": len(entries),
        "mode_counts": mode_counts,
        "required_selection_branches": sorted(REQUIRED_SELECTION_BRANCHES),
        "missing_required_selection_branches": sorted(
            REQUIRED_SELECTION_BRANCHES
            - {
                str(branch)
                for entry in entries
                for branch in entry.get("covered_consumer_branches") or ()
            }
        ),
        "selected_result_entries": entries,
        "entries": entries,
    }
    decisions = Counter()
    reasons = Counter()
    result_rows = []
    timeout_correspondence = []
    duplicate_keys: Dict[Tuple[str, str], list] = defaultdict(list)
    for entry in entries:
        payload = payload_by_id[entry["result_entry_id"]]
        decision = str(entry["decision"] or "ERROR")
        records = coerce_unknown_reason_records(payload.get("unknown_reasons") or ())
        decisions[decision] += 1
        reasons.update(record.reason_id for record in records)
        result_rows.append(
            {
                "result_entry_id": entry["result_entry_id"],
                "evidence_mode": entry["evidence_mode"],
                "decision": decision,
                "reason_ids": [record.reason_id for record in records],
            }
        )
        timeout_correspondence.append(_timeout_correspondence_row(entry, payload, records))
        duplicate_keys[(entry["comparison_identity_digest"], entry["source_artifact_digest"])].append(
            entry["result_entry_id"]
        )
    duplicates = [
        {
            "comparison_identity_digest": key[0],
            "source_artifact_digest": key[1],
            "result_entry_ids": value,
        }
        for key, value in sorted(duplicate_keys.items())
        if len(value) > 1
    ]
    if duplicates:
        entries_by_id = {entry["result_entry_id"]: entry for entry in entries}
        for duplicate in duplicates:
            if not all(
                entries_by_id[entry_id].get("duplicate_policy")
                for entry_id in duplicate["result_entry_ids"]
            ):
                raise ValueError("duplicate stable result lacks an explicit duplicate_policy")
    sections = {}
    for mode in sorted(PHASE0_EVIDENCE_MODES):
        selected = [row for row in result_rows if row["evidence_mode"] == mode]
        sections[mode] = {
            "result_count": len(selected),
            "decision_counts": dict(sorted(Counter(row["decision"] for row in selected).items())),
            "results": selected,
        }
    census = {
        **common,
        "census_kind": "phase0_observed_v1_diagnostic",
        "non_authoritative": True,
        "census_mode": "LEGACY_DIAGNOSTIC",
        "canonical_v2_metrics": False,
        "manifest_digest": _json_digest(manifest),
        "result_count": len(entries),
        "diagnostic_decision_counts": dict(sorted(decisions.items())),
        "diagnostic_reason_record_counts": dict(sorted(reasons.items())),
        "results": result_rows,
        "evidence_sections": sections,
        "duplicate_stable_results": duplicates,
        "runtime_timeout_correspondence": timeout_correspondence,
        "timeout_count_contract": (
            "Diagnostic solver_unknown_timeout occurrence counts are independent from final "
            "TIMEOUT result counts. A final TIMEOUT requires one terminal solver TIMEOUT event; "
            "nonterminal timeout observations remain attached to their final outcome."
        ),
    }
    return manifest, census


def _timeout_correspondence_row(
    entry: Mapping[str, Any],
    payload: Mapping[str, Any],
    records: Sequence[Any],
) -> Mapping[str, Any]:
    solver_rows = tuple(
        row
        for row in ((payload.get("solver_results") or {}).get("all_results") or ())
        if isinstance(row, Mapping)
    )
    timeout_rows = tuple(row for row in solver_rows if row.get("status") == "TIMEOUT")
    decision = str(entry.get("decision") or "ERROR")
    reason_rows = tuple(
        record for record in records
        if getattr(record, "reason_id", None) == UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT.value
    )
    reason_budgets = sorted(
        {
            value
            for record in reason_rows
            for value in _find_labeled_numeric_values(
                getattr(record, "object_target_key", None), "timeout_budget_seconds"
            )
        }
    )
    config = entry.get("analysis_config") or {}
    if config.get("strategy") == "monolithic":
        configured_budget = config.get("monolithic_timeout")
        configured_budget_field = "monolithic_timeout"
    elif config.get("pairwise_timeout_hard") is not None:
        configured_budget = config.get("pairwise_timeout_hard")
        configured_budget_field = "pairwise_timeout_hard"
    else:
        configured_budget = config.get("equiv_timeout")
        configured_budget_field = "equiv_timeout"
    if not timeout_rows and not reason_rows:
        correspondence = "not_applicable"
    elif timeout_rows and not reason_rows:
        correspondence = "missing_solver_timeout_reason"
    elif configured_budget is not None and reason_budgets and any(
        float(value) != float(configured_budget) for value in reason_budgets
    ):
        correspondence = "reason_budget_mismatch"
    else:
        correspondence = "aligned_or_budget_not_recorded"
    return {
        "result_entry_id": entry.get("result_entry_id"),
        "final_outcome": decision,
        "terminal_timeout_event_count": len(timeout_rows) if decision == "TIMEOUT" else 0,
        "observed_nonterminal_timeout_event_count": (
            len(timeout_rows) if decision != "TIMEOUT" else 0
        ),
        "solver_unknown_timeout_reason_occurrence_count": len(reason_rows),
        "configured_timeout_budget_field": configured_budget_field,
        "configured_timeout_budget_seconds": configured_budget,
        "reason_evidence_timeout_budget_seconds": reason_budgets,
        "observed_solver_elapsed_seconds": [row.get("elapsed_time") for row in timeout_rows],
        "correspondence": correspondence,
    }


def _find_labeled_numeric_values(value: Any, label: str) -> Tuple[float, ...]:
    found = []
    if isinstance(value, Mapping):
        for key, child in value.items():
            if str(key) == label and isinstance(child, (int, float)):
                found.append(float(child))
            found.extend(_find_labeled_numeric_values(child, label))
    elif isinstance(value, (list, tuple)):
        if len(value) == 2 and str(value[0]) == label and isinstance(value[1], (int, float)):
            found.append(float(value[1]))
        for child in value:
            found.extend(_find_labeled_numeric_values(child, label))
    return tuple(found)


def _overlap_candidates(definitions: Mapping[str, Any]) -> list:
    groups: Dict[Tuple[str, str, str, str], list] = defaultdict(list)
    for reason_id, definition in definitions.items():
        groups[
            (
                definition.reason_class,
                definition.decision_effect,
                definition.reason_scope,
                definition.aggregation_unit,
            )
        ].append(reason_id)
    return [
        {
            "shared_v1_metadata": {
                "reason_class": key[0],
                "decision_effect": key[1],
                "reason_scope": key[2],
                "aggregation_unit": key[3],
            },
            "reason_ids": sorted(values),
            "review_required": True,
        }
        for key, values in sorted(groups.items())
        if len(values) > 1
    ]


def _migration_posture(reason_id: str, definition: Any) -> Mapping[str, Any]:
    del definition
    reviewed = {
        "decompilation_failed": ("map_decompiler_failure_to_operational_cause_and_policy", "decompiler_operational_cause", "decide explicitly whether exhausted decompilation is UNKNOWN or ERROR"),
        "empty_return_cases": ("materialize_return_partition_absence_cause", "return_partition_cause", "distinguish proved no-return from extraction failure and missing cases"),
        "equivalence_blocking_unsafety": ("split_umbrella_by_call_effect_and_control_flow_target", "domain_specific_unsafety_cause", "umbrella currently merges unrelated call effect and incomplete-control-flow blockers"),
        "high_function_missing": ("map_missing_high_function_to_decompiler_artifact_cause", "high_function_operational_cause", "separate absent HighFunction from general decompilation failure"),
        "loop_summary_proof_missing": ("retain_loop_summary_cause_and_attach_live_proof_frontier", "loop_summary_semantic_cause", "proof alternatives must not participate in cause identity"),
        "method_b_closure_blocked": ("rename_to_loop_closure_contract_cause", "loop_closure_semantic_cause", "method name is strategy-specific and overlaps loop-summary proof absence"),
        "normalization_no_change": ("demote_failed_normalization_to_attempt_event", "normalization_attempt_event", "a no-change attempt is history and must not remain an active cause"),
        "outcome_cfg_reachability_incomplete": ("retain_cfg_reachability_cause_with_reachability_requirement", "cfg_reachability_cause", "bind the exact CFG region rather than the whole function"),
        "outcome_cross_kind_overlap": ("retain_cross_kind_overlap_cause_with_disjointness_requirement", "outcome_overlap_cause", "identify the overlapping return and divergence members"),
        "outcome_member_unclassified": ("retain_unclassified_member_cause_per_outcome_member", "outcome_member_classification_cause", "aggregation at function scope hides which member needs proof"),
        "outcome_partition_residual_sat": ("retain_residual_sat_cause_with_model_evidence", "outcome_partition_residual_cause", "SAT witness and totality proof backlog must remain distinct"),
        "outcome_partition_totality_timeout": ("split_totality_timeout_event_from_partition_cause", "outcome_totality_cause_plus_timeout_event", "timeout is an observation while partition incompleteness is the semantic cause"),
        "outcome_partition_unknown": ("split_unknown_partition_umbrella_into_member_or_totality_causes", "domain_specific_outcome_partition_cause", "fallback reason overlaps the typed outcome reasons"),
        "outcome_path_region_incomplete": ("retain_path_region_cause_per_uncovered_region", "path_region_coverage_cause", "function-level identity merges independent uncovered regions"),
        "outcome_return_consistency_unknown": ("retain_return_consistency_cause_with_equality_requirement", "return_consistency_cause", "unknown consistency must not be merged with a proved value conflict"),
        "outcome_return_value_conflict": ("retain_proved_return_conflict_as_disequivalence_blocker", "return_value_conflict_cause", "clarify whether a safe decisive NOT_EQ receipt can discharge UNKNOWN"),
        "phi_circular_replacement_unproven": ("retain_phi_cycle_cause_per_scc", "phi_cycle_lowering_cause", "bind the PHI strongly connected component and lowering contract"),
        "readonly_identity_missing": ("retain_object_identity_cause_per_storage_object", "readonly_object_identity_cause", "current pair scope can merge distinct readonly objects"),
        "recoverable_partial": ("split_partial_recovery_state_into_attempt_event_and_remaining_cause", "recovery_attempt_event_plus_typed_cause", "completed recovery history must not remain active"),
        "return_coverage_gap": ("retain_proved_coverage_gap_with_uncovered_region", "return_coverage_gap_cause", "do not merge SAT coverage gaps with inconclusive coverage checks"),
        "return_coverage_inconclusive": ("retain_coverage_query_cause_with_live_disambiguation_requirement", "return_coverage_inconclusive_cause", "decision-blocking policy differs from a proved gap"),
        "return_width_bridge_missing": ("retain_return_width_cause_bound_to_observation_contract", "return_width_bridge_cause", "cause identity must exclude the chosen bridge proof strategy"),
        "sat_counterexample_ambiguous": ("retain_counterexample_ambiguity_cause_with_replay_requirement", "counterexample_ambiguity_cause", "ambiguity blocks disequivalence and is not generic SAT unsafety"),
        "sat_unsafety": ("split_sat_unsafety_by_active_semantic_safety_gate", "domain_specific_sat_safety_cause", "umbrella currently hides which safety gate rejected the model"),
        "solver_proven_rewrite_no_change": ("demote_rewrite_no_change_to_attempt_event", "rewrite_attempt_event", "no-change is an attempted recovery outcome rather than semantic cause"),
        "solver_proven_rewrite_proof_failed": ("retain_rewrite_proof_cause_only_while_requirement_live", "rewrite_proof_cause", "separate solver failure event from the unproved rewrite relation"),
        "solver_unknown_timeout": ("split_terminal_timeout_event_from_nonterminal_solver_cause", "solver_requirement_cause_plus_timeout_event", "diagnostic occurrence count is not final TIMEOUT result authority"),
        "strategy_exception": ("route_strategy_exception_to_error_event_with_optional_recovery_cause", "strategy_error_event", "exception authority must not be inferred from an UNKNOWN reason"),
        "summary_effect_unmodeled": ("retain_unmodeled_effect_cause_per_effect_surface", "summary_effect_cause", "bind memory or call effect surface instead of whole summary"),
        "summary_partition_not_total": ("retain_summary_totality_cause_with_residual_region", "summary_partition_totality_cause", "distinguish construction gap from timeout while proving totality"),
        "summary_precondition_incomplete": ("retain_precondition_cause_per_missing_predicate", "summary_precondition_cause", "multiple missing predicates need independent cause identities"),
        "summary_return_candidate_invalid": ("retain_invalid_candidate_cause_with_candidate_identity", "summary_return_candidate_cause", "do not merge all rejected return candidates for one function"),
        "summary_return_overlap_unproven": ("retain_summary_overlap_cause_with_pairwise_disjointness_requirement", "summary_return_overlap_cause", "bind the exact candidate pair whose overlap is unproved"),
        "unexpected_pairwise_state": ("route_impossible_pairwise_state_to_internal_error_event", "pairwise_internal_error_event", "unexpected state is tool failure authority rather than semantic uncertainty"),
        "unknown": ("eliminate_umbrella_and_require_typed_cause", "no_canonical_v2_reason", "fallback normalization erases the originating semantic distinction"),
        "unresolved_expression": ("retain_expression_lowering_cause_per_expression_identity", "expression_lowering_cause", "separate unsupported opcode from missing symbol and malformed expression"),
        "unresolved_value_expression": ("retain_value_relation_lowering_cause_per_pair_expression", "value_expression_lowering_cause", "distinguish pairwise value lowering from general expression extraction"),
    }
    try:
        action, target_kind, issue = reviewed[reason_id]
    except KeyError as exc:
        raise ValueError(f"missing reviewed migration posture for {reason_id}") from exc
    return {
        "migration_status": "phase0_classified",
        "recommended_action": action,
        "recommended_v2_kind": target_kind,
        "classification_confidence": "reviewed_phase0",
        "known_issue": issue,
    }


def _build_excluded_observations(
    root: Path, exclusions: Sequence[Mapping[str, Any]]
) -> list:
    rows = []
    for exclusion_index, exclusion in enumerate(exclusions):
        raw_path = exclusion.get("source_artifact_path")
        rationale = str(exclusion.get("exclusion_reason") or "")
        if not raw_path or not rationale:
            raise ValueError("excluded observation requires a path and rationale")
        path = Path(str(raw_path))
        if not path.is_absolute():
            path = root / path
        path = path.resolve()
        payloads = extract_result_payloads_from_text(path.read_text(errors="replace"))
        if not payloads:
            raise ValueError(f"excluded observation has no result payload: {path}")
        rows.append(
            {
                "source_artifact_path": _relative_or_absolute(path, root),
                "source_artifact_digest": _sha256_file(path),
                "observed_decision": classify_result_payload(payloads[-1]),
                "exclusion_reason": rationale,
                "non_authoritative": True,
                "selection_row_index": exclusion_index,
                "selection_row_digest": _json_digest(exclusion),
            }
        )
    return sorted(rows, key=lambda row: row["source_artifact_path"])


def _validate_run_artifact_accounting(
    *,
    output: Path,
    root: Path,
    selected_entries: Sequence[Mapping[str, Any]],
    excluded_entries: Sequence[Mapping[str, Any]],
) -> None:
    runs_dir = output / "runs"
    if not runs_dir.is_dir():
        return
    observed_run_paths = {
        _relative_or_absolute(path.resolve(), root) for path in runs_dir.glob("*.log")
    }
    all_accounted_paths = {
        str(entry["source_artifact_path"])
        for entry in (*selected_entries, *excluded_entries)
    }
    run_prefix = _relative_or_absolute(runs_dir.resolve(), root).rstrip("/") + "/"
    accounted_paths = {path for path in all_accounted_paths if path.startswith(run_prefix)}
    if observed_run_paths != accounted_paths:
        raise ValueError(
            "run artifact accounting mismatch: "
            f"unaccounted={sorted(observed_run_paths - accounted_paths)} "
            f"missing={sorted(accounted_paths - observed_run_paths)}"
        )


def _build_legacy_baseline(root: Path) -> Mapping[str, Any]:
    baseline_root = root / "logs" / "EqBench" / "all_eq_matrix_current"
    paths = tuple(sorted(baseline_root.rglob("results_summary.txt")))
    if len(paths) != 411:
        raise ValueError(f"expected 411 saved legacy summaries, found {len(paths)}")
    aggregate_decisions: Counter = Counter()
    aggregate_reasons: Counter = Counter()
    entries = []
    decision_labels = {
        "Total pairs": "TOTAL",
        "Equivalent": "EQUIVALENT",
        "Not equivalent": "NOT_EQ",
        "Error": "ERROR",
        "Unknown": "UNKNOWN",
        "Timeout": "TIMEOUT",
        "Incomplete": "INCOMPLETE",
    }
    for path in paths:
        text = path.read_text(encoding="utf-8", errors="replace")
        counts = {}
        for label, canonical in decision_labels.items():
            match = re.search(rf"^\s*{re.escape(label)}\s*:\s*(\d+)\s*$", text, re.MULTILINE)
            if match:
                counts[canonical] = int(match.group(1))
        for key, value in counts.items():
            aggregate_decisions[key] += value
        section = re.search(
            r"^\s*UNKNOWN by reason:\s*$\n(?P<body>.*?)(?=^\s*[A-Z][^\n]*:\s*$|\Z)",
            text,
            re.MULTILINE | re.DOTALL,
        )
        reason_counts = {}
        if section:
            for reason_id, raw_count in re.findall(
                r"^\s*-\s+([a-z0-9_]+):\s*(\d+)\s*$",
                section.group("body"),
                re.MULTILINE,
            ):
                reason_counts[reason_id] = int(raw_count)
                aggregate_reasons[reason_id] += int(raw_count)
        entries.append(
            {
                "path": _relative_or_absolute(path, root),
                "digest": _sha256_file(path),
                "decision_counts": counts,
                "unknown_by_reason": reason_counts,
            }
        )
    baseline_digest = _json_digest({"entries": entries})
    return {
        "baseline_kind": "saved_eqbench_411_summary_legacy_diagnostic",
        "non_current_diagnostic": True,
        "canonical_v2_metrics": False,
        "source_root": _relative_or_absolute(baseline_root, root),
        "summary_file_count": len(entries),
        "aggregate_saved_decision_counts": dict(sorted(aggregate_decisions.items())),
        "aggregate_saved_unknown_by_reason": dict(sorted(aggregate_reasons.items())),
        "entries": entries,
        "baseline_digest": baseline_digest,
    }


def _validate_run_receipt(
    *,
    root: Path,
    selection: Mapping[str, Any],
    source_path: Path,
    source_digest: str,
    payload: Mapping[str, Any],
    payload_index: int,
    head: str,
    head_tree_digest: Optional[str],
    tracked_worktree_digest: Optional[str],
) -> Tuple[str, str]:
    raw_receipt_path = selection.get("run_receipt_path")
    if not raw_receipt_path:
        raise ValueError("current-HEAD rerun selection lacks a run receipt")
    receipt_path = Path(str(raw_receipt_path))
    if not receipt_path.is_absolute():
        receipt_path = root / receipt_path
    receipt_path = receipt_path.resolve()
    if not receipt_path.is_file():
        raise FileNotFoundError(receipt_path)
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    expected = {
        "receipt_kind": "phase0_current_head_run_receipt",
        "repository_commit": head,
        "head_tree_digest": head_tree_digest,
        "tracked_worktree_digest": tracked_worktree_digest,
        "analysis_command": selection.get("analysis_command"),
        "analysis_command_digest": _json_digest(selection.get("analysis_command")),
        "analysis_config": selection.get("analysis_config") or {},
        "analysis_config_digest": _json_digest(selection.get("analysis_config") or {}),
        "binary_content_identities": selection.get("binary_content_identities") or {},
        "source_artifact_path": _relative_or_absolute(source_path, root),
        "source_artifact_digest": source_digest,
        "payload_index": payload_index,
        "payload_digest": _json_digest(payload),
        "decision": classify_result_payload(payload),
        "observed_binary_content_identities": {
            "left": payload.get("binary1_content_identity"),
            "right": payload.get("binary2_content_identity"),
        },
    }
    for key, value in expected.items():
        if receipt.get(key) != value:
            raise ValueError(f"run receipt field mismatch: {key}")
    if not receipt.get("started_at_utc") or not receipt.get("finished_at_utc"):
        raise ValueError("run receipt lacks execution timestamps")
    return _relative_or_absolute(receipt_path, root), _sha256_file(receipt_path)


def _validate_selection_row_binding(
    entry: Mapping[str, Any],
    rows: Sequence[Mapping[str, Any]],
    *,
    row_kind: str,
) -> None:
    index = int(entry.get("selection_row_index", -1))
    if index < 0 or index >= len(rows):
        raise ValueError(f"{row_kind} row index is outside the selection input")
    row = rows[index]
    if _json_digest(row) != entry.get("selection_row_digest"):
        raise ValueError(f"{row_kind} row digest mismatch")
    if row_kind == "selection":
        expected = {
            "evidence_mode": row.get("evidence_mode"),
            "repository_commit": row.get("repository_commit"),
            "analysis_command": row.get("analysis_command"),
            "analysis_config": row.get("analysis_config") or {},
            "binary_content_identities": row.get("binary_content_identities") or {},
            "source_artifact_path": row.get("source_artifact_path"),
            "run_receipt_path": row.get("run_receipt_path"),
            "selection_reason": row.get("selection_reason"),
            "covered_consumer_branches": list(row.get("covered_branches") or ()),
            "duplicate_policy": row.get("duplicate_policy"),
        }
    else:
        expected = {
            "source_artifact_path": row.get("source_artifact_path"),
            "exclusion_reason": row.get("exclusion_reason"),
        }
    for field, value in expected.items():
        if entry.get(field) != value:
            raise ValueError(f"{row_kind} row field mismatch: {field}")


def _validate_bound_receipt_entry(
    root: Path,
    entry: Mapping[str, Any],
    payload: Mapping[str, Any],
    *,
    head_tree_digest: str,
    tracked_worktree_digest: str,
) -> None:
    raw_path = entry.get("run_receipt_path")
    if not raw_path or not entry.get("run_receipt_digest"):
        raise ValueError("real rerun manifest entry lacks a bound run receipt")
    receipt_path = Path(str(raw_path))
    if not receipt_path.is_absolute():
        receipt_path = root / receipt_path
    if _sha256_file(receipt_path) != entry.get("run_receipt_digest"):
        raise ValueError("run receipt digest mismatch")
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    checks = {
        "repository_commit": entry.get("repository_commit"),
        "head_tree_digest": head_tree_digest,
        "tracked_worktree_digest": tracked_worktree_digest,
        "analysis_command": entry.get("analysis_command"),
        "analysis_command_digest": entry.get("analysis_command_digest"),
        "analysis_config": entry.get("analysis_config"),
        "analysis_config_digest": entry.get("analysis_config_digest"),
        "binary_content_identities": entry.get("binary_content_identities"),
        "source_artifact_path": entry.get("source_artifact_path"),
        "source_artifact_digest": entry.get("source_artifact_digest"),
        "payload_index": entry.get("payload_index"),
        "payload_digest": entry.get("legacy_projection_input_digest"),
        "decision": entry.get("decision"),
        "observed_binary_content_identities": {
            "left": payload.get("binary1_content_identity"),
            "right": payload.get("binary2_content_identity"),
        },
    }
    for key, value in checks.items():
        if receipt.get(key) != value:
            raise ValueError(f"bound run receipt mismatch: {key}")


def _git_value(root: Path, *args: str) -> str:
    completed = subprocess.run(
        ["git", *args], cwd=root, check=True, capture_output=True, text=True
    )
    return completed.stdout.strip()


def _tracked_worktree_digest(root: Path) -> str:
    state = subprocess.run(
        ["git", "diff", "HEAD", "--binary", "--no-ext-diff"],
        cwd=root,
        check=True,
        capture_output=True,
    ).stdout
    state_digest = hashlib.sha256(state).hexdigest()
    cache_key = (str(root.resolve()), state_digest)
    cached = _TRACKED_WORKTREE_DIGEST_CACHE.get(cache_key)
    if cached is not None:
        return cached
    paths = tuple(line for line in _git_value(root, "ls-files").splitlines() if line)
    digest = hashlib.sha256()
    for rel in paths:
        path = root / rel
        digest.update(rel.encode("utf-8"))
        digest.update(b"\0")
        digest.update(
            bytes.fromhex(_sha256_file(path)) if path.is_file() else b"MISSING"
        )
        digest.update(b"\0")
    value = digest.hexdigest()
    _TRACKED_WORKTREE_DIGEST_CACHE[cache_key] = value
    return value


def _reason_consumer_status(reason_id: str, consumers: Sequence[Mapping[str, Any]]) -> str:
    del reason_id
    return "generic_registry_driven" if consumers else "not_observed"


def _legacy_status(reason_id: str) -> str:
    if reason_id == UnknownReasonId.UNKNOWN.value:
        return "fallback_and_exact_id"
    return "exact_id_and_suffix_alias"


def _static_reason_value(node: ast.AST) -> Optional[str]:
    if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and node.value.id == "UnknownReasonId":
        try:
            return UnknownReasonId[node.attr].value
        except KeyError:
            return None
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    return None


def _call_name(node: ast.AST) -> str:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        prefix = _call_name(node.value)
        return f"{prefix}.{node.attr}" if prefix else node.attr
    return ""


def _site(scan: Mapping[str, Any], line_no: int, **extra: Any) -> Dict[str, Any]:
    line = scan["lines"][line_no - 1].strip() if 0 < line_no <= len(scan["lines"]) else ""
    return {"path": scan["path"], "line": line_no, "source": line, **extra}


def _source_reference(path: Path, root: Path, needle: str) -> Mapping[str, Any]:
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if needle in line:
            return {"path": path.relative_to(root).as_posix(), "line": line_no}
    raise ValueError(f"source reference not found: {needle}")


def _result_identity(payload: Mapping[str, Any], path: Path) -> Mapping[str, Any]:
    del path
    return {
        "function1_name": payload.get("function1_name") or payload.get("function_name"),
        "function2_name": payload.get("function2_name") or payload.get("function_name"),
        "binary1_name": payload.get("binary1_name"),
        "binary2_name": payload.get("binary2_name"),
    }


def _relative_or_absolute(path: Path, root: Path) -> str:
    try:
        return path.relative_to(root).as_posix()
    except ValueError:
        return path.as_posix()


def _git_head(root: Path) -> str:
    completed = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=str(root),
        check=True,
        capture_output=True,
        text=True,
    )
    return completed.stdout.strip()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _json_digest(payload: Any) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.write_text(
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Generate the Phase 0 UNKNOWN taxonomy audit.")
    parser.add_argument("--repo-root", default=".")
    parser.add_argument(
        "--output-dir",
        default="artifacts/unknown_reason_audit/current-head",
    )
    parser.add_argument(
        "--selection-input",
        help="JSON file containing a top-level selections array",
    )
    parser.add_argument(
        "--print-candidate-digest",
        action="store_true",
        help="Print the discovered inventory candidate count and digest, then exit",
    )
    parser.add_argument("--inventory-review", help="Reviewed per-site inventory classification JSON")
    parser.add_argument(
        "--write-review-template",
        help="Write an unreviewed per-site classification template and exit",
    )
    args = parser.parse_args(argv)
    if args.print_candidate_digest:
        digest, count = discover_inventory_candidate_digest(Path(args.repo_root))
        print(f"candidate_count={count}")
        print(f"candidate_set_digest={digest}")
        return 0
    if args.write_review_template:
        template_path = Path(args.write_review_template)
        _write_json(template_path, build_inventory_review_template(Path(args.repo_root)))
        print(template_path)
        return 0
    selections = ()
    exclusions = ()
    selection_input_digest = None
    if args.selection_input:
        selection_file = Path(args.selection_input)
        selection_payload = json.loads(selection_file.read_text(encoding="utf-8"))
        selections = tuple(selection_payload.get("selections") or ())
        exclusions = tuple(selection_payload.get("excluded_observations") or ())
        selection_input_digest = _json_digest(selection_payload)
    inventory_review = None
    if args.inventory_review:
        inventory_review = json.loads(Path(args.inventory_review).read_text(encoding="utf-8"))
    paths = build_unknown_taxonomy_audit(
        repo_root=Path(args.repo_root),
        output_dir=Path(args.output_dir),
        selections=selections,
        exclusions=exclusions,
        inventory_review=inventory_review,
        selection_input_digest=selection_input_digest,
        selection_input_path=args.selection_input,
    )
    for name in ARTIFACT_NAMES:
        print(paths[name])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
