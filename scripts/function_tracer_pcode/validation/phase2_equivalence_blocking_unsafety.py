# -*- coding: utf-8 -*-
"""Validate Phase 2 expected movement for equivalence_blocking_unsafety."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence, Tuple

from ..equivalence.unknown_reason import (
    UNKNOWN_TUPLE_MISSING,
    UnknownCountKind,
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    build_proof_obligation_id,
    build_unknown_recovery_actions,
    coerce_unknown_reason_records,
)
from .result_summary import (
    STATUS_EQ,
    STATUS_ORDER,
    STATUS_TIMEOUT,
    STATUS_UNKNOWN,
    ValidationBaselineComparison,
    ValidationLogRecord,
    aggregate_validation_logs,
    compare_validation_baseline_records,
)
from .unknown_reason_summary import (
    _extract_final_unknown_reasons,
    _global_reason_tuple_from_action,
    _global_reason_tuple_from_record,
    _select_primary_records_by_aggregation_unit,
)


MANIFEST_VERSION = 1
MANIFEST_KIND = "phase2_equivalence_blocking_unsafety_expected_movement"
BASELINE_ID = "observed-v0@0a53352"
BASELINE_GIT_HEAD = "0a53352cf3c9528abfb654906ed7b963474bedc5"
TARGET_REASON_ID = "equivalence_blocking_unsafety"
EXPECTED_RECOVERY_ACTION = "call_effect_summary_proof_required"
EXPECTED_PROOF_KIND = UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value
EXPECTED_PROOF_STAGE = "object_evidence_collected"
EXPECTED_ACTION_STATUS = UnknownRecoveryActionStatus.PENDING_PROOF.value
EXPECTED_REQUIRED_EVIDENCE = (
    "call_effect_summary",
    "runtime_ref",
    "callsite_storage",
)
REQUIRED_PRODUCER_EQUIV_ARGS = (
    "--no-completed-recovery-proofs",
)
REQUIRED_PRODUCER_RUN_MANIFEST_VALUES = {
    "run_kind": "phase2_function_call_full_matrix_pre_producer",
    "expected_final_result_movement": "none",
    "expected_reason_movement": "call_effect_summary_proof/object_evidence_collected/pending_proof",
    "validation_skip_completed": "0",
    "validation_require_phase2_object_keys": "1",
    "phase2_run_expected_movement_gate": "1",
}
MISSING_SENTINEL = UNKNOWN_TUPLE_MISSING
TARGET_REPRESENTATIVE_IDS = (
    "representative-equivalence-blocking-unsafety-apply",
    "representative-equivalence-blocking-unsafety-dispatch",
    "representative-equivalence-blocking-unsafety-recursive-stress",
)
KNOWN_LOG_ROOT_CATEGORIES = frozenset({"function_call", "loop"})
ALLOWED_NEW_REASON_TUPLE = (
    TARGET_REASON_ID,
    "blocks_equivalence",
    "function",
    EXPECTED_PROOF_KIND,
    EXPECTED_PROOF_STAGE,
    EXPECTED_ACTION_STATUS,
)
ALLOWED_OLD_REASON_TUPLE = (
    TARGET_REASON_ID,
    "blocks_equivalence",
    "function",
    "none",
    MISSING_SENTINEL,
    MISSING_SENTINEL,
)
UNRESOLVED_EXPRESSION_REASON_TUPLE = (
    "unresolved_expression",
    "blocks_decision",
    "expression",
    "none",
    MISSING_SENTINEL,
    MISSING_SENTINEL,
)
UNRESOLVED_EXPRESSION_PROOF_ACTION_TUPLES = {
    (
        "unresolved_expression",
        "blocks_decision",
        "expression",
        "solver_retry_or_normalization",
        "typed_expression_lowering",
        "planned",
    ),
    (
        "unresolved_expression",
        "blocks_decision",
        "expression",
        "solver_retry_or_normalization",
        "type_normalization",
        "planned",
    ),
}
RETURN_COVERAGE_INCONCLUSIVE_REASON_TUPLE = (
    "return_coverage_inconclusive",
    "blocks_decision",
    "function",
    "return_coverage_completion",
    "return_coverage_smt_disambiguation",
    MISSING_SENTINEL,
)
RETURN_COVERAGE_INCONCLUSIVE_PROOF_ACTION_TUPLE = (
    "return_coverage_inconclusive",
    "blocks_decision",
    "function",
    "return_coverage_completion",
    "return_coverage_smt_disambiguation",
    "planned",
)
SOLVER_PROVEN_REWRITE_PROOF_FAILED_REASON_TUPLE = (
    "solver_proven_rewrite_proof_failed",
    "retryable",
    "pair",
    "solver_retry_or_normalization",
    MISSING_SENTINEL,
    MISSING_SENTINEL,
)
SOLVER_PROVEN_REWRITE_PROOF_ACTION_TUPLES = {
    (
        "solver_proven_rewrite_proof_failed",
        "retryable",
        "pair",
        "solver_retry_or_normalization",
        "rewrite_proof_recheck",
        "planned",
    ),
    (
        "solver_proven_rewrite_proof_failed",
        "retryable",
        "pair",
        "solver_retry_or_normalization",
        "solver_retry",
        "planned",
    ),
}
SAT_UNSAFETY_PROOF_KIND = UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value
SAT_UNSAFETY_PROOF_STAGE = "sat_counterexample_safety"
SAT_UNSAFETY_REASON_TUPLE = (
    "sat_unsafety",
    "blocks_disequivalence",
    "pair",
    SAT_UNSAFETY_PROOF_KIND,
    SAT_UNSAFETY_PROOF_STAGE,
    MISSING_SENTINEL,
)
SAT_UNSAFETY_PENDING_REASON_TUPLE = (
    "sat_unsafety",
    "blocks_disequivalence",
    "pair",
    SAT_UNSAFETY_PROOF_KIND,
    SAT_UNSAFETY_PROOF_STAGE,
    UnknownRecoveryActionStatus.PENDING_PROOF.value,
)
SAT_UNSAFETY_REASON_TUPLES = {
    SAT_UNSAFETY_REASON_TUPLE,
    SAT_UNSAFETY_PENDING_REASON_TUPLE,
}
SAT_UNSAFETY_PROOF_ACTION_TUPLE = (
    "sat_unsafety",
    "blocks_disequivalence",
    "pair",
    SAT_UNSAFETY_PROOF_KIND,
    SAT_UNSAFETY_PROOF_STAGE,
    UnknownRecoveryActionStatus.PLANNED.value,
)
SAT_UNSAFETY_PENDING_PROOF_ACTION_TUPLE = (
    "sat_unsafety",
    "blocks_disequivalence",
    "pair",
    SAT_UNSAFETY_PROOF_KIND,
    SAT_UNSAFETY_PROOF_STAGE,
    UnknownRecoveryActionStatus.PENDING_PROOF.value,
)
SAT_UNSAFETY_PROOF_ACTION_TUPLES = {
    SAT_UNSAFETY_PROOF_ACTION_TUPLE,
    SAT_UNSAFETY_PENDING_PROOF_ACTION_TUPLE,
}
ALLOWED_EXPOSED_REASON_TUPLES = {
    UNRESOLVED_EXPRESSION_REASON_TUPLE,
    (
        "return_coverage_gap",
        "blocks_equivalence",
        "function",
        "return_coverage_completion",
        MISSING_SENTINEL,
        MISSING_SENTINEL,
    ),
    (
        "return_coverage_gap",
        "blocks_equivalence",
        "function",
        "return_coverage_completion",
        MISSING_SENTINEL,
        UnknownRecoveryActionStatus.PENDING_PROOF.value,
    ),
    (
        "return_width_bridge_missing",
        "blocks_equivalence",
        "query",
        "abi_relation_high_bit_proof",
        MISSING_SENTINEL,
        MISSING_SENTINEL,
    ),
    ALLOWED_NEW_REASON_TUPLE,
} | SAT_UNSAFETY_REASON_TUPLES
ALLOWED_EXPOSED_PROOF_ACTION_TUPLES = {
    (
        "return_coverage_gap",
        "blocks_equivalence",
        "function",
        "return_coverage_completion",
        "return_guard_coverage",
        "planned",
    ),
    (
        "return_coverage_gap",
        "blocks_equivalence",
        "function",
        "return_coverage_completion",
        "return_guard_coverage",
        UnknownRecoveryActionStatus.PENDING_PROOF.value,
    ),
    (
        "return_coverage_gap",
        "blocks_equivalence",
        "function",
        "return_coverage_completion",
        "return_partition_extraction",
        "planned",
    ),
    (
        "return_coverage_gap",
        "blocks_equivalence",
        "function",
        "return_coverage_completion",
        "return_partition_extraction",
        UnknownRecoveryActionStatus.PENDING_PROOF.value,
    ),
    (
        "return_width_bridge_missing",
        "blocks_equivalence",
        "query",
        "abi_relation_proof",
        "abi_relation",
        "planned",
    ),
    (
        "return_width_bridge_missing",
        "blocks_equivalence",
        "query",
        "high_bit_proof",
        "high_bit_relation",
        "planned",
    ),
    ALLOWED_NEW_REASON_TUPLE,
} | SAT_UNSAFETY_PROOF_ACTION_TUPLES | UNRESOLVED_EXPRESSION_PROOF_ACTION_TUPLES
ALLOWED_PAIR_EXPOSED_REASONS = {
    TARGET_REASON_ID,
    "return_coverage_gap",
    "return_width_bridge_missing",
    "sat_unsafety",
}
ALLOWED_PAIR_REMOVED_REASONS = {
    "return_coverage_inconclusive",
    "return_width_bridge_missing",
    "sat_unsafety",
    "solver_proven_rewrite_proof_failed",
    "unresolved_expression",
}
RETURN_COVERAGE_GAP_LEGACY_REASON_TUPLE = (
    "return_coverage_gap",
    "blocks_equivalence",
    "function",
    "return_coverage_completion",
    MISSING_SENTINEL,
    MISSING_SENTINEL,
)
RETURN_COVERAGE_GAP_LEGACY_PROOF_ACTION_TUPLES = {
    (
        "return_coverage_gap",
        "blocks_equivalence",
        "function",
        "return_coverage_completion",
        "return_guard_coverage",
        "planned",
    ),
    (
        "return_coverage_gap",
        "blocks_equivalence",
        "function",
        "return_coverage_completion",
        "return_partition_extraction",
        "planned",
    ),
}
RETURN_WIDTH_BRIDGE_MISSING_REASON_TUPLE = (
    "return_width_bridge_missing",
    "blocks_equivalence",
    "query",
    "abi_relation_high_bit_proof",
    MISSING_SENTINEL,
    MISSING_SENTINEL,
)
RETURN_WIDTH_BRIDGE_MISSING_PROOF_ACTION_TUPLES = {
    (
        "return_width_bridge_missing",
        "blocks_equivalence",
        "query",
        "abi_relation_proof",
        "abi_relation",
        "planned",
    ),
    (
        "return_width_bridge_missing",
        "blocks_equivalence",
        "query",
        "high_bit_proof",
        "high_bit_relation",
        "planned",
    ),
}
SAT_UNSAFETY_LEGACY_REASON_TUPLE = (
    "sat_unsafety",
    "blocks_disequivalence",
    "pair",
    "none",
    MISSING_SENTINEL,
    MISSING_SENTINEL,
)
ALLOWED_METADATA_ENRICHMENT_REASON_TUPLES = {
    RETURN_COVERAGE_GAP_LEGACY_REASON_TUPLE,
    SAT_UNSAFETY_LEGACY_REASON_TUPLE,
}
ALLOWED_METADATA_ENRICHMENT_PROOF_ACTION_TUPLES = (
    RETURN_COVERAGE_GAP_LEGACY_PROOF_ACTION_TUPLES
    | {SAT_UNSAFETY_PROOF_ACTION_TUPLE}
)
ALLOWED_BROAD_REMOVED_REASON_TUPLES = {
    RETURN_COVERAGE_INCONCLUSIVE_REASON_TUPLE,
    RETURN_WIDTH_BRIDGE_MISSING_REASON_TUPLE,
    SOLVER_PROVEN_REWRITE_PROOF_FAILED_REASON_TUPLE,
    UNRESOLVED_EXPRESSION_REASON_TUPLE,
}
ALLOWED_BROAD_REMOVED_PROOF_ACTION_TUPLES = (
    RETURN_WIDTH_BRIDGE_MISSING_PROOF_ACTION_TUPLES
    | SOLVER_PROVEN_REWRITE_PROOF_ACTION_TUPLES
    | UNRESOLVED_EXPRESSION_PROOF_ACTION_TUPLES
    | {RETURN_COVERAGE_INCONCLUSIVE_PROOF_ACTION_TUPLE}
)


def build_phase2_equivalence_blocking_unsafety_movement(
    *,
    phase1_dir: Path,
    output_dir: Path,
    current_log_roots: Mapping[str, Path],
    baseline_log_roots: Optional[Mapping[str, Path]] = None,
    baseline_match_scope: str = "all",
) -> Path:
    phase1 = Path(phase1_dir).resolve()
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)
    normalized_current_log_roots = _normalize_log_root_mapping(current_log_roots)
    normalized_baseline_log_roots = _normalize_log_root_mapping(baseline_log_roots or {})
    representative = _read_json(phase1 / "representative_manifest.json")
    phase1_index = _read_optional_json(phase1 / "phase1_manifest_index.json")
    phase1_index_gate = _phase1_manifest_index_gate(phase1_index)
    current_records = _records_by_key(normalized_current_log_roots)
    entries = []
    for entry in _target_representatives(representative):
        entries.append(_validate_representative_expected_movement(entry, current_records))
    producer_gate = _validate_phase2_producer_config(normalized_current_log_roots)
    baseline_gate = _validate_overall_baseline_comparison(
        normalized_baseline_log_roots,
        normalized_current_log_roots,
        baseline_match_scope=baseline_match_scope,
    )
    summary = _movement_summary(entries, baseline_gate, producer_gate)
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": MANIFEST_KIND,
        "baseline_id": phase1_index.get("baseline_id") or MISSING_SENTINEL,
        "baseline_git_head": phase1_index.get("baseline_git_head") or MISSING_SENTINEL,
        "target_reason_id": TARGET_REASON_ID,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "phase1_manifest_index_ref": _file_ref(phase1 / "phase1_manifest_index.json"),
        "phase1_manifest_index_gate": phase1_index_gate,
        "phase1_representative_manifest_ref": {
            "path": "representative_manifest.json",
            "sha256": _sha256_file(phase1 / "representative_manifest.json"),
        },
        "current_log_roots": {
            category: str(path)
            for category, path in sorted(normalized_current_log_roots.items())
        },
        "baseline_log_roots": {
            category: str(path)
            for category, path in sorted(normalized_baseline_log_roots.items())
        },
        "movement_summary": summary,
        "phase2_producer_config_gate": producer_gate,
        "overall_baseline_comparison_gate": baseline_gate,
        "phase2_ready": (
            summary["failed"] == 0
            and producer_gate.get("passed") is True
            and baseline_gate.get("passed") is True
            and phase1_index_gate.get("passed") is True
        ),
        "entries": entries,
    }
    path = output / "equivalence_blocking_unsafety_expected_movement.json"
    _write_json(path, manifest)
    return path


def validate_phase2_equivalence_blocking_unsafety_movement(manifest: Mapping[str, Any]) -> None:
    failed = _phase2_movement_failure_kinds(manifest)
    if not failed:
        return
    raise ValueError(f"Phase 2 expected movement failed: {', '.join(map(str, failed))}")


def _phase2_movement_failure_kinds(manifest: Mapping[str, Any]) -> Sequence[str]:
    failures = []
    if not isinstance(manifest, Mapping):
        return ("manifest_not_mapping",)

    if manifest.get("manifest_version") != MANIFEST_VERSION:
        failures.append("manifest_version_mismatch")
    if manifest.get("manifest_kind") != MANIFEST_KIND:
        failures.append("manifest_kind_mismatch")
    if manifest.get("baseline_id") != BASELINE_ID:
        failures.append("baseline_id_mismatch")
    if manifest.get("baseline_git_head") != BASELINE_GIT_HEAD:
        failures.append("baseline_git_head_mismatch")
    if manifest.get("target_reason_id") != TARGET_REASON_ID:
        failures.append("target_reason_id_mismatch")

    summary = manifest.get("movement_summary")
    entries_value = manifest.get("entries")
    baseline_gate = manifest.get("overall_baseline_comparison_gate")
    producer_gate = manifest.get("phase2_producer_config_gate")
    phase1_index_gate = manifest.get("phase1_manifest_index_gate")
    entries = _phase2_entries(entries_value, failures)
    summary_is_mapping = isinstance(summary, Mapping)
    baseline_gate_is_mapping = isinstance(baseline_gate, Mapping)
    producer_gate_is_mapping = isinstance(producer_gate, Mapping)
    phase1_index_gate_is_mapping = isinstance(phase1_index_gate, Mapping)

    if not summary_is_mapping:
        failures.append("movement_summary_missing")
    if not baseline_gate_is_mapping:
        failures.append("overall_baseline_comparison_gate_missing")
    if not producer_gate_is_mapping:
        failures.append("phase2_producer_config_gate_missing")
    if not phase1_index_gate_is_mapping:
        failures.append("phase1_manifest_index_gate_missing")

    if entries is not None:
        failures.extend(_phase2_entry_failures(entries))
    if baseline_gate_is_mapping:
        failures.extend(_phase2_baseline_gate_failures(baseline_gate))
    if producer_gate_is_mapping:
        failures.extend(_phase2_producer_gate_failures(producer_gate))
    if phase1_index_gate_is_mapping:
        failures.extend(_phase1_index_gate_failures(phase1_index_gate))

    if (
        entries is not None
        and summary_is_mapping
        and baseline_gate_is_mapping
        and producer_gate_is_mapping
        and phase1_index_gate_is_mapping
    ):
        expected_summary = _movement_summary(entries, baseline_gate, producer_gate)
        failures.extend(_phase2_movement_summary_failures(summary, expected_summary))
        expected_ready = (
            expected_summary.get("failed") == 0
            and producer_gate.get("passed") is True
            and baseline_gate.get("passed") is True
            and phase1_index_gate.get("passed") is True
        )
        if manifest.get("phase2_ready") is not expected_ready:
            failures.append("phase2_ready_consistency")
        if not expected_ready:
            expected_failed_kinds = expected_summary.get("failed_kinds") or ()
            if expected_failed_kinds:
                failures.extend(str(kind) for kind in expected_failed_kinds)
            else:
                failures.append("movement_summary_failed_kinds_missing")
    elif manifest.get("phase2_ready") is True:
        failures.append("phase2_ready_without_valid_inputs")

    return tuple(sorted(set(str(failure) for failure in failures)))


def _phase1_manifest_index_gate(phase1_index: Mapping[str, Any]) -> Mapping[str, Any]:
    failures = []
    if not isinstance(phase1_index, Mapping):
        return {
            "passed": False,
            "status": "failed",
            "failed_kinds": ["phase1_manifest_index_missing"],
        }
    if phase1_index.get("baseline_id") != BASELINE_ID:
        failures.append("baseline_id_mismatch")
    if phase1_index.get("baseline_git_head") != BASELINE_GIT_HEAD:
        failures.append("baseline_git_head_mismatch")
    if failures:
        return {
            "passed": False,
            "status": "failed",
            "failed_kinds": failures,
        }
    return {"passed": True, "status": "passed", "failed_kinds": []}


def _phase2_entries(value: Any, failures: list) -> Optional[Sequence[Mapping[str, Any]]]:
    if not _is_non_string_sequence(value):
        failures.append("entries_missing")
        return None
    entries = []
    for entry in value:
        if not isinstance(entry, Mapping):
            failures.append("entry_not_mapping")
            return None
        entries.append(entry)
    return tuple(entries)


def _phase2_entry_failures(entries: Sequence[Mapping[str, Any]]) -> Sequence[str]:
    failures = []
    entry_ids = [str(entry.get("entry_id") or MISSING_SENTINEL) for entry in entries]
    duplicate_ids = sorted(
        entry_id
        for entry_id, count in Counter(entry_ids).items()
        if count > 1
    )
    missing_ids = sorted(set(TARGET_REPRESENTATIVE_IDS) - set(entry_ids))
    unexpected_ids = sorted(set(entry_ids) - set(TARGET_REPRESENTATIVE_IDS))
    if duplicate_ids:
        failures.append("representative_entry_duplicate_id")
    if missing_ids:
        failures.append("missing_target_representative")
    if unexpected_ids:
        failures.append("unexpected_target_representative")
    for entry in entries:
        if entry.get("target_reason_id") != TARGET_REASON_ID:
            failures.append("entry_target_reason_id_mismatch")
        status = entry.get("movement_status")
        failed_kinds = entry.get("failed_kinds") or ()
        if status == "expected_movement" and failed_kinds:
            failures.append("entry_failed_kinds_on_expected_movement")
        if status != "expected_movement" and not failed_kinds:
            failures.append("entry_failure_without_failed_kinds")
        if status == "expected_movement":
            accepted_records = entry.get("accepted_reason_records")
            if not _is_non_string_sequence(accepted_records) or not accepted_records:
                failures.append("entry_expected_movement_without_accepted_reason")
            else:
                for record in accepted_records:
                    if not isinstance(record, Mapping):
                        failures.append("entry_accepted_reason_not_mapping")
                        continue
                    failures.extend(_accepted_reason_record_failures(record))
    return failures


def _accepted_reason_record_failures(record: Mapping[str, Any]) -> Sequence[str]:
    failures = []
    if record.get("reason_id") != TARGET_REASON_ID:
        failures.append("entry_accepted_reason_target_reason_mismatch")
    if record.get("decision_effect") != "blocks_equivalence":
        failures.append("entry_accepted_reason_decision_effect_mismatch")
    if record.get("reason_scope") != "function":
        failures.append("entry_accepted_reason_scope_mismatch")
    if record.get("recovery_proof_kind") != EXPECTED_PROOF_KIND:
        failures.append("entry_accepted_reason_proof_kind_mismatch")
    if record.get("proof_stage") != EXPECTED_PROOF_STAGE:
        failures.append("entry_accepted_reason_proof_stage_mismatch")
    if record.get("action_status") != EXPECTED_ACTION_STATUS:
        failures.append("entry_accepted_reason_action_status_mismatch")
    if record.get("recovery_action") != EXPECTED_RECOVERY_ACTION:
        failures.append("entry_accepted_reason_recovery_action_mismatch")
    evidence_kind = record.get("evidence_kind")
    if evidence_kind not in EXPECTED_REQUIRED_EVIDENCE:
        failures.append("entry_accepted_reason_evidence_kind_mismatch")
    if tuple(record.get("required_evidence") or ()) != EXPECTED_REQUIRED_EVIDENCE:
        failures.append("entry_accepted_reason_required_evidence_mismatch")
    object_target_key = _json_tuple(record.get("object_target_key"))
    if not _object_target_key_is_specific(object_target_key):
        failures.append("entry_accepted_reason_object_target_key_not_specific")
    expected_proof_obligation_id = None
    if object_target_key is not None and evidence_kind is not None:
        expected_proof_obligation_id = build_proof_obligation_id(
            str(record.get("reason_id") or MISSING_SENTINEL),
            str(record.get("proof_stage") or MISSING_SENTINEL),
            str(record.get("recovery_proof_kind") or MISSING_SENTINEL),
            str(evidence_kind),
            object_target_key,
        )
    if _json_tuple(record.get("proof_obligation_id")) != expected_proof_obligation_id:
        failures.append("entry_accepted_reason_proof_obligation_id_mismatch")
    return failures


def _phase2_baseline_gate_failures(baseline_gate: Mapping[str, Any]) -> Sequence[str]:
    failures = []
    passed = baseline_gate.get("passed")
    status = baseline_gate.get("status")
    failed_kinds = baseline_gate.get("failed_kinds")
    if passed is not True and passed is not False:
        failures.append("overall_baseline_comparison_gate_passed_not_bool")
    if not _is_non_string_sequence(failed_kinds):
        failures.append("overall_baseline_comparison_gate_failed_kinds_invalid")
        failed_kinds = ()
    if passed is True:
        if status != "passed":
            failures.append("overall_baseline_comparison_gate_status_mismatch")
        if failed_kinds:
            failures.append("overall_baseline_comparison_gate_passed_with_failures")
    elif passed is False:
        if status != "failed":
            failures.append("overall_baseline_comparison_gate_status_mismatch")
        if not failed_kinds:
            failures.append("overall_baseline_comparison_gate_failed_without_kinds")
    return failures


def _phase2_producer_gate_failures(producer_gate: Mapping[str, Any]) -> Sequence[str]:
    failures = []
    passed = producer_gate.get("passed")
    status = producer_gate.get("status")
    failed_kinds = producer_gate.get("failed_kinds")
    if passed is not True and passed is not False:
        failures.append("phase2_producer_config_gate_passed_not_bool")
    if not _is_non_string_sequence(failed_kinds):
        failures.append("phase2_producer_config_gate_failed_kinds_invalid")
        failed_kinds = ()
    if passed is True:
        if status != "passed":
            failures.append("phase2_producer_config_gate_status_mismatch")
        if failed_kinds:
            failures.append("phase2_producer_config_gate_passed_with_failures")
    elif passed is False:
        if status != "failed":
            failures.append("phase2_producer_config_gate_status_mismatch")
        if not failed_kinds:
            failures.append("phase2_producer_config_gate_failed_without_kinds")
    return failures


def _phase1_index_gate_failures(phase1_index_gate: Mapping[str, Any]) -> Sequence[str]:
    failures = []
    passed = phase1_index_gate.get("passed")
    status = phase1_index_gate.get("status")
    failed_kinds = phase1_index_gate.get("failed_kinds")
    if passed is not True and passed is not False:
        failures.append("phase1_manifest_index_gate_passed_not_bool")
    if not _is_non_string_sequence(failed_kinds):
        failures.append("phase1_manifest_index_gate_failed_kinds_invalid")
        failed_kinds = ()
    if passed is True:
        if status != "passed":
            failures.append("phase1_manifest_index_gate_status_mismatch")
        if failed_kinds:
            failures.append("phase1_manifest_index_gate_passed_with_failures")
    elif passed is False:
        if status != "failed":
            failures.append("phase1_manifest_index_gate_status_mismatch")
        if not failed_kinds:
            failures.append("phase1_manifest_index_gate_failed_without_kinds")
    return failures


def _phase2_movement_summary_failures(
    summary: Mapping[str, Any],
    expected_summary: Mapping[str, Any],
) -> Sequence[str]:
    failures = []
    for key in (
        "target_reason_id",
        "total",
        "passed",
        "failed",
        "failed_kinds",
        "expected_representative_ids",
        "missing_representative_ids",
        "unexpected_representative_ids",
        "allowed_movement",
    ):
        if summary.get(key) != expected_summary.get(key):
            failures.append(f"movement_summary_{key}_mismatch")
    return failures


def _is_non_string_sequence(value: Any) -> bool:
    return isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray))


def _json_tuple(value: Any) -> Any:
    if isinstance(value, list):
        return tuple(_json_tuple(item) for item in value)
    if isinstance(value, tuple):
        return tuple(_json_tuple(item) for item in value)
    return value


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Validate Phase 2 equivalence_blocking_unsafety expected movement.",
    )
    parser.add_argument("--phase1-dir", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument(
        "--current-log-root",
        action="append",
        default=None,
        metavar="CATEGORY=PATH",
        help="current validation log root for a category; may be repeated",
    )
    parser.add_argument(
        "--baseline-log-root",
        action="append",
        default=None,
        metavar="CATEGORY=PATH",
        help="observed-v0 baseline log root for a category; may be repeated",
    )
    parser.add_argument(
        "--baseline-match-scope",
        choices=("all", "after-pairs"),
        default="all",
        help="Compare all baseline pairs or only identities present in current logs.",
    )
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)
    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=Path(args.phase1_dir),
        output_dir=Path(args.output_dir),
        current_log_roots=_parse_current_log_roots(args.current_log_root or ()),
        baseline_log_roots=_parse_current_log_roots(args.baseline_log_root or ()),
        baseline_match_scope=str(args.baseline_match_scope),
    )
    print(path)
    if args.require_ready:
        validate_phase2_equivalence_blocking_unsafety_movement(_read_json(path))
    return 0


def _validate_representative_expected_movement(
    entry: Mapping[str, Any],
    current_records: Mapping[Tuple[str, str, str], ValidationLogRecord],
) -> Dict[str, Any]:
    entry_id = str(entry.get("id") or MISSING_SENTINEL)
    expected = entry.get("expected_movement") or {}
    failures = []
    record = current_records.get(_entry_key(entry))
    result: Dict[str, Any] = {
        "entry_id": entry_id,
        "function": entry.get("function"),
        "category": entry.get("category"),
        "binary_pair": entry.get("binary_pair"),
        "target_reason_id": TARGET_REASON_ID,
        "expected_movement": expected,
    }
    if record is None:
        failures.append("missing_current_log")
        result["movement_status"] = "failed"
        result["failed_kinds"] = failures
        return result

    payload = record.payloads[-1] if record.payloads else {}
    result["current_result"] = record.status
    result["current_log_path"] = record.path
    if record.status == STATUS_EQ or payload.get("is_equivalent") is True:
        failures.append("pending_proof_allowed_equivalent")
    elif record.status != STATUS_UNKNOWN:
        failures.append("representative_result_not_unknown")

    matching_records = [
        reason
        for reason in coerce_unknown_reason_records(payload.get("unknown_reasons") or ())
        if reason.reason_id == TARGET_REASON_ID
    ]
    if not matching_records:
        failures.append("target_reason_missing")

    accepted_records = []
    rejected_records = []
    for reason in matching_records:
        record_failures = _reason_movement_failures(reason, expected)
        item = {
            "reason_id": reason.reason_id,
            "decision_effect": reason.decision_effect,
            "reason_scope": reason.reason_scope,
            "recovery_proof_kind": reason.recovery_proof_kind,
            "required_evidence": list(_phase2_required_evidence(reason)),
            "proof_stage": reason.proof_stage,
            "action_status": reason.action_status,
            "evidence_kind": reason.evidence_kind,
            "recovery_action": reason.recovery_action,
            "object_target_key": reason.object_target_key,
            "proof_obligation_id": reason.proof_obligation_id,
        }
        if record_failures:
            rejected_records.append({**item, "failed_kinds": record_failures})
        else:
            accepted_records.append(item)

    if matching_records and not accepted_records:
        failures.extend(_unique_failures(rejected_records))
    result["accepted_reason_records"] = accepted_records
    result["rejected_reason_records"] = rejected_records
    result["movement_status"] = "expected_movement" if not failures else "failed"
    result["failed_kinds"] = sorted(set(failures))
    return result


def _reason_movement_failures(reason: Any, expected: Mapping[str, Any]) -> Sequence[str]:
    failures = []
    expected_evidence = set(str(item) for item in (expected.get("evidence_kind") or ()))
    if reason.decision_effect != str(expected.get("decision_effect")):
        failures.append("decision_effect_mismatch")
    if reason.reason_scope != str(expected.get("reason_scope")):
        failures.append("reason_scope_mismatch")
    if reason.recovery_proof_kind != str(expected.get("recovery_proof_kind") or EXPECTED_PROOF_KIND):
        failures.append("recovery_proof_kind_mismatch")
    if reason.proof_stage != str(expected.get("proof_stage") or EXPECTED_PROOF_STAGE):
        failures.append("proof_stage_mismatch")
    if reason.action_status != str(expected.get("action_status") or EXPECTED_ACTION_STATUS):
        failures.append("action_status_mismatch")
    if reason.evidence_kind not in expected_evidence:
        failures.append("evidence_kind_mismatch")
    if reason.recovery_action != EXPECTED_RECOVERY_ACTION:
        failures.append("recovery_action_mismatch")
    if not _phase2_required_evidence_obligation_present(reason):
        failures.append("recovery_proof_obligation_required_evidence_mismatch")
    if not _object_target_key_is_specific(reason.object_target_key):
        failures.append("object_target_key_missing_or_not_specific")
    expected_proof_obligation_id = None
    if reason.object_target_key is not None and reason.evidence_kind is not None:
        expected_proof_obligation_id = build_proof_obligation_id(
            reason.reason_id,
            reason.proof_stage,
            reason.recovery_proof_kind,
            reason.evidence_kind,
            reason.object_target_key,
        )
    if reason.proof_obligation_id != expected_proof_obligation_id:
        failures.append("proof_obligation_id_mismatch")
    return failures


def _phase2_required_evidence_obligation_present(reason: Any) -> bool:
    return bool(_phase2_required_evidence(reason))


def _phase2_required_evidence(reason: Any) -> Tuple[str, ...]:
    for obligation in getattr(reason, "recovery_proof_obligations", ()) or ():
        if getattr(obligation, "proof_kind", None) != EXPECTED_PROOF_KIND:
            continue
        if getattr(obligation, "proof_stage", None) != EXPECTED_PROOF_STAGE:
            continue
        if tuple(getattr(obligation, "required_evidence", ()) or ()) == EXPECTED_REQUIRED_EVIDENCE:
            return EXPECTED_REQUIRED_EVIDENCE
    return ()


def _object_target_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or not value:
        return False
    kind = value[0]
    if kind == "unsupported_call_effect":
        return _unsupported_call_effect_key_is_specific(value)
    if kind == "deferred_call":
        return _deferred_call_key_is_specific(value)
    if kind == "call_argument_evidence":
        return _call_argument_evidence_key_is_specific(value)
    return False


def _unsupported_call_effect_key_is_specific(value: Tuple[Any, ...]) -> bool:
    if len(value) < 7:
        return False
    runtime_ref = value[3]
    callsite_storage = value[4]
    effect_ordinal = value[5]
    return all(
        (
            value[1] in {"function1", "function2"},
            _analysis_key_is_specific(value[2]),
            _runtime_ref_is_specific(runtime_ref),
            _callsite_storage_key_is_specific(callsite_storage),
            _unsupported_call_effect_runtime_and_storage_match(runtime_ref, callsite_storage),
            _effect_ordinal_key_is_specific(effect_ordinal),
            value[6] is not None,
        )
    )


def _unsupported_call_effect_runtime_and_storage_match(runtime_ref: Any, callsite_storage: Any) -> bool:
    if (
        not isinstance(runtime_ref, tuple)
        or len(runtime_ref) < 5
        or not isinstance(callsite_storage, tuple)
        or len(callsite_storage) < 4
    ):
        return False
    return all(
        (
            runtime_ref[2] == callsite_storage[1],
            runtime_ref[3] == callsite_storage[2],
            _tagged_payload(runtime_ref[4], "typed_target_expression")
            == _tagged_payload(callsite_storage[3], "target_expression"),
        )
    )


def _runtime_ref_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 5 or value[0] != "runtime_ref":
        return False
    return all(
        (
            value[1] == "unsupported_call_effect",
            _tagged_pcode_ref_is_specific(value[2]),
            _tagged_callee_identity_is_specific(value[3]),
            _tagged_typed_target_expression_is_specific(value[4]),
        )
    )


def _callsite_storage_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 4 or value[0] != "callsite_storage":
        return False
    return all(
        (
            _tagged_pcode_ref_is_specific(value[1]),
            _tagged_callee_identity_is_specific(value[2]),
            _tagged_target_expression_is_specific(value[3]),
        )
    )


def _effect_ordinal_key_is_specific(value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and value[0] == "effect_ordinal"
        and _nonnegative_int(value[1])
    )


def _tagged_pcode_ref_is_specific(value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and value[0] == "pcode_op_ref"
        and _pcode_ref_is_specific(value[1])
    )


def _tagged_callee_identity_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 2 or value[0] != "callee_identity":
        return False
    callee = value[1]
    if not isinstance(callee, tuple) or len(callee) < 2:
        return False
    if callee[0] == "unknown":
        return (
            len(callee) == 3
            and _binary_id_is_specific(callee[1])
            and _unknown_callee_target_expression_is_specific(callee[2])
        )
    return (
        len(callee) >= 3
        and callee[0] in {"function", "code_address"}
        and _binary_id_is_specific(callee[1])
        and _nonnegative_int_like(callee[2])
    )


def _unknown_callee_target_expression_is_specific(value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and value[0] == "target_expression"
        and _typed_target_expression_is_specific(value[1])
    )


def _tagged_typed_target_expression_is_specific(value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and value[0] == "typed_target_expression"
        and _typed_target_expression_is_specific(value[1])
    )


def _tagged_target_expression_is_specific(value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and value[0] == "target_expression"
        and _typed_target_expression_is_specific(value[1])
    )


def _tagged_payload(value: Any, expected_tag: str) -> Any:
    if not isinstance(value, tuple) or len(value) != 2 or value[0] != expected_tag:
        return None
    return value[1]


def _deferred_call_key_is_specific(value: Tuple[Any, ...]) -> bool:
    if len(value) < 9:
        return False
    return all(
        (
            value[1] in {"function1", "function2", None},
            _analysis_key_is_specific(value[2]),
            _pcode_ref_is_specific(value[4]),
            _typed_target_expression_is_specific(value[6]),
            _argument_keys_are_specific(value[7]),
        )
    )


def _call_argument_evidence_key_is_specific(value: Tuple[Any, ...]) -> bool:
    if len(value) < 7:
        return False
    return all(
        (
            value[1] in {"function1", "function2", None},
            _analysis_key_is_specific(value[2]),
            _argument_keys_are_specific(value[5]),
            value[6] is not None,
        )
    )


def _analysis_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or not value:
        return False
    if value[0] == "function_ref":
        return _function_ref_key_is_specific(value[1] if len(value) > 1 else None)
    if value[0] == "entry_point":
        return False
    return False


def _function_ref_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 3:
        return False
    kind, binary_id, address_offset = value[:3]
    if kind not in {"function", "code_address"}:
        return False
    return _binary_id_is_specific(binary_id) and _nonnegative_int_like(address_offset)


def _pcode_ref_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 8 or value[0] != "pcode_op":
        return False
    (
        _kind,
        binary_id,
        function_entry,
        seq_target,
        seq_time,
        seq_order,
        opcode,
        local_op_ordinal,
    ) = value
    return all(
        (
            _binary_id_is_specific(binary_id),
            _pcode_address_ref_is_specific(function_entry, "function_entry"),
            _pcode_address_ref_is_specific(seq_target, "seq_target"),
            _nonnegative_int_like(seq_time),
            _nonnegative_int_like(seq_order),
            opcode is not None,
            _nonnegative_int_like(local_op_ordinal),
        )
    )


def _binary_id_is_specific(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip()) and not value.strip().isdecimal()


def _pcode_address_ref_is_specific(value: Any, expected_kind: str) -> bool:
    if not isinstance(value, tuple) or len(value) != 3 or value[0] != expected_kind:
        return False
    return isinstance(value[1], str) and bool(value[1]) and _nonnegative_int_like(value[2])


def _nonnegative_int_like(value: Any) -> bool:
    if isinstance(value, bool) or value is None:
        return False
    try:
        return int(value) >= 0
    except (TypeError, ValueError):
        return False


def _nonnegative_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def _typed_target_expression_is_specific(value: Any) -> bool:
    return isinstance(value, tuple) and len(value) >= 2 and value[0] == "typed_target_expression"


def _argument_keys_are_specific(value: Any) -> bool:
    if not isinstance(value, tuple):
        return False
    return all(
        isinstance(item, tuple)
        and len(item) >= 3
        and item[0] == "argument"
        and isinstance(item[1], int)
        for item in value
    )


def _target_representatives(manifest: Mapping[str, Any]) -> Sequence[Mapping[str, Any]]:
    entries = manifest.get("entries") or ()
    return tuple(
        entry
        for entry in entries
        if isinstance(entry, Mapping)
        and (entry.get("expected_movement") or {}).get("reason_id") == TARGET_REASON_ID
    )


def _movement_summary(
    entries: Sequence[Mapping[str, Any]],
    baseline_gate: Mapping[str, Any],
    producer_gate: Mapping[str, Any],
) -> Dict[str, Any]:
    entry_ids = {str(entry.get("entry_id") or MISSING_SENTINEL) for entry in entries}
    missing_representatives = sorted(set(TARGET_REPRESENTATIVE_IDS) - entry_ids)
    unexpected_representatives = sorted(entry_ids - set(TARGET_REPRESENTATIVE_IDS))
    failed_kinds = sorted(
        {
            str(kind)
            for entry in entries
            for kind in (entry.get("failed_kinds") or ())
        }
        | ({"missing_target_representative"} if missing_representatives else set())
        | ({"unexpected_target_representative"} if unexpected_representatives else set())
        | set(str(kind) for kind in (baseline_gate.get("failed_kinds") or ()))
        | set(str(kind) for kind in (producer_gate.get("failed_kinds") or ()))
    )
    failed_entries = sum(1 for entry in entries if entry.get("movement_status") != "expected_movement")
    baseline_failures = 0 if baseline_gate.get("passed") is True else 1
    producer_failures = 0 if producer_gate.get("passed") is True else 1
    return {
        "target_reason_id": TARGET_REASON_ID,
        "total": len(entries),
        "passed": sum(1 for entry in entries if entry.get("movement_status") == "expected_movement"),
        "failed": (
            failed_entries
            + len(missing_representatives)
            + len(unexpected_representatives)
            + baseline_failures
            + producer_failures
        ),
        "failed_kinds": failed_kinds,
        "expected_representative_ids": list(TARGET_REPRESENTATIVE_IDS),
        "missing_representative_ids": missing_representatives,
        "unexpected_representative_ids": unexpected_representatives,
        "allowed_movement": {
            "reason_id": TARGET_REASON_ID,
            "recovery_proof_kind": EXPECTED_PROOF_KIND,
            "proof_stage": EXPECTED_PROOF_STAGE,
            "action_status": EXPECTED_ACTION_STATUS,
            "recovery_action": EXPECTED_RECOVERY_ACTION,
        },
    }


def _validate_phase2_producer_config(
    current_log_roots: Mapping[str, Path],
) -> Dict[str, Any]:
    failed_kinds = []
    roots: Dict[str, Any] = {}
    if not current_log_roots:
        failed_kinds.append("phase2_producer_current_log_root_missing")

    for category, root_value in sorted(current_log_roots.items()):
        root = Path(root_value)
        manifest_path = root / "run_manifest.txt"
        root_result: Dict[str, Any] = {
            "root": str(root),
            "run_manifest": str(manifest_path),
            "run_manifest_present": manifest_path.is_file(),
            "required_equivalence_args": list(REQUIRED_PRODUCER_EQUIV_ARGS),
            "required_run_manifest_values": dict(REQUIRED_PRODUCER_RUN_MANIFEST_VALUES),
            "function_call_extra_equiv_args": MISSING_SENTINEL,
            "missing_required_equivalence_args": list(REQUIRED_PRODUCER_EQUIV_ARGS),
            "run_manifest_values": {},
            "mismatched_required_run_manifest_values": dict(REQUIRED_PRODUCER_RUN_MANIFEST_VALUES),
        }
        if not manifest_path.is_file():
            failed_kinds.append("phase2_producer_run_manifest_missing")
            roots[str(category)] = root_result
            continue

        manifest_values = _read_run_manifest_values(manifest_path)
        extra_args = str(manifest_values.get("function_call_extra_equiv_args") or "")
        present_args = set(extra_args.split())
        missing_args = [
            arg
            for arg in REQUIRED_PRODUCER_EQUIV_ARGS
            if arg not in present_args
        ]
        root_result["function_call_extra_equiv_args"] = extra_args
        root_result["missing_required_equivalence_args"] = missing_args
        if missing_args:
            failed_kinds.append("phase2_producer_recovery_flags_missing")
        observed_required_values = {
            key: str(manifest_values.get(key) or "")
            for key in REQUIRED_PRODUCER_RUN_MANIFEST_VALUES
        }
        mismatched_values = {
            key: {
                "expected": expected,
                "actual": observed_required_values.get(key) or MISSING_SENTINEL,
            }
            for key, expected in REQUIRED_PRODUCER_RUN_MANIFEST_VALUES.items()
            if observed_required_values.get(key) != expected
        }
        root_result["run_manifest_values"] = observed_required_values
        root_result["mismatched_required_run_manifest_values"] = mismatched_values
        if mismatched_values:
            failed_kinds.append("phase2_producer_run_manifest_values_mismatch")
        roots[str(category)] = root_result

    failed_kinds = sorted(set(failed_kinds))
    return {
        "passed": not failed_kinds,
        "status": "passed" if not failed_kinds else "failed",
        "failed_kinds": failed_kinds,
        "required_equivalence_args": list(REQUIRED_PRODUCER_EQUIV_ARGS),
        "required_run_manifest_values": dict(REQUIRED_PRODUCER_RUN_MANIFEST_VALUES),
        "roots": roots,
    }


def _read_run_manifest_values(path: Path) -> Dict[str, str]:
    values: Dict[str, str] = {}
    try:
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return values
    for line in lines:
        key, separator, value = line.partition("=")
        if not separator:
            continue
        key = key.strip()
        if not key:
            continue
        values[key] = value.strip()
    return values


def _validate_overall_baseline_comparison(
    baseline_log_roots: Mapping[str, Path],
    current_log_roots: Mapping[str, Path],
    *,
    baseline_match_scope: str = "all",
) -> Dict[str, Any]:
    if not baseline_log_roots:
        return {
            "passed": False,
            "failed_kinds": ["baseline_log_root_missing"],
            "status": "failed",
        }
    before_records = aggregate_validation_logs(_log_paths_from_roots(baseline_log_roots)).records
    after_records = aggregate_validation_logs(_log_paths_from_roots(current_log_roots)).records
    if baseline_match_scope == "after-pairs":
        after_identities = set(_records_by_pair_identity(after_records))
        before_records = [
            record
            for record in before_records
            if _record_pair_result_bucket(record)[:2] in after_identities
        ]
    elif baseline_match_scope != "all":
        return {
            "passed": False,
            "failed_kinds": ["baseline_match_scope_invalid"],
            "status": "failed",
            "baseline_match_scope": baseline_match_scope,
        }
    comparison = compare_validation_baseline_records(before_records, after_records)
    failed_kinds = _baseline_comparison_failures(comparison, before_records, after_records)
    return {
        "passed": not failed_kinds,
        "status": "passed" if not failed_kinds else "failed",
        "failed_kinds": failed_kinds,
        "baseline_match_scope": baseline_match_scope,
        "before_total_results": comparison.before_total_results,
        "after_total_results": comparison.after_total_results,
        "unknown_final_results_delta": comparison.unknown_final_results_delta,
        "timeout_final_results_delta": comparison.timeout_final_results_delta,
        "allowed_tuple_movement": {
            "old": _reason_tuple_to_string(ALLOWED_OLD_REASON_TUPLE),
            "new": _reason_tuple_to_string(ALLOWED_NEW_REASON_TUPLE),
        },
        "unexpected_deltas": _unexpected_baseline_deltas(
            comparison,
            before_records,
            after_records,
        ),
    }


def _baseline_comparison_failures(
    comparison: ValidationBaselineComparison,
    before_records: Sequence[ValidationLogRecord] = (),
    after_records: Sequence[ValidationLogRecord] = (),
) -> Sequence[str]:
    failures = []
    pair_reason_deltas = _pair_reason_id_deltas(before_records, after_records)
    allowed_positive_tuple_deltas = _allowed_positive_tuple_deltas(
        _pair_unknown_tuple_deltas(before_records, after_records)
    )
    allow_reason_reclassification = _allows_reason_reclassification(
        comparison,
        pair_reason_deltas=pair_reason_deltas,
    )
    if comparison.before_total_results != comparison.after_total_results:
        failures.append("total_result_count_delta")
    if comparison.final_result_counts_delta:
        failures.append("final_result_count_delta")
    if comparison.unknown_final_results_delta != 0:
        failures.append("unknown_final_result_delta")
    if comparison.timeout_final_results_delta != 0:
        failures.append("timeout_final_result_delta")
    if _non_target_final_result_movements(before_records, after_records):
        failures.append("unexpected_non_target_final_result_movement")
    if comparison.timeout_class_multiset_delta:
        failures.append("timeout_class_delta")
    if _unexpected_pair_result_deltas(
        comparison.pair_result_multiset_delta,
        pair_reason_deltas=pair_reason_deltas,
    ):
        failures.append("pair_result_tuple_delta")
    if comparison.missing_pair_identities:
        failures.append("missing_pair_identities")
    if comparison.added_pair_identities:
        failures.append("added_pair_identities")
    if _unexpected_tuple_deltas(
        comparison.validation_unknown_unit_multiset_delta,
        "validation_unknown_unit",
        allow_reason_reclassification=allow_reason_reclassification,
        allowed_positive_deltas=allowed_positive_tuple_deltas,
    ):
        failures.append("unexpected_validation_unknown_unit_delta")
    if _unexpected_tuple_deltas(
        comparison.reason_record_multiset_delta,
        "reason_record",
        allow_reason_reclassification=allow_reason_reclassification,
        allowed_positive_deltas=allowed_positive_tuple_deltas,
    ):
        failures.append("unexpected_reason_record_delta")
    if _unexpected_tuple_deltas(
        comparison.proof_action_multiset_delta,
        "proof_action",
        allow_reason_reclassification=allow_reason_reclassification,
        allowed_positive_deltas=allowed_positive_tuple_deltas,
    ):
        failures.append("unexpected_proof_action_delta")
    return sorted(set(failures))


def _unexpected_baseline_deltas(
    comparison: ValidationBaselineComparison,
    before_records: Sequence[ValidationLogRecord] = (),
    after_records: Sequence[ValidationLogRecord] = (),
) -> Dict[str, Any]:
    pair_reason_deltas = _pair_reason_id_deltas(before_records, after_records)
    allowed_positive_tuple_deltas = _allowed_positive_tuple_deltas(
        _pair_unknown_tuple_deltas(before_records, after_records)
    )
    allow_reason_reclassification = _allows_reason_reclassification(
        comparison,
        pair_reason_deltas=pair_reason_deltas,
    )
    unexpected = {
        "validation_unknown_unit_multiset_delta": _stringify_delta_mapping(
            _unexpected_tuple_deltas(
                comparison.validation_unknown_unit_multiset_delta,
                "validation_unknown_unit",
                allow_reason_reclassification=allow_reason_reclassification,
                allowed_positive_deltas=allowed_positive_tuple_deltas,
            )
        ),
        "reason_record_multiset_delta": _stringify_delta_mapping(
            _unexpected_tuple_deltas(
                comparison.reason_record_multiset_delta,
                "reason_record",
                allow_reason_reclassification=allow_reason_reclassification,
                allowed_positive_deltas=allowed_positive_tuple_deltas,
            )
        ),
        "proof_action_multiset_delta": _stringify_delta_mapping(
            _unexpected_tuple_deltas(
                comparison.proof_action_multiset_delta,
                "proof_action",
                allow_reason_reclassification=allow_reason_reclassification,
                allowed_positive_deltas=allowed_positive_tuple_deltas,
            )
        ),
        "pair_result_multiset_delta": _stringify_delta_mapping(
            _unexpected_pair_result_deltas(
                comparison.pair_result_multiset_delta,
                pair_reason_deltas=pair_reason_deltas,
            )
        ),
        "timeout_class_multiset_delta": dict(comparison.timeout_class_multiset_delta),
        "final_result_counts_delta": dict(comparison.final_result_counts_delta),
    }
    non_target_movements = _non_target_final_result_movements(before_records, after_records)
    if non_target_movements:
        unexpected["non_target_final_result_movements"] = non_target_movements
    return unexpected


def _non_target_final_result_movements(
    before_records: Sequence[ValidationLogRecord],
    after_records: Sequence[ValidationLogRecord],
) -> Sequence[Dict[str, Any]]:
    before_by_identity = _records_by_pair_identity(before_records)
    after_by_identity = _records_by_pair_identity(after_records)
    movements: list = []
    pair_tuple_deltas = _pair_unknown_tuple_deltas(before_records, after_records)
    for identity in sorted(set(before_by_identity) & set(after_by_identity)):
        before_record = before_by_identity[identity]
        after_record = after_by_identity[identity]
        if before_record.status == after_record.status:
            continue
        before_payload = before_record.payloads[-1] if before_record.payloads else {}
        after_payload = after_record.payloads[-1] if after_record.payloads else {}
        before_reasons = _reason_id_counts(_extract_final_unknown_reasons(before_payload))
        after_reasons = _reason_id_counts(_extract_final_unknown_reasons(after_payload))
        disappeared = sorted(
            reason_id
            for reason_id, count in before_reasons.items()
            if int(after_reasons.get(reason_id, 0) or 0) < int(count or 0)
        )
        non_target_disappeared = [
            reason_id for reason_id in disappeared if reason_id != TARGET_REASON_ID
        ]
        if not non_target_disappeared:
            continue
        before_bucket = _record_pair_result_bucket(before_record)
        tuple_deltas = pair_tuple_deltas.get(before_bucket, {})
        movements.append(
            {
                "pair_identity": {
                    "function": identity[0],
                    "binary_pair": identity[1],
                },
                "before_status": before_record.status,
                "after_status": after_record.status,
                "status_movement": f"{before_record.status}->{after_record.status}",
                "disappeared_reasons": disappeared,
                "non_target_disappeared_reasons": non_target_disappeared,
                "non_target_reason_movement": True,
                "count_kind_deltas": {
                    count_kind: _stringify_delta_mapping(deltas)
                    for count_kind, deltas in tuple_deltas.items()
                    if deltas
                },
            }
        )
    return movements


def _records_by_pair_identity(
    records: Sequence[ValidationLogRecord],
) -> Dict[Tuple[str, str], ValidationLogRecord]:
    return {
        _record_pair_result_bucket(record)[:2]: record
        for record in records
    }


def _reason_id_counts(records: Sequence[Any]) -> Counter:
    counts: Counter = Counter()
    for record in records:
        counts[str(record.reason_id)] += 1
    return counts


def _unexpected_tuple_deltas(
    deltas: Mapping[Tuple[str, ...], int],
    count_kind: str,
    *,
    allow_reason_reclassification: bool = False,
    allowed_positive_deltas: Optional[Mapping[str, Mapping[Tuple[str, ...], int]]] = None,
) -> Dict[Tuple[str, ...], int]:
    unexpected = {}
    allowed_positive_deltas = allowed_positive_deltas or {}
    for key, value in deltas.items():
        if _allowed_phase2_tuple_delta(
            key,
            value,
            count_kind,
            allow_reason_reclassification=allow_reason_reclassification,
            allowed_positive_deltas=allowed_positive_deltas,
        ):
            continue
        unexpected[key] = value
    return unexpected


def _allowed_phase2_tuple_delta(
    key: Tuple[str, ...],
    value: int,
    count_kind: str,
    *,
    allow_reason_reclassification: bool = False,
    allowed_positive_deltas: Optional[Mapping[str, Mapping[Tuple[str, ...], int]]] = None,
) -> bool:
    allowed_positive_deltas = allowed_positive_deltas or {}
    if value == 0 or not isinstance(key, tuple) or len(key) != 7:
        return False
    if key[0] != count_kind:
        return False
    reason_tuple = key[1:]
    if count_kind in {"validation_unknown_unit", "reason_record"}:
        if reason_tuple == ALLOWED_NEW_REASON_TUPLE:
            return value > 0
        if reason_tuple == ALLOWED_OLD_REASON_TUPLE:
            return value < 0
        if allow_reason_reclassification:
            if reason_tuple in ALLOWED_BROAD_REMOVED_REASON_TUPLES and value < 0:
                return True
            if reason_tuple in ALLOWED_METADATA_ENRICHMENT_REASON_TUPLES and value < 0:
                return True
            if reason_tuple in ALLOWED_EXPOSED_REASON_TUPLES:
                return (
                    value > 0
                    and value
                    <= int(
                        allowed_positive_deltas.get(count_kind, {}).get(reason_tuple, 0)
                        or 0
                    )
                )
        return False
    if count_kind == "proof_action":
        if reason_tuple == ALLOWED_NEW_REASON_TUPLE and value > 0:
            return True
        if allow_reason_reclassification:
            if reason_tuple in ALLOWED_BROAD_REMOVED_PROOF_ACTION_TUPLES and value < 0:
                return True
            if reason_tuple in ALLOWED_METADATA_ENRICHMENT_PROOF_ACTION_TUPLES and value < 0:
                return True
            if reason_tuple in ALLOWED_EXPOSED_PROOF_ACTION_TUPLES:
                return (
                    value > 0
                    and value
                    <= int(
                        allowed_positive_deltas.get(count_kind, {}).get(reason_tuple, 0)
                        or 0
                    )
                )
        return False
    return False


def _allows_reason_reclassification(
    comparison: ValidationBaselineComparison,
    *,
    pair_reason_deltas: Optional[Mapping[Tuple[str, str, str, str], Mapping[str, int]]] = None,
) -> bool:
    return (
        comparison.before_total_results == comparison.after_total_results
        and not comparison.final_result_counts_delta
        and comparison.unknown_final_results_delta == 0
        and comparison.timeout_final_results_delta == 0
        and not comparison.timeout_class_multiset_delta
        and not comparison.missing_pair_identities
        and not comparison.added_pair_identities
        and not _unexpected_pair_result_deltas(
            comparison.pair_result_multiset_delta,
            pair_reason_deltas=pair_reason_deltas,
        )
        and _has_allowed_broad_reason_reduction(comparison)
    )


def _has_allowed_broad_reason_reduction(comparison: ValidationBaselineComparison) -> bool:
    for deltas in (
        comparison.validation_unknown_unit_multiset_delta,
        comparison.reason_record_multiset_delta,
    ):
        for key, value in deltas.items():
            if (
                isinstance(key, tuple)
                and len(key) == 7
                and (
                    key[1:] in ALLOWED_BROAD_REMOVED_REASON_TUPLES
                    or key[1:] in ALLOWED_METADATA_ENRICHMENT_REASON_TUPLES
                )
                and value < 0
            ):
                return True
    return False


def _unexpected_pair_result_deltas(
    deltas: Mapping[Tuple[str, ...], int],
    *,
    pair_reason_deltas: Optional[Mapping[Tuple[str, str, str, str], Mapping[str, int]]] = None,
) -> Dict[Tuple[str, ...], int]:
    unexpected: Dict[Tuple[str, ...], int] = {}
    pair_reason_deltas = pair_reason_deltas or {}
    grouped: Dict[Tuple[str, str, str, str], Dict[str, list]] = {}
    for key, value in deltas.items():
        if not isinstance(key, tuple) or len(key) != 5:
            unexpected[key] = value
            continue
        function_name, binary_pair, status, reasons, timeout_class = key
        if status != STATUS_UNKNOWN or timeout_class != MISSING_SENTINEL:
            unexpected[key] = value
            continue
        bucket = grouped.setdefault(
            (function_name, binary_pair, status, timeout_class),
            {"before": [], "after": []},
        )
        if value < 0:
            bucket["before"].extend([key] * abs(int(value)))
        elif value > 0:
            bucket["after"].extend([key] * int(value))

    for bucket in grouped.values():
        unmatched_after = list(bucket["after"])
        for before_key in bucket["before"]:
            match_index = next(
                (
                    index
                    for index, after_key in enumerate(unmatched_after)
                    if _allowed_pair_reason_reclassification(
                        before_key,
                        after_key,
                        pair_reason_deltas.get(before_key[:3] + (before_key[4],), {}),
                    )
                ),
                None,
            )
            if match_index is None:
                unexpected[before_key] = unexpected.get(before_key, 0) - 1
                continue
            unmatched_after.pop(match_index)
        for after_key in unmatched_after:
            unexpected[after_key] = unexpected.get(after_key, 0) + 1
    return {key: value for key, value in unexpected.items() if value}


def _allowed_pair_reason_reclassification(
    before_key: Tuple[str, ...],
    after_key: Tuple[str, ...],
    pair_reason_delta: Optional[Mapping[str, int]] = None,
) -> bool:
    pair_reason_delta = pair_reason_delta or {}
    if before_key[:3] != after_key[:3] or before_key[4] != after_key[4]:
        return False
    before_reasons = _pair_reason_set(before_key[3])
    after_reasons = _pair_reason_set(after_key[3])
    removed = before_reasons - after_reasons
    added = after_reasons - before_reasons
    if not removed <= ALLOWED_PAIR_REMOVED_REASONS:
        return False
    if not added <= ALLOWED_PAIR_EXPOSED_REASONS:
        return False
    if not removed and added and before_reasons & ALLOWED_PAIR_REMOVED_REASONS:
        if added == {TARGET_REASON_ID} and int(pair_reason_delta.get(TARGET_REASON_ID, 0) or 0) > 0:
            return True
        return _has_pair_broad_reason_reduction(pair_reason_delta, before_reasons)
    if "unresolved_expression" in removed and added:
        return True
    if "unresolved_expression" in removed:
        return bool(after_reasons)
    if "return_width_bridge_missing" in removed:
        return bool(after_reasons)
    if "sat_unsafety" in removed:
        return bool(after_reasons & {TARGET_REASON_ID, "return_coverage_gap"})
    if removed == {"solver_proven_rewrite_proof_failed"}:
        return added == {"sat_unsafety"}
    if removed == {"return_coverage_inconclusive"}:
        if added == {"return_coverage_gap"}:
            return True
        return (
            not added
            and "return_coverage_gap" in after_reasons
            and int(pair_reason_delta.get("return_coverage_inconclusive", 0) or 0) < 0
        )
    return False


def _has_pair_broad_reason_reduction(
    pair_reason_delta: Mapping[str, int],
    before_reasons: set,
) -> bool:
    return any(
        reason_id in before_reasons
        and int(pair_reason_delta.get(reason_id, 0) or 0) < 0
        for reason_id in ALLOWED_PAIR_REMOVED_REASONS
    )


def _pair_reason_set(reasons: Any) -> set:
    if reasons is None:
        return set()
    if str(reasons) in {"", MISSING_SENTINEL}:
        return set()
    return {
        item
        for item in str(reasons).split(",")
        if item and item != MISSING_SENTINEL
    }


def _allowed_positive_tuple_deltas(
    pair_tuple_deltas: Mapping[
        Tuple[str, str, str, str],
        Mapping[str, Mapping[Tuple[str, ...], int]],
    ],
) -> Dict[str, Counter]:
    result: Dict[str, Counter] = {
        UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value: Counter(),
        UnknownCountKind.REASON_RECORD.value: Counter(),
        UnknownCountKind.PROOF_ACTION.value: Counter(),
    }
    for count_deltas in pair_tuple_deltas.values():
        reason_record_deltas = count_deltas.get(UnknownCountKind.REASON_RECORD.value, {})
        validation_unit_deltas = count_deltas.get(
            UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value,
            {},
        )
        proof_action_deltas = count_deltas.get(UnknownCountKind.PROOF_ACTION.value, {})
        if _has_allowed_broad_tuple_reduction(reason_record_deltas):
            _add_positive_tuple_allowance(
                result[UnknownCountKind.REASON_RECORD.value],
                reason_record_deltas,
                ALLOWED_EXPOSED_REASON_TUPLES,
            )
            _add_positive_tuple_allowance(
                result[UnknownCountKind.PROOF_ACTION.value],
                proof_action_deltas,
                ALLOWED_EXPOSED_PROOF_ACTION_TUPLES,
            )
        elif _has_solver_proven_rewrite_reduction(reason_record_deltas):
            _add_positive_tuple_allowance(
                result[UnknownCountKind.REASON_RECORD.value],
                reason_record_deltas,
                SAT_UNSAFETY_REASON_TUPLES,
            )
            _add_positive_tuple_allowance(
                result[UnknownCountKind.PROOF_ACTION.value],
                proof_action_deltas,
                SAT_UNSAFETY_PROOF_ACTION_TUPLES,
            )
        elif _has_target_reason_exposure(reason_record_deltas):
            _add_positive_tuple_allowance(
                result[UnknownCountKind.REASON_RECORD.value],
                reason_record_deltas,
                ALLOWED_EXPOSED_REASON_TUPLES,
            )
            _add_positive_tuple_allowance(
                result[UnknownCountKind.PROOF_ACTION.value],
                proof_action_deltas,
                ALLOWED_EXPOSED_PROOF_ACTION_TUPLES,
            )
        if _has_allowed_broad_tuple_reduction(validation_unit_deltas):
            _add_positive_tuple_allowance(
                result[UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value],
                validation_unit_deltas,
                ALLOWED_EXPOSED_REASON_TUPLES,
            )
        elif _has_solver_proven_rewrite_reduction(validation_unit_deltas):
            _add_positive_tuple_allowance(
                result[UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value],
                validation_unit_deltas,
                SAT_UNSAFETY_REASON_TUPLES,
            )
        elif _has_target_reason_exposure(validation_unit_deltas):
            _add_positive_tuple_allowance(
                result[UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value],
                validation_unit_deltas,
                ALLOWED_EXPOSED_REASON_TUPLES,
            )
    return result


def _has_allowed_broad_tuple_reduction(
    deltas: Mapping[Tuple[str, ...], int],
) -> bool:
    return any(
        (
            reason_tuple in ALLOWED_BROAD_REMOVED_REASON_TUPLES
            or reason_tuple in ALLOWED_METADATA_ENRICHMENT_REASON_TUPLES
        )
        and value < 0
        for reason_tuple, value in deltas.items()
    )


def _has_solver_proven_rewrite_reduction(
    deltas: Mapping[Tuple[str, ...], int],
) -> bool:
    return int(deltas.get(SOLVER_PROVEN_REWRITE_PROOF_FAILED_REASON_TUPLE, 0) or 0) < 0


def _has_target_reason_exposure(
    deltas: Mapping[Tuple[str, ...], int],
) -> bool:
    return int(deltas.get(ALLOWED_NEW_REASON_TUPLE, 0) or 0) > 0


def _add_positive_tuple_allowance(
    result: Counter,
    deltas: Mapping[Tuple[str, ...], int],
    allowed_tuples: Iterable[Tuple[str, ...]],
) -> None:
    allowed = set(allowed_tuples)
    for reason_tuple, value in deltas.items():
        if reason_tuple in allowed and value > 0:
            result[reason_tuple] += int(value)


def _pair_unknown_tuple_deltas(
    before_records: Sequence[ValidationLogRecord],
    after_records: Sequence[ValidationLogRecord],
) -> Dict[Tuple[str, str, str, str], Dict[str, Dict[Tuple[str, ...], int]]]:
    before_counts = _pair_unknown_tuple_counts(before_records)
    after_counts = _pair_unknown_tuple_counts(after_records)
    result: Dict[Tuple[str, str, str, str], Dict[str, Dict[Tuple[str, ...], int]]] = {}
    for pair_key in sorted(set(before_counts) | set(after_counts)):
        pair_result: Dict[str, Dict[Tuple[str, ...], int]] = {}
        count_kinds = set(before_counts.get(pair_key, {})) | set(after_counts.get(pair_key, {}))
        for count_kind in sorted(count_kinds):
            before_kind_counts = before_counts.get(pair_key, {}).get(count_kind, {})
            after_kind_counts = after_counts.get(pair_key, {}).get(count_kind, {})
            reason_tuples = set(before_kind_counts) | set(after_kind_counts)
            deltas = {
                reason_tuple: int(after_kind_counts.get(reason_tuple, 0) or 0)
                - int(before_kind_counts.get(reason_tuple, 0) or 0)
                for reason_tuple in reason_tuples
            }
            pair_result[count_kind] = {
                reason_tuple: value
                for reason_tuple, value in deltas.items()
                if value
            }
        result[pair_key] = pair_result
    return result


def _pair_unknown_tuple_counts(
    records: Sequence[ValidationLogRecord],
) -> Dict[Tuple[str, str, str, str], Dict[str, Counter]]:
    result: Dict[Tuple[str, str, str, str], Dict[str, Counter]] = {}
    for record in records:
        payload = record.payloads[-1] if record.payloads else {}
        pair_key = _record_pair_result_bucket(record)
        if pair_key[2] != STATUS_UNKNOWN or pair_key[3] != MISSING_SENTINEL:
            continue
        extracted_records = _extract_final_unknown_reasons(payload)
        primary_records = _select_primary_records_by_aggregation_unit(extracted_records)
        pair_counts = result.setdefault(pair_key, {})
        for reason in extracted_records:
            _increment_pair_tuple_count(
                pair_counts,
                _global_reason_tuple_from_record(reason, UnknownCountKind.REASON_RECORD.value),
            )
            for action in build_unknown_recovery_actions((reason,)):
                _increment_pair_tuple_count(
                    pair_counts,
                    _global_reason_tuple_from_action(action),
                )
        for reason in primary_records:
            _increment_pair_tuple_count(
                pair_counts,
                _global_reason_tuple_from_record(
                    reason,
                    UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value,
                ),
            )
    return result


def _increment_pair_tuple_count(
    counts: Dict[str, Counter],
    key: Tuple[str, ...],
) -> None:
    if len(key) != 7:
        return
    count_kind = str(key[0])
    counts.setdefault(count_kind, Counter())[key[1:]] += 1


def _pair_reason_id_deltas(
    before_records: Sequence[ValidationLogRecord],
    after_records: Sequence[ValidationLogRecord],
) -> Dict[Tuple[str, str, str, str], Dict[str, int]]:
    before_counts = _pair_reason_id_counts(before_records)
    after_counts = _pair_reason_id_counts(after_records)
    result: Dict[Tuple[str, str, str, str], Dict[str, int]] = {}
    for pair_key in sorted(set(before_counts) | set(after_counts)):
        reason_ids = set(before_counts.get(pair_key, ())) | set(after_counts.get(pair_key, ()))
        deltas = {
            reason_id: int(after_counts.get(pair_key, {}).get(reason_id, 0) or 0)
            - int(before_counts.get(pair_key, {}).get(reason_id, 0) or 0)
            for reason_id in reason_ids
        }
        result[pair_key] = {
            reason_id: value
            for reason_id, value in deltas.items()
            if value
        }
    return result


def _pair_reason_id_counts(
    records: Sequence[ValidationLogRecord],
) -> Dict[Tuple[str, str, str, str], Counter]:
    result: Dict[Tuple[str, str, str, str], Counter] = {}
    for record in records:
        payload = record.payloads[-1] if record.payloads else {}
        pair_key = _record_pair_result_bucket(record)
        if pair_key[2] != STATUS_UNKNOWN or pair_key[3] != MISSING_SENTINEL:
            continue
        counts = result.setdefault(pair_key, Counter())
        for reason in _extract_final_unknown_reasons(payload):
            counts[str(reason.reason_id)] += 1
    return result


def _record_pair_result_bucket(record: ValidationLogRecord) -> Tuple[str, str, str, str]:
    payload = record.payloads[-1] if record.payloads else {}
    function_name = str(
        payload.get("function1_name")
        or payload.get("function_name")
        or record.function_name
    )
    left_binary, right_binary = _payload_or_record_binary_ids(payload, record)
    binary_pair = " ↔ ".join(sorted((left_binary, right_binary)))
    status = record.status if record.status in STATUS_ORDER else STATUS_UNKNOWN
    return (
        function_name,
        binary_pair,
        status,
        _record_timeout_class(payload, status),
    )


def _payload_or_record_binary_ids(
    payload: Mapping[str, Any],
    record: ValidationLogRecord,
) -> Tuple[str, str]:
    left = payload.get("binary1_name")
    right = payload.get("binary2_name")
    if left is not None and right is not None:
        return _path_name(left), _path_name(right)
    if "↔" in record.pair_label:
        raw_left, raw_right = record.pair_label.split("↔", 1)
        return raw_left.strip(), raw_right.strip()
    return record.pair_label, record.pair_label


def _path_name(value: Any) -> str:
    text = str(value)
    return Path(text).name if text else MISSING_SENTINEL


def _record_timeout_class(payload: Mapping[str, Any], status: str) -> str:
    if status != STATUS_TIMEOUT:
        return MISSING_SENTINEL
    for key in ("timeout_class", "timeout_reason"):
        value = payload.get(key)
        if value:
            return str(value)
    solver_results = payload.get("solver_results")
    if isinstance(solver_results, Mapping):
        all_results = solver_results.get("all_results") or solver_results.get("results") or ()
        for solver_result in all_results:
            if isinstance(solver_result, Mapping) and str(solver_result.get("status")) == "TIMEOUT":
                return str(solver_result.get("reason") or "solver_timeout")
    return "timeout"


def _log_paths_from_roots(log_roots: Mapping[str, Path]) -> Sequence[Path]:
    paths = []
    for _category, root in sorted(log_roots.items()):
        paths.extend(_log_paths(Path(root)))
    return tuple(paths)


def _stringify_delta_mapping(deltas: Mapping[Any, int]) -> Dict[str, int]:
    return {
        _reason_tuple_to_string(key): value
        for key, value in sorted(deltas.items(), key=lambda item: str(item[0]))
    }


def _reason_tuple_to_string(value: Any) -> str:
    if isinstance(value, tuple):
        return " | ".join(str(item) for item in value)
    return str(value)


def _unique_failures(rejected_records: Sequence[Mapping[str, Any]]) -> Sequence[str]:
    return sorted(
        {
            str(kind)
            for item in rejected_records
            for kind in (item.get("failed_kinds") or ())
        }
    )


def _records_by_key(
    current_log_roots: Mapping[str, Path],
) -> Dict[Tuple[str, str, str], ValidationLogRecord]:
    result = {}
    for category, root in sorted(current_log_roots.items()):
        for record in aggregate_validation_logs(_log_paths(Path(root))).records:
            result[(str(category), record.function_name, _canonical_binary_pair(_record_pair_label(record)))] = record
    return result


def _record_pair_label(record: ValidationLogRecord) -> str:
    if "↔" not in record.pair_label:
        return record.pair_label
    left, right = record.pair_label.split("↔", 1)
    return f"{left.strip()}_{right.strip()}"


def _entry_key(entry: Mapping[str, Any]) -> Tuple[str, str, str]:
    return (
        str(entry.get("category") or MISSING_SENTINEL),
        str(entry.get("function") or MISSING_SENTINEL),
        _canonical_binary_pair(str(entry.get("binary_pair") or MISSING_SENTINEL)),
    )


def _parse_current_log_roots(values: Iterable[str]) -> Dict[str, Path]:
    result = {}
    for value in values:
        if "=" not in value:
            raise ValueError(f"--current-log-root must be CATEGORY=PATH, got {value!r}")
        category, raw_path = value.split("=", 1)
        category = category.strip()
        if category not in KNOWN_LOG_ROOT_CATEGORIES:
            expected = ", ".join(sorted(KNOWN_LOG_ROOT_CATEGORIES))
            raise ValueError(
                f"unknown log root category: {category}; expected one of {expected}"
            )
        result[category] = Path(raw_path)
    return result


def _normalize_log_root_mapping(values: Mapping[str, Path]) -> Dict[str, Path]:
    result: Dict[str, Path] = {}
    for category, path in values.items():
        normalized = str(category).strip()
        if normalized not in KNOWN_LOG_ROOT_CATEGORIES:
            expected = ", ".join(sorted(KNOWN_LOG_ROOT_CATEGORIES))
            raise ValueError(
                f"unknown log root category: {normalized}; expected one of {expected}"
            )
        result[normalized] = Path(path)
    return result


def _log_paths(root: Path) -> Sequence[Path]:
    if not root.is_dir():
        return ()
    return tuple(sorted(root.glob("*/*.log"), key=lambda path: str(path)))


def _canonical_binary_pair(pair: str) -> str:
    if "_" not in pair:
        return pair
    left, right = pair.split("_", 1)
    return "_".join(sorted((left, right), key=_binary_sort_key))


def _binary_sort_key(binary_id: str) -> Tuple[str, int, str]:
    text = str(binary_id)
    if len(text) > 1 and text[0].isalpha() and text[1:].isdigit():
        return text[0], int(text[1:]), text
    return text, -1, text


def _read_json(path: Path) -> Dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def _read_optional_json(path: Path) -> Dict[str, Any]:
    if not path.is_file():
        return {}
    return _read_json(path)


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _file_ref(path: Path) -> Dict[str, str]:
    if not path.is_file():
        return {
            "path": path.name,
            "sha256": MISSING_SENTINEL,
        }
    return {
        "path": path.name,
        "sha256": _sha256_file(path),
    }


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


if __name__ == "__main__":
    raise SystemExit(main())
