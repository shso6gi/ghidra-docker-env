# -*- coding: utf-8 -*-
"""Freeze Phase 3 lane 1 representatives for return coverage work."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Sequence, Tuple

from .result_summary import (
    STATUS_EQ,
    STATUS_TIMEOUT,
    STATUS_UNKNOWN,
    aggregate_validation_logs,
    classify_result_payload,
    read_validation_log_record,
)
from .unknown_reason_summary import (
    _FINAL_UNKNOWN_TRANSITIONS,
    _extract_final_unknown_reasons,
    _global_reason_tuple_from_action,
    _global_reason_tuple_from_record,
    extract_result_payloads_from_text,
)
from ..equivalence.unknown_reason import (
    UNKNOWN_TUPLE_MISSING,
    UnknownCountKind,
    build_proof_obligation_id,
    coerce_unknown_recovery_actions,
    build_unknown_recovery_actions,
)


MANIFEST_VERSION = 1
TARGET_REASON_IDS = ("return_coverage_gap",)
OBSERVED_RETURN_REASON_IDS = ("return_coverage_gap", "return_coverage_inconclusive")
RETIRED_REASON_IDS = ("return_coverage_inconclusive",)
MISSING_SENTINEL = UNKNOWN_TUPLE_MISSING
RETURN_COVERAGE_COMPLETION_PROOF_STAGES = (
    "return_partition_extraction",
    "return_guard_coverage",
)
RETURN_COVERAGE_COMPLETION_EVIDENCE_KIND_BY_STAGE = {
    "return_partition_extraction": "missing_return_guard",
    "return_guard_coverage": "case_guard_disjunction",
}
RETURN_COVERAGE_COMPLETION_REQUIRED_EVIDENCE_BY_STAGE = {
    "return_partition_extraction": (
        "missing_return_guard",
        "tail_or_default_return_value",
        "return_storage",
    ),
    "return_guard_coverage": (
        "case_guard_disjunction",
        "path_feasibility",
        "function_precondition",
    ),
}
RETURN_COVERAGE_GAP_REASON_TUPLE = (
    UnknownCountKind.REASON_RECORD.value,
    "return_coverage_gap",
    "blocks_equivalence",
    "function",
    "return_coverage_completion",
    MISSING_SENTINEL,
    "pending_proof",
)
RETURN_COVERAGE_GAP_PARTITION_ACTION_TUPLE = (
    UnknownCountKind.PROOF_ACTION.value,
    "return_coverage_gap",
    "blocks_equivalence",
    "function",
    "return_coverage_completion",
    "return_partition_extraction",
    "pending_proof",
)
RETURN_COVERAGE_GAP_GUARD_ACTION_TUPLE = (
    UnknownCountKind.PROOF_ACTION.value,
    "return_coverage_gap",
    "blocks_equivalence",
    "function",
    "return_coverage_completion",
    "return_guard_coverage",
    "pending_proof",
)
RETIRED_RETURN_COVERAGE_INCONCLUSIVE_REASON_TUPLE = (
    UnknownCountKind.REASON_RECORD.value,
    "return_coverage_inconclusive",
    "blocks_decision",
    "function",
    "return_coverage_completion",
    "return_coverage_smt_disambiguation",
    MISSING_SENTINEL,
)
RETIRED_RETURN_COVERAGE_INCONCLUSIVE_ACTION_TUPLE = (
    UnknownCountKind.PROOF_ACTION.value,
    "return_coverage_inconclusive",
    "blocks_decision",
    "function",
    "return_coverage_completion",
    "return_coverage_smt_disambiguation",
    "planned",
)
FUNCTION_CALL_BINARY_NAMES = {
    "B8": "function_call_test-arm64-gcc-O3",
    "B11": "function_call_test-mips64-clang-O2",
    "B12": "function_call_test-mips64-clang-O3",
    "B15": "function_call_test-mips64-gcc-O2",
    "B16": "function_call_test-mips64-gcc-O3",
}


def _expected_reason_record(
    movement_id: str,
    tuple_key: Tuple[str, ...],
    *,
    aggregation_unit: str = "function",
    stage: str = "S_PAIRWISE",
    pair_or_case: str = MISSING_SENTINEL,
    expected_evidence_refs: Optional[Sequence[str]] = None,
) -> Dict[str, Any]:
    movement = {
        "id": movement_id,
        "count_kind": UnknownCountKind.REASON_RECORD.value,
        "tuple": list(tuple_key),
        "aggregation_unit": aggregation_unit,
        "stage": stage,
        "pair_or_case": pair_or_case,
    }
    if expected_evidence_refs is not None:
        movement["expected_evidence_refs"] = list(expected_evidence_refs)
    movement["required_object_target_kind"] = "return_coverage"
    return movement


def _expected_proof_action(
    movement_id: str,
    tuple_key: Tuple[str, ...],
    *,
    required_evidence: Sequence[str],
    aggregation_unit: str = "function",
    stage: str = "S_PAIRWISE",
    pair_or_case: str = MISSING_SENTINEL,
    expected_evidence_refs: Optional[Sequence[str]] = None,
) -> Dict[str, Any]:
    movement = {
        "id": movement_id,
        "count_kind": UnknownCountKind.PROOF_ACTION.value,
        "tuple": list(tuple_key),
        "aggregation_unit": aggregation_unit,
        "stage": stage,
        "pair_or_case": pair_or_case,
        "required_evidence": list(required_evidence),
    }
    if expected_evidence_refs is not None:
        movement["expected_evidence_refs"] = list(expected_evidence_refs)
    movement["required_object_target_kind"] = "return_coverage"
    movement["require_proof_obligation_id"] = True
    return movement


def _gap_both_sides_movements() -> Sequence[Mapping[str, Any]]:
    return [
        _expected_reason_record(
            "gap-reason-record-function1",
            RETURN_COVERAGE_GAP_REASON_TUPLE,
            expected_evidence_refs=["function1:return_coverage_gap"],
        ),
        _expected_reason_record(
            "gap-reason-record-function2",
            RETURN_COVERAGE_GAP_REASON_TUPLE,
            expected_evidence_refs=["function2:return_coverage_gap"],
        ),
        _expected_proof_action(
            "gap-return-partition-extraction-function1",
            RETURN_COVERAGE_GAP_PARTITION_ACTION_TUPLE,
            required_evidence=[
                "missing_return_guard",
                "tail_or_default_return_value",
                "return_storage",
            ],
            expected_evidence_refs=["function1:return_coverage_gap"],
        ),
        _expected_proof_action(
            "gap-return-partition-extraction-function2",
            RETURN_COVERAGE_GAP_PARTITION_ACTION_TUPLE,
            required_evidence=[
                "missing_return_guard",
                "tail_or_default_return_value",
                "return_storage",
            ],
            expected_evidence_refs=["function2:return_coverage_gap"],
        ),
        _expected_proof_action(
            "gap-return-guard-coverage-function1",
            RETURN_COVERAGE_GAP_GUARD_ACTION_TUPLE,
            required_evidence=[
                "case_guard_disjunction",
                "path_feasibility",
                "function_precondition",
            ],
            expected_evidence_refs=["function1:return_coverage_gap"],
        ),
        _expected_proof_action(
            "gap-return-guard-coverage-function2",
            RETURN_COVERAGE_GAP_GUARD_ACTION_TUPLE,
            required_evidence=[
                "case_guard_disjunction",
                "path_feasibility",
                "function_precondition",
            ],
            expected_evidence_refs=["function2:return_coverage_gap"],
        ),
    ]


DEFAULT_REPRESENTATIVES: Tuple[Mapping[str, Any], ...] = (
    {
        "id": "representative-return-coverage-gap-recursive-simple",
        "category": "function_call",
        "function": "fc_recursive_sum",
        "binary_pair": "B11_B15",
        "expected_observed_binary1_name": FUNCTION_CALL_BINARY_NAMES["B11"],
        "expected_observed_binary2_name": FUNCTION_CALL_BINARY_NAMES["B15"],
        "required_reason_ids": ["return_coverage_gap"],
        "role": "pure return coverage gap with one blocked side",
        "expected_movements": [
            _expected_reason_record(
                "gap-reason-record",
                RETURN_COVERAGE_GAP_REASON_TUPLE,
                expected_evidence_refs=["function2:return_coverage_gap"],
            ),
            _expected_proof_action(
                "gap-return-partition-extraction",
                RETURN_COVERAGE_GAP_PARTITION_ACTION_TUPLE,
                required_evidence=[
                    "missing_return_guard",
                    "tail_or_default_return_value",
                    "return_storage",
                ],
                expected_evidence_refs=["function2:return_coverage_gap"],
            ),
            _expected_proof_action(
                "gap-return-guard-coverage",
                RETURN_COVERAGE_GAP_GUARD_ACTION_TUPLE,
                required_evidence=[
                    "case_guard_disjunction",
                    "path_feasibility",
                    "function_precondition",
                ],
                expected_evidence_refs=["function2:return_coverage_gap"],
            ),
        ],
    },
    {
        "id": "representative-return-coverage-gap-even-both-sides",
        "category": "function_call",
        "function": "fc_is_even",
        "binary_pair": "B11_B12",
        "expected_observed_binary1_name": FUNCTION_CALL_BINARY_NAMES["B11"],
        "expected_observed_binary2_name": FUNCTION_CALL_BINARY_NAMES["B12"],
        "required_reason_ids": ["return_coverage_gap"],
        "role": "return coverage gap present on both sides",
        "expected_movements": _gap_both_sides_movements(),
    },
)


DEFAULT_RETIRED_TRANSITIONS: Tuple[Mapping[str, Any], ...] = (
    {
        "id": "retired-inconclusive-reclassified-to-gap-odd-B8-B15",
        "category": "function_call",
        "function": "fc_is_odd",
        "binary_pair": "B8_B15",
        "retired_reason_id": "return_coverage_inconclusive",
        "reclassified_to_reason_id": "return_coverage_gap",
        "transition_status": "retired_inconclusive_reclassified_to_gap",
        "baseline_expected_reason_tuple": list(RETIRED_RETURN_COVERAGE_INCONCLUSIVE_REASON_TUPLE),
        "baseline_expected_proof_action_tuple": list(RETIRED_RETURN_COVERAGE_INCONCLUSIVE_ACTION_TUPLE),
        "expected_baseline_observed_left_binary_id": "B15",
        "expected_baseline_observed_right_binary_id": "B8",
        "expected_baseline_binary1_name": FUNCTION_CALL_BINARY_NAMES["B15"],
        "expected_baseline_binary2_name": FUNCTION_CALL_BINARY_NAMES["B8"],
        "expected_current_observed_left_binary_id": "B8",
        "expected_current_observed_right_binary_id": "B15",
        "expected_current_binary1_name": FUNCTION_CALL_BINARY_NAMES["B8"],
        "expected_current_binary2_name": FUNCTION_CALL_BINARY_NAMES["B15"],
        "current_expected_movements": _gap_both_sides_movements(),
    },
    {
        "id": "retired-inconclusive-reclassified-to-gap-odd-B11-B16",
        "category": "function_call",
        "function": "fc_is_odd",
        "binary_pair": "B11_B16",
        "retired_reason_id": "return_coverage_inconclusive",
        "reclassified_to_reason_id": "return_coverage_gap",
        "transition_status": "retired_inconclusive_reclassified_to_gap",
        "baseline_expected_reason_tuple": list(RETIRED_RETURN_COVERAGE_INCONCLUSIVE_REASON_TUPLE),
        "baseline_expected_proof_action_tuple": list(RETIRED_RETURN_COVERAGE_INCONCLUSIVE_ACTION_TUPLE),
        "expected_baseline_observed_left_binary_id": "B11",
        "expected_baseline_observed_right_binary_id": "B16",
        "expected_baseline_binary1_name": FUNCTION_CALL_BINARY_NAMES["B11"],
        "expected_baseline_binary2_name": FUNCTION_CALL_BINARY_NAMES["B16"],
        "expected_current_observed_left_binary_id": "B11",
        "expected_current_observed_right_binary_id": "B16",
        "expected_current_binary1_name": FUNCTION_CALL_BINARY_NAMES["B11"],
        "expected_current_binary2_name": FUNCTION_CALL_BINARY_NAMES["B16"],
        "current_expected_movements": _gap_both_sides_movements(),
    },
    {
        "id": "retired-inconclusive-reclassified-to-gap-odd-B12-B16",
        "category": "function_call",
        "function": "fc_is_odd",
        "binary_pair": "B12_B16",
        "retired_reason_id": "return_coverage_inconclusive",
        "reclassified_to_reason_id": "return_coverage_gap",
        "transition_status": "retired_inconclusive_reclassified_to_gap",
        "baseline_expected_reason_tuple": list(RETIRED_RETURN_COVERAGE_INCONCLUSIVE_REASON_TUPLE),
        "baseline_expected_proof_action_tuple": list(RETIRED_RETURN_COVERAGE_INCONCLUSIVE_ACTION_TUPLE),
        "expected_baseline_observed_left_binary_id": "B12",
        "expected_baseline_observed_right_binary_id": "B16",
        "expected_baseline_binary1_name": FUNCTION_CALL_BINARY_NAMES["B12"],
        "expected_baseline_binary2_name": FUNCTION_CALL_BINARY_NAMES["B16"],
        "expected_current_observed_left_binary_id": "B12",
        "expected_current_observed_right_binary_id": "B16",
        "expected_current_binary1_name": FUNCTION_CALL_BINARY_NAMES["B12"],
        "expected_current_binary2_name": FUNCTION_CALL_BINARY_NAMES["B16"],
        "current_expected_movements": _gap_both_sides_movements(),
    },
)

_PAIR_RE = re.compile(r";\s*Pairwise Query(?: \([^)]+\))?: Pair \((\d+),(\d+)\)")
_CASE_RE = re.compile(r";\s*(Case[12])\[(\d+)\]:\s*(.*)")


def build_phase3_return_coverage_lane1_manifest(
    *,
    baseline_raw_dir: Path,
    output_dir: Path,
    current_log_roots: Mapping[str, Path],
    baseline_log_roots: Mapping[str, Path],
    phase1_dir: Optional[Path] = None,
    phase1_current_log_roots: Optional[Mapping[str, Path]] = None,
    representatives: Sequence[Mapping[str, Any]] = DEFAULT_REPRESENTATIVES,
    retired_transitions: Sequence[Mapping[str, Any]] = DEFAULT_RETIRED_TRANSITIONS,
) -> Path:
    raw_dir = Path(baseline_raw_dir)
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)
    baseline_manifest = _read_json(raw_dir / "artifact_manifest.json")
    current_records = _records_by_key(current_log_roots)
    baseline_records = _records_by_key(baseline_log_roots)
    entries = [
        _materialize_entry(raw_entry, current_records, baseline_records)
        for raw_entry in representatives
    ]
    transition_entries = [
        _materialize_retired_transition(raw_entry, current_records, baseline_records)
        for raw_entry in retired_transitions
    ]
    retired_reason_inventory = _retired_reason_inventory(
        current_records=current_records,
        baseline_records=baseline_records,
        transition_entries=transition_entries,
    )
    readiness = _readiness(entries, transition_entries, retired_reason_inventory)
    implementation_manifest = _implementation_manifest(entries, transition_entries)
    pre_fix_gate = _pre_fix_regression_gate(
        entries=entries,
        transition_entries=transition_entries,
        retired_reason_inventory=retired_reason_inventory,
        phase1_dir=Path(phase1_dir) if phase1_dir is not None else raw_dir.parent / "phase1",
        current_log_roots=current_log_roots,
        phase1_current_log_roots=phase1_current_log_roots,
        baseline_log_roots=baseline_log_roots,
    )
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase3_return_coverage_lane1_representatives",
        "artifact_role": "derived_audit_reclassification_gate",
        "baseline_id": baseline_manifest.get("baseline_id") or MISSING_SENTINEL,
        "baseline_git_head": baseline_manifest.get("git_head") or MISSING_SENTINEL,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "target_reason_ids": list(TARGET_REASON_IDS),
        "retired_reason_ids": list(RETIRED_REASON_IDS),
        "baseline_raw_artifact_ref": _file_ref(raw_dir / "artifact_manifest.json"),
        "superseded_phase3_manifest_ref": _file_ref(
            raw_dir.parent
            / "phase3"
            / "return_coverage_lane1"
            / "return_coverage_lane1_representatives.json"
        ),
        "reclassification_rationale": {
            "summary": (
                "Current return_coverage_inconclusive representatives are retired because "
                "the existing logs reclassify them to return_coverage_gap with pending proof "
                "and object-derived evidence while preserving UNKNOWN final results."
            ),
            "retired_status": "retired_inconclusive_reclassified_to_gap",
            "active_lane_target": "return_coverage_gap",
            "requires_final_result_unchanged_unknown": True,
            "requires_no_false_eq": True,
            "requires_no_timeout": True,
        },
        "current_log_roots": {
            category: str(path)
            for category, path in sorted(current_log_roots.items())
        },
        "baseline_log_roots": {
            category: str(path)
            for category, path in sorted(baseline_log_roots.items())
        },
        "selection_policy": {
            "representative_count": len(entries),
            "criteria": [
                "concrete function x binary_pair ids",
                "baseline/current UNKNOWN result",
                "baseline/current required reason records present",
                "baseline/current payload binary1_name and binary2_name match expected direction",
                "current expected movement and object detail present",
                "raw baseline legacy tuples may have missing proof/action detail",
                "return_coverage_inconclusive is tracked only as retired reclassification input",
                "avoid semantic decision changes before lane implementation",
            ],
        },
        "implementation_manifest": implementation_manifest,
        "pre_fix_regression_gate": pre_fix_gate,
        "readiness": readiness,
        "phase3_lane1_ready": readiness["ready"] and pre_fix_gate["ready"],
        "entries": entries,
        "retired_reason_inventory": retired_reason_inventory,
        "retired_transitions": transition_entries,
    }
    path = output / "return_coverage_lane1_representatives.json"
    _write_json(path, manifest)
    return path


def validate_phase3_return_coverage_lane1_manifest(manifest: Mapping[str, Any]) -> None:
    readiness = manifest.get("readiness")
    pre_fix_gate = manifest.get("pre_fix_regression_gate")
    failures = []
    if not isinstance(readiness, Mapping):
        failures.append("readiness_missing")
    else:
        failures.extend(str(kind) for kind in (readiness.get("failure_kinds") or ()))
    if isinstance(pre_fix_gate, Mapping):
        summary = pre_fix_gate.get("summary")
        if isinstance(summary, Mapping):
            failures.extend(str(kind) for kind in (summary.get("failed_kinds") or ()))
        else:
            failures.append("pre_fix_summary_missing")
    else:
        failures.append("pre_fix_regression_gate_missing")
    if manifest.get("phase3_lane1_ready") is not True:
        failures.append("phase3_lane1_not_ready")
    if manifest.get("phase3_lane1_ready") is False and not failures:
        raise ValueError("Phase 3 lane 1 readiness is false without failure details")
    if failures:
        raise ValueError(f"Phase 3 lane 1 representative manifest is not ready: {', '.join(failures)}")


def build_phase3_return_coverage_lane1_post_fix_gate(
    *,
    baseline_raw_dir: Path,
    output_dir: Path,
    current_log_roots: Mapping[str, Path],
    baseline_log_roots: Mapping[str, Path],
    phase1_dir: Optional[Path] = None,
    phase1_current_log_roots: Optional[Mapping[str, Path]] = None,
    phase3_manifest_path: Optional[Path] = None,
    phase3_manifest_sha256: Optional[str] = None,
) -> Path:
    raw_dir = Path(baseline_raw_dir)
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)
    baseline_manifest = _read_json(raw_dir / "artifact_manifest.json")
    current_records = _records_by_key(current_log_roots)
    baseline_records = _records_by_key(baseline_log_roots)
    phase3_manifest, phase3_ref = _load_phase3_lane1_manifest(
        raw_dir=raw_dir,
        explicit_path=phase3_manifest_path,
    )
    frozen_entries = tuple(phase3_manifest.get("entries") or ())
    frozen_transitions = tuple(phase3_manifest.get("retired_transitions") or ())
    phase3_manifest_checks = _phase3_pre_fix_manifest_checks(
        phase3_manifest=phase3_manifest,
        phase3_manifest_ref=phase3_ref,
        expected_phase3_manifest_sha256=phase3_manifest_sha256,
        frozen_entries=frozen_entries,
        frozen_transitions=frozen_transitions,
    )
    entries = [
        _materialize_post_fix_entry(raw_entry, current_records)
        for raw_entry in frozen_entries
        if isinstance(raw_entry, Mapping)
    ]
    transition_entries = [
        _materialize_retired_transition(
            raw_entry,
            current_records,
            baseline_records,
            require_current_expected_movements=False,
        )
        for raw_entry in frozen_transitions
        if isinstance(raw_entry, Mapping)
    ]
    retired_reason_inventory = _retired_reason_inventory(
        current_records=current_records,
        baseline_records=baseline_records,
        transition_entries=transition_entries,
    )
    post_fix_gate = _post_fix_regression_gate(
        entries=entries,
        transition_entries=transition_entries,
        retired_reason_inventory=retired_reason_inventory,
        phase1_dir=Path(phase1_dir) if phase1_dir is not None else raw_dir.parent / "phase1",
        current_log_roots=current_log_roots,
        phase1_current_log_roots=phase1_current_log_roots,
        baseline_log_roots=baseline_log_roots,
        phase3_manifest_ref=phase3_ref,
        phase3_manifest_checks=phase3_manifest_checks,
    )
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase3_return_coverage_lane1_post_fix_gate",
        "artifact_role": "derived_audit_post_fix_gate",
        "baseline_id": baseline_manifest.get("baseline_id") or MISSING_SENTINEL,
        "baseline_git_head": baseline_manifest.get("git_head") or MISSING_SENTINEL,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "target_reason_ids": list(TARGET_REASON_IDS),
        "retired_reason_ids": list(RETIRED_REASON_IDS),
        "baseline_raw_artifact_ref": _file_ref(raw_dir / "artifact_manifest.json"),
        "phase3_pre_fix_manifest_ref": phase3_ref,
        "current_log_roots": {
            category: str(path)
            for category, path in sorted(current_log_roots.items())
        },
        "baseline_log_roots": {
            category: str(path)
            for category, path in sorted(baseline_log_roots.items())
        },
        "post_fix_policy": {
            "unknown_with_pending_proof": "accepted_pending_proof",
            "eq_requires_completed_recovery_proof": True,
            "completed_proof_id_source": "pre_fix_manifest_current_observation",
            "reject_eq_with_active_return_coverage_reason": True,
            "retired_inconclusive_stays_retired": True,
        },
        "post_fix_regression_gate": post_fix_gate,
        "phase3_lane1_post_fix_ready": post_fix_gate["ready"],
        "entries": entries,
        "retired_reason_inventory": retired_reason_inventory,
        "retired_transitions": transition_entries,
    }
    path = output / "return_coverage_lane1_post_fix_gate.json"
    _write_json(path, manifest)
    return path


def validate_phase3_return_coverage_lane1_post_fix_gate(manifest: Mapping[str, Any]) -> None:
    gate = manifest.get("post_fix_regression_gate")
    failures = []
    if isinstance(gate, Mapping):
        summary = gate.get("summary")
        if isinstance(summary, Mapping):
            failures.extend(str(kind) for kind in (summary.get("failed_kinds") or ()))
        else:
            failures.append("post_fix_summary_missing")
    else:
        failures.append("post_fix_regression_gate_missing")
    if manifest.get("phase3_lane1_post_fix_ready") is not True:
        failures.append("phase3_lane1_post_fix_not_ready")
    if manifest.get("phase3_lane1_post_fix_ready") is False and not failures:
        raise ValueError("Phase 3 lane 1 post-fix gate is false without failure details")
    if failures:
        raise ValueError(f"Phase 3 lane 1 post-fix gate is not ready: {', '.join(failures)}")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Build Phase 3 lane 1 return coverage representative manifest.",
    )
    parser.add_argument(
        "--gate-stage",
        choices=("pre-fix", "post-fix"),
        default="pre-fix",
        help="which Phase 3 lane 1 gate artifact to build",
    )
    parser.add_argument("--baseline-raw-dir", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument(
        "--current-log-root",
        action="append",
        default=[],
        metavar="CATEGORY=PATH",
        help="current log root for a category; may be repeated",
    )
    parser.add_argument(
        "--baseline-log-root",
        action="append",
        default=[],
        metavar="CATEGORY=PATH",
        help="baseline log root for a category; may be repeated",
    )
    parser.add_argument(
        "--phase1-dir",
        default=None,
        help="Phase 1 manifest directory for positive/negative representative gates",
    )
    parser.add_argument(
        "--phase1-current-log-root",
        action="append",
        default=None,
        metavar="CATEGORY=PATH",
        help="current log root for Phase 1 positive/negative gates; defaults to --current-log-root",
    )
    parser.add_argument(
        "--phase3-manifest",
        default=None,
        help="frozen Phase 3 lane 1 pre-fix manifest used by the post-fix gate",
    )
    parser.add_argument(
        "--phase3-manifest-sha256",
        default=None,
        help="required expected sha256 of the frozen Phase 3 lane 1 pre-fix manifest for post-fix gate",
    )
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)
    current_roots = _parse_roots(args.current_log_root)
    baseline_roots = _parse_roots(args.baseline_log_root)
    phase1_current_roots = (
        _parse_roots(args.phase1_current_log_root)
        if args.phase1_current_log_root is not None
        else None
    )
    if args.gate_stage == "post-fix" and not args.phase3_manifest_sha256:
        parser.error("--phase3-manifest-sha256 is required when --gate-stage=post-fix")
    if args.gate_stage == "post-fix":
        path = build_phase3_return_coverage_lane1_post_fix_gate(
            baseline_raw_dir=Path(args.baseline_raw_dir),
            output_dir=Path(args.output_dir),
            current_log_roots=current_roots,
            baseline_log_roots=baseline_roots,
            phase1_dir=Path(args.phase1_dir) if args.phase1_dir else None,
            phase1_current_log_roots=phase1_current_roots,
            phase3_manifest_path=Path(args.phase3_manifest) if args.phase3_manifest else None,
            phase3_manifest_sha256=args.phase3_manifest_sha256,
        )
    else:
        path = build_phase3_return_coverage_lane1_manifest(
            baseline_raw_dir=Path(args.baseline_raw_dir),
            output_dir=Path(args.output_dir),
            current_log_roots=current_roots,
            baseline_log_roots=baseline_roots,
            phase1_dir=Path(args.phase1_dir) if args.phase1_dir else None,
            phase1_current_log_roots=phase1_current_roots,
        )
    if args.require_ready:
        if args.gate_stage == "post-fix":
            validate_phase3_return_coverage_lane1_post_fix_gate(_read_json(path))
        else:
            validate_phase3_return_coverage_lane1_manifest(_read_json(path))
    print(path)
    return 0


def _implementation_manifest(
    entries: Sequence[Mapping[str, Any]],
    transition_entries: Sequence[Mapping[str, Any]],
) -> Dict[str, Any]:
    return {
        "lane_id": "phase3_return_coverage_lane1",
        "lane_reason_ids": ["return_coverage_gap", "return_coverage_inconclusive"],
        "active_target_reason_id": "return_coverage_gap",
        "retired_reason_id_policy": {
            "return_coverage_inconclusive": "retired_reclassification_reference_only",
        },
        "proof_completion_gate": {
            "eq_allowed_without_completed_proof": False,
            "pending_proof_keeps_final_result": STATUS_UNKNOWN,
            "completion_required_for_recovery": [
                "return_partition_extraction",
                "return_guard_coverage",
            ],
            "required_recovery_action": "return_coverage_proof_required",
        },
        "expected_movement_entries": [
            {
                "id": entry.get("id"),
                "function": entry.get("function"),
                "binary_pair": entry.get("binary_pair"),
                "record_case_stage_aggregation_units": _movement_units(entry.get("expected_movements") or ()),
                "expected_movements": entry.get("expected_movements") or (),
                "expected_return_coverage_targets": _canonical_return_coverage_targets_for_entry(entry),
                "required_completion_actions": _canonical_return_coverage_completion_actions(
                    _frozen_required_return_coverage_actions(entry)
                ),
            }
            for entry in entries
        ],
        "retired_observation_entries": [
            {
                "id": entry.get("id"),
                "function": entry.get("function"),
                "binary_pair": entry.get("binary_pair"),
                "retired_reason_id": entry.get("retired_reason_id"),
                "reclassified_to_reason_id": entry.get("reclassified_to_reason_id"),
                "record_case_stage_aggregation_units": _movement_units(
                    entry.get("current_expected_movements") or ()
                ),
                "current_expected_movements": entry.get("current_expected_movements") or (),
            }
            for entry in transition_entries
        ],
    }


def _movement_units(movements: Sequence[Any]) -> Sequence[Dict[str, Any]]:
    units = []
    for movement in movements:
        if not isinstance(movement, Mapping):
            continue
        units.append(
            {
                "movement_id": movement.get("id") or MISSING_SENTINEL,
                "count_kind": movement.get("count_kind") or MISSING_SENTINEL,
                "record_or_case": movement.get("pair_or_case") or MISSING_SENTINEL,
                "stage": movement.get("stage") or MISSING_SENTINEL,
                "aggregation_unit": movement.get("aggregation_unit") or MISSING_SENTINEL,
            }
        )
    return units


def _pre_fix_regression_gate(
    *,
    entries: Sequence[Mapping[str, Any]],
    transition_entries: Sequence[Mapping[str, Any]],
    retired_reason_inventory: Mapping[str, Any],
    phase1_dir: Path,
    current_log_roots: Mapping[str, Path],
    phase1_current_log_roots: Optional[Mapping[str, Path]],
    baseline_log_roots: Mapping[str, Path],
) -> Dict[str, Any]:
    phase1_roots = phase1_current_log_roots or current_log_roots
    checks: list[Dict[str, Any]] = []
    checks.extend(_lane_manifest_checks(entries, transition_entries, retired_reason_inventory))
    checks.extend(
        _phase1_positive_negative_checks(
            phase1_dir=phase1_dir,
            current_log_roots=phase1_roots,
            baseline_log_roots=baseline_log_roots,
        )
    )
    failed = [check for check in checks if check.get("status") == "failed"]
    return {
        "gate_kind": "phase3_return_coverage_lane1_pre_fix_regression",
        "baseline_mode": "current_logs_exact_match_to_implementation_manifest",
        "phase1_current_log_roots": {
            category: str(path)
            for category, path in sorted(phase1_roots.items())
        },
        "ready": not failed,
        "summary": {
            "total": len(checks),
            "passed": sum(1 for check in checks if check.get("status") == "ok"),
            "not_evaluated": sum(1 for check in checks if check.get("status") == "not_evaluated"),
            "failed": len(failed),
            "failed_kinds": sorted({str(check.get("kind")) for check in failed}),
            "locked_gates": [
                "current_logs_exact_match",
                "positive_representative_non_regression",
                "negative_representative_non_regression",
                "retired_inconclusive_stays_retired",
                "return_coverage_gap_object_evidence_proof_id",
                "proof_completion_required_before_eq",
            ],
        },
        "checks": checks,
    }


def _post_fix_regression_gate(
    *,
    entries: Sequence[Mapping[str, Any]],
    transition_entries: Sequence[Mapping[str, Any]],
    retired_reason_inventory: Mapping[str, Any],
    phase1_dir: Path,
    current_log_roots: Mapping[str, Path],
    phase1_current_log_roots: Optional[Mapping[str, Path]],
    baseline_log_roots: Mapping[str, Path],
    phase3_manifest_ref: Mapping[str, Any],
    phase3_manifest_checks: Sequence[Mapping[str, Any]],
) -> Dict[str, Any]:
    phase1_roots = phase1_current_log_roots or current_log_roots
    checks: list[Dict[str, Any]] = [dict(check) for check in phase3_manifest_checks]
    for entry in entries:
        checks.append(
            _ok(
                "return_coverage_post_fix_expected_movement",
                entry_id=entry.get("id"),
                function=entry.get("function"),
                binary_pair=entry.get("binary_pair"),
                post_fix_status=entry.get("post_fix_status"),
            )
            if entry.get("post_fix_status")
            in {
                "pending_proof",
                "completed_recovery",
                "completed_recovery_with_operational_unknown",
            }
            else _failed(
                "return_coverage_post_fix_expected_movement",
                entry_id=entry.get("id"),
                function=entry.get("function"),
                binary_pair=entry.get("binary_pair"),
                failures=entry.get("post_fix_failures") or (),
                current_result=(entry.get("current_observation") or {}).get("final_result"),
            )
        )
    checks.extend(_retired_transition_invariant_checks(transition_entries, retired_reason_inventory))
    checks.extend(
        _phase1_positive_negative_checks(
            phase1_dir=phase1_dir,
            current_log_roots=phase1_roots,
            baseline_log_roots=baseline_log_roots,
            strict_negative_reason_ids=False,
        )
    )
    failed = [check for check in checks if check.get("status") == "failed"]
    return {
        "gate_kind": "phase3_return_coverage_lane1_post_fix_regression",
        "baseline_mode": "expected_movement_or_completed_proof_against_pre_fix_manifest",
        "phase1_current_log_roots": {
            category: str(path)
            for category, path in sorted(phase1_roots.items())
        },
        "ready": not failed,
        "summary": {
            "total": len(checks),
            "passed": sum(1 for check in checks if check.get("status") == "ok"),
            "not_evaluated": sum(1 for check in checks if check.get("status") == "not_evaluated"),
            "failed": len(failed),
            "failed_kinds": sorted({str(check.get("kind")) for check in failed}),
            "locked_gates": [
                "completed_return_coverage_proof_before_eq",
                "proof_obligation_id_matches_pre_fix_manifest",
                "positive_representative_non_regression",
                "negative_representative_non_regression",
                "retired_inconclusive_stays_retired",
                "no_pending_proof_gate_on_eq",
            ],
        },
        "checks": checks,
    }


def _phase3_pre_fix_manifest_checks(
    *,
    phase3_manifest: Mapping[str, Any],
    phase3_manifest_ref: Mapping[str, Any],
    expected_phase3_manifest_sha256: Optional[str],
    frozen_entries: Sequence[Any],
    frozen_transitions: Sequence[Any],
) -> Sequence[Dict[str, Any]]:
    checks: list[Dict[str, Any]] = []
    if phase3_manifest_ref.get("sha256") == "__missing__":
        checks.append(
            _failed(
                "phase3_pre_fix_manifest_available",
                phase3_manifest_ref=dict(phase3_manifest_ref),
            )
        )
    else:
        checks.append(
            _ok(
                "phase3_pre_fix_manifest_available",
                phase3_manifest_ref=dict(phase3_manifest_ref),
            )
        )
    if expected_phase3_manifest_sha256 is None:
        checks.append(
            _failed(
                "phase3_pre_fix_manifest_sha256_required",
                actual_sha256=phase3_manifest_ref.get("sha256") or MISSING_SENTINEL,
            )
        )
    else:
        actual_sha256 = phase3_manifest_ref.get("sha256")
        checks.append(
            _ok(
                "phase3_pre_fix_manifest_sha256",
                sha256=actual_sha256,
            )
            if actual_sha256 == expected_phase3_manifest_sha256
            else _failed(
                "phase3_pre_fix_manifest_sha256",
                expected_sha256=expected_phase3_manifest_sha256,
                actual_sha256=actual_sha256 or MISSING_SENTINEL,
            )
        )
    expected_kind = "phase3_return_coverage_lane1_representatives"
    actual_kind = phase3_manifest.get("manifest_kind")
    checks.append(
        _ok(
            "phase3_pre_fix_manifest_kind",
            manifest_kind=actual_kind,
        )
        if actual_kind == expected_kind
        else _failed(
            "phase3_pre_fix_manifest_kind",
            manifest_kind=actual_kind or MISSING_SENTINEL,
            expected_manifest_kind=expected_kind,
        )
    )
    try:
        validate_phase3_return_coverage_lane1_manifest(phase3_manifest)
    except ValueError as exc:
        checks.append(_failed("phase3_pre_fix_manifest_ready", error=str(exc)))
    else:
        checks.append(_ok("phase3_pre_fix_manifest_ready"))
    checks.append(
        _ok("phase3_pre_fix_entries_non_empty", count=len(frozen_entries))
        if frozen_entries
        else _failed("phase3_pre_fix_entries_non_empty", count=0)
    )
    checks.append(
        _ok("phase3_pre_fix_retired_transitions_non_empty", count=len(frozen_transitions))
        if frozen_transitions
        else _failed("phase3_pre_fix_retired_transitions_non_empty", count=0)
    )
    checks.extend(
        _phase3_pre_fix_manifest_identity_set_checks(
            phase3_manifest=phase3_manifest,
            frozen_entries=frozen_entries,
            frozen_transitions=frozen_transitions,
        )
    )
    for index, entry in enumerate(frozen_entries):
        if not isinstance(entry, Mapping):
            checks.append(
                _failed(
                    "phase3_pre_fix_entry_mapping",
                    entry_index=index,
                    entry_type=type(entry).__name__,
                )
            )
            continue
        entry_details = {
            "entry_index": index,
            "entry_id": entry.get("id"),
            "function": entry.get("function"),
            "binary_pair": entry.get("binary_pair"),
        }
        frozen_observation = entry.get("current_observation")
        proof_actions = ()
        if isinstance(frozen_observation, Mapping):
            raw_actions = frozen_observation.get("proof_actions")
            if isinstance(raw_actions, Sequence) and not isinstance(raw_actions, (str, bytes)):
                proof_actions = tuple(raw_actions)
        checks.append(
            _ok(
                "phase3_pre_fix_entry_has_proof_actions",
                count=len(proof_actions),
                **entry_details,
            )
            if proof_actions
            else _failed(
                "phase3_pre_fix_entry_has_proof_actions",
                count=0,
                **entry_details,
            )
        )
        valid_actions = tuple(_frozen_existing_return_coverage_completion_actions(entry))
        checks.append(
            _ok(
                "phase3_pre_fix_entry_has_return_coverage_completion_proof_ids",
                count=len(valid_actions),
                **entry_details,
            )
            if valid_actions
            else _failed(
                "phase3_pre_fix_entry_has_return_coverage_completion_proof_ids",
                count=0,
                **entry_details,
            )
        )
        required_targets = tuple(_frozen_return_coverage_targets(entry))
        checks.append(
            _ok(
                "phase3_pre_fix_entry_has_return_coverage_targets",
                count=len(required_targets),
                **entry_details,
            )
            if required_targets
            else _failed(
                "phase3_pre_fix_entry_has_return_coverage_targets",
                count=0,
                **entry_details,
            )
        )
        missing_target_refs = tuple(_missing_expected_return_coverage_target_refs(entry))
        checks.append(
            _ok(
                "phase3_pre_fix_entry_expected_return_coverage_targets_resolved",
                count=len(required_targets),
                **entry_details,
            )
            if not missing_target_refs
            else _failed(
                "phase3_pre_fix_entry_expected_return_coverage_targets_resolved",
                missing_evidence_refs=[list(refs) for refs in missing_target_refs],
                **entry_details,
            )
        )
        missing_actions = tuple(_missing_frozen_return_coverage_completion_actions(entry))
        checks.append(
            _ok(
                "phase3_pre_fix_entry_has_complete_return_coverage_completion_proof_ids",
                count=len(_frozen_required_return_coverage_actions(entry)),
                **entry_details,
            )
            if required_targets and not missing_actions
            else _failed(
                "phase3_pre_fix_entry_has_complete_return_coverage_completion_proof_ids",
                missing=[
                    {
                        "proof_stage": action.get("proof_stage") or MISSING_SENTINEL,
                        "evidence_kind": action.get("evidence_kind") or MISSING_SENTINEL,
                        "object_target_key": action.get("object_target_key"),
                        "proof_obligation_id": action.get("proof_obligation_id"),
                    }
                    for action in missing_actions
                ],
                **entry_details,
            )
        )
    return checks


def _phase3_pre_fix_manifest_identity_set_checks(
    *,
    phase3_manifest: Mapping[str, Any],
    frozen_entries: Sequence[Any],
    frozen_transitions: Sequence[Any],
) -> Sequence[Dict[str, Any]]:
    checks: list[Dict[str, Any]] = []
    expected_entries = _phase3_expected_entry_identities(DEFAULT_REPRESENTATIVES)
    actual_entries = _phase3_manifest_entry_identities(frozen_entries)
    checks.append(
        _identity_set_check(
            "phase3_pre_fix_entries_exact_set",
            expected=expected_entries,
            actual=actual_entries,
        )
    )
    expected_transitions = _phase3_expected_entry_identities(DEFAULT_RETIRED_TRANSITIONS)
    actual_transitions = _phase3_manifest_entry_identities(frozen_transitions)
    checks.append(
        _identity_set_check(
            "phase3_pre_fix_retired_transitions_exact_set",
            expected=expected_transitions,
            actual=actual_transitions,
        )
    )
    implementation = phase3_manifest.get("implementation_manifest")
    if not isinstance(implementation, Mapping):
        checks.append(
            _failed(
                "phase3_pre_fix_implementation_manifest_available",
                reason="implementation_manifest_missing",
            )
        )
        implementation_entries = ()
        implementation_transitions = ()
    else:
        checks.append(_ok("phase3_pre_fix_implementation_manifest_available"))
        implementation_entries = implementation.get("expected_movement_entries") or ()
        implementation_transitions = implementation.get("retired_observation_entries") or ()
    implementation_entry_identities = _phase3_manifest_entry_identities(
        implementation_entries
    )
    checks.append(
        _identity_set_check(
            "phase3_pre_fix_implementation_entries_consistent",
            expected=implementation_entry_identities,
            actual=actual_entries,
        )
    )
    implementation_transition_identities = _phase3_manifest_entry_identities(
        implementation_transitions
    )
    checks.append(
        _identity_set_check(
            "phase3_pre_fix_implementation_retired_transitions_consistent",
            expected=implementation_transition_identities,
            actual=actual_transitions,
        )
    )
    checks.extend(
        _phase3_pre_fix_representative_movement_checks(
            frozen_entries=frozen_entries,
            implementation_entries=implementation_entries,
        )
    )
    checks.extend(
        _phase3_pre_fix_retired_transition_movement_checks(
            frozen_transitions=frozen_transitions,
            implementation_transitions=implementation_transitions,
        )
    )
    return checks


def _phase3_pre_fix_representative_movement_checks(
    *,
    frozen_entries: Sequence[Any],
    implementation_entries: Any,
) -> Sequence[Dict[str, Any]]:
    expected_entries = _phase3_entry_map(DEFAULT_REPRESENTATIVES)
    actual_entries = _phase3_entry_map(frozen_entries)
    implementation_entry_map = _phase3_entry_map(implementation_entries)
    checks: list[Dict[str, Any]] = []
    for identity, expected_entry in sorted(expected_entries.items()):
        actual_entry = actual_entries.get(identity)
        implementation_entry = implementation_entry_map.get(identity)
        checks.append(
            _movement_content_check(
                "phase3_pre_fix_entry_expected_movements_match_definition",
                identity=identity,
                expected_movements=expected_entry.get("expected_movements"),
                actual_movements=(
                    actual_entry.get("expected_movements")
                    if isinstance(actual_entry, Mapping)
                    else None
                ),
            )
        )
        checks.append(
            _movement_content_check(
                "phase3_pre_fix_implementation_expected_movements_match_definition",
                identity=identity,
                expected_movements=expected_entry.get("expected_movements"),
                actual_movements=(
                    implementation_entry.get("expected_movements")
                    if isinstance(implementation_entry, Mapping)
                    else None
                ),
            )
        )
        checks.append(
            _movement_content_check(
                "phase3_pre_fix_entry_expected_movements_match_implementation",
                identity=identity,
                expected_movements=(
                    implementation_entry.get("expected_movements")
                    if isinstance(implementation_entry, Mapping)
                    else None
                ),
                actual_movements=(
                    actual_entry.get("expected_movements")
                    if isinstance(actual_entry, Mapping)
                    else None
                ),
            )
        )
        checks.append(
            _target_content_check(
                "phase3_pre_fix_entry_return_coverage_targets_match_implementation",
                identity=identity,
                expected_targets=(
                    implementation_entry.get("expected_return_coverage_targets")
                    if isinstance(implementation_entry, Mapping)
                    else None
                ),
                actual_targets=(
                    _frozen_return_coverage_targets(actual_entry)
                    if isinstance(actual_entry, Mapping)
                    else None
                ),
            )
        )
        checks.append(
            _completion_action_content_check(
                "phase3_pre_fix_entry_required_completion_actions_match_implementation",
                identity=identity,
                expected_actions=(
                    implementation_entry.get("required_completion_actions")
                    if isinstance(implementation_entry, Mapping)
                    else None
                ),
                actual_actions=(
                    _frozen_existing_return_coverage_completion_actions(actual_entry)
                    if isinstance(actual_entry, Mapping)
                    else None
                ),
            )
        )
    return checks


def _phase3_pre_fix_retired_transition_movement_checks(
    *,
    frozen_transitions: Sequence[Any],
    implementation_transitions: Any,
) -> Sequence[Dict[str, Any]]:
    expected_transitions = _phase3_entry_map(DEFAULT_RETIRED_TRANSITIONS)
    actual_transitions = _phase3_entry_map(frozen_transitions)
    implementation_transition_map = _phase3_entry_map(implementation_transitions)
    checks: list[Dict[str, Any]] = []
    for identity, expected_transition in sorted(expected_transitions.items()):
        actual_transition = actual_transitions.get(identity)
        implementation_transition = implementation_transition_map.get(identity)
        checks.append(
            _movement_content_check(
                "phase3_pre_fix_retired_transition_current_expected_movements_match_definition",
                identity=identity,
                expected_movements=expected_transition.get("current_expected_movements"),
                actual_movements=(
                    actual_transition.get("current_expected_movements")
                    if isinstance(actual_transition, Mapping)
                    else None
                ),
            )
        )
        checks.append(
            _movement_content_check(
                "phase3_pre_fix_implementation_retired_movements_match_definition",
                identity=identity,
                expected_movements=expected_transition.get("current_expected_movements"),
                actual_movements=(
                    implementation_transition.get("current_expected_movements")
                    if isinstance(implementation_transition, Mapping)
                    else None
                ),
            )
        )
        checks.append(
            _movement_content_check(
                "phase3_pre_fix_retired_transition_current_expected_movements_match_implementation",
                identity=identity,
                expected_movements=(
                    implementation_transition.get("current_expected_movements")
                    if isinstance(implementation_transition, Mapping)
                    else None
                ),
                actual_movements=(
                    actual_transition.get("current_expected_movements")
                    if isinstance(actual_transition, Mapping)
                    else None
                ),
            )
        )
    return checks


def _movement_content_check(
    kind: str,
    *,
    identity: Tuple[str, str, str],
    expected_movements: Any,
    actual_movements: Any,
) -> Dict[str, Any]:
    expected = _canonical_phase3_expected_movements(expected_movements)
    actual = _canonical_phase3_expected_movements(actual_movements)
    details = {
        "entry": _identity_to_dict(identity),
        "expected_count": len(expected),
        "actual_count": len(actual),
        "expected_movements": expected,
        "actual_movements": actual,
    }
    if actual == expected:
        return _ok(kind, **details)
    return _failed(kind, **details)


def _target_content_check(
    kind: str,
    *,
    identity: Tuple[str, str, str],
    expected_targets: Any,
    actual_targets: Any,
) -> Dict[str, Any]:
    expected = _canonical_return_coverage_targets(expected_targets)
    actual = _canonical_return_coverage_targets(actual_targets)
    details = {
        "entry": _identity_to_dict(identity),
        "expected_count": len(expected),
        "actual_count": len(actual),
        "expected_targets": expected,
        "actual_targets": actual,
    }
    if actual == expected:
        return _ok(kind, **details)
    return _failed(kind, **details)


def _completion_action_content_check(
    kind: str,
    *,
    identity: Tuple[str, str, str],
    expected_actions: Any,
    actual_actions: Any,
) -> Dict[str, Any]:
    expected = _canonical_return_coverage_completion_actions(expected_actions)
    actual = _canonical_return_coverage_completion_actions(actual_actions)
    details = {
        "entry": _identity_to_dict(identity),
        "expected_count": len(expected),
        "actual_count": len(actual),
        "expected_actions": expected,
        "actual_actions": actual,
    }
    if actual == expected:
        return _ok(kind, **details)
    return _failed(kind, **details)


def _canonical_phase3_expected_movements(value: Any) -> Sequence[Dict[str, Any]]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes)):
        return ()
    movements = []
    for index, movement in enumerate(value):
        if not isinstance(movement, Mapping):
            movements.append(
                {
                    "index": index,
                    "id": MISSING_SENTINEL,
                    "invalid_type": type(movement).__name__,
                }
            )
            continue
        movements.append(
            {
                "index": index,
                "id": str(movement.get("id") or MISSING_SENTINEL),
                "count_kind": str(movement.get("count_kind") or MISSING_SENTINEL),
                "tuple": _normalized_string_list(movement.get("tuple")),
                "aggregation_unit": str(movement.get("aggregation_unit") or MISSING_SENTINEL),
                "stage": str(movement.get("stage") or MISSING_SENTINEL),
                "pair_or_case": str(movement.get("pair_or_case") or MISSING_SENTINEL),
                "expected_evidence_refs": _normalized_string_list(
                    movement.get("expected_evidence_refs")
                ),
                "required_evidence": _normalized_string_list(movement.get("required_evidence")),
                "require_proof_obligation_id": bool(
                    movement.get("require_proof_obligation_id")
                ),
                "required_object_target_kind": str(
                    movement.get("required_object_target_kind") or MISSING_SENTINEL
                ),
            }
        )
    return tuple(movements)


def _normalized_string_list(value: Any) -> Sequence[str]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes)):
        return ()
    return tuple(str(item) for item in value)


def _canonical_return_coverage_targets_for_entry(
    entry: Mapping[str, Any],
) -> Sequence[Any]:
    return _canonical_return_coverage_targets(_frozen_return_coverage_targets(entry))


def _canonical_return_coverage_targets(value: Any) -> Sequence[Any]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes)):
        return ()
    return tuple(_normalize_nested_tuple(item) for item in value)


def _canonical_return_coverage_completion_actions(value: Any) -> Sequence[Dict[str, Any]]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes)):
        return ()
    actions = []
    for index, action in enumerate(value):
        if not isinstance(action, Mapping):
            actions.append(
                {
                    "index": index,
                    "invalid_type": type(action).__name__,
                }
            )
            continue
        actions.append(
            {
                "index": index,
                "reason_id": str(action.get("reason_id") or MISSING_SENTINEL),
                "proof_kind": str(action.get("proof_kind") or MISSING_SENTINEL),
                "proof_stage": str(action.get("proof_stage") or MISSING_SENTINEL),
                "evidence_kind": str(action.get("evidence_kind") or MISSING_SENTINEL),
                "object_target_key": _normalize_nested_tuple(action.get("object_target_key")),
                "proof_obligation_id": _normalize_nested_tuple(action.get("proof_obligation_id")),
                "raw_proof_obligation_id_present": action.get("raw_proof_obligation_id_present")
                is True,
            }
        )
    return tuple(actions)


def _identity_set_check(
    kind: str,
    *,
    expected: Sequence[Tuple[str, str, str]],
    actual: Sequence[Tuple[str, str, str]],
) -> Dict[str, Any]:
    expected_counts = Counter(expected)
    actual_counts = Counter(actual)
    missing = _identity_diff(expected_counts, actual_counts)
    unexpected = _identity_diff(actual_counts, expected_counts)
    duplicate_actual = [
        identity for identity, count in sorted(actual_counts.items()) if count > 1
    ]
    details = {
        "expected_count": len(expected),
        "actual_count": len(actual),
        "expected": [_identity_to_dict(identity) for identity in sorted(expected_counts)],
        "actual": [_identity_to_dict(identity) for identity in sorted(actual_counts)],
    }
    if not missing and not unexpected and not duplicate_actual:
        return _ok(kind, **details)
    return _failed(
        kind,
        missing=[_identity_to_dict(identity) for identity in missing],
        unexpected=[_identity_to_dict(identity) for identity in unexpected],
        duplicate_actual=[_identity_to_dict(identity) for identity in duplicate_actual],
        **details,
    )


def _identity_diff(
    left: Counter[Tuple[str, str, str]],
    right: Counter[Tuple[str, str, str]],
) -> Sequence[Tuple[str, str, str]]:
    values = []
    for identity, count in sorted((left - right).items()):
        values.extend([identity] * count)
    return tuple(values)


def _phase3_expected_entry_identities(
    entries: Sequence[Mapping[str, Any]],
) -> Sequence[Tuple[str, str, str]]:
    return tuple(_phase3_entry_identity(entry) for entry in entries)


def _phase3_manifest_entry_identities(entries: Any) -> Sequence[Tuple[str, str, str]]:
    if not isinstance(entries, Sequence) or isinstance(entries, (str, bytes)):
        return ()
    return tuple(
        _phase3_entry_identity(entry)
        for entry in entries
        if isinstance(entry, Mapping)
    )


def _phase3_entry_map(entries: Any) -> Dict[Tuple[str, str, str], Mapping[str, Any]]:
    if not isinstance(entries, Sequence) or isinstance(entries, (str, bytes)):
        return {}
    result: Dict[Tuple[str, str, str], Mapping[str, Any]] = {}
    for entry in entries:
        if not isinstance(entry, Mapping):
            continue
        result[_phase3_entry_identity(entry)] = entry
    return result


def _phase3_entry_identity(entry: Mapping[str, Any]) -> Tuple[str, str, str]:
    return (
        str(entry.get("id") or MISSING_SENTINEL),
        str(entry.get("function") or MISSING_SENTINEL),
        _safe_canonical_binary_pair(entry.get("binary_pair")),
    )


def _safe_canonical_binary_pair(value: Any) -> str:
    text = str(value or MISSING_SENTINEL)
    if "_" not in text:
        return text
    try:
        return _canonical_binary_pair(text)
    except ValueError:
        return text


def _identity_to_dict(identity: Tuple[str, str, str]) -> Dict[str, str]:
    entry_id, function, binary_pair = identity
    return {
        "id": entry_id,
        "function": function,
        "binary_pair": binary_pair,
    }


def _lane_manifest_checks(
    entries: Sequence[Mapping[str, Any]],
    transition_entries: Sequence[Mapping[str, Any]],
    retired_reason_inventory: Mapping[str, Any],
) -> Sequence[Dict[str, Any]]:
    checks: list[Dict[str, Any]] = []
    for entry in entries:
        checks.append(
            _ok(
                "current_logs_exact_match",
                entry_id=entry.get("id"),
                function=entry.get("function"),
                binary_pair=entry.get("binary_pair"),
            )
            if entry.get("selection_status") == "ready"
            else _failed(
                "current_logs_exact_match",
                entry_id=entry.get("id"),
                function=entry.get("function"),
                binary_pair=entry.get("binary_pair"),
                failures=entry.get("selection_failures") or (),
            )
        )
        checks.extend(_object_proof_id_checks(entry))
        checks.append(
            _ok(
                "proof_completion_required_before_eq",
                entry_id=entry.get("id"),
                current_result=(entry.get("current_observation") or {}).get("final_result"),
            )
            if (entry.get("current_observation") or {}).get("final_result") == STATUS_UNKNOWN
            else _failed(
                "proof_completion_required_before_eq",
                entry_id=entry.get("id"),
                current_result=(entry.get("current_observation") or {}).get("final_result"),
            )
        )
    checks.extend(_retired_transition_invariant_checks(transition_entries, retired_reason_inventory))
    return checks


def _retired_transition_invariant_checks(
    transition_entries: Sequence[Mapping[str, Any]],
    retired_reason_inventory: Mapping[str, Any],
) -> Sequence[Dict[str, Any]]:
    checks: list[Dict[str, Any]] = []
    for entry in transition_entries:
        invariant = entry.get("final_result_invariant") or {}
        checks.append(
            _ok(
                "retired_inconclusive_stays_retired",
                entry_id=entry.get("id"),
                function=entry.get("function"),
                binary_pair=entry.get("binary_pair"),
            )
            if entry.get("selection_status") == "retired_by_reclassification"
            and invariant.get("final_result_unchanged_unknown") is True
            and invariant.get("false_eq") is False
            else _failed(
                "retired_inconclusive_stays_retired",
                entry_id=entry.get("id"),
                function=entry.get("function"),
                binary_pair=entry.get("binary_pair"),
                failures=entry.get("selection_failures") or (),
                final_result_invariant=invariant,
            )
        )
    inventory = retired_reason_inventory.get("return_coverage_inconclusive")
    checks.append(
        _ok("retired_inconclusive_inventory")
        if isinstance(inventory, Mapping) and inventory.get("status") == "retired_by_reclassification"
        else _failed("retired_inconclusive_inventory", inventory=inventory)
    )
    return checks


def _object_proof_id_checks(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    checks = []
    actions = (entry.get("current_observation") or {}).get("proof_actions") or ()
    for movement in entry.get("expected_movements") or ():
        if not isinstance(movement, Mapping) or movement.get("count_kind") != UnknownCountKind.PROOF_ACTION.value:
            continue
        candidates = _records_matching_evidence_refs(
            _records_matching_scope(
                _records_matching_tuple(actions, _movement_tuple(movement) or ()),
                movement,
            ),
            movement,
        )
        movement_id = movement.get("id") or MISSING_SENTINEL
        if len(candidates) != 1:
            checks.append(
                _failed(
                    "return_coverage_gap_object_evidence_proof_id",
                    entry_id=entry.get("id"),
                    movement_id=movement_id,
                    candidate_count=len(candidates),
                )
            )
            continue
        candidate = candidates[0]
        checks.append(
            _ok(
                "return_coverage_gap_object_evidence_proof_id",
                entry_id=entry.get("id"),
                movement_id=movement_id,
            )
            if _record_has_object_target(candidate, movement)
            and _proof_action_has_proof_id(candidate, movement)
            else _failed(
                "return_coverage_gap_object_evidence_proof_id",
                entry_id=entry.get("id"),
                movement_id=movement_id,
                object_target_key=candidate.get("object_target_key"),
                proof_obligation_id=candidate.get("proof_obligation_id"),
            )
        )
    return checks


def _phase1_positive_negative_checks(
    *,
    phase1_dir: Path,
    current_log_roots: Mapping[str, Path],
    baseline_log_roots: Mapping[str, Path],
    strict_negative_reason_ids: bool = True,
) -> Sequence[Dict[str, Any]]:
    if not phase1_dir.is_dir():
        return [
            _failed(
                "phase1_positive_negative_manifest_available",
                phase1_dir=str(phase1_dir),
                error="missing phase1 manifest directory",
            )
        ]
    positive = _read_json(phase1_dir / "positive_manifest.json")
    negative = _read_json(phase1_dir / "negative_manifest.json")
    phase1_entries = tuple(positive.get("entries") or ()) + tuple(negative.get("entries") or ())
    records = _validation_records_for_entries(current_log_roots, phase1_entries)
    checks: list[Dict[str, Any]] = []
    for entry in positive.get("entries") or ():
        record = records.get(_entry_key(entry))
        if record is None:
            checks.append(_failed("positive_representative_non_regression", entry_id=entry.get("id"), error="missing log"))
        elif record["status"] == STATUS_EQ:
            checks.append(_ok("positive_representative_non_regression", entry_id=entry.get("id")))
        else:
            checks.append(
                _failed(
                    "positive_representative_non_regression",
                    entry_id=entry.get("id"),
                    expected_result=STATUS_EQ,
                    current_result=record["status"],
                )
            )
    for entry in negative.get("entries") or ():
        checks.append(
            _negative_representative_check(
                entry,
                records,
                strict_reason_ids=strict_negative_reason_ids,
            )
        )
    return checks


def _validation_records_for_entries(
    current_log_roots: Mapping[str, Path],
    entries: Sequence[Mapping[str, Any]],
) -> Dict[Tuple[str, str, str], Dict[str, Any]]:
    records = {}
    for entry in entries:
        key = _entry_key(entry)
        category, function, binary_pair = key
        root = current_log_roots.get(category)
        if root is None:
            continue
        record = _read_entry_validation_record(Path(root), function, binary_pair)
        if record is None:
            continue
        records[key] = {
            "status": record.status,
            "reason_ids": _validation_record_reason_ids(record),
        }
    return records


def _read_entry_validation_record(root: Path, function: str, binary_pair: str):
    for path in _entry_log_paths(root, function, binary_pair):
        if not path.is_file():
            continue
        return read_validation_log_record(path)
    return None


def _entry_log_paths(root: Path, function: str, binary_pair: str) -> Sequence[Path]:
    if not root.is_dir() or "_" not in binary_pair:
        return ()
    left, right = binary_pair.split("_", 1)
    return (
        root / function / f"{function}_{left}_{right}.log",
        root / function / f"{function}_{right}_{left}.log",
    )


def _negative_representative_check(
    entry: Mapping[str, Any],
    records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
    *,
    strict_reason_ids: bool = True,
) -> Dict[str, Any]:
    entry_id = entry.get("id")
    if entry.get("category") == "synthetic_negative":
        if entry.get("current_result") == "NOT_EQ" and entry.get("must_not_be_equivalent") is True:
            return _ok("negative_representative_non_regression", entry_id=entry_id, synthetic=True)
        return _failed("negative_representative_non_regression", entry_id=entry_id, synthetic=True)
    record = records.get(_entry_key(entry))
    if record is None:
        return _failed("negative_representative_non_regression", entry_id=entry_id, error="missing log")
    if record["status"] == STATUS_EQ:
        return _failed(
            "negative_representative_non_regression",
            entry_id=entry_id,
            current_result=record["status"],
            error="false_eq",
        )
    if not strict_reason_ids:
        if record["status"] in {STATUS_UNKNOWN, "NOT_EQ"}:
            return _ok(
                "negative_representative_non_regression",
                entry_id=entry_id,
                reason_policy="post_fix_no_false_eq",
                current_result=record["status"],
                observed_reason_ids=sorted(record.get("reason_ids") or ()),
            )
        return _failed(
            "negative_representative_non_regression",
            entry_id=entry_id,
            current_result=record["status"],
            error="post_fix_negative_result_not_accepted",
        )
    required = set(str(reason) for reason in (entry.get("required_reason_ids") or ()))
    observed = set(record.get("reason_ids") or ())
    if required.issubset(observed):
        return _ok("negative_representative_non_regression", entry_id=entry_id)
    if (
        entry_id == "negative-inconclusive-return-coverage-near-miss"
        and required == {"return_coverage_inconclusive"}
        and "return_coverage_gap" in observed
        and record["status"] == STATUS_UNKNOWN
    ):
        return _ok(
            "negative_representative_non_regression",
            entry_id=entry_id,
            reclassification="return_coverage_inconclusive_retired_to_return_coverage_gap",
        )
    return _failed(
        "negative_representative_non_regression",
        entry_id=entry_id,
        current_result=record["status"],
        missing_required_reason_ids=sorted(required - observed),
    )


def _validation_records_by_key(
    current_log_roots: Mapping[str, Path],
) -> Dict[Tuple[str, str, str], Dict[str, Any]]:
    category_roots = {str(category): Path(path) for category, path in current_log_roots.items()}
    records = {}
    for category, root in sorted(category_roots.items()):
        for record in aggregate_validation_logs(_log_paths(root)).records:
            records[(category, record.function_name, _canonical_binary_pair(_record_pair_label(record)))] = {
                "status": record.status,
                "reason_ids": _validation_record_reason_ids(record),
            }
    return records


def _entry_key(entry: Mapping[str, Any]) -> Tuple[str, str, str]:
    return (
        str(entry.get("category") or MISSING_SENTINEL),
        str(entry.get("function") or MISSING_SENTINEL),
        _canonical_binary_pair(str(entry.get("binary_pair") or MISSING_SENTINEL)),
    )


def _validation_record_reason_ids(record: Any) -> Sequence[str]:
    payload = record.payloads[-1] if record.payloads else {}
    return sorted(
        {
            reason.reason_id
            for reason in _extract_final_unknown_reasons(payload)
        }
    )


def _record_pair_label(record: Any) -> str:
    pair_label = str(getattr(record, "pair_label", ""))
    if "↔" in pair_label:
        left, right = pair_label.split("↔", 1)
        return f"{left.strip()}_{right.strip()}"
    return pair_label


def _log_paths(root: Path) -> Sequence[Path]:
    if not root.is_dir():
        return ()
    return tuple(sorted(root.glob("*/*.log"), key=lambda path: str(path)))


def _ok(kind: str, **details: Any) -> Dict[str, Any]:
    result = {"kind": kind, "status": "ok"}
    result.update(details)
    return result


def _failed(kind: str, **details: Any) -> Dict[str, Any]:
    result = {"kind": kind, "status": "failed"}
    result.update(details)
    return result


def _materialize_entry(
    raw_entry: Mapping[str, Any],
    current_records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
    baseline_records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
) -> Dict[str, Any]:
    category = str(raw_entry["category"])
    function = str(raw_entry["function"])
    binary_pair = _canonical_binary_pair(str(raw_entry["binary_pair"]))
    key = (category, function, binary_pair)
    current = current_records.get(key)
    baseline = baseline_records.get(key)
    entry: Dict[str, Any] = {
        **dict(raw_entry),
        "binary_pair": binary_pair,
        "left_binary_id": binary_pair.split("_", 1)[0],
        "right_binary_id": binary_pair.split("_", 1)[1],
        "expected_observed_left_binary_id": raw_entry.get("expected_observed_left_binary_id")
        or binary_pair.split("_", 1)[0],
        "expected_observed_right_binary_id": raw_entry.get("expected_observed_right_binary_id")
        or binary_pair.split("_", 1)[1],
        "expected_observed_binary1_name": raw_entry.get("expected_observed_binary1_name")
        or raw_entry.get("expected_observed_left_binary_id")
        or binary_pair.split("_", 1)[0],
        "expected_observed_binary2_name": raw_entry.get("expected_observed_binary2_name")
        or raw_entry.get("expected_observed_right_binary_id")
        or binary_pair.split("_", 1)[1],
        "current_observation": _observation(current),
        "baseline_observation": _observation(baseline),
    }
    failures = []
    required = tuple(str(reason_id) for reason_id in raw_entry.get("required_reason_ids") or ())
    for label, observation in (
        ("current", entry["current_observation"]),
        ("baseline", entry["baseline_observation"]),
    ):
        if observation.get("log_status") == "missing":
            failures.append(f"{label}_log_missing")
            continue
        if not _observation_direction_matches(entry, observation):
            failures.append(f"{label}_observed_direction_mismatch")
        if not _observation_payload_direction_matches(entry, observation):
            failures.append(f"{label}_observed_payload_direction_mismatch")
        if observation.get("final_result") != STATUS_UNKNOWN:
            failures.append(f"{label}_not_unknown")
        observed = set(observation.get("observed_reason_ids") or ())
        for reason_id in required:
            if reason_id not in observed:
                failures.append(f"{label}_missing_{reason_id}")
        if label == "current":
            failures.extend(_expected_movement_failures(entry, observation, label))
    entry["selection_status"] = "ready" if not failures else "failed"
    entry["selection_failures"] = sorted(set(failures))
    return entry


def _materialize_post_fix_entry(
    raw_entry: Mapping[str, Any],
    current_records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
) -> Dict[str, Any]:
    category = str(raw_entry["category"])
    function = str(raw_entry["function"])
    binary_pair = _canonical_binary_pair(str(raw_entry["binary_pair"]))
    key = (category, function, binary_pair)
    current = _observation(current_records.get(key))
    entry: Dict[str, Any] = {
        **dict(raw_entry),
        "binary_pair": binary_pair,
        "left_binary_id": binary_pair.split("_", 1)[0],
        "right_binary_id": binary_pair.split("_", 1)[1],
        "expected_observed_left_binary_id": raw_entry.get("expected_observed_left_binary_id")
        or binary_pair.split("_", 1)[0],
        "expected_observed_right_binary_id": raw_entry.get("expected_observed_right_binary_id")
        or binary_pair.split("_", 1)[1],
        "expected_observed_binary1_name": raw_entry.get("expected_observed_binary1_name")
        or raw_entry.get("expected_observed_left_binary_id")
        or binary_pair.split("_", 1)[0],
        "expected_observed_binary2_name": raw_entry.get("expected_observed_binary2_name")
        or raw_entry.get("expected_observed_right_binary_id")
        or binary_pair.split("_", 1)[1],
        "frozen_pre_fix_observation": raw_entry.get("current_observation") or {},
        "current_observation": current,
    }
    failures = []
    completed_recovery_with_operational_unknown = False
    if current.get("log_status") == "missing":
        failures.append("current_log_missing")
    else:
        if not _observation_direction_matches(entry, current):
            failures.append("current_observed_direction_mismatch")
        if not _observation_payload_direction_matches(entry, current):
            failures.append("current_observed_payload_direction_mismatch")
        current_result = current.get("final_result")
        if current_result == STATUS_UNKNOWN:
            movement_failures = list(_expected_movement_failures(entry, current, "current"))
            if movement_failures:
                completion_failures = list(_completed_operational_unknown_failures(entry, current))
                if completion_failures:
                    failures.extend(movement_failures)
                else:
                    completed_recovery_with_operational_unknown = True
        elif current_result == STATUS_EQ:
            failures.extend(_completed_recovery_failures(entry, current))
        elif current_result == STATUS_TIMEOUT:
            failures.append("current_timeout")
        else:
            failures.append(f"current_result_not_accepted:{current_result or MISSING_SENTINEL}")
    if failures:
        entry["post_fix_status"] = "failed"
    elif completed_recovery_with_operational_unknown:
        entry["post_fix_status"] = "completed_recovery_with_operational_unknown"
    elif current.get("final_result") == STATUS_EQ:
        entry["post_fix_status"] = "completed_recovery"
    else:
        entry["post_fix_status"] = "pending_proof"
    entry["post_fix_failures"] = sorted(set(failures))
    entry["required_completion_actions"] = (
        _frozen_required_return_coverage_actions(entry)
        if entry["post_fix_status"] == "pending_proof"
        else []
    )
    entry["pending_proof_obligations"] = (
        _pending_proof_obligations(entry)
        if entry["post_fix_status"] == "pending_proof"
        else []
    )
    return entry


def _completed_recovery_failures(
    entry: Mapping[str, Any],
    current: Mapping[str, Any],
) -> Sequence[str]:
    failures = []
    if current.get("decision_gated_by_pending_proof") is True:
        failures.append("decision_gated_by_pending_proof")
    active_return_reasons = sorted(
        reason_id
        for reason_id in (current.get("observed_reason_ids") or ())
        if reason_id in OBSERVED_RETURN_REASON_IDS
    )
    failures.extend(
        f"active_return_coverage_reason_not_cleared:{reason_id}"
        for reason_id in active_return_reasons
    )
    pending_actions = [
        action
        for action in current.get("proof_actions") or ()
        if isinstance(action, Mapping)
        and action.get("reason_id") in OBSERVED_RETURN_REASON_IDS
        and action.get("status") == "pending_proof"
    ]
    if pending_actions:
        failures.append("pending_return_coverage_proof_action_still_active")
    required_actions = _frozen_required_return_coverage_actions(entry)
    if not required_actions:
        failures.append("frozen_return_coverage_proof_actions_missing")
        return failures
    completed = tuple(current.get("completed_recovery_proof_evidence") or ())
    if not completed:
        failures.append("return_coverage_completed_proof_required")
        return failures
    for action in required_actions:
        if not any(_completed_evidence_matches_action(evidence, action) for evidence in completed):
            failures.append(
                "return_coverage_completed_proof_required:"
                f"{action.get('proof_stage') or MISSING_SENTINEL}:"
                f"{action.get('evidence_kind') or MISSING_SENTINEL}"
            )
    return failures


def _completed_operational_unknown_failures(
    entry: Mapping[str, Any],
    current: Mapping[str, Any],
) -> Sequence[str]:
    failures = []
    if current.get("decision_gated_by_pending_proof") is True:
        failures.append("decision_gated_by_pending_proof")
    active_return_reasons = sorted(
        reason_id
        for reason_id in (current.get("observed_reason_ids") or ())
        if reason_id in OBSERVED_RETURN_REASON_IDS
    )
    failures.extend(
        f"active_return_coverage_reason_not_cleared:{reason_id}"
        for reason_id in active_return_reasons
    )
    pending_actions = [
        action
        for action in current.get("proof_actions") or ()
        if isinstance(action, Mapping)
        and action.get("reason_id") in OBSERVED_RETURN_REASON_IDS
        and action.get("status") == "pending_proof"
    ]
    if pending_actions:
        failures.append("pending_return_coverage_proof_action_still_active")
    required_actions = _frozen_required_return_coverage_actions(entry)
    if not required_actions:
        failures.append("frozen_return_coverage_proof_actions_missing")
        return failures
    completed = tuple(current.get("completed_recovery_proof_evidence") or ())
    if not completed:
        failures.append("return_coverage_completed_proof_required")
        return failures
    for action in required_actions:
        if not any(
            _completed_evidence_covers_operational_unknown_action(evidence, action)
            for evidence in completed
        ):
            failures.append(
                "return_coverage_completed_proof_required:"
                f"{action.get('proof_stage') or MISSING_SENTINEL}:"
                f"{action.get('evidence_kind') or MISSING_SENTINEL}"
            )
    return failures


def _completed_evidence_covers_operational_unknown_action(
    evidence_summary: Mapping[str, Any],
    action: Mapping[str, Any],
) -> bool:
    if not isinstance(evidence_summary, Mapping):
        return False
    evidence = evidence_summary.get("evidence")
    if not isinstance(evidence, Mapping):
        evidence = evidence_summary
    if evidence_summary.get("object_derived") is not True and evidence.get("object_derived") is not True:
        return False
    if str(evidence_summary.get("status") or evidence.get("status") or "") not in {
        "complete",
        "completed",
        "proven",
    }:
        return False
    proof_kind = (
        evidence_summary.get("proof_kind")
        or evidence.get("recovery_proof_kind")
        or evidence.get("proof_kind")
    )
    if (
        str(evidence_summary.get("reason_id") or evidence.get("reason_id") or MISSING_SENTINEL)
        != str(action.get("reason_id") or MISSING_SENTINEL)
        or str(evidence_summary.get("proof_stage") or evidence.get("proof_stage") or MISSING_SENTINEL)
        != str(action.get("proof_stage") or MISSING_SENTINEL)
        or str(proof_kind or MISSING_SENTINEL)
        != str(action.get("proof_kind") or MISSING_SENTINEL)
        or str(evidence_summary.get("evidence_kind") or evidence.get("evidence_kind") or MISSING_SENTINEL)
        != str(action.get("evidence_kind") or MISSING_SENTINEL)
    ):
        return False
    object_target_key = _normalize_nested_tuple(
        evidence_summary.get("object_target_key") or evidence.get("object_target_key")
    )
    action_target_key = _normalize_nested_tuple(action.get("object_target_key"))
    if not _return_coverage_operational_unknown_target_is_usable(object_target_key):
        return False
    if (
        isinstance(object_target_key, tuple)
        and isinstance(action_target_key, tuple)
        and len(object_target_key) > 1
        and len(action_target_key) > 1
        and object_target_key[1] != action_target_key[1]
    ):
        return False
    if object_target_key != action_target_key and str(evidence.get("coverage_status") or "") != "covered":
        return False
    return not _completed_evidence_has_active_blocker(evidence)


def _return_coverage_operational_unknown_target_is_usable(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if not isinstance(normalized, tuple) or len(normalized) != 7:
        return False
    (
        kind,
        side_label,
        function_key,
        reason_kind,
        return_storage_key,
        return_partition_key,
        guard_disjunction_key,
    ) = normalized
    if (
        kind != "return_coverage"
        or side_label not in {"function1", "function2"}
        or reason_kind not in TARGET_REASON_IDS
    ):
        return False
    return all(
        (
            _analysis_key_has_address_identity(function_key),
            _return_storage_key_is_specific(return_storage_key),
            _return_partition_key_is_specific(return_partition_key),
            _guard_disjunction_key_is_specific(guard_disjunction_key),
        )
    )


def _analysis_key_has_address_identity(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if not isinstance(normalized, tuple) or len(normalized) < 2:
        return False
    if normalized[0] != "function_ref":
        return False
    function_ref = normalized[1]
    if not isinstance(function_ref, tuple) or len(function_ref) < 3:
        return False
    kind, _binary_identity, address_offset = function_ref[:3]
    return kind in {"function", "code_address"} and _address_like_is_specific(address_offset)


def _pending_proof_obligations(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    current = entry.get("current_observation") if isinstance(entry.get("current_observation"), Mapping) else {}
    completed = tuple(current.get("completed_recovery_proof_evidence") or ())
    obligations = []
    for action in _frozen_required_return_coverage_actions(entry):
        has_completed_evidence = any(
            _completed_evidence_matches_action(evidence, action)
            for evidence in completed
        )
        obligations.append(
            {
                "reason_id": action.get("reason_id") or MISSING_SENTINEL,
                "proof_kind": action.get("proof_kind") or MISSING_SENTINEL,
                "proof_stage": action.get("proof_stage") or MISSING_SENTINEL,
                "evidence_kind": action.get("evidence_kind") or MISSING_SENTINEL,
                "required_evidence": list(action.get("required_evidence") or ()),
                "proof_obligation_id": action.get("proof_obligation_id") or MISSING_SENTINEL,
                "completed_evidence_present": has_completed_evidence,
                "status": "completed_evidence_present" if has_completed_evidence else "pending_evidence",
            }
        )
    return obligations


def _frozen_required_return_coverage_actions(entry: Mapping[str, Any]) -> Sequence[Mapping[str, Any]]:
    required = []
    for target in _frozen_return_coverage_targets(entry):
        for proof_stage in RETURN_COVERAGE_COMPLETION_PROOF_STAGES:
            evidence_kind = RETURN_COVERAGE_COMPLETION_EVIDENCE_KIND_BY_STAGE[proof_stage]
            required.append(
                {
                    "reason_id": "return_coverage_gap",
                    "proof_kind": "return_coverage_completion",
                    "proof_stage": proof_stage,
                    "evidence_kind": evidence_kind,
                    "required_evidence": list(
                        RETURN_COVERAGE_COMPLETION_REQUIRED_EVIDENCE_BY_STAGE[proof_stage]
                    ),
                    "object_target_key": target,
                    "proof_obligation_id": build_proof_obligation_id(
                        "return_coverage_gap",
                        proof_stage,
                        "return_coverage_completion",
                        evidence_kind,
                        target,
                    ),
                    "raw_proof_obligation_id_present": True,
                }
            )
    return tuple(required)


def _frozen_existing_return_coverage_completion_actions(
    entry: Mapping[str, Any],
) -> Sequence[Mapping[str, Any]]:
    frozen_observation = entry.get("frozen_pre_fix_observation")
    if not isinstance(frozen_observation, Mapping):
        frozen_observation = entry.get("current_observation")
    actions = []
    for action in (frozen_observation or {}).get("proof_actions") or ():
        if not isinstance(action, Mapping):
            continue
        if action.get("reason_id") != "return_coverage_gap":
            continue
        if action.get("proof_kind") != "return_coverage_completion":
            continue
        if action.get("proof_stage") not in RETURN_COVERAGE_COMPLETION_PROOF_STAGES:
            continue
        if not _proof_action_has_proof_id(action, {"require_proof_obligation_id": True}):
            continue
        actions.append(action)
    return tuple(actions)


def _missing_frozen_return_coverage_completion_actions(
    entry: Mapping[str, Any],
) -> Sequence[Mapping[str, Any]]:
    existing = tuple(_frozen_existing_return_coverage_completion_actions(entry))
    missing = []
    for required in _frozen_required_return_coverage_actions(entry):
        if not any(_frozen_action_matches_required_completion(action, required) for action in existing):
            missing.append(required)
    return tuple(missing)


def _frozen_action_matches_required_completion(
    action: Mapping[str, Any],
    required: Mapping[str, Any],
) -> bool:
    return (
        str(action.get("reason_id") or MISSING_SENTINEL)
        == str(required.get("reason_id") or MISSING_SENTINEL)
        and str(action.get("proof_kind") or MISSING_SENTINEL)
        == str(required.get("proof_kind") or MISSING_SENTINEL)
        and str(action.get("proof_stage") or MISSING_SENTINEL)
        == str(required.get("proof_stage") or MISSING_SENTINEL)
        and str(action.get("evidence_kind") or MISSING_SENTINEL)
        == str(required.get("evidence_kind") or MISSING_SENTINEL)
        and _normalize_nested_tuple(action.get("object_target_key"))
        == _normalize_nested_tuple(required.get("object_target_key"))
        and _normalize_nested_tuple(action.get("proof_obligation_id"))
        == _normalize_nested_tuple(required.get("proof_obligation_id"))
    )


def _frozen_return_coverage_targets(entry: Mapping[str, Any]) -> Sequence[Any]:
    frozen_observation = entry.get("frozen_pre_fix_observation")
    if not isinstance(frozen_observation, Mapping):
        frozen_observation = entry.get("current_observation")
    expected_ref_order = _expected_return_coverage_evidence_ref_order(entry)
    targets_by_ref: Dict[Tuple[str, ...], Any] = {}
    fallback_targets: list[Any] = []
    seen_targets: set[Any] = set()
    for record in (frozen_observation or {}).get("reason_records") or ():
        if not isinstance(record, Mapping):
            continue
        if record.get("reason_id") != "return_coverage_gap":
            continue
        object_target_key = _normalize_nested_tuple(record.get("object_target_key"))
        if not _object_target_key_is_specific(object_target_key):
            continue
        refs = tuple(str(ref) for ref in record.get("evidence_refs") or ())
        if refs:
            targets_by_ref[refs] = object_target_key
        if object_target_key not in seen_targets:
            fallback_targets.append(object_target_key)
            seen_targets.add(object_target_key)
    ordered_targets = []
    seen_ordered: set[Any] = set()
    for refs in expected_ref_order:
        target = targets_by_ref.get(refs)
        if target is None or target in seen_ordered:
            continue
        ordered_targets.append(target)
        seen_ordered.add(target)
    for target in fallback_targets:
        if target not in seen_ordered:
            ordered_targets.append(target)
            seen_ordered.add(target)
    return tuple(ordered_targets)


def _expected_return_coverage_evidence_ref_order(entry: Mapping[str, Any]) -> Sequence[Tuple[str, ...]]:
    refs = []
    seen = set()
    for movement in entry.get("expected_movements") or ():
        if not isinstance(movement, Mapping):
            continue
        tuple_key = _movement_tuple(movement)
        if tuple_key is None:
            continue
        if tuple_key[1] != "return_coverage_gap":
            continue
        expected_refs = movement.get("expected_evidence_refs")
        if expected_refs is None:
            continue
        normalized = tuple(str(ref) for ref in expected_refs or ())
        if not normalized or normalized in seen:
            continue
        refs.append(normalized)
        seen.add(normalized)
    return tuple(refs)


def _missing_expected_return_coverage_target_refs(entry: Mapping[str, Any]) -> Sequence[Tuple[str, ...]]:
    expected_refs = tuple(_expected_return_coverage_evidence_ref_order(entry))
    if not expected_refs:
        return ()
    frozen_observation = entry.get("frozen_pre_fix_observation")
    if not isinstance(frozen_observation, Mapping):
        frozen_observation = entry.get("current_observation")
    resolved_refs = set()
    for record in (frozen_observation or {}).get("reason_records") or ():
        if not isinstance(record, Mapping):
            continue
        if record.get("reason_id") != "return_coverage_gap":
            continue
        object_target_key = _normalize_nested_tuple(record.get("object_target_key"))
        if not _object_target_key_is_specific(object_target_key):
            continue
        refs = tuple(str(ref) for ref in record.get("evidence_refs") or ())
        if refs:
            resolved_refs.add(refs)
    return tuple(refs for refs in expected_refs if refs not in resolved_refs)


def _completed_evidence_matches_action(
    evidence_summary: Mapping[str, Any],
    action: Mapping[str, Any],
) -> bool:
    if not isinstance(evidence_summary, Mapping):
        return False
    evidence = evidence_summary.get("evidence")
    if not isinstance(evidence, Mapping):
        evidence = evidence_summary
    if evidence_summary.get("object_derived") is not True and evidence.get("object_derived") is not True:
        return False
    if str(evidence_summary.get("status") or evidence.get("status") or "") not in {
        "complete",
        "completed",
        "proven",
    }:
        return False
    proof_kind = (
        evidence_summary.get("proof_kind")
        or evidence.get("recovery_proof_kind")
        or evidence.get("proof_kind")
    )
    object_target_key = _normalize_nested_tuple(
        evidence_summary.get("object_target_key") or evidence.get("object_target_key")
    )
    action_target_key = _normalize_nested_tuple(action.get("object_target_key"))
    if not _object_target_key_is_specific(object_target_key):
        return False
    if (
        str(evidence_summary.get("reason_id") or evidence.get("reason_id") or MISSING_SENTINEL)
        != str(action.get("reason_id") or MISSING_SENTINEL)
        or str(evidence_summary.get("proof_stage") or evidence.get("proof_stage") or MISSING_SENTINEL)
        != str(action.get("proof_stage") or MISSING_SENTINEL)
        or str(proof_kind or MISSING_SENTINEL)
        != str(action.get("proof_kind") or MISSING_SENTINEL)
        or str(evidence_summary.get("evidence_kind") or evidence.get("evidence_kind") or MISSING_SENTINEL)
        != str(action.get("evidence_kind") or MISSING_SENTINEL)
    ):
        return False
    if _completed_evidence_has_active_blocker(evidence):
        return False
    expected_id = build_proof_obligation_id(
        action.get("reason_id"),
        action.get("proof_stage"),
        action.get("proof_kind"),
        action.get("evidence_kind"),
        object_target_key,
    )
    provided_id = _normalize_nested_tuple(
        evidence_summary.get("proof_obligation_id") or evidence.get("proof_obligation_id")
    )
    if provided_id != expected_id:
        return False
    if object_target_key == action_target_key:
        return expected_id == _normalize_nested_tuple(action.get("proof_obligation_id"))
    return _completed_evidence_supersedes_frozen_return_coverage_action(
        evidence,
        action,
        current_target_key=object_target_key,
        frozen_target_key=action_target_key,
    )


def _completed_evidence_supersedes_frozen_return_coverage_action(
    evidence: Mapping[str, Any],
    action: Mapping[str, Any],
    *,
    current_target_key: Any,
    frozen_target_key: Any,
) -> bool:
    if not _object_target_key_is_specific(frozen_target_key):
        return False
    if not _return_coverage_targets_share_fixed_identity(
        current_target_key,
        frozen_target_key,
    ):
        return False
    if str(evidence.get("coverage_status") or MISSING_SENTINEL) != "covered":
        return False
    expected_frozen_id = build_proof_obligation_id(
        action.get("reason_id"),
        action.get("proof_stage"),
        action.get("proof_kind"),
        action.get("evidence_kind"),
        frozen_target_key,
    )
    return _normalize_nested_tuple(action.get("proof_obligation_id")) == expected_frozen_id


def _return_coverage_targets_share_fixed_identity(left: Any, right: Any) -> bool:
    left = _normalize_nested_tuple(left)
    right = _normalize_nested_tuple(right)
    if not (
        isinstance(left, tuple)
        and isinstance(right, tuple)
        and len(left) == 7
        and len(right) == 7
    ):
        return False
    return left[:5] == right[:5]


def _completed_evidence_has_active_blocker(evidence: Mapping[str, Any]) -> bool:
    for field_name in (
        "sat_unsafety_reasons",
        "coverage_gap_reasons",
        "unsupported_effect_reasons",
        "active_unsafety_reasons",
        "active_coverage_gaps",
        "active_coverage_gap_reasons",
        "active_unsupported_effects",
        "unsupported_call_effect_reasons",
        "unsupported_memory_effect_reasons",
    ):
        if evidence.get(field_name):
            return True
    return False


def _materialize_retired_transition(
    raw_entry: Mapping[str, Any],
    current_records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
    baseline_records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
    *,
    require_current_expected_movements: bool = True,
) -> Dict[str, Any]:
    category = str(raw_entry["category"])
    function = str(raw_entry["function"])
    binary_pair = _canonical_binary_pair(str(raw_entry["binary_pair"]))
    key = (category, function, binary_pair)
    baseline = _observation(baseline_records.get(key))
    current = _observation(current_records.get(key))
    entry: Dict[str, Any] = {
        **dict(raw_entry),
        "binary_pair": binary_pair,
        "left_binary_id": binary_pair.split("_", 1)[0],
        "right_binary_id": binary_pair.split("_", 1)[1],
        "baseline_observation": baseline,
        "current_observation": current,
        "final_result_invariant": {
            "baseline_final_result": baseline.get("final_result") or MISSING_SENTINEL,
            "current_final_result": current.get("final_result") or MISSING_SENTINEL,
            "final_result_unchanged_unknown": (
                baseline.get("final_result") == STATUS_UNKNOWN
                and current.get("final_result") == STATUS_UNKNOWN
            ),
            "false_eq": (
                baseline.get("final_result") == STATUS_EQ
                or current.get("final_result") == STATUS_EQ
            ),
            "timeout": (
                baseline.get("final_result") == STATUS_TIMEOUT
                or current.get("final_result") == STATUS_TIMEOUT
            ),
        },
    }
    failures = []
    retired_reason_id = str(raw_entry.get("retired_reason_id") or MISSING_SENTINEL)
    reclassified_to_reason_id = str(raw_entry.get("reclassified_to_reason_id") or MISSING_SENTINEL)
    for label, observation in (("baseline", baseline), ("current", current)):
        if observation.get("log_status") == "missing":
            failures.append(f"{label}_log_missing")
            continue
        if not _transition_observation_direction_matches(raw_entry, observation, label):
            failures.append(f"{label}_observed_direction_mismatch")
        if not _transition_observation_payload_direction_matches(raw_entry, observation, label):
            failures.append(f"{label}_observed_payload_direction_mismatch")
        if observation.get("final_result") != STATUS_UNKNOWN:
            failures.append(f"{label}_not_unknown")
    baseline_reasons = set(baseline.get("observed_reason_ids") or ())
    current_reasons = set(current.get("observed_reason_ids") or ())
    if retired_reason_id not in baseline_reasons:
        failures.append(f"baseline_missing_retired_{retired_reason_id}")
    baseline_expected_reason_tuple = _expected_transition_tuple(
        raw_entry,
        "baseline_expected_reason_tuple",
    )
    if (
        baseline_expected_reason_tuple is None
        or baseline_expected_reason_tuple
        not in _observation_tuple_set(baseline, "reason_record_tuples")
    ):
        failures.append(f"baseline_retired_reason_tuple_missing:{retired_reason_id}")
    baseline_expected_proof_action_tuple = _expected_transition_tuple(
        raw_entry,
        "baseline_expected_proof_action_tuple",
    )
    if (
        baseline_expected_proof_action_tuple is None
        or baseline_expected_proof_action_tuple
        not in _observation_tuple_set(baseline, "proof_action_tuples")
    ):
        failures.append(f"baseline_retired_proof_action_tuple_missing:{retired_reason_id}")
    if retired_reason_id in current_reasons:
        failures.append(f"current_retired_reason_still_active:{retired_reason_id}")
    if baseline_expected_reason_tuple in _observation_tuple_set(current, "reason_record_tuples"):
        failures.append(f"current_retired_reason_tuple_still_active:{retired_reason_id}")
    if baseline_expected_proof_action_tuple in _observation_tuple_set(current, "proof_action_tuples"):
        failures.append(f"current_retired_proof_action_tuple_still_active:{retired_reason_id}")
    if reclassified_to_reason_id not in current_reasons:
        failures.append(f"current_missing_reclassified_{reclassified_to_reason_id}")
    if require_current_expected_movements:
        movement_entry = {
            "expected_movements": raw_entry.get("current_expected_movements") or (),
        }
        failures.extend(_expected_movement_failures(movement_entry, current, "current"))
    entry["selection_status"] = "retired_by_reclassification" if not failures else "failed"
    entry["selection_failures"] = sorted(set(failures))
    return entry


def _expected_transition_tuple(
    entry: Mapping[str, Any],
    field_name: str,
) -> Optional[Tuple[str, ...]]:
    value = entry.get(field_name)
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes)):
        return None
    normalized = tuple(str(item) for item in value)
    if len(normalized) != 7:
        return None
    return normalized


def _observation_tuple_set(
    observation: Mapping[str, Any],
    field_name: str,
) -> set[Tuple[str, ...]]:
    return {
        tuple(str(item) for item in value)
        for value in observation.get(field_name) or ()
        if isinstance(value, Sequence) and not isinstance(value, (str, bytes))
    }


def _observation(record: Optional[Mapping[str, Any]]) -> Dict[str, Any]:
    if not record:
        return {"log_status": "missing"}
    payload = record["payload"]
    raw_reason_payloads = _extract_final_unknown_reason_payloads(payload)
    reason_records = _extract_final_unknown_reasons(payload)
    proof_action_records = _proof_action_records(
        payload,
        raw_reason_payloads,
        reason_records,
    )
    return {
        "log_status": "present",
        "log_path": record["relative_log_path"],
        "log_sha256": record["log_sha256"],
        "observed_left_binary_id": record["observed_left_binary_id"],
        "observed_right_binary_id": record["observed_right_binary_id"],
        "observed_binary1_name": payload.get("binary1_name") or MISSING_SENTINEL,
        "observed_binary2_name": payload.get("binary2_name") or MISSING_SENTINEL,
        "observed_function1_name": payload.get("function1_name") or MISSING_SENTINEL,
        "observed_function2_name": payload.get("function2_name") or MISSING_SENTINEL,
        "final_result": classify_result_payload(payload),
        "decision_gated_by_pending_proof": bool(payload.get("decision_gated_by_pending_proof")),
        "completed_recovery_proof_evidence": _completed_recovery_proof_summaries(payload),
        "observed_reason_ids": sorted({reason.reason_id for reason in reason_records}),
        "reason_record_tuples": [
            list(_global_reason_tuple_from_record(reason, UnknownCountKind.REASON_RECORD.value))
            for reason in reason_records
            if reason.reason_id in OBSERVED_RETURN_REASON_IDS
        ],
        "reason_records": [
            _reason_record_summary(reason, raw_reason_payload=raw_reason)
            for raw_reason, reason in zip(raw_reason_payloads, reason_records)
            if reason.reason_id in OBSERVED_RETURN_REASON_IDS
        ],
        "proof_action_tuples": [
            list(_global_reason_tuple_from_action(record["action"]))
            for record in proof_action_records
            if getattr(record["action"], "reason_id", None) in OBSERVED_RETURN_REASON_IDS
        ],
        "proof_actions": [
            _proof_action_summary(
                record["action"],
                raw_proof_obligation_id_present=record["raw_proof_obligation_id_present"],
            )
            for record in proof_action_records
            if getattr(record["action"], "reason_id", None) in OBSERVED_RETURN_REASON_IDS
        ],
        "return_case_grid_diagnostic": _return_case_grid_diagnostic(payload),
    }


def _completed_recovery_proof_summaries(payload: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    raw_items = payload.get("completed_recovery_proof_evidence") or ()
    if not isinstance(raw_items, Sequence) or isinstance(raw_items, (str, bytes)):
        return ()
    summaries = []
    for raw_item in raw_items:
        if not isinstance(raw_item, Mapping):
            continue
        wrapper = raw_item
        evidence = raw_item.get("evidence")
        if not isinstance(evidence, Mapping):
            evidence = raw_item
            wrapper = {}
        proof_kind = evidence.get("recovery_proof_kind") or evidence.get("proof_kind") or MISSING_SENTINEL
        summaries.append(
            {
                "side": wrapper.get("side") or evidence.get("side") or MISSING_SENTINEL,
                "function_name": wrapper.get("function_name") or evidence.get("function_name") or MISSING_SENTINEL,
                "binary_name": wrapper.get("binary_name") or evidence.get("binary_name") or MISSING_SENTINEL,
                "binary_id": wrapper.get("binary_id") or evidence.get("binary_id") or MISSING_SENTINEL,
                "reason_id": evidence.get("reason_id") or MISSING_SENTINEL,
                "proof_stage": evidence.get("proof_stage") or MISSING_SENTINEL,
                "proof_kind": proof_kind,
                "evidence_kind": evidence.get("evidence_kind") or MISSING_SENTINEL,
                "status": evidence.get("status") or MISSING_SENTINEL,
                "object_derived": evidence.get("object_derived") is True,
                "object_target_key": evidence.get("object_target_key"),
                "proof_obligation_id": evidence.get("proof_obligation_id"),
                "evidence": dict(evidence),
            }
        )
    return summaries


def _extract_final_unknown_reason_payloads(payload: Mapping[str, Any]) -> Tuple[Any, ...]:
    debug_trace = payload.get("debug_trace")
    if isinstance(debug_trace, Mapping) and debug_trace.get("final_result") is None:
        attempts = debug_trace.get("attempts") or ()
        for attempt in reversed(tuple(attempts)):
            if not isinstance(attempt, Mapping):
                continue
            if (
                attempt.get("result") is None
                and str(attempt.get("transition_reason")) in _FINAL_UNKNOWN_TRANSITIONS
            ):
                return tuple(attempt.get("unknown_reasons") or ())
    return tuple(payload.get("unknown_reasons") or ())


def _proof_action_records(
    payload: Mapping[str, Any],
    raw_reason_payloads: Sequence[Any],
    reason_records: Sequence[Any],
) -> Sequence[Dict[str, Any]]:
    raw_actions = _extract_final_unknown_recovery_action_payloads(payload)
    if raw_actions:
        actions = coerce_unknown_recovery_actions(raw_actions)
        return [
            {
                "action": action,
                "raw_proof_obligation_id_present": _raw_proof_obligation_id_present(raw_action),
            }
            for raw_action, action in zip(raw_actions, actions)
        ]

    records: list[Dict[str, Any]] = []
    for raw_reason, reason in zip(raw_reason_payloads, reason_records):
        for action in build_unknown_recovery_actions((reason,)):
            records.append(
                {
                    "action": action,
                    "raw_proof_obligation_id_present": False,
                }
            )
    return records


def _extract_final_unknown_recovery_action_payloads(payload: Mapping[str, Any]) -> Tuple[Any, ...]:
    raw_actions = payload.get("unknown_recovery_actions")
    if isinstance(raw_actions, Sequence) and not isinstance(raw_actions, (str, bytes)) and raw_actions:
        return tuple(raw_actions)
    debug_trace = payload.get("debug_trace")
    if isinstance(debug_trace, Mapping) and debug_trace.get("final_result") is None:
        debug_actions = debug_trace.get("unknown_recovery_actions")
        if (
            isinstance(debug_actions, Sequence)
            and not isinstance(debug_actions, (str, bytes))
            and debug_actions
        ):
            return tuple(debug_actions)
    return ()


def _raw_proof_obligation_id_present(raw_reason: Any) -> bool:
    return (
        isinstance(raw_reason, Mapping)
        and "proof_obligation_id" in raw_reason
        and raw_reason.get("proof_obligation_id") is not None
    )


def _reason_record_summary(reason: Any, *, raw_reason_payload: Any = None) -> Dict[str, Any]:
    return {
        "tuple": list(_global_reason_tuple_from_record(reason, UnknownCountKind.REASON_RECORD.value)),
        "reason_id": reason.reason_id,
        "decision_effect": reason.decision_effect,
        "reason_scope": reason.reason_scope,
        "recovery_proof_kind": reason.recovery_proof_kind or MISSING_SENTINEL,
        "proof_stage": reason.proof_stage or MISSING_SENTINEL,
        "action_status": reason.action_status or MISSING_SENTINEL,
        "stage": reason.stage or MISSING_SENTINEL,
        "aggregation_unit": reason.aggregation_unit or MISSING_SENTINEL,
        "pair_or_case": reason.pair_or_case or MISSING_SENTINEL,
        "detail": reason.detail or MISSING_SENTINEL,
        "evidence_refs": list(reason.evidence_refs or ()),
        "object_target_key": reason.object_target_key,
        "proof_obligation_id": reason.proof_obligation_id,
        "raw_proof_obligation_id_present": _raw_proof_obligation_id_present(raw_reason_payload),
        "recovery_action": reason.recovery_action or MISSING_SENTINEL,
        "recovery_proof_obligations": [
            dict(obligation)
            for obligation in (reason.recovery_proof_obligations or ())
            if isinstance(obligation, Mapping)
        ],
    }


def _proof_action_summary(
    action: Any,
    *,
    raw_proof_obligation_id_present: bool = False,
) -> Dict[str, Any]:
    return {
        "tuple": list(_global_reason_tuple_from_action(action)),
        "reason_id": str(getattr(action, "reason_id", MISSING_SENTINEL)),
        "decision_effect": str(getattr(action, "decision_effect", MISSING_SENTINEL)),
        "reason_scope": str(getattr(action, "reason_scope", MISSING_SENTINEL)),
        "proof_kind": str(getattr(action, "proof_kind", MISSING_SENTINEL)),
        "proof_stage": str(getattr(action, "proof_stage", MISSING_SENTINEL)),
        "status": str(getattr(action, "status", MISSING_SENTINEL)),
        "aggregation_unit": str(getattr(action, "aggregation_unit", MISSING_SENTINEL)),
        "stage": str(getattr(action, "stage", MISSING_SENTINEL) or MISSING_SENTINEL),
        "pair_or_case": str(getattr(action, "pair_or_case", MISSING_SENTINEL) or MISSING_SENTINEL),
        "required_evidence": list(getattr(action, "required_evidence", ()) or ()),
        "evidence_kind": str(getattr(action, "evidence_kind", MISSING_SENTINEL) or MISSING_SENTINEL),
        "object_target_key": getattr(action, "object_target_key", None),
        "proof_obligation_id": getattr(action, "proof_obligation_id", None),
        "raw_proof_obligation_id_present": raw_proof_obligation_id_present,
        "recovery_action": str(getattr(action, "recovery_action", MISSING_SENTINEL) or MISSING_SENTINEL),
        "evidence_refs": list(getattr(action, "evidence_refs", ()) or ()),
        "detail": str(getattr(action, "detail", MISSING_SENTINEL) or MISSING_SENTINEL),
    }


def _return_case_grid_diagnostic(payload: Mapping[str, Any]) -> Dict[str, Any]:
    debug_trace = payload.get("debug_trace")
    attempts = debug_trace.get("attempts") if isinstance(debug_trace, Mapping) else ()
    grid_attempts = []
    for attempt in attempts or ():
        if not isinstance(attempt, Mapping):
            continue
        rows = _return_case_rows(str(attempt.get("final_smt") or ""))
        if not rows:
            continue
        pairwise = attempt.get("pairwise_decisive")
        solver_results = attempt.get("solver_results")
        grid_attempts.append(
            {
                "attempt_id": attempt.get("attempt_id"),
                "phase": attempt.get("phase"),
                "transition_reason": attempt.get("transition_reason"),
                "pairwise_decisive": dict(pairwise) if isinstance(pairwise, Mapping) else None,
                "solver_statuses": _solver_statuses(solver_results),
                "rows": rows,
            }
        )
    stats = payload.get("pairwise_stats")
    return {
        "source_kind": "raw_smt_diagnostic",
        "object_derived": False,
        "evidence_role": "diagnostic_only",
        "pairwise_stats": dict(stats) if isinstance(stats, Mapping) else {},
        "attempts": grid_attempts,
    }


def _return_case_rows(final_smt: str) -> Sequence[Mapping[str, Any]]:
    rows = []
    current: Optional[Dict[str, Any]] = None
    for line in final_smt.splitlines():
        pair_match = _PAIR_RE.match(line)
        if pair_match:
            current = {
                "pair": [int(pair_match.group(1)), int(pair_match.group(2))],
                "case1": None,
                "case2": None,
            }
            rows.append(current)
            continue
        case_match = _CASE_RE.match(line)
        if case_match and current is not None:
            target = "case1" if case_match.group(1) == "Case1" else "case2"
            current[target] = {
                "index": int(case_match.group(2)),
                "condition": case_match.group(3),
            }
    return rows


def _solver_statuses(solver_results: Any) -> Sequence[str]:
    if not isinstance(solver_results, Mapping):
        return []
    statuses = []
    for item in solver_results.get("all_results") or solver_results.get("results") or ():
        if isinstance(item, Mapping) and item.get("status") is not None:
            statuses.append(str(item.get("status")))
    return statuses


def _expected_movement_failures(
    entry: Mapping[str, Any],
    observation: Mapping[str, Any],
    label: str,
) -> Sequence[str]:
    movements = entry.get("expected_movements")
    if not isinstance(movements, Sequence) or isinstance(movements, (str, bytes)) or not movements:
        return ["expected_movements_missing"]
    failures = []
    reason_records = observation.get("reason_records") or ()
    proof_actions = observation.get("proof_actions") or ()
    for movement in movements:
        if not isinstance(movement, Mapping):
            failures.append(f"{label}_expected_movement_not_object")
            continue
        movement_id = str(movement.get("id") or "unknown")
        tuple_key = _movement_tuple(movement)
        if tuple_key is None:
            failures.append(f"{label}_expected_movement_tuple_invalid:{movement_id}")
            continue
        count_kind = movement.get("count_kind")
        if count_kind == UnknownCountKind.REASON_RECORD.value:
            tuple_candidates = _records_matching_tuple(reason_records, tuple_key)
            if not tuple_candidates:
                failures.append(f"{label}_expected_reason_tuple_missing:{movement_id}")
                continue
            scoped_candidates = _records_matching_scope(tuple_candidates, movement)
            if not scoped_candidates:
                failures.append(f"{label}_expected_reason_scope_mismatch:{movement_id}")
                continue
            candidates = _records_matching_evidence_refs(scoped_candidates, movement)
            if not candidates:
                failures.append(f"{label}_expected_reason_evidence_refs_mismatch:{movement_id}")
                continue
            if not _single_movement_candidate(candidates):
                failures.append(f"{label}_expected_reason_candidate_ambiguous:{movement_id}")
                continue
            candidate = candidates[0]
            if not _record_has_object_target(candidate, movement):
                failures.append(f"{label}_expected_reason_object_target_mismatch:{movement_id}")
        elif count_kind == UnknownCountKind.PROOF_ACTION.value:
            tuple_candidates = _records_matching_tuple(proof_actions, tuple_key)
            if not tuple_candidates:
                failures.append(f"{label}_expected_proof_action_tuple_missing:{movement_id}")
                continue
            expected_evidence = tuple(str(item) for item in movement.get("required_evidence") or ())
            if not expected_evidence:
                failures.append(f"{label}_expected_proof_action_evidence_missing:{movement_id}")
                continue
            scoped_candidates = _records_matching_scope(tuple_candidates, movement)
            if not scoped_candidates:
                failures.append(f"{label}_expected_proof_action_scope_mismatch:{movement_id}")
                continue
            candidates = _records_matching_evidence_refs(scoped_candidates, movement)
            if not candidates:
                failures.append(f"{label}_expected_proof_action_evidence_refs_mismatch:{movement_id}")
                continue
            if not _single_movement_candidate(candidates):
                failures.append(f"{label}_expected_proof_action_candidate_ambiguous:{movement_id}")
                continue
            candidate = candidates[0]
            if not _proof_action_has_required_evidence(candidate, expected_evidence):
                failures.append(f"{label}_expected_proof_action_evidence_mismatch:{movement_id}")
            if not _record_has_object_target(candidate, movement):
                failures.append(f"{label}_expected_proof_action_object_target_mismatch:{movement_id}")
            if not _proof_action_has_proof_id(candidate, movement):
                failures.append(f"{label}_expected_proof_action_id_mismatch:{movement_id}")
        else:
            failures.append(f"{label}_expected_movement_count_kind_invalid:{movement_id}")
    return failures


def _observation_direction_matches(
    entry: Mapping[str, Any],
    observation: Mapping[str, Any],
) -> bool:
    return (
        str(observation.get("observed_left_binary_id") or MISSING_SENTINEL)
        == str(entry.get("expected_observed_left_binary_id") or MISSING_SENTINEL)
        and str(observation.get("observed_right_binary_id") or MISSING_SENTINEL)
        == str(entry.get("expected_observed_right_binary_id") or MISSING_SENTINEL)
    )


def _observation_payload_direction_matches(
    entry: Mapping[str, Any],
    observation: Mapping[str, Any],
) -> bool:
    return (
        str(observation.get("observed_binary1_name") or MISSING_SENTINEL)
        == str(entry.get("expected_observed_binary1_name") or MISSING_SENTINEL)
        and str(observation.get("observed_binary2_name") or MISSING_SENTINEL)
        == str(entry.get("expected_observed_binary2_name") or MISSING_SENTINEL)
    )


def _transition_observation_direction_matches(
    entry: Mapping[str, Any],
    observation: Mapping[str, Any],
    label: str,
) -> bool:
    return (
        str(observation.get("observed_left_binary_id") or MISSING_SENTINEL)
        == str(entry.get(f"expected_{label}_observed_left_binary_id") or MISSING_SENTINEL)
        and str(observation.get("observed_right_binary_id") or MISSING_SENTINEL)
        == str(entry.get(f"expected_{label}_observed_right_binary_id") or MISSING_SENTINEL)
    )


def _transition_observation_payload_direction_matches(
    entry: Mapping[str, Any],
    observation: Mapping[str, Any],
    label: str,
) -> bool:
    return (
        str(observation.get("observed_binary1_name") or MISSING_SENTINEL)
        == str(entry.get(f"expected_{label}_binary1_name") or MISSING_SENTINEL)
        and str(observation.get("observed_binary2_name") or MISSING_SENTINEL)
        == str(entry.get(f"expected_{label}_binary2_name") or MISSING_SENTINEL)
    )


def _movement_tuple(movement: Mapping[str, Any]) -> Optional[Tuple[str, ...]]:
    tuple_value = movement.get("tuple")
    if not isinstance(tuple_value, Sequence) or isinstance(tuple_value, (str, bytes)):
        return None
    normalized = tuple(str(item) for item in tuple_value)
    if len(normalized) != 7:
        return None
    return normalized


def _records_matching_tuple(
    records: Any,
    tuple_key: Tuple[str, ...],
) -> Sequence[Mapping[str, Any]]:
    matches = []
    for record in records:
        if not isinstance(record, Mapping):
            continue
        if tuple(str(item) for item in record.get("tuple") or ()) != tuple_key:
            continue
        matches.append(record)
    return matches


def _records_matching_scope(
    records: Any,
    movement: Mapping[str, Any],
) -> Sequence[Mapping[str, Any]]:
    expected_scope = _movement_scope(movement)
    matches = []
    for record in records:
        if not isinstance(record, Mapping):
            continue
        actual_scope = (
            _normalize_optional(record.get("aggregation_unit")),
            _normalize_optional(record.get("stage")),
            _normalize_optional(record.get("pair_or_case")),
        )
        if actual_scope == expected_scope:
            matches.append(record)
    return matches


def _records_matching_evidence_refs(
    records: Any,
    movement: Mapping[str, Any],
) -> Sequence[Mapping[str, Any]]:
    expected_refs = movement.get("expected_evidence_refs")
    if expected_refs is None:
        return tuple(record for record in records if isinstance(record, Mapping))
    normalized_expected_refs = tuple(str(ref) for ref in expected_refs or ())
    matches = []
    for record in records:
        if not isinstance(record, Mapping):
            continue
        actual_refs = tuple(str(ref) for ref in record.get("evidence_refs") or ())
        if actual_refs == normalized_expected_refs:
            matches.append(record)
    return matches


def _single_movement_candidate(records: Any) -> bool:
    return isinstance(records, Sequence) and not isinstance(records, (str, bytes)) and len(records) == 1


def _record_has_object_target(
    record: Mapping[str, Any],
    movement: Mapping[str, Any],
) -> bool:
    required_kind = movement.get("required_object_target_kind")
    if required_kind is None:
        return True
    object_target_key = _normalize_nested_tuple(record.get("object_target_key"))
    return (
        _nested_tuple_kind(object_target_key) == str(required_kind)
        and _object_target_key_is_specific(object_target_key)
    )


def _proof_action_has_required_evidence(
    action: Mapping[str, Any],
    expected_evidence: Tuple[str, ...],
) -> bool:
    actual = tuple(str(item) for item in action.get("required_evidence") or ())
    return actual == expected_evidence


def _proof_action_has_proof_id(
    action: Mapping[str, Any],
    movement: Mapping[str, Any],
) -> bool:
    if not movement.get("require_proof_obligation_id"):
        return True
    if action.get("raw_proof_obligation_id_present") is not True:
        return False
    object_target_key = _normalize_nested_tuple(action.get("object_target_key"))
    if object_target_key is None or not _object_target_key_is_specific(object_target_key):
        return False
    expected_id = build_proof_obligation_id(
        action.get("reason_id"),
        action.get("proof_stage"),
        action.get("proof_kind"),
        action.get("evidence_kind"),
        object_target_key,
    )
    return _normalize_nested_tuple(action.get("proof_obligation_id")) == expected_id


def _nested_tuple_kind(value: Any) -> Optional[str]:
    normalized = _normalize_nested_tuple(value)
    if isinstance(normalized, tuple) and normalized:
        return str(normalized[0])
    return None


def _normalize_nested_tuple(value: Any) -> Any:
    if value is None:
        return None
    if isinstance(value, (list, tuple)):
        return tuple(_normalize_nested_tuple(item) for item in value)
    return value


def _object_target_key_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if not isinstance(normalized, tuple) or not normalized:
        return False
    if normalized[0] == "return_coverage":
        return _return_coverage_key_is_specific(normalized)
    return False


def _return_coverage_key_is_specific(value: Tuple[Any, ...]) -> bool:
    if _nested_contains_forbidden_identity_atom(value):
        return False
    if (
        len(value) == 8
        and isinstance(value[1], tuple)
        and len(value[1]) == 2
        and value[1][0] == "target_schema_version"
        # v2 is accepted for existing lane artifacts; v3 is the strict
        # return-coverage identity schema used by new proof targets.
        and value[1][1] in {2, 3}
    ):
        (
            _kind,
            _schema,
            side_label,
            function_identity,
            reason_kind,
            return_storage_key,
            return_partition_key,
            guard_disjunction_key,
        ) = value
        return all(
            (
                side_label in {"function1", "function2"},
                _function_identity_key_is_specific(function_identity),
                reason_kind in {"return_coverage_gap", "return_coverage_inconclusive"},
                _return_storage_key_is_specific(return_storage_key),
                _return_partition_identity_key_is_specific(return_partition_key),
                _guard_disjunction_identity_key_is_specific(guard_disjunction_key),
            )
        )
    if len(value) != 7:
        return False
    (
        _kind,
        side_label,
        function_key,
        reason_kind,
        return_storage_key,
        return_partition_key,
        guard_disjunction_key,
    ) = value
    return all(
        (
            side_label in {"function1", "function2"},
            _analysis_key_is_specific(function_key),
            reason_kind in TARGET_REASON_IDS,
            _return_storage_key_is_specific(return_storage_key),
            _return_partition_key_is_specific(return_partition_key),
            _guard_disjunction_key_is_specific(guard_disjunction_key),
        )
    )


def _function_identity_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 8 or value[0] != "function_identity":
        return False
    schema = value[1]
    binary_identity = value[2]
    entry_offset = value[4]
    signature = value[6]
    if not (
        isinstance(schema, tuple)
        and len(schema) == 2
        and schema[0] == "identity_schema_version"
        and _int_like_is_specific(schema[1])
    ):
        return False
    if not _binary_identity_key_is_specific(binary_identity):
        return False
    if not (
        isinstance(entry_offset, tuple)
        and len(entry_offset) == 2
        and entry_offset[0] == "entry_offset"
        and _address_like_is_specific(entry_offset[1])
    ):
        return False
    return isinstance(signature, tuple) and signature and signature[0] == "signature"


def _binary_identity_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 2 or value[0] != "binary_identity":
        return False
    fields = {
        item[0]: item[1]
        for item in value[1:]
        if isinstance(item, tuple) and len(item) == 2
    }
    binary_id = fields.get("binary_id")
    language_id = fields.get("language_id")
    return _binary_id_is_specific(binary_id) and isinstance(language_id, str) and bool(language_id.strip())


def _return_partition_identity_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 3 or value[0] != "return_partition_identity":
        return False
    schema = value[1]
    cases = value[2]
    if not (
        isinstance(schema, tuple)
        and len(schema) == 2
        and schema[0] == "normalization_schema_version"
        and _int_like_is_specific(schema[1])
    ):
        return False
    if not isinstance(cases, tuple) or not cases:
        return False
    return all(_return_case_identity_key_is_specific(case) for case in cases)


def _return_case_identity_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 8 or value[0] != "return_case_identity":
        return False
    fields = {
        item[0]: item[1]
        for item in value[1:]
        if isinstance(item, tuple) and len(item) == 2
    }
    pcode_sequence = fields.get("pcode_sequence")
    pcode_identity = fields.get("pcode_identity")
    return_value = fields.get("return_value")
    case_miss_formula = fields.get("case_miss_formula")
    guards = fields.get("guards")
    if pcode_sequence is not None:
        if not _pcode_ref_is_specific(pcode_sequence):
            return False
    elif pcode_identity is not None:
        if not _nested_has_specific_leaf(pcode_identity):
            return False
    else:
        return False
    if not _nested_has_specific_leaf(return_value) or _nested_contains_log_prose(return_value):
        return False
    if case_miss_formula is not None and (
        not _nested_has_specific_leaf(case_miss_formula)
        or _nested_contains_log_prose(case_miss_formula)
    ):
        return False
    if not isinstance(guards, tuple):
        return False
    return all(_return_guard_key_is_specific(guard) for guard in guards)


def _guard_disjunction_identity_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 3 or value[0] != "guard_disjunction_identity":
        return False
    schema = value[1]
    cases = value[2]
    if not (
        isinstance(schema, tuple)
        and len(schema) == 2
        and schema[0] == "normalization_schema_version"
        and _int_like_is_specific(schema[1])
    ):
        return False
    if not isinstance(cases, tuple):
        return False
    for case in cases:
        if not isinstance(case, tuple) or len(case) != 2 or case[0] != "return_case_guard_identity":
            return False
        guards = case[1]
        if not isinstance(guards, tuple):
            return False
        if not all(_return_guard_key_is_specific(guard) for guard in guards):
            return False
    return True


def _analysis_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 2:
        return False
    if value[0] == "function_ref":
        return _function_ref_key_is_specific(value[1])
    if value[0] == "entry_point":
        return False
    return False


def _function_ref_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 3:
        return False
    kind, binary_id, address_offset = value[:3]
    if kind not in {"function", "code_address"}:
        return False
    return _binary_id_is_specific(binary_id) and _address_like_is_specific(address_offset)


def _return_storage_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 5 or value[0] != "return_storage":
        return False
    surface_kind = value[1]
    bit_width = value[2]
    if surface_kind not in {"return_value", "memory_effect"}:
        return False
    try:
        return int(bit_width) > 0
    except (TypeError, ValueError):
        return False


def _return_partition_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 2 or value[0] != "return_partition":
        return False
    cases = value[1]
    if not isinstance(cases, tuple) or not cases:
        return False
    return all(_return_case_key_is_specific(case) for case in cases)


def _return_case_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 8 or value[0] != "return_case":
        return False
    try:
        int(value[1])
    except (TypeError, ValueError):
        return False
    pcode_ref = value[3]
    pcode_identity = value[4]
    if pcode_ref is not None:
        if not _pcode_ref_is_specific(pcode_ref):
            return False
    elif pcode_identity is not None:
        if not _pcode_ref_is_specific(pcode_identity):
            return False
    else:
        return False
    if not _nested_has_specific_leaf(value[6]):
        return False
    if _nested_contains_log_prose(value[6]):
        return False
    guards = value[7]
    return isinstance(guards, tuple) and all(_return_guard_key_is_specific(guard) for guard in guards)


def _guard_disjunction_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 2 or value[0] != "guard_disjunction":
        return False
    cases = value[1]
    if not isinstance(cases, tuple):
        return False
    for case in cases:
        if not isinstance(case, tuple) or len(case) != 2:
            return False
        try:
            int(case[0])
        except (TypeError, ValueError):
            return False
        guards = case[1]
        if not isinstance(guards, tuple):
            return False
        if not all(_return_guard_key_is_specific(guard) for guard in guards):
            return False
    return True


def _return_guard_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 4 or value[0] != "return_guard":
        return False
    if not isinstance(value[1], bool):
        return False
    if _nested_contains_log_prose(value[2]) or _nested_contains_log_prose(value[3]):
        return False
    return _nested_has_specific_leaf(value[2]) and _nested_has_specific_leaf(value[3])


def _pcode_ref_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 8 or value[0] != "pcode_op":
        return False
    if _nested_contains_log_prose(value):
        return False
    (
        _kind,
        binary_id,
        function_entry,
        seq_target,
        seq_time,
        seq_order,
        opcode,
        local_ordinal,
    ) = value
    return all(
        (
            _binary_id_is_specific(binary_id),
            _pcode_address_ref_is_specific(function_entry, "function_entry"),
            _pcode_address_ref_is_specific(seq_target, "seq_target"),
            _int_like_is_specific(seq_time),
            _int_like_is_specific(seq_order),
            opcode is not None,
            _int_like_is_specific(local_ordinal),
        )
    )


def _binary_id_is_specific(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip()) and not value.strip().isdecimal()


def _pcode_address_ref_is_specific(value: Any, expected_kind: str) -> bool:
    if not isinstance(value, tuple) or len(value) != 3 or value[0] != expected_kind:
        return False
    return isinstance(value[1], str) and bool(value[1]) and _address_like_is_specific(value[2])


def _address_like_is_specific(value: Any) -> bool:
    if value is None or value == "" or value == MISSING_SENTINEL:
        return False
    if isinstance(value, str):
        if _nested_contains_log_prose(value):
            return False
        text = value.strip()
        if not text:
            return False
        try:
            int(text, 0)
            return True
        except ValueError:
            return False
    return _int_like_is_specific(value)


def _int_like_is_specific(value: Any) -> bool:
    if isinstance(value, bool) or value is None or value == "" or value == MISSING_SENTINEL:
        return False
    try:
        int(value)
        return True
    except (TypeError, ValueError):
        return False


def _nested_has_specific_leaf(value: Any) -> bool:
    if value is None or value == "" or value == MISSING_SENTINEL:
        return False
    if _identity_atom_is_forbidden(value):
        return False
    if isinstance(value, tuple):
        return any(_nested_has_specific_leaf(item) for item in value)
    if isinstance(value, list):
        return any(_nested_has_specific_leaf(item) for item in value)
    return True


def _nested_contains_forbidden_identity_atom(value: Any) -> bool:
    if _identity_atom_is_forbidden(value):
        return True
    if isinstance(value, tuple):
        return any(_nested_contains_forbidden_identity_atom(item) for item in value)
    if isinstance(value, list):
        return any(_nested_contains_forbidden_identity_atom(item) for item in value)
    return False


def _identity_atom_is_forbidden(value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and bool(value)
        and value[0] in {"opaque", "object_id", "program_uid"}
    )


def _nested_contains_log_prose(value: Any) -> bool:
    if isinstance(value, str):
        return any(reason_id in value for reason_id in OBSERVED_RETURN_REASON_IDS)
    if isinstance(value, tuple):
        return any(_nested_contains_log_prose(item) for item in value)
    if isinstance(value, list):
        return any(_nested_contains_log_prose(item) for item in value)
    return False


def _movement_scope(movement: Mapping[str, Any]) -> Tuple[str, str, str]:
    return (
        _normalize_optional(movement.get("aggregation_unit")),
        _normalize_optional(movement.get("stage")),
        _normalize_optional(movement.get("pair_or_case")),
    )


def _normalize_optional(value: Any) -> str:
    if value is None or value == "":
        return MISSING_SENTINEL
    return str(value)


def _retired_reason_inventory(
    *,
    current_records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
    baseline_records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
    transition_entries: Sequence[Mapping[str, Any]],
) -> Dict[str, Any]:
    baseline_transition_records = _retired_transition_record_subset(
        baseline_records,
        transition_entries,
    )
    current_transition_records = _retired_transition_record_subset(
        current_records,
        transition_entries,
    )
    baseline_reason_counts = _reason_record_tuple_counts(baseline_transition_records)
    current_reason_counts = _reason_record_tuple_counts(current_transition_records)
    baseline_action_counts = _proof_action_tuple_counts(baseline_transition_records)
    current_action_counts = _proof_action_tuple_counts(current_transition_records)
    expected_baseline_reason_counts = Counter(
        expected_tuple
        for entry in transition_entries
        for expected_tuple in (_expected_transition_tuple(entry, "baseline_expected_reason_tuple"),)
        if expected_tuple is not None
    )
    expected_baseline_action_counts = Counter(
        expected_tuple
        for entry in transition_entries
        for expected_tuple in (_expected_transition_tuple(entry, "baseline_expected_proof_action_tuple"),)
        if expected_tuple is not None
    )
    expected_current_reason_counts: Counter = Counter()
    expected_current_action_counts: Counter = Counter()
    inventory = {}
    for reason_id in RETIRED_REASON_IDS:
        baseline_reason_subset = _tuple_counter_for_reason(baseline_reason_counts, reason_id)
        current_reason_subset = _tuple_counter_for_reason(current_reason_counts, reason_id)
        expected_baseline_reason_subset = _tuple_counter_for_reason(
            expected_baseline_reason_counts,
            reason_id,
        )
        expected_current_reason_subset = _tuple_counter_for_reason(
            expected_current_reason_counts,
            reason_id,
        )
        baseline_action_subset = _tuple_counter_for_reason(baseline_action_counts, reason_id)
        current_action_subset = _tuple_counter_for_reason(current_action_counts, reason_id)
        expected_baseline_action_subset = _tuple_counter_for_reason(
            expected_baseline_action_counts,
            reason_id,
        )
        expected_current_action_subset = _tuple_counter_for_reason(
            expected_current_action_counts,
            reason_id,
        )
        status_ok = (
            baseline_reason_subset == expected_baseline_reason_subset
            and current_reason_subset == expected_current_reason_subset
            and baseline_action_subset == expected_baseline_action_subset
            and current_action_subset == expected_current_action_subset
        )
        inventory[reason_id] = {
            "inventory_scope": "selected_retired_transitions",
            "baseline_record_count": len(baseline_transition_records),
            "current_record_count": len(current_transition_records),
            "reason_record": {
                "baseline_tuple_counts": _serialize_tuple_counter(baseline_reason_subset),
                "current_tuple_counts": _serialize_tuple_counter(current_reason_subset),
                "expected_baseline_tuple_counts": _serialize_tuple_counter(
                    expected_baseline_reason_subset
                ),
                "expected_current_tuple_counts": _serialize_tuple_counter(
                    expected_current_reason_subset
                ),
            },
            "proof_action": {
                "baseline_tuple_counts": _serialize_tuple_counter(baseline_action_subset),
                "current_tuple_counts": _serialize_tuple_counter(current_action_subset),
                "expected_baseline_tuple_counts": _serialize_tuple_counter(
                    expected_baseline_action_subset
                ),
                "expected_current_tuple_counts": _serialize_tuple_counter(
                    expected_current_action_subset
                ),
            },
            "status": "retired_by_reclassification" if status_ok else "failed",
        }
    return inventory


def _retired_transition_record_subset(
    records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
    transition_entries: Sequence[Mapping[str, Any]],
) -> Dict[Tuple[str, str, str], Mapping[str, Any]]:
    keys = {
        (
            str(entry.get("category") or MISSING_SENTINEL),
            str(entry.get("function") or MISSING_SENTINEL),
            _canonical_binary_pair(str(entry.get("binary_pair") or MISSING_SENTINEL)),
        )
        for entry in transition_entries
    }
    return {key: record for key, record in records.items() if key in keys}


def _reason_record_tuple_counts(
    records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
) -> Counter:
    counts: Counter = Counter()
    for record in records.values():
        payload = record.get("payload")
        if not isinstance(payload, Mapping):
            continue
        for reason in _extract_final_unknown_reasons(payload):
            counts[_global_reason_tuple_from_record(reason, UnknownCountKind.REASON_RECORD.value)] += 1
    return counts


def _proof_action_tuple_counts(
    records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
) -> Counter:
    counts: Counter = Counter()
    for record in records.values():
        payload = record.get("payload")
        if not isinstance(payload, Mapping):
            continue
        for reason in _extract_final_unknown_reasons(payload):
            for action in build_unknown_recovery_actions((reason,)):
                counts[_global_reason_tuple_from_action(action)] += 1
    return counts


def _tuple_counter_for_reason(counter: Counter, reason_id: str) -> Counter:
    return Counter({
        tuple_key: count
        for tuple_key, count in counter.items()
        if len(tuple_key) > 1 and str(tuple_key[1]) == reason_id
    })


def _serialize_tuple_counter(counter: Counter) -> Sequence[Mapping[str, Any]]:
    return [
        {"tuple": list(tuple_key), "count": int(count)}
        for tuple_key, count in sorted(counter.items())
    ]


def _readiness(
    entries: Sequence[Mapping[str, Any]],
    transition_entries: Sequence[Mapping[str, Any]],
    retired_reason_inventory: Mapping[str, Any],
) -> Dict[str, Any]:
    failures = [
        failure
        for entry in entries
        for failure in (entry.get("selection_failures") or ())
    ]
    failures.extend(
        failure
        for entry in transition_entries
        for failure in (entry.get("selection_failures") or ())
    )
    for reason_id, inventory in retired_reason_inventory.items():
        if not isinstance(inventory, Mapping) or inventory.get("status") != "retired_by_reclassification":
            failures.append(f"retired_reason_inventory_mismatch:{reason_id}")
    covered_reasons = sorted(
        {
            reason_id
            for entry in entries
            if entry.get("selection_status") == "ready"
            for reason_id in (entry.get("required_reason_ids") or ())
        }
    )
    missing_targets = [
        reason_id for reason_id in TARGET_REASON_IDS if reason_id not in covered_reasons
    ]
    failures.extend(f"target_reason_not_covered:{reason_id}" for reason_id in missing_targets)
    counts = Counter(failures)
    return {
        "ready": not counts,
        "ready_entries": sum(1 for entry in entries if entry.get("selection_status") == "ready"),
        "failed_entries": sum(1 for entry in entries if entry.get("selection_status") != "ready"),
        "retired_by_reclassification_entries": sum(
            1
            for entry in transition_entries
            if entry.get("selection_status") == "retired_by_reclassification"
        ),
        "failed_retired_transition_entries": sum(
            1
            for entry in transition_entries
            if entry.get("selection_status") != "retired_by_reclassification"
        ),
        "covered_target_reason_ids": covered_reasons,
        "failure_kinds": sorted(counts),
        "failure_counts": dict(sorted(counts.items())),
    }


def _records_by_key(roots: Mapping[str, Path]) -> Dict[Tuple[str, str, str], Mapping[str, Any]]:
    records: Dict[Tuple[str, str, str], Mapping[str, Any]] = {}
    for category, root in roots.items():
        for path in sorted(Path(root).glob("*/*.log")):
            function, binary_pair = _identity_from_path(path)
            observed_left, observed_right = _directed_binary_pair_from_path(path)
            payloads = extract_result_payloads_from_text(path.read_text(errors="replace"))
            if not payloads:
                continue
            records[(str(category), function, binary_pair)] = {
                "payload": payloads[-1],
                "relative_log_path": str(path),
                "log_sha256": _sha256_file(path),
                "observed_left_binary_id": observed_left,
                "observed_right_binary_id": observed_right,
            }
    return records


def _load_phase3_lane1_manifest(
    *,
    raw_dir: Path,
    explicit_path: Optional[Path],
) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    candidates = []
    if explicit_path is not None:
        candidates.append(Path(explicit_path))
    else:
        candidates.extend(
            [
                raw_dir.parent
                / "audit"
                / "phase3_return_coverage_lane1_reclassification"
                / "return_coverage_lane1_representatives.json",
                raw_dir.parent
                / "phase3"
                / "return_coverage_lane1"
                / "return_coverage_lane1_representatives.json",
            ]
        )
    for path in candidates:
        if path.is_file():
            return _read_json(path), _file_ref(path)
    fallback = candidates[0] if candidates else raw_dir.parent / "phase3" / "return_coverage_lane1" / "return_coverage_lane1_representatives.json"
    return {}, {"path": str(fallback), "sha256": "__missing__"}


def _identity_from_path(path: Path) -> Tuple[str, str]:
    function = path.parent.name
    tail = path.stem.removeprefix(f"{function}_")
    return function, _canonical_binary_pair(tail)


def _directed_binary_pair_from_path(path: Path) -> Tuple[str, str]:
    function = path.parent.name
    tail = path.stem.removeprefix(f"{function}_")
    left, right = tail.split("_", 1)
    return left, right


def _canonical_binary_pair(binary_pair: str) -> str:
    left, right = str(binary_pair).split("_", 1)
    return "_".join(sorted((left, right), key=_binary_sort_key))


def _binary_sort_key(binary_id: str) -> Tuple[int, str]:
    if len(binary_id) > 1 and binary_id[0] == "B" and binary_id[1:].isdigit():
        return int(binary_id[1:]), binary_id
    return 10**9, binary_id


def _parse_roots(values: Sequence[str]) -> Dict[str, Path]:
    roots: Dict[str, Path] = {}
    for value in values:
        if "=" not in value:
            raise ValueError(f"log root must be CATEGORY=PATH, got {value!r}")
        category, path = value.split("=", 1)
        roots[category] = Path(path)
    return roots


def _file_ref(path: Path) -> Dict[str, Any]:
    return {
        "path": str(path),
        "sha256": _sha256_file(path) if path.is_file() else "__missing__",
    }


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _read_json(path: Path) -> Dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        value = json.load(handle)
    if not isinstance(value, dict):
        raise ValueError(f"JSON object expected in {path}")
    return value


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    raise SystemExit(main())
