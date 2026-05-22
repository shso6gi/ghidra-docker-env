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
    if manifest.get("phase3_lane1_ready") is True:
        return
    readiness = manifest.get("readiness")
    pre_fix_gate = manifest.get("pre_fix_regression_gate")
    if not isinstance(readiness, Mapping):
        raise ValueError("Phase 3 lane 1 readiness is false and readiness details are missing")
    failures = list(readiness.get("failure_kinds") or ())
    if isinstance(pre_fix_gate, Mapping):
        summary = pre_fix_gate.get("summary")
        if isinstance(summary, Mapping):
            failures.extend(str(kind) for kind in (summary.get("failed_kinds") or ()))
    if not failures:
        raise ValueError("Phase 3 lane 1 readiness is false without failure details")
    raise ValueError(f"Phase 3 lane 1 representative manifest is not ready: {', '.join(failures)}")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Build Phase 3 lane 1 return coverage representative manifest.",
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
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)
    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=Path(args.baseline_raw_dir),
        output_dir=Path(args.output_dir),
        current_log_roots=_parse_roots(args.current_log_root),
        baseline_log_roots=_parse_roots(args.baseline_log_root),
        phase1_dir=Path(args.phase1_dir) if args.phase1_dir else None,
        phase1_current_log_roots=(
            _parse_roots(args.phase1_current_log_root)
            if args.phase1_current_log_root is not None
            else None
        ),
    )
    if args.require_ready:
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
    records = _validation_records_by_key(current_log_roots)
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
        checks.append(_negative_representative_check(entry, records))
    return checks


def _negative_representative_check(
    entry: Mapping[str, Any],
    records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
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


def _materialize_retired_transition(
    raw_entry: Mapping[str, Any],
    current_records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
    baseline_records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
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
    if isinstance(value, tuple):
        return any(_nested_has_specific_leaf(item) for item in value)
    if isinstance(value, list):
        return any(_nested_has_specific_leaf(item) for item in value)
    return True


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
    baseline_reason_counts = _reason_record_tuple_counts(baseline_records)
    current_reason_counts = _reason_record_tuple_counts(current_records)
    baseline_action_counts = _proof_action_tuple_counts(baseline_records)
    current_action_counts = _proof_action_tuple_counts(current_records)
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
