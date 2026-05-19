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

from .result_summary import STATUS_UNKNOWN, classify_result_payload
from .unknown_reason_summary import (
    _extract_final_unknown_reasons,
    _global_reason_tuple_from_action,
    _global_reason_tuple_from_record,
    extract_result_payloads_from_text,
)
from ..equivalence.unknown_reason import (
    UNKNOWN_TUPLE_MISSING,
    UnknownCountKind,
    build_proof_obligation_id,
    build_unknown_recovery_actions,
)


MANIFEST_VERSION = 1
TARGET_REASON_IDS = ("return_coverage_gap", "return_coverage_inconclusive")
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
RETURN_COVERAGE_INCONCLUSIVE_REASON_TUPLE = (
    UnknownCountKind.REASON_RECORD.value,
    "return_coverage_inconclusive",
    "blocks_decision",
    "function",
    "return_coverage_completion",
    "return_coverage_smt_disambiguation",
    "pending_proof",
)
RETURN_COVERAGE_INCONCLUSIVE_ACTION_TUPLE = (
    UnknownCountKind.PROOF_ACTION.value,
    "return_coverage_inconclusive",
    "blocks_decision",
    "function",
    "return_coverage_completion",
    "return_coverage_smt_disambiguation",
    "pending_proof",
)
FUNCTION_CALL_BINARY_NAMES = {
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
        "id": "representative-return-coverage-inconclusive-odd",
        "category": "function_call",
        "function": "fc_is_odd",
        "binary_pair": "B11_B16",
        "expected_observed_binary1_name": FUNCTION_CALL_BINARY_NAMES["B11"],
        "expected_observed_binary2_name": FUNCTION_CALL_BINARY_NAMES["B16"],
        "required_reason_ids": ["return_coverage_inconclusive"],
        "supporting_reason_ids": ["return_coverage_gap"],
        "role": "inconclusive return coverage near-miss with stable gap co-reason",
        "expected_movements": [
            _expected_reason_record(
                "inconclusive-reason-record",
                RETURN_COVERAGE_INCONCLUSIVE_REASON_TUPLE,
                expected_evidence_refs=["function2:return_coverage_inconclusive"],
            ),
            _expected_proof_action(
                "inconclusive-smt-disambiguation",
                RETURN_COVERAGE_INCONCLUSIVE_ACTION_TUPLE,
                required_evidence=[
                    "case_guard_disjunction",
                    "normalized_guard_formula",
                    "solver_model_or_timeout",
                ],
                expected_evidence_refs=["function2:return_coverage_inconclusive"],
            ),
            _expected_reason_record(
                "supporting-gap-reason-record",
                RETURN_COVERAGE_GAP_REASON_TUPLE,
                expected_evidence_refs=["function1:return_coverage_gap"],
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
        "expected_movements": [
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
        ],
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
    representatives: Sequence[Mapping[str, Any]] = DEFAULT_REPRESENTATIVES,
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
    readiness = _readiness(entries)
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase3_return_coverage_lane1_representatives",
        "baseline_id": baseline_manifest.get("baseline_id") or MISSING_SENTINEL,
        "baseline_git_head": baseline_manifest.get("git_head") or MISSING_SENTINEL,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "target_reason_ids": list(TARGET_REASON_IDS),
        "baseline_raw_artifact_ref": _file_ref(raw_dir / "artifact_manifest.json"),
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
                "return_coverage_gap and return_coverage_inconclusive covered",
                "avoid semantic decision changes before lane implementation",
            ],
        },
        "readiness": readiness,
        "phase3_lane1_ready": readiness["ready"],
        "entries": entries,
    }
    path = output / "return_coverage_lane1_representatives.json"
    _write_json(path, manifest)
    return path


def validate_phase3_return_coverage_lane1_manifest(manifest: Mapping[str, Any]) -> None:
    if manifest.get("phase3_lane1_ready") is True:
        return
    readiness = manifest.get("readiness")
    if not isinstance(readiness, Mapping):
        raise ValueError("Phase 3 lane 1 readiness is false and readiness details are missing")
    failures = readiness.get("failure_kinds") or ()
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
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)
    path = build_phase3_return_coverage_lane1_manifest(
        baseline_raw_dir=Path(args.baseline_raw_dir),
        output_dir=Path(args.output_dir),
        current_log_roots=_parse_roots(args.current_log_root),
        baseline_log_roots=_parse_roots(args.baseline_log_root),
    )
    if args.require_ready:
        validate_phase3_return_coverage_lane1_manifest(_read_json(path))
    print(path)
    return 0


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
        failures.extend(_expected_movement_failures(entry, observation, label))
    entry["selection_status"] = "ready" if not failures else "failed"
    entry["selection_failures"] = sorted(set(failures))
    return entry


def _observation(record: Optional[Mapping[str, Any]]) -> Dict[str, Any]:
    if not record:
        return {"log_status": "missing"}
    payload = record["payload"]
    reason_records = _extract_final_unknown_reasons(payload)
    proof_actions = [
        action
        for reason in reason_records
        for action in build_unknown_recovery_actions((reason,))
    ]
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
            if reason.reason_id in TARGET_REASON_IDS
        ],
        "reason_records": [
            _reason_record_summary(reason)
            for reason in reason_records
            if reason.reason_id in TARGET_REASON_IDS
        ],
        "proof_action_tuples": [
            list(_global_reason_tuple_from_action(action))
            for action in proof_actions
            if getattr(action, "reason_id", None) in TARGET_REASON_IDS
        ],
        "proof_actions": [
            _proof_action_summary(action)
            for action in proof_actions
            if getattr(action, "reason_id", None) in TARGET_REASON_IDS
        ],
        "return_case_grid_diagnostic": _return_case_grid_diagnostic(payload),
    }


def _reason_record_summary(reason: Any) -> Dict[str, Any]:
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
        "recovery_action": reason.recovery_action or MISSING_SENTINEL,
        "recovery_proof_obligations": [
            dict(obligation)
            for obligation in (reason.recovery_proof_obligations or ())
            if isinstance(obligation, Mapping)
        ],
    }


def _proof_action_summary(action: Any) -> Dict[str, Any]:
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
    reason_tuples = {
        tuple(item)
        for item in observation.get("reason_record_tuples") or ()
        if isinstance(item, Sequence) and not isinstance(item, (str, bytes))
    }
    proof_tuples = {
        tuple(item)
        for item in observation.get("proof_action_tuples") or ()
        if isinstance(item, Sequence) and not isinstance(item, (str, bytes))
    }
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
            if tuple_key not in reason_tuples:
                failures.append(f"{label}_expected_reason_tuple_missing:{movement_id}")
                continue
            if not _matching_record_has_scope(reason_records, tuple_key, movement):
                failures.append(f"{label}_expected_reason_scope_mismatch:{movement_id}")
                continue
            if not _matching_record_has_evidence_refs(reason_records, tuple_key, movement):
                failures.append(f"{label}_expected_reason_evidence_refs_mismatch:{movement_id}")
            if not _matching_record_has_object_target(reason_records, tuple_key, movement):
                failures.append(f"{label}_expected_reason_object_target_mismatch:{movement_id}")
        elif count_kind == UnknownCountKind.PROOF_ACTION.value:
            if tuple_key not in proof_tuples:
                failures.append(f"{label}_expected_proof_action_tuple_missing:{movement_id}")
                continue
            expected_evidence = tuple(str(item) for item in movement.get("required_evidence") or ())
            if not expected_evidence:
                failures.append(f"{label}_expected_proof_action_evidence_missing:{movement_id}")
                continue
            if not _matching_proof_action_has_evidence(proof_actions, tuple_key, expected_evidence):
                failures.append(f"{label}_expected_proof_action_evidence_mismatch:{movement_id}")
            if not _matching_record_has_scope(proof_actions, tuple_key, movement):
                failures.append(f"{label}_expected_proof_action_scope_mismatch:{movement_id}")
                continue
            if not _matching_record_has_evidence_refs(proof_actions, tuple_key, movement):
                failures.append(f"{label}_expected_proof_action_evidence_refs_mismatch:{movement_id}")
            if not _matching_record_has_object_target(proof_actions, tuple_key, movement):
                failures.append(f"{label}_expected_proof_action_object_target_mismatch:{movement_id}")
            if not _matching_proof_action_has_proof_id(proof_actions, tuple_key, movement):
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


def _movement_tuple(movement: Mapping[str, Any]) -> Optional[Tuple[str, ...]]:
    tuple_value = movement.get("tuple")
    if not isinstance(tuple_value, Sequence) or isinstance(tuple_value, (str, bytes)):
        return None
    normalized = tuple(str(item) for item in tuple_value)
    if len(normalized) != 7:
        return None
    return normalized


def _matching_proof_action_has_evidence(
    proof_actions: Any,
    tuple_key: Tuple[str, ...],
    expected_evidence: Tuple[str, ...],
) -> bool:
    for action in proof_actions:
        if not isinstance(action, Mapping):
            continue
        if tuple(str(item) for item in action.get("tuple") or ()) != tuple_key:
            continue
        actual = tuple(str(item) for item in action.get("required_evidence") or ())
        if actual == expected_evidence:
            return True
    return False


def _matching_record_has_scope(
    records: Any,
    tuple_key: Tuple[str, ...],
    movement: Mapping[str, Any],
) -> bool:
    expected_scope = _movement_scope(movement)
    for record in records:
        if not isinstance(record, Mapping):
            continue
        if tuple(str(item) for item in record.get("tuple") or ()) != tuple_key:
            continue
        actual_scope = (
            _normalize_optional(record.get("aggregation_unit")),
            _normalize_optional(record.get("stage")),
            _normalize_optional(record.get("pair_or_case")),
        )
        if actual_scope == expected_scope:
            return True
    return False


def _matching_record_has_evidence_refs(
    records: Any,
    tuple_key: Tuple[str, ...],
    movement: Mapping[str, Any],
) -> bool:
    expected_refs = movement.get("expected_evidence_refs")
    if expected_refs is None:
        return True
    expected_scope = _movement_scope(movement)
    normalized_expected_refs = tuple(str(ref) for ref in expected_refs or ())
    for record in records:
        if not isinstance(record, Mapping):
            continue
        if tuple(str(item) for item in record.get("tuple") or ()) != tuple_key:
            continue
        actual_scope = (
            _normalize_optional(record.get("aggregation_unit")),
            _normalize_optional(record.get("stage")),
            _normalize_optional(record.get("pair_or_case")),
        )
        if actual_scope != expected_scope:
            continue
        actual_refs = tuple(str(ref) for ref in record.get("evidence_refs") or ())
        if actual_refs == normalized_expected_refs:
            return True
    return False


def _matching_record_has_object_target(
    records: Any,
    tuple_key: Tuple[str, ...],
    movement: Mapping[str, Any],
) -> bool:
    required_kind = movement.get("required_object_target_kind")
    if required_kind is None:
        return True
    expected_scope = _movement_scope(movement)
    for record in records:
        if not isinstance(record, Mapping):
            continue
        if tuple(str(item) for item in record.get("tuple") or ()) != tuple_key:
            continue
        actual_scope = (
            _normalize_optional(record.get("aggregation_unit")),
            _normalize_optional(record.get("stage")),
            _normalize_optional(record.get("pair_or_case")),
        )
        if actual_scope != expected_scope:
            continue
        object_target_key = _normalize_nested_tuple(record.get("object_target_key"))
        if (
            _nested_tuple_kind(object_target_key) == str(required_kind)
            and _object_target_key_is_specific(object_target_key)
        ):
            return True
    return False


def _matching_proof_action_has_proof_id(
    proof_actions: Any,
    tuple_key: Tuple[str, ...],
    movement: Mapping[str, Any],
) -> bool:
    if not movement.get("require_proof_obligation_id"):
        return True
    expected_scope = _movement_scope(movement)
    for action in proof_actions:
        if not isinstance(action, Mapping):
            continue
        if tuple(str(item) for item in action.get("tuple") or ()) != tuple_key:
            continue
        actual_scope = (
            _normalize_optional(action.get("aggregation_unit")),
            _normalize_optional(action.get("stage")),
            _normalize_optional(action.get("pair_or_case")),
        )
        if actual_scope != expected_scope:
            continue
        object_target_key = _normalize_nested_tuple(action.get("object_target_key"))
        if object_target_key is None or not _object_target_key_is_specific(object_target_key):
            continue
        expected_id = build_proof_obligation_id(
            action.get("reason_id"),
            action.get("proof_stage"),
            action.get("proof_kind"),
            action.get("evidence_kind"),
            object_target_key,
        )
        if _normalize_nested_tuple(action.get("proof_obligation_id")) == expected_id:
            return True
    return False


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
        return _address_like_is_specific(value[1])
    return False


def _function_ref_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or not value:
        return False
    kind = value[0]
    if kind == "function":
        if len(value) < 3:
            return False
        return _address_like_is_specific(value[2])
    if kind == "code_address":
        if len(value) < 3:
            return False
        return _address_like_is_specific(value[2])
    return False


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
    if not isinstance(value, tuple) or not value or value[0] != "pcode_op":
        return False
    if _nested_contains_log_prose(value):
        return False
    if len(value) == 6:
        _kind, address_offset, seq_time, seq_order, block_index, mnemonic = value
        if not isinstance(mnemonic, str) or not mnemonic:
            return False
        return _address_like_is_specific(address_offset) and (
            _int_like_is_specific(seq_time)
            or _int_like_is_specific(seq_order)
            or _int_like_is_specific(block_index)
        )
    if len(value) >= 8:
        _kind, address_space, address_offset, seq_space, seq_offset, seq_order, opcode, local_ordinal = value[:8]
        if not isinstance(opcode, str) or not opcode:
            return False
        return all(
            (
                _nested_has_specific_leaf(address_space),
                _address_like_is_specific(address_offset),
                _nested_has_specific_leaf(seq_space),
                _address_like_is_specific(seq_offset),
                _int_like_is_specific(seq_order),
                _int_like_is_specific(local_ordinal),
            )
        )
    return False


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
        return any(reason_id in value for reason_id in TARGET_REASON_IDS)
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


def _readiness(entries: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    failures = [
        failure
        for entry in entries
        for failure in (entry.get("selection_failures") or ())
    ]
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
