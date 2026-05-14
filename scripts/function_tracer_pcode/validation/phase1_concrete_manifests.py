# -*- coding: utf-8 -*-
"""Build Phase 1 concrete pair manifests from a frozen observed baseline."""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence, Tuple

from ..equivalence.unknown_reason import coerce_unknown_reason_records
from .result_summary import classify_result_payload
from .unknown_reason_summary import extract_result_payloads_from_text


MANIFEST_VERSION = 1
CONSERVATIVE_UNKNOWN_ALLOWANCE_KINDS = frozenset(
    {
        "false_eq_guard",
        "explicit_proof_obligation",
    }
)
REJECTED_UNKNOWN_FAILURE_ORIGINS = frozenset(
    {
        "parser_failure",
        "internal_failure",
        "extraction_failure",
        "schema_failure",
    }
)
NEGATIVE_MINIMUM_CASES = (
    "call target mismatch",
    "argument storage mismatch",
    "call/memory side-effect mismatch",
    "width/high-bit near-miss",
    "readonly count mismatch",
    "return partition miss",
    "guard coverage miss",
    "inconclusive return coverage near-miss",
    "Method-B wrong-tail / guard partition miss",
)


DEFAULT_PHASE1_PLAN: Mapping[str, Any] = {
    "positive": [
        {
            "id": "positive-call-chain-existing-eq",
            "category": "function_call",
            "function": "fc_equiv_call_chain",
            "binary_pair": "B10_B11",
            "expected_result": "EQ",
            "role": "call-chain existing EQ",
        },
        {
            "id": "positive-recorded-call-effect-existing-eq",
            "category": "function_call",
            "function": "fc_recorded_chain",
            "binary_pair": "B10_B11",
            "expected_result": "EQ",
            "role": "recorded call/effect existing EQ",
        },
        {
            "id": "positive-direct-call-control",
            "category": "function_call",
            "function": "fc_guarded_call",
            "binary_pair": "B10_B11",
            "expected_result": "EQ",
            "role": "direct-call control",
        },
        {
            "id": "positive-no-call-control",
            "category": "function_call",
            "function": "fc_equiv_direct",
            "binary_pair": "B10_B11",
            "expected_result": "EQ",
            "role": "no-call control",
        },
        {
            "id": "positive-indirect-deferred-call-existing-eq",
            "category": "function_call",
            "function": "fc_dispatch_indirect",
            "binary_pair": "B13_B2",
            "expected_result": "EQ",
            "role": "indirect/deferred call positive",
        },
    ],
    "negative": [
        {
            "id": "negative-call-memory-side-effect-guard",
            "category": "function_call",
            "function": "fc_apply_indirect",
            "binary_pair": "B10_B11",
            "expected_result": "UNKNOWN",
            "must_not_be_equivalent": True,
            "negative_case": "call/memory side-effect mismatch",
            "required_reason_ids": ["equivalence_blocking_unsafety"],
            "unknown_allowance": {
                "allowance_kind": "explicit_proof_obligation",
                "failure_origin": "false_eq_guard",
                "proof_obligation": "call_effect_summary_proof",
            },
        },
        {
            "id": "negative-width-high-bit-near-miss",
            "category": "function_call",
            "function": "fc_apply_indirect",
            "binary_pair": "B10_B13",
            "expected_result": "UNKNOWN",
            "must_not_be_equivalent": True,
            "negative_case": "width/high-bit near-miss",
            "required_reason_ids": ["return_width_bridge_missing"],
            "unknown_allowance": {
                "allowance_kind": "explicit_proof_obligation",
                "failure_origin": "false_eq_guard",
                "proof_obligation": "abi_relation_high_bit_proof",
            },
        },
        {
            "id": "negative-return-partition-miss",
            "category": "function_call",
            "function": "fc_is_even",
            "binary_pair": "B10_B11",
            "expected_result": "UNKNOWN",
            "must_not_be_equivalent": True,
            "negative_case": "return partition miss",
            "required_reason_ids": ["return_coverage_gap"],
            "unknown_allowance": {
                "allowance_kind": "explicit_proof_obligation",
                "failure_origin": "false_eq_guard",
                "proof_obligation": "return_coverage_completion",
            },
        },
        {
            "id": "negative-inconclusive-return-coverage-near-miss",
            "category": "function_call",
            "function": "fc_is_odd",
            "binary_pair": "B11_B16",
            "expected_result": "UNKNOWN",
            "must_not_be_equivalent": True,
            "negative_case": "inconclusive return coverage near-miss",
            "required_reason_ids": ["return_coverage_inconclusive"],
            "unknown_allowance": {
                "allowance_kind": "explicit_proof_obligation",
                "failure_origin": "false_eq_guard",
                "proof_obligation": "return_coverage_smt_disambiguation",
            },
        },
        {
            "id": "negative-method-b-guard-partition-miss",
            "category": "loop",
            "function": "lmb_sum_even_index_step2",
            "binary_pair": "B10_B13",
            "expected_result": "UNKNOWN",
            "must_not_be_equivalent": True,
            "negative_case": "Method-B wrong-tail / guard partition miss",
            "required_reason_ids": ["method_b_closure_blocked"],
            "unknown_allowance": {
                "allowance_kind": "explicit_proof_obligation",
                "failure_origin": "false_eq_guard",
                "proof_obligation": "method_b_guard_partition",
            },
        },
        {
            "id": "negative-readonly-count-mismatch",
            "category": "loop",
            "function": "lmb_sum_even_index_step2",
            "binary_pair": "B10_B13",
            "expected_result": "UNKNOWN",
            "must_not_be_equivalent": True,
            "negative_case": "readonly count mismatch",
            "required_reason_ids": ["readonly_identity_missing"],
            "unknown_allowance": {
                "allowance_kind": "explicit_proof_obligation",
                "failure_origin": "false_eq_guard",
                "proof_obligation": "readonly_operand_identity",
            },
        },
        {
            "id": "negative-sat-unsafety-guard",
            "category": "function_call",
            "function": "fc_is_even",
            "binary_pair": "B10_B9",
            "expected_result": "UNKNOWN",
            "must_not_be_equivalent": True,
            "negative_case": "guard coverage miss",
            "required_reason_ids": ["sat_unsafety"],
            "unknown_allowance": {
                "allowance_kind": "false_eq_guard",
                "failure_origin": "false_eq_guard",
                "proof_obligation": "sat_unsafety_resolution",
            },
        },
    ],
    "representative": [
        {
            "id": "representative-equivalence-blocking-unsafety-apply",
            "category": "function_call",
            "function": "fc_apply_indirect",
            "binary_pair": "B10_B11",
            "current_result": "UNKNOWN",
            "required_reason_ids": ["equivalence_blocking_unsafety"],
            "expected_movement": {
                "reason_id": "equivalence_blocking_unsafety",
                "decision_effect": "blocks_equivalence",
                "reason_scope": "function",
                "recovery_proof_kind": "call_effect_summary_proof",
                "proof_stage": "object_evidence_collected",
                "action_status": "pending_proof",
                "evidence_kind": [
                    "call_effect_summary",
                    "runtime_ref",
                    "callsite_storage",
                ],
            },
        },
        {
            "id": "representative-equivalence-blocking-unsafety-dispatch",
            "category": "function_call",
            "function": "fc_dispatch_indirect",
            "binary_pair": "B10_B11",
            "current_result": "UNKNOWN",
            "required_reason_ids": ["equivalence_blocking_unsafety"],
            "expected_movement": {
                "reason_id": "equivalence_blocking_unsafety",
                "decision_effect": "blocks_equivalence",
                "reason_scope": "function",
                "recovery_proof_kind": "call_effect_summary_proof",
                "proof_stage": "object_evidence_collected",
                "action_status": "pending_proof",
                "evidence_kind": [
                    "call_effect_summary",
                    "runtime_ref",
                    "callsite_storage",
                ],
            },
        },
        {
            "id": "representative-equivalence-blocking-unsafety-recursive-stress",
            "category": "function_call",
            "function": "fc_recursive_sum",
            "binary_pair": "B10_B14",
            "current_result": "UNKNOWN",
            "required_reason_ids": ["equivalence_blocking_unsafety"],
            "expected_movement": {
                "reason_id": "equivalence_blocking_unsafety",
                "decision_effect": "blocks_equivalence",
                "reason_scope": "function",
                "recovery_proof_kind": "call_effect_summary_proof",
                "proof_stage": "object_evidence_collected",
                "action_status": "pending_proof",
                "evidence_kind": [
                    "call_effect_summary",
                    "runtime_ref",
                    "callsite_storage",
                ],
            },
        },
    ],
    "synthetic": {
        "synthetic_positive_required": False,
        "synthetic_positive_baseline_id": None,
        "reason": "observed baseline contains an indirect/deferred-call positive representative",
        "existing_positive_ref": "positive-indirect-deferred-call-existing-eq",
        "entries": [],
        "planned_negative_synthetic_entries": [
            {
                "id": "synthetic-negative-call-target-mismatch",
                "category": "synthetic_negative",
                "function": "syn_call_target_mismatch",
                "binary_pair": "S1_S2",
                "expected_result": "NOT_EQ",
                "must_not_be_equivalent": True,
                "artifact_status": "planned_not_created",
                "reason": "observed baseline has no concrete call-target mismatch negative guard",
            },
            {
                "id": "synthetic-negative-argument-storage-mismatch",
                "category": "synthetic_negative",
                "function": "syn_argument_storage_mismatch",
                "binary_pair": "S3_S4",
                "expected_result": "NOT_EQ",
                "must_not_be_equivalent": True,
                "artifact_status": "planned_not_created",
                "reason": "observed baseline has no concrete argument-storage mismatch negative guard",
            },
        ],
    },
}


@dataclass(frozen=True)
class PairEvidence:
    category: str
    function: str
    binary_pair: str
    left_binary_id: str
    right_binary_id: str
    current_result: str
    payload: Mapping[str, Any]
    log_path: Path
    relative_log_path: str
    log_sha256: str
    observed_reason_ids: Tuple[str, ...]
    observed_reason_records: Tuple[Dict[str, Any], ...]


def build_phase1_concrete_manifests(
    *,
    baseline_raw_dir: Path,
    output_dir: Path,
    plan: Optional[Mapping[str, Any]] = None,
) -> Path:
    raw_dir = Path(baseline_raw_dir).resolve()
    output = Path(output_dir)
    active_plan = plan or DEFAULT_PHASE1_PLAN
    baseline_manifest = _read_json(raw_dir / "artifact_manifest.json")
    baseline_id = str(baseline_manifest.get("baseline_id") or "")
    baseline_git_head = baseline_manifest.get("git_head")
    evidence = _load_pair_evidence(raw_dir, baseline_manifest)

    positive_entries = [
        _materialize_entry(raw_entry, evidence, expected_current_result="EQ")
        for raw_entry in active_plan.get("positive", ())
    ]
    positive = _build_manifest(
        manifest_kind="positive_concrete_pairs",
        baseline_id=baseline_id,
        baseline_git_head=baseline_git_head,
        entries=positive_entries,
    )
    negative_entries = [
        _materialize_entry(raw_entry, evidence, expected_current_result=str(raw_entry["expected_result"]))
        for raw_entry in active_plan.get("negative", ())
    ]
    negative = _build_manifest(
        manifest_kind="negative_concrete_pairs",
        baseline_id=baseline_id,
        baseline_git_head=baseline_git_head,
        entries=negative_entries,
    )
    negative["minimum_case_coverage"] = _negative_minimum_coverage(negative_entries)
    representative = _build_manifest(
        manifest_kind="representative_concrete_pairs",
        baseline_id=baseline_id,
        baseline_git_head=baseline_git_head,
        entries=[
            _materialize_entry(raw_entry, evidence, expected_current_result=str(raw_entry["current_result"]))
            for raw_entry in active_plan.get("representative", ())
        ],
    )
    synthetic = _build_synthetic_manifest(
        baseline_id=baseline_id,
        baseline_git_head=baseline_git_head,
        synthetic_plan=active_plan.get("synthetic") or {},
    )

    validate_positive_manifest(positive)
    validate_negative_manifest(negative)
    validate_representative_manifest(representative)
    validate_synthetic_manifest(synthetic)
    readiness = _phase1_readiness(
        positive=positive,
        negative=negative,
        representative=representative,
        synthetic=synthetic,
    )

    paths = {
        "positive": "positive_manifest.json",
        "negative": "negative_manifest.json",
        "representative": "representative_manifest.json",
        "synthetic": "synthetic_manifest.json",
    }
    _write_json(output / paths["positive"], positive)
    _write_json(output / paths["negative"], negative)
    _write_json(output / paths["representative"], representative)
    _write_json(output / paths["synthetic"], synthetic)
    index = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase1_concrete_manifest_index",
        "baseline_id": baseline_id,
        "baseline_git_head": baseline_git_head,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "manifests": paths,
        "counts": {
            "positive": len(positive["entries"]),
            "negative": len(negative["entries"]),
            "representative": len(representative["entries"]),
            "synthetic": len(synthetic["entries"]),
            "planned_negative_synthetic": synthetic.get("planned_negative_synthetic_count", 0),
        },
        "phase1_ready": readiness["phase1_ready"],
        "blocking_issue_kinds": readiness["blocking_issue_kinds"],
        "readiness": readiness,
    }
    index_path = output / "phase1_manifest_index.json"
    _write_json(index_path, index)
    return index_path


def validate_positive_manifest(
    manifest: Mapping[str, Any],
    *,
    require_object_evidence: bool = False,
) -> None:
    for entry in _entries(manifest):
        _require_concrete_pair_fields(entry)
        if entry.get("expected_result") != "EQ" or entry.get("current_result") != "EQ":
            raise ValueError(f"positive entry {entry.get('id')} must be current/expected EQ")
        status = entry.get("object_evidence_status")
        if require_object_evidence and status != "verified":
            raise ValueError(f"positive entry {entry.get('id')} lacks verified object evidence")


def validate_negative_manifest(manifest: Mapping[str, Any]) -> None:
    for entry in _entries(manifest):
        if entry.get("must_not_be_equivalent") is not True:
            raise ValueError(f"negative entry {entry.get('id')} requires must_not_be_equivalent=true")
        expected = entry.get("expected_result")
        if expected == "UNKNOWN":
            allowance = entry.get("unknown_allowance")
            if not isinstance(allowance, Mapping):
                raise ValueError(
                    f"negative entry {entry.get('id')} requires conservative UNKNOWN allowance"
                )
            kind = allowance.get("allowance_kind")
            if kind not in CONSERVATIVE_UNKNOWN_ALLOWANCE_KINDS:
                raise ValueError(f"negative entry {entry.get('id')} has invalid UNKNOWN allowance")
            origin = allowance.get("failure_origin")
            if origin in REJECTED_UNKNOWN_FAILURE_ORIGINS:
                raise ValueError(
                    f"negative entry {entry.get('id')} cannot allow parser/internal/extraction/schema UNKNOWN"
                )
            if not allowance.get("proof_obligation"):
                raise ValueError(f"negative entry {entry.get('id')} requires explicit proof obligation")
        elif expected == "NOT_EQ":
            source = entry.get("ground_truth_source")
            if (
                not isinstance(source, Mapping)
                or source.get("classification") != "ground_truth_not_eq"
                or source.get("oracle_review_status") != "accepted"
            ):
                raise ValueError(
                    f"negative entry {entry.get('id')} expected NOT_EQ requires accepted ground_truth_not_eq"
                )
        else:
            raise ValueError(f"negative entry {entry.get('id')} has invalid expected result {expected!r}")
        _require_concrete_pair_fields(entry)
        required = set(entry.get("required_reason_ids") or ())
        observed = set(entry.get("observed_reason_ids") or ())
        if expected == "UNKNOWN" and required and not required.issubset(observed):
            raise ValueError(f"negative entry {entry.get('id')} missing required observed reasons")
    coverage = manifest.get("minimum_case_coverage")
    if isinstance(coverage, Mapping):
        for missing in coverage.get("missing_cases") or ():
            if missing not in NEGATIVE_MINIMUM_CASES:
                raise ValueError(f"negative manifest reports unknown minimum case {missing!r}")


def validate_representative_manifest(manifest: Mapping[str, Any]) -> None:
    for entry in _entries(manifest):
        _require_concrete_pair_fields(entry)
        movement = entry.get("expected_movement")
        if not isinstance(movement, Mapping):
            raise ValueError(f"representative entry {entry.get('id')} requires expected_movement")
        for field_name in (
            "reason_id",
            "decision_effect",
            "reason_scope",
            "recovery_proof_kind",
            "proof_stage",
            "action_status",
        ):
            if not movement.get(field_name):
                raise ValueError(
                    f"representative entry {entry.get('id')} missing expected movement {field_name}"
                )


def validate_synthetic_manifest(manifest: Mapping[str, Any]) -> None:
    if manifest.get("synthetic_positive_required") is True:
        for field_name in (
            "synthetic_positive_baseline_id",
            "binary_hashes",
            "source_revision",
            "build_flags",
            "oracle",
            "expected_result",
            "build_import_decompiler_settings",
            "expected_counts",
        ):
            if not manifest.get(field_name):
                raise ValueError(f"synthetic positive manifest missing {field_name}")
    for entry in manifest.get("planned_negative_synthetic_entries") or ():
        if entry.get("artifact_status") != "planned_not_created":
            raise ValueError(f"synthetic negative entry {entry.get('id')} must be planned_not_created")
        if entry.get("must_not_be_equivalent") is not True:
            raise ValueError(f"synthetic negative entry {entry.get('id')} requires must_not_be_equivalent")


def validate_phase1_readiness(index: Mapping[str, Any]) -> None:
    if index.get("phase1_ready") is True:
        return
    readiness = index.get("readiness")
    if not isinstance(readiness, Mapping):
        raise ValueError("Phase 1 readiness is false and readiness details are missing")
    issues = readiness.get("blocking_issues") or ()
    if not issues:
        raise ValueError("Phase 1 readiness is false without blocking issues")
    kinds = ", ".join(str(issue.get("kind")) for issue in issues if isinstance(issue, Mapping))
    raise ValueError(f"Phase 1 manifest set is not ready: {kinds}")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Build Phase 1 concrete pair manifests.")
    parser.add_argument("--baseline-raw-dir", required=True)
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args(argv)
    index = build_phase1_concrete_manifests(
        baseline_raw_dir=Path(args.baseline_raw_dir),
        output_dir=Path(args.output_dir),
    )
    print(index)
    return 0


def _build_manifest(
    *,
    manifest_kind: str,
    baseline_id: str,
    baseline_git_head: Any,
    entries: Sequence[Mapping[str, Any]],
) -> Dict[str, Any]:
    return {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": manifest_kind,
        "baseline_id": baseline_id,
        "baseline_git_head": baseline_git_head,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "entries": list(entries),
    }


def _build_synthetic_manifest(
    *,
    baseline_id: str,
    baseline_git_head: Any,
    synthetic_plan: Mapping[str, Any],
) -> Dict[str, Any]:
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "synthetic_positive_manifest",
        "baseline_id": baseline_id,
        "baseline_git_head": baseline_git_head,
        "created_at": datetime.now(timezone.utc).isoformat(),
    }
    manifest.update(dict(synthetic_plan))
    manifest.setdefault("entries", [])
    manifest.setdefault("synthetic_positive_required", False)
    manifest["planned_negative_synthetic_count"] = len(
        manifest.get("planned_negative_synthetic_entries") or ()
    )
    return manifest


def _negative_minimum_coverage(entries: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    covered = sorted({str(entry.get("negative_case")) for entry in entries if entry.get("negative_case")})
    missing = [case for case in NEGATIVE_MINIMUM_CASES if case not in covered]
    return {
        "minimum_cases": list(NEGATIVE_MINIMUM_CASES),
        "covered_cases": covered,
        "missing_cases": missing,
        "missing_case_action": (
            "covered_by_planned synthetic negative entries; not observed-v0 baseline inputs"
            if missing
            else "none"
        ),
    }


def _materialize_entry(
    raw_entry: Mapping[str, Any],
    evidence: Mapping[Tuple[str, str, str], PairEvidence],
    *,
    expected_current_result: str,
) -> Dict[str, Any]:
    key = (
        str(raw_entry["category"]),
        str(raw_entry["function"]),
        _canonical_binary_pair(str(raw_entry["binary_pair"])),
    )
    item = evidence.get(key)
    if item is None:
        raise ValueError(f"missing concrete pair evidence for {key}")
    if item.current_result != expected_current_result:
        raise ValueError(
            f"concrete pair {key} has current result {item.current_result}, expected {expected_current_result}"
        )
    entry = dict(raw_entry)
    entry.update(
        {
            "function": item.function,
            "category": item.category,
            "binary_pair": item.binary_pair,
            "left_binary_id": item.left_binary_id,
            "right_binary_id": item.right_binary_id,
            "current_result": item.current_result,
            "observed_reason_ids": list(item.observed_reason_ids),
            "observed_reason_records": list(item.observed_reason_records),
            "source_artifact": {
                "log_path": item.relative_log_path,
                "log_sha256": item.log_sha256,
                "payload_pointer": "/typed_result_payloads/-1",
            },
        }
    )
    if item.current_result == "EQ":
        entry.setdefault("object_evidence_status", "not_verified")
        entry.setdefault(
            "object_evidence_requirement",
            "PyGhidra/object-derived shape confirmation required before Phase 1 readiness",
        )
    required = set(entry.get("required_reason_ids") or ())
    if required and not required.issubset(set(item.observed_reason_ids)):
        raise ValueError(f"concrete pair {key} missing required reasons {sorted(required)}")
    return entry


def _phase1_readiness(
    *,
    positive: Mapping[str, Any],
    negative: Mapping[str, Any],
    representative: Mapping[str, Any],
    synthetic: Mapping[str, Any],
) -> Dict[str, Any]:
    issues = []
    missing_cases = []
    coverage = negative.get("minimum_case_coverage")
    if isinstance(coverage, Mapping):
        missing_cases = list(coverage.get("missing_cases") or ())
    if missing_cases:
        issues.append(
            {
                "kind": "missing_negative_minimum_cases",
                "severity": "blocking",
                "missing_cases": missing_cases,
                "required_action": "create concrete observed or synthetic negative artifacts before semantic fixes",
            }
        )
    unverified_positive = [
        str(entry.get("id"))
        for entry in _entries(positive)
        if entry.get("object_evidence_status") != "verified"
    ]
    if unverified_positive:
        issues.append(
            {
                "kind": "positive_object_evidence_not_verified",
                "severity": "blocking",
                "entries": unverified_positive,
                "required_action": "confirm positive shape with object-derived PyGhidra evidence",
            }
        )
    planned_negative = list(synthetic.get("planned_negative_synthetic_entries") or ())
    if planned_negative:
        issues.append(
            {
                "kind": "planned_synthetic_negative_artifacts_not_created",
                "severity": "blocking",
                "entries": [str(entry.get("id")) for entry in planned_negative],
                "required_action": "materialize planned synthetic negative artifacts and rerun manifest builder",
            }
        )
    return {
        "phase1_ready": not issues,
        "blocking_issue_kinds": sorted({str(issue["kind"]) for issue in issues}),
        "blocking_issues": issues,
        "positive_count": len(_entries(positive)),
        "negative_count": len(_entries(negative)),
        "representative_count": len(_entries(representative)),
        "synthetic_positive_required": synthetic.get("synthetic_positive_required") is True,
        "planned_negative_synthetic_count": len(planned_negative),
    }


def _load_pair_evidence(
    raw_dir: Path,
    baseline_manifest: Mapping[str, Any],
) -> Dict[Tuple[str, str, str], PairEvidence]:
    file_hashes = _load_file_hashes(raw_dir, baseline_manifest)
    log_root = raw_dir / str(baseline_manifest.get("raw_logs_root") or "logs")
    result = {}
    for log_path in sorted(log_root.glob("*/*/*.log"), key=lambda path: str(path)):
        payloads = extract_result_payloads_from_text(log_path.read_text(errors="replace"))
        if not payloads:
            continue
        payload = payloads[-1]
        category = _category_from_log_path(log_path, raw_dir)
        function = str(payload.get("function1_name") or payload.get("function_name") or log_path.parent.name)
        left, right = _pair_from_log_path(log_path, function)
        binary_pair = "_".join(sorted((left, right), key=_binary_sort_key))
        relative_log_path = _relative_posix(log_path, raw_dir)
        reason_records = coerce_unknown_reason_records(payload.get("unknown_reasons") or ())
        reason_ids = tuple(sorted({str(record.reason_id) for record in reason_records}))
        record_dicts = tuple(
            {
                "reason_id": str(record.reason_id),
                "decision_effect": str(record.decision_effect),
                "reason_scope": str(record.reason_scope),
                "recovery_proof_kind": str(record.recovery_proof_kind),
                "proof_stage": str(record.proof_stage) if record.proof_stage is not None else "<missing>",
                "action_status": str(record.action_status) if record.action_status is not None else "<missing>",
            }
            for record in reason_records
        )
        item = PairEvidence(
            category=category,
            function=function,
            binary_pair=binary_pair,
            left_binary_id=left,
            right_binary_id=right,
            current_result=classify_result_payload(payload),
            payload=payload,
            log_path=log_path,
            relative_log_path=relative_log_path,
            log_sha256=file_hashes.get(relative_log_path) or _sha256_file(log_path),
            observed_reason_ids=reason_ids,
            observed_reason_records=record_dicts,
        )
        result[(category, function, binary_pair)] = item
    return result


def _entries(manifest: Mapping[str, Any]) -> Sequence[Mapping[str, Any]]:
    entries = manifest.get("entries") or ()
    if not isinstance(entries, Sequence):
        raise ValueError("manifest entries must be a sequence")
    return entries


def _require_concrete_pair_fields(entry: Mapping[str, Any]) -> None:
    for field_name in ("function", "category", "binary_pair", "left_binary_id", "right_binary_id"):
        if not entry.get(field_name):
            raise ValueError(f"manifest entry {entry.get('id')} missing {field_name}")


def _load_file_hashes(raw_dir: Path, manifest: Mapping[str, Any]) -> Dict[str, str]:
    path = raw_dir / "file_hashes.json"
    if path.is_file():
        payload = _read_json(path)
        return {str(key): str(value) for key, value in payload.items()}
    return {str(key): str(value) for key, value in (manifest.get("file_content_hashes") or {}).items()}


def _category_from_log_path(log_path: Path, raw_dir: Path) -> str:
    relative = log_path.relative_to(raw_dir)
    parts = relative.parts
    if len(parts) >= 4 and parts[0] == "logs":
        return parts[1]
    return "<missing>"


def _pair_from_log_path(log_path: Path, function: str) -> Tuple[str, str]:
    stem = log_path.stem
    prefix = f"{function}_"
    if stem.startswith(prefix):
        tail = stem[len(prefix):]
        parts = tail.rsplit("_", 1)
        if len(parts) == 2:
            return parts[0], parts[1]
    return "<missing-left>", "<missing-right>"


def _canonical_binary_pair(pair: str) -> str:
    left, right = pair.split("_", 1)
    return "_".join(sorted((left, right), key=_binary_sort_key))


def _binary_sort_key(binary_id: str) -> Tuple[str, int, str]:
    text = str(binary_id)
    if len(text) > 1 and text[0].isalpha() and text[1:].isdigit():
        return text[0], int(text[1:]), text
    return text, -1, text


def _relative_posix(path: Path, base: Path) -> str:
    try:
        return path.resolve().relative_to(base.resolve()).as_posix()
    except ValueError:
        return path.as_posix()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _read_json(path: Path) -> Dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"expected JSON object in {path}")
    return payload


def _write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    raise SystemExit(main())
