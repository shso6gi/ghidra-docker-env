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
TARGET_REASON_ID = "equivalence_blocking_unsafety"
EXPECTED_RECOVERY_ACTION = "call_effect_summary_proof_required"
EXPECTED_PROOF_KIND = UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value
EXPECTED_PROOF_STAGE = "object_evidence_collected"
EXPECTED_ACTION_STATUS = UnknownRecoveryActionStatus.PENDING_PROOF.value
MISSING_SENTINEL = UNKNOWN_TUPLE_MISSING
TARGET_REPRESENTATIVE_IDS = (
    "representative-equivalence-blocking-unsafety-apply",
    "representative-equivalence-blocking-unsafety-dispatch",
    "representative-equivalence-blocking-unsafety-recursive-stress",
)
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
SAT_UNSAFETY_REASON_TUPLE = (
    "sat_unsafety",
    "blocks_disequivalence",
    "pair",
    "none",
    MISSING_SENTINEL,
    MISSING_SENTINEL,
)
ALLOWED_EXPOSED_REASON_TUPLES = {
    (
        "return_coverage_gap",
        "blocks_equivalence",
        "function",
        "return_coverage_completion",
        MISSING_SENTINEL,
        MISSING_SENTINEL,
    ),
    (
        "return_width_bridge_missing",
        "blocks_equivalence",
        "query",
        "abi_relation_high_bit_proof",
        MISSING_SENTINEL,
        MISSING_SENTINEL,
    ),
    (
        "sat_unsafety",
        "blocks_disequivalence",
        "pair",
        "none",
        MISSING_SENTINEL,
        MISSING_SENTINEL,
    ),
    ALLOWED_NEW_REASON_TUPLE,
}
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
        "return_partition_extraction",
        "planned",
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
}
ALLOWED_PAIR_EXPOSED_REASONS = {
    TARGET_REASON_ID,
    "return_coverage_gap",
    "return_width_bridge_missing",
    "sat_unsafety",
}
ALLOWED_PAIR_REMOVED_REASONS = {
    "return_coverage_inconclusive",
    "solver_proven_rewrite_proof_failed",
    "unresolved_expression",
}


def build_phase2_equivalence_blocking_unsafety_movement(
    *,
    phase1_dir: Path,
    output_dir: Path,
    current_log_roots: Mapping[str, Path],
    baseline_log_roots: Optional[Mapping[str, Path]] = None,
) -> Path:
    phase1 = Path(phase1_dir).resolve()
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)
    representative = _read_json(phase1 / "representative_manifest.json")
    phase1_index = _read_optional_json(phase1 / "phase1_manifest_index.json")
    current_records = _records_by_key(current_log_roots)
    entries = []
    for entry in _target_representatives(representative):
        entries.append(_validate_representative_expected_movement(entry, current_records))
    baseline_gate = _validate_overall_baseline_comparison(
        baseline_log_roots or {},
        current_log_roots,
    )
    summary = _movement_summary(entries, baseline_gate)
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase2_equivalence_blocking_unsafety_expected_movement",
        "baseline_id": phase1_index.get("baseline_id") or MISSING_SENTINEL,
        "baseline_git_head": phase1_index.get("baseline_git_head") or MISSING_SENTINEL,
        "target_reason_id": TARGET_REASON_ID,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "phase1_manifest_index_ref": _file_ref(phase1 / "phase1_manifest_index.json"),
        "phase1_representative_manifest_ref": {
            "path": "representative_manifest.json",
            "sha256": _sha256_file(phase1 / "representative_manifest.json"),
        },
        "current_log_roots": {
            category: str(path)
            for category, path in sorted(current_log_roots.items())
        },
        "baseline_log_roots": {
            category: str(path)
            for category, path in sorted((baseline_log_roots or {}).items())
        },
        "movement_summary": summary,
        "overall_baseline_comparison_gate": baseline_gate,
        "phase2_ready": summary["failed"] == 0 and baseline_gate.get("passed") is True,
        "entries": entries,
    }
    path = output / "equivalence_blocking_unsafety_expected_movement.json"
    _write_json(path, manifest)
    return path


def validate_phase2_equivalence_blocking_unsafety_movement(manifest: Mapping[str, Any]) -> None:
    if manifest.get("phase2_ready") is True:
        return
    summary = manifest.get("movement_summary")
    if not isinstance(summary, Mapping):
        raise ValueError("Phase 2 movement is false and movement summary is missing")
    failed = summary.get("failed_kinds") or ()
    if not failed:
        raise ValueError("Phase 2 movement is false without failed movement kinds")
    raise ValueError(f"Phase 2 expected movement failed: {', '.join(map(str, failed))}")


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
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)
    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=Path(args.phase1_dir),
        output_dir=Path(args.output_dir),
        current_log_roots=_parse_current_log_roots(args.current_log_root or ()),
        baseline_log_roots=_parse_current_log_roots(args.baseline_log_root or ()),
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
    if len(value) < 8:
        return False
    return all(
        (
            value[1] in {"function1", "function2"},
            _analysis_key_is_specific(value[2]),
            _pcode_ref_is_specific(value[3]),
            _typed_target_expression_is_specific(value[5]),
            value[7] is not None,
        )
    )


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
        return isinstance(value[1] if len(value) > 1 else None, tuple)
    if value[0] == "entry_point":
        return len(value) > 1 and value[1] is not None
    return False


def _pcode_ref_is_specific(value: Any) -> bool:
    return isinstance(value, tuple) and len(value) >= 6 and value[0] == "pcode_op"


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
    )
    failed_entries = sum(1 for entry in entries if entry.get("movement_status") != "expected_movement")
    baseline_failures = 0 if baseline_gate.get("passed") is True else 1
    return {
        "target_reason_id": TARGET_REASON_ID,
        "total": len(entries),
        "passed": sum(1 for entry in entries if entry.get("movement_status") == "expected_movement"),
        "failed": failed_entries + len(missing_representatives) + len(unexpected_representatives) + baseline_failures,
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


def _validate_overall_baseline_comparison(
    baseline_log_roots: Mapping[str, Path],
    current_log_roots: Mapping[str, Path],
) -> Dict[str, Any]:
    if not baseline_log_roots:
        return {
            "passed": False,
            "failed_kinds": ["baseline_log_root_missing"],
            "status": "failed",
        }
    before_records = aggregate_validation_logs(_log_paths_from_roots(baseline_log_roots)).records
    after_records = aggregate_validation_logs(_log_paths_from_roots(current_log_roots)).records
    comparison = compare_validation_baseline_records(before_records, after_records)
    failed_kinds = _baseline_comparison_failures(comparison, before_records, after_records)
    return {
        "passed": not failed_kinds,
        "status": "passed" if not failed_kinds else "failed",
        "failed_kinds": failed_kinds,
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
    return {
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
            if reason_tuple == UNRESOLVED_EXPRESSION_REASON_TUPLE:
                return value < 0
            if reason_tuple == RETURN_COVERAGE_INCONCLUSIVE_REASON_TUPLE:
                return value < 0
            if reason_tuple == SOLVER_PROVEN_REWRITE_PROOF_FAILED_REASON_TUPLE:
                return value < 0
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
            if reason_tuple == RETURN_COVERAGE_INCONCLUSIVE_PROOF_ACTION_TUPLE:
                return value < 0
            if reason_tuple in SOLVER_PROVEN_REWRITE_PROOF_ACTION_TUPLES:
                return value < 0
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
    broad_tuples = {
        SOLVER_PROVEN_REWRITE_PROOF_FAILED_REASON_TUPLE,
        UNRESOLVED_EXPRESSION_REASON_TUPLE,
        RETURN_COVERAGE_INCONCLUSIVE_REASON_TUPLE,
    }
    for deltas in (
        comparison.validation_unknown_unit_multiset_delta,
        comparison.reason_record_multiset_delta,
    ):
        for key, value in deltas.items():
            if (
                isinstance(key, tuple)
                and len(key) == 7
                and key[1:] in broad_tuples
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
        return _has_pair_broad_reason_reduction(pair_reason_delta, before_reasons)
    if "unresolved_expression" in removed and added:
        return True
    if "unresolved_expression" in removed:
        return bool(after_reasons)
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
                {SAT_UNSAFETY_REASON_TUPLE},
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
                {SAT_UNSAFETY_REASON_TUPLE},
            )
    return result


def _has_allowed_broad_tuple_reduction(
    deltas: Mapping[Tuple[str, ...], int],
) -> bool:
    return any(
        reason_tuple in {
            RETURN_COVERAGE_INCONCLUSIVE_REASON_TUPLE,
            UNRESOLVED_EXPRESSION_REASON_TUPLE,
        }
        and value < 0
        for reason_tuple, value in deltas.items()
    )


def _has_solver_proven_rewrite_reduction(
    deltas: Mapping[Tuple[str, ...], int],
) -> bool:
    return int(deltas.get(SOLVER_PROVEN_REWRITE_PROOF_FAILED_REASON_TUPLE, 0) or 0) < 0


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
        result[category] = Path(raw_path)
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
