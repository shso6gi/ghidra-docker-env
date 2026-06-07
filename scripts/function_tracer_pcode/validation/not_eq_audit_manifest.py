# -*- coding: utf-8 -*-
"""Build Phase 0D NOT_EQ audit manifests from frozen validation artifacts."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence, Tuple

from ..equivalence.unknown_reason import coerce_unknown_reason_records
from .result_summary import STATUS_NOT_EQ, classify_result_payload, parse_log_identity
from .unknown_reason_summary import extract_result_payloads_from_text


MANIFEST_VERSION = 1
ORACLE_MANIFEST_VERSION = 1
CLASSIFICATIONS = frozenset(
    {
        "ground_truth_not_eq",
        "suspected_false_not_eq",
        "ub_or_domain_mismatch",
        "unresolved",
    }
)
ORACLE_REVIEW_STATUSES = frozenset({"draft", "reviewed", "accepted"})
ORACLE_SCOPES = frozenset({"function_category", "pair"})


def build_not_eq_audit_manifest(
    *,
    baseline_raw_dir: Path,
    output_path: Path,
    oracle_output_path: Optional[Path] = None,
) -> Path:
    raw_dir = Path(baseline_raw_dir).resolve()
    manifest = _read_json(raw_dir / "artifact_manifest.json")
    baseline_id = str(manifest.get("baseline_id") or "")
    file_hashes = _load_file_hashes(raw_dir, manifest)
    log_root = raw_dir / str(manifest.get("raw_logs_root") or "logs")
    if not log_root.is_dir():
        raise FileNotFoundError(f"raw logs root does not exist: {log_root}")

    records = []
    oracle_entries: Dict[Tuple[str, str], Dict[str, Any]] = {}
    for log_path in sorted(log_root.glob("*/*/*.log"), key=lambda path: str(path)):
        record = _not_eq_record_from_log(
            log_path=log_path,
            raw_dir=raw_dir,
            baseline_id=baseline_id,
            file_hashes=file_hashes,
        )
        if record is None:
            continue
        records.append(record)
        oracle_key = (record["category"], record["function"])
        oracle_entries.setdefault(oracle_key, _draft_oracle_entry(record))

    audit = {
        "manifest_version": MANIFEST_VERSION,
        "audit_kind": "not_eq_ground_truth_audit",
        "baseline_id": baseline_id,
        "baseline_manifest_ref": "raw/artifact_manifest.json",
        "baseline_git_head": manifest.get("git_head"),
        "created_at": datetime.now(timezone.utc).isoformat(),
        "classification_enum": sorted(CLASSIFICATIONS),
        "default_expected_equivalent_policy": {
            "expected_equivalent": True,
            "oracle_review_status": "draft",
            "source": "same_source_default_pending_oracle_review",
        },
        "entry_count": len(records),
        "classification_counts": dict(sorted(Counter(r["classification"] for r in records).items())),
        "entries": records,
    }
    validate_not_eq_audit_manifest(audit)

    if oracle_output_path is not None:
        oracle_path = Path(oracle_output_path)
        oracle_manifest = _build_oracle_manifest(
            baseline_id=baseline_id,
            baseline_git_head=manifest.get("git_head"),
            entries=tuple(oracle_entries.values()),
            audit_output_path=Path(output_path),
        )
        validate_oracle_manifest(oracle_manifest)
        _write_json(oracle_path, oracle_manifest)
        _attach_oracle_manifest_path(audit, oracle_path, Path(output_path))

    validate_not_eq_audit_manifest(audit, oracle_manifest=oracle_manifest if oracle_output_path is not None else None)
    _write_json(Path(output_path), audit)
    return Path(output_path)


def validate_not_eq_audit_manifest(
    audit: Mapping[str, Any],
    *,
    oracle_manifest: Optional[Mapping[str, Any]] = None,
) -> None:
    entries = audit.get("entries") or ()
    if "entry_count" in audit and int(audit.get("entry_count") or 0) != len(entries):
        raise ValueError("NOT_EQ audit entry_count does not match entries")
    classification_counts = audit.get("classification_counts")
    if isinstance(classification_counts, Mapping):
        actual_counts = dict(sorted(Counter(str(entry.get("classification") or "") for entry in entries).items()))
        if {str(key): int(value) for key, value in classification_counts.items()} != actual_counts:
            raise ValueError("NOT_EQ audit classification_counts do not match entries")
    classification_enum = audit.get("classification_enum")
    if classification_enum is not None and tuple(classification_enum) != tuple(sorted(CLASSIFICATIONS)):
        raise ValueError("NOT_EQ audit classification_enum is not canonical")
    oracle_entries = None
    if oracle_manifest is not None:
        validate_oracle_manifest(oracle_manifest)
        oracle_entries = _oracle_entries_by_key(oracle_manifest)
    for index, entry in enumerate(audit.get("entries") or ()):
        if not isinstance(entry, Mapping):
            raise ValueError(f"NOT_EQ audit entry {index} is not an object")
        classification = str(entry.get("classification") or "")
        if classification not in CLASSIFICATIONS:
            raise ValueError(f"invalid NOT_EQ audit classification: {classification!r}")
        if entry.get("current_result") not in {None, STATUS_NOT_EQ}:
            raise ValueError(f"NOT_EQ audit entry {index} current_result is not NOT_EQ")
        if oracle_entries is not None:
            _validate_audit_oracle_ref(entry, index, oracle_entries)
        if classification == "ground_truth_not_eq":
            _validate_ground_truth_entry(entry, index)


def validate_oracle_manifest(oracle: Mapping[str, Any]) -> None:
    if int(oracle.get("manifest_version") or 0) != ORACLE_MANIFEST_VERSION:
        raise ValueError("oracle manifest_version mismatch")
    if oracle.get("oracle_manifest_kind") != "same_source_expected_equivalence_draft":
        raise ValueError("oracle manifest kind mismatch")
    if not oracle.get("baseline_id"):
        raise ValueError("oracle manifest missing baseline_id")
    if not oracle.get("baseline_git_head"):
        raise ValueError("oracle manifest missing baseline_git_head")
    seen_keys: set[str] = set()
    for index, entry in enumerate(oracle.get("entries") or ()):
        if not isinstance(entry, Mapping):
            raise ValueError(f"oracle entry {index} is not an object")
        _validate_oracle_entry(entry, index)
        entry_key = str(entry.get("entry_key") or "")
        if entry_key in seen_keys:
            raise ValueError(f"duplicate oracle entry_key: {entry_key}")
        seen_keys.add(entry_key)


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Build a Phase 0D NOT_EQ audit manifest.")
    parser.add_argument("--baseline-raw-dir", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--oracle-output", default=None)
    args = parser.parse_args(argv)

    output = build_not_eq_audit_manifest(
        baseline_raw_dir=Path(args.baseline_raw_dir),
        output_path=Path(args.output),
        oracle_output_path=Path(args.oracle_output) if args.oracle_output else None,
    )
    print(output)
    return 0


def _not_eq_record_from_log(
    *,
    log_path: Path,
    raw_dir: Path,
    baseline_id: str,
    file_hashes: Mapping[str, str],
) -> Optional[Dict[str, Any]]:
    payloads = extract_result_payloads_from_text(log_path.read_text(errors="replace"))
    if not payloads:
        return None
    payload = payloads[-1]
    if classify_result_payload(payload) != STATUS_NOT_EQ:
        return None

    category = _category_from_log_path(log_path, raw_dir)
    function = str(payload.get("function1_name") or payload.get("function_name") or log_path.parent.name)
    left_id, right_id = _pair_from_log_path(log_path, function)
    binary_pair = "_".join(sorted((left_id, right_id), key=_binary_sort_key))
    relative_log_path = _relative_posix(log_path, raw_dir)
    log_hash = file_hashes.get(relative_log_path) or _sha256_file(log_path)
    unknown_reasons = coerce_unknown_reason_records(payload.get("unknown_reasons") or ())
    pairwise_stats = payload.get("pairwise_stats") if isinstance(payload.get("pairwise_stats"), Mapping) else {}

    return {
        "function": function,
        "category": category,
        "binary_pair": binary_pair,
        "left_binary_id": left_id,
        "right_binary_id": right_id,
        "left_binary_name": payload.get("binary1_name"),
        "right_binary_name": payload.get("binary2_name"),
        "side_or_role": "left_vs_right",
        "current_result": "NOT_EQ",
        "expected_equivalent": True,
        "oracle_manifest_ref": {
            "manifest_path": None,
            "entry_key": _oracle_entry_key(category, function),
            "oracle_review_status": "draft",
            "expected_equivalent": True,
        },
        "oracle_exception": {
            "status": "missing",
            "required_if_expected_equivalent_conflict": True,
        },
        "eq_goal_exclusion": {
            "status": "missing",
            "required_if_expected_equivalent_conflict": True,
        },
        "classification": "unresolved",
        "counterexample_model_ref": _counterexample_model_ref(
            payload=payload,
            relative_log_path=relative_log_path,
            log_hash=log_hash,
        ),
        "sat_unsafety_status": _sat_unsafety_status(unknown_reasons),
        "coverage_status": _coverage_status(pairwise_stats),
        "coverage_status_source": "/pairwise_stats" if pairwise_stats else "<missing>",
        "coverage_gap_status": _coverage_gap_status(pairwise_stats, unknown_reasons),
        "call_memory_effect_status": _call_memory_effect_status(unknown_reasons),
        "target_proof_lane": "not_eq_counterexample_replay",
        "oracle_decision_status": "draft_expected_equivalent_not_reviewed",
        "replay_harness": {
            "status": "missing",
            "required_for_ground_truth_not_eq": True,
        },
        "input_width_policy": _input_width_policy(payload),
        "return_compare_width": _return_compare_width(payload),
        "memory_initial_state": _memory_initial_state(payload),
        "ub_exclusion_rule": {
            "status": "not_audited",
            "required_for_ground_truth_not_eq": True,
        },
        "audit_source": {
            "baseline_id": baseline_id,
            "log_path": relative_log_path,
            "log_sha256": log_hash,
            "payload_index": len(payloads) - 1,
        },
    }


def _validate_ground_truth_entry(entry: Mapping[str, Any], index: int) -> None:
    oracle_ref = entry.get("oracle_manifest_ref")
    if not isinstance(oracle_ref, Mapping) or oracle_ref.get("oracle_review_status") != "accepted":
        raise ValueError(f"ground_truth_not_eq entry {index} requires accepted oracle")
    if _has_expected_equivalent_conflict(entry) and not _has_accepted_not_eq_override(entry):
        raise ValueError(
            f"ground_truth_not_eq entry {index} has expected_equivalent=true conflict; "
            "requires accepted oracle_exception or EQ goal exclusion"
        )
    counterexample = entry.get("counterexample_model_ref")
    if (
        not isinstance(counterexample, Mapping)
        or counterexample.get("replay_status") != "replayed"
        or counterexample.get("counterexample_present") is not True
        or counterexample.get("solver_model_present") is not True
    ):
        raise ValueError(f"ground_truth_not_eq entry {index} requires counterexample replay")
    replay_harness = entry.get("replay_harness")
    if not isinstance(replay_harness, Mapping) or replay_harness.get("status") not in {
        "available",
        "recorded",
        "replayed",
    }:
        raise ValueError(f"ground_truth_not_eq entry {index} requires replay harness")
    coverage_status = entry.get("coverage_status")
    if (
        not isinstance(coverage_status, Mapping)
        or coverage_status.get("status") != "reported_pairwise_no_unknown_or_error_pairs"
        or int(coverage_status.get("unknown_pairs") or 0) != 0
        or int(coverage_status.get("error_pairs") or 0) != 0
    ):
        raise ValueError(f"ground_truth_not_eq entry {index} requires no coverage unknown/error pairs")
    required_clear = (
        ("sat_unsafety_status", "not_reported_in_final_payload"),
        ("coverage_gap_status", "not_reported_in_final_payload"),
        ("call_memory_effect_status", "not_reported_in_final_payload"),
    )
    for field_name, expected in required_clear:
        value = entry.get(field_name)
        if not isinstance(value, Mapping) or value.get("status") != expected:
            raise ValueError(f"ground_truth_not_eq entry {index} has active or unknown {field_name}")
    if not _status_proven(entry.get("input_width_policy"), {"abi_storage_width_proven", "proven"}):
        raise ValueError(f"ground_truth_not_eq entry {index} requires ABI/storage width proof")
    if not _status_proven(entry.get("return_compare_width"), {"smt_type_widths_proven", "proven"}):
        raise ValueError(f"ground_truth_not_eq entry {index} requires return compare width proof")
    if not _status_proven(entry.get("ub_exclusion_rule"), {"proven", "ub_excluded"}):
        raise ValueError(f"ground_truth_not_eq entry {index} requires UB exclusion proof")


def _validate_oracle_entry(entry: Mapping[str, Any], index: int) -> None:
    required_fields = {
        "function",
        "category",
        "oracle_scope",
        "scope_target",
        "manifest_version",
        "oracle_owner",
        "oracle_review_status",
        "expected_equivalent",
        "oracle_source",
        "oracle_exception_reason",
        "domain_assumptions",
        "last_verified_by_evidence",
        "entry_key",
    }
    missing = sorted(field for field in required_fields if field not in entry)
    if missing:
        raise ValueError(f"oracle entry {index} missing required fields: {', '.join(missing)}")
    if int(entry.get("manifest_version") or 0) != ORACLE_MANIFEST_VERSION:
        raise ValueError(f"oracle entry {index} manifest_version mismatch")
    if entry.get("oracle_review_status") not in ORACLE_REVIEW_STATUSES:
        raise ValueError(f"oracle entry {index} invalid review status")
    if entry.get("oracle_scope") not in ORACLE_SCOPES:
        raise ValueError(f"oracle entry {index} invalid scope")
    if not isinstance(entry.get("expected_equivalent"), bool):
        raise ValueError(f"oracle entry {index} expected_equivalent must be boolean")
    if not isinstance(entry.get("domain_assumptions"), Sequence) or isinstance(entry.get("domain_assumptions"), (str, bytes)):
        raise ValueError(f"oracle entry {index} domain_assumptions must be a list")
    if not isinstance(entry.get("last_verified_by_evidence"), Mapping):
        raise ValueError(f"oracle entry {index} last_verified_by_evidence must be an object")
    expected_key = _oracle_entry_key(str(entry.get("category")), str(entry.get("function")))
    if entry.get("oracle_scope") == "pair":
        scope_target = entry.get("scope_target")
        if not isinstance(scope_target, Mapping) or not scope_target.get("binary_pair"):
            raise ValueError(f"oracle entry {index} pair scope requires binary_pair")
        expected_key = f"{expected_key}:{scope_target.get('binary_pair')}"
    if entry.get("entry_key") != expected_key:
        raise ValueError(f"oracle entry {index} entry_key does not match scope")
    _validate_oracle_scope_target(entry, index)


def _validate_oracle_scope_target(entry: Mapping[str, Any], index: int) -> None:
    scope_target = entry.get("scope_target")
    if not isinstance(scope_target, Mapping):
        raise ValueError(f"oracle entry {index} scope_target must be an object")
    if scope_target.get("category") != entry.get("category") or scope_target.get("function") != entry.get("function"):
        raise ValueError(f"oracle entry {index} scope_target does not match entry")
    if entry.get("oracle_scope") == "function_category" and "binary_pair" in scope_target:
        raise ValueError(f"oracle entry {index} function_category scope must not include binary_pair")


def _oracle_entries_by_key(oracle: Mapping[str, Any]) -> Dict[str, Mapping[str, Any]]:
    return {
        str(entry.get("entry_key")): entry
        for entry in oracle.get("entries") or ()
        if isinstance(entry, Mapping)
    }


def _validate_audit_oracle_ref(
    entry: Mapping[str, Any],
    index: int,
    oracle_entries: Mapping[str, Mapping[str, Any]],
) -> None:
    ref = entry.get("oracle_manifest_ref")
    if not isinstance(ref, Mapping):
        raise ValueError(f"NOT_EQ audit entry {index} missing oracle_manifest_ref")
    key = str(ref.get("entry_key") or "")
    oracle_entry = oracle_entries.get(key)
    if oracle_entry is None:
        raise ValueError(f"NOT_EQ audit entry {index} references missing oracle entry: {key}")
    if ref.get("expected_equivalent") != oracle_entry.get("expected_equivalent"):
        raise ValueError(f"NOT_EQ audit entry {index} oracle expected_equivalent mismatch")
    if ref.get("oracle_review_status") != oracle_entry.get("oracle_review_status"):
        raise ValueError(f"NOT_EQ audit entry {index} oracle review status mismatch")
    if not _oracle_entry_covers_audit_entry(oracle_entry, entry):
        raise ValueError(f"NOT_EQ audit entry {index} is outside oracle scope")


def _oracle_entry_covers_audit_entry(oracle_entry: Mapping[str, Any], audit_entry: Mapping[str, Any]) -> bool:
    if oracle_entry.get("category") != audit_entry.get("category"):
        return False
    if oracle_entry.get("function") != audit_entry.get("function"):
        return False
    if oracle_entry.get("oracle_scope") == "pair":
        scope_target = oracle_entry.get("scope_target")
        return isinstance(scope_target, Mapping) and scope_target.get("binary_pair") == audit_entry.get("binary_pair")
    return oracle_entry.get("oracle_scope") == "function_category"


def _has_expected_equivalent_conflict(entry: Mapping[str, Any]) -> bool:
    if entry.get("expected_equivalent") is True:
        return True
    oracle_ref = entry.get("oracle_manifest_ref")
    return isinstance(oracle_ref, Mapping) and oracle_ref.get("expected_equivalent") is True


def _has_accepted_not_eq_override(entry: Mapping[str, Any]) -> bool:
    for field_name in ("oracle_exception", "eq_goal_exclusion"):
        value = entry.get(field_name)
        if not isinstance(value, Mapping):
            continue
        if value.get("status") == "accepted":
            return True
        if value.get("review_status") == "accepted":
            return True
        if value.get("oracle_review_status") == "accepted":
            return True
    return False


def _status_proven(value: Any, allowed_statuses: set) -> bool:
    if not isinstance(value, Mapping):
        return False
    if value.get("status") in allowed_statuses:
        return True
    return value.get("proof_status") == "proven"


def _build_oracle_manifest(
    *,
    baseline_id: str,
    baseline_git_head: Any,
    entries: Sequence[Mapping[str, Any]],
    audit_output_path: Path,
) -> Dict[str, Any]:
    return {
        "manifest_version": ORACLE_MANIFEST_VERSION,
        "oracle_manifest_kind": "same_source_expected_equivalence_draft",
        "baseline_id": baseline_id,
        "baseline_git_head": baseline_git_head,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "audit_manifest_ref": _relative_posix(audit_output_path, audit_output_path.parent.parent),
        "entries": sorted(entries, key=lambda item: (str(item.get("category")), str(item.get("function")))),
    }


def _draft_oracle_entry(record: Mapping[str, Any]) -> Dict[str, Any]:
    return {
        "function": record["function"],
        "category": record["category"],
        "oracle_scope": "function_category",
        "scope_target": {
            "category": record["category"],
            "function": record["function"],
        },
        "manifest_version": ORACLE_MANIFEST_VERSION,
        "oracle_owner": "phase_0d_bootstrap",
        "oracle_review_status": "draft",
        "expected_equivalent": True,
        "oracle_source": "same_source_default_pending_review",
        "oracle_exception_reason": None,
        "domain_assumptions": [
            "same-source sample default; not accepted ground truth",
        ],
        "last_verified_by_evidence": {
            "status": "not_reviewed",
            "audit_entry_scope": "NOT_EQ observed pairs only",
        },
        "entry_key": _oracle_entry_key(str(record["category"]), str(record["function"])),
    }


def _attach_oracle_manifest_path(audit: Dict[str, Any], oracle_path: Path, audit_path: Path) -> None:
    ref_path = _relative_posix(oracle_path, audit_path.parent.parent)
    for entry in audit.get("entries") or ():
        if isinstance(entry, Mapping):
            ref = entry.get("oracle_manifest_ref")
            if isinstance(ref, dict):
                ref["manifest_path"] = ref_path


def _counterexample_model_ref(
    *,
    payload: Mapping[str, Any],
    relative_log_path: str,
    log_hash: str,
) -> Dict[str, Any]:
    counterexample = payload.get("counterexample") or payload.get("counterexample_raw")
    solver_results = payload.get("solver_results")
    model = None
    solver_status = None
    if isinstance(solver_results, Mapping):
        first = solver_results.get("first_definitive")
        if isinstance(first, Mapping):
            model = first.get("model")
            solver_status = first.get("status")
    return {
        "source_log_path": relative_log_path,
        "source_log_sha256": log_hash,
        "payload_pointer": "/counterexample",
        "solver_model_pointer": "/solver_results/first_definitive/model",
        "counterexample_present": counterexample is not None,
        "counterexample_sha256": _stable_json_hash(counterexample) if counterexample is not None else None,
        "solver_model_present": model is not None,
        "solver_model_sha256": _stable_json_hash(model) if model is not None else None,
        "solver_status": solver_status,
        "replay_status": "missing",
    }


def _sat_unsafety_status(unknown_reasons: Sequence[Any]) -> Dict[str, Any]:
    active = [str(reason.reason_id) for reason in unknown_reasons if str(reason.reason_id) == "sat_unsafety"]
    return {
        "status": "active" if active else "not_reported_in_final_payload",
        "source": "/unknown_reasons",
        "active_reason_ids": active,
    }


def _coverage_status(pairwise_stats: Mapping[str, Any]) -> Dict[str, Any]:
    unknown_pairs = int(pairwise_stats.get("unknown_pairs") or 0) if pairwise_stats else None
    error_pairs = int(pairwise_stats.get("error_pairs") or 0) if pairwise_stats else None
    if pairwise_stats and unknown_pairs == 0 and error_pairs == 0:
        status = "reported_pairwise_no_unknown_or_error_pairs"
    elif pairwise_stats:
        status = "reported_pairwise_gaps_or_errors"
    else:
        status = "not_reported"
    return {
        "status": status,
        "total_pairs": pairwise_stats.get("total_pairs") if pairwise_stats else None,
        "sat_pairs": pairwise_stats.get("sat_pairs") if pairwise_stats else None,
        "unknown_pairs": unknown_pairs,
        "error_pairs": error_pairs,
    }


def _coverage_gap_status(
    pairwise_stats: Mapping[str, Any],
    unknown_reasons: Sequence[Any],
) -> Dict[str, Any]:
    coverage_reason_ids = {
        "return_coverage_gap",
        "return_coverage_inconclusive",
        "method_b_closure_blocked",
    }
    active = sorted(
        str(reason.reason_id)
        for reason in unknown_reasons
        if str(reason.reason_id) in coverage_reason_ids
    )
    if active:
        status = "active"
    elif pairwise_stats and int(pairwise_stats.get("unknown_pairs") or 0) == 0:
        status = "not_reported_in_final_payload"
    else:
        status = "not_audited"
    return {
        "status": status,
        "source": ["/unknown_reasons", "/pairwise_stats"],
        "active_reason_ids": active,
    }


def _call_memory_effect_status(unknown_reasons: Sequence[Any]) -> Dict[str, Any]:
    effect_reason_ids = {
        "equivalence_blocking_unsafety",
        "unsupported_call_effect_summary",
        "call_effect_summary_missing",
        "readonly_identity_missing",
    }
    active = sorted(
        str(reason.reason_id)
        for reason in unknown_reasons
        if str(reason.reason_id) in effect_reason_ids
    )
    return {
        "status": "active" if active else "not_reported_in_final_payload",
        "source": "/unknown_reasons",
        "active_reason_ids": active,
    }


def _input_width_policy(payload: Mapping[str, Any]) -> Dict[str, Any]:
    return {
        "status": "captured_from_effective_signatures",
        "proof_status": "missing",
        "abi_domain_status": "not_audited",
        "abi_storage_width_proof_status": "missing",
        "source": [
            "/effective_function1_signature",
            "/effective_function2_signature",
            "/mips64_abi_constraints",
        ],
        "parameter_widths": {
            "left": _signature_parameter_widths(payload.get("effective_function1_signature")),
            "right": _signature_parameter_widths(payload.get("effective_function2_signature")),
        },
        "mips64_abi_constraints_present": payload.get("mips64_abi_constraints") is not None,
    }


def _return_compare_width(payload: Mapping[str, Any]) -> Dict[str, Any]:
    sat_pair_info = payload.get("sat_pair_info")
    return {
        "status": "requires_replay_for_width_proof",
        "proof_status": "missing",
        "source": [
            "/sat_pair_info/value1",
            "/sat_pair_info/value2",
            "/effective_function1_signature/return_type",
            "/effective_function2_signature/return_type",
        ],
        "left_return_type": _signature_return_type(payload.get("effective_function1_signature")),
        "right_return_type": _signature_return_type(payload.get("effective_function2_signature")),
        "sat_pair_indices": {
            "left_case_index": sat_pair_info.get("i") if isinstance(sat_pair_info, Mapping) else None,
            "right_case_index": sat_pair_info.get("j") if isinstance(sat_pair_info, Mapping) else None,
            "pair_stage": sat_pair_info.get("pair_stage") if isinstance(sat_pair_info, Mapping) else None,
        },
    }


def _memory_initial_state(payload: Mapping[str, Any]) -> Dict[str, Any]:
    sat_pair_info = payload.get("sat_pair_info")
    final_query = sat_pair_info.get("final_query") if isinstance(sat_pair_info, Mapping) else None
    has_memory_arrays = isinstance(final_query, str) and "(Array" in final_query
    return {
        "status": "captured_in_smt_query" if has_memory_arrays else "not_reported_in_final_payload",
        "source": "/sat_pair_info/final_query" if final_query is not None else "<missing>",
        "shared_memory_arrays_detected": bool(has_memory_arrays),
    }


def _signature_parameter_widths(signature: Any) -> Tuple[Dict[str, Any], ...]:
    if not isinstance(signature, Mapping):
        return ()
    parameters = signature.get("parameters")
    if not isinstance(parameters, Sequence):
        return ()
    result = []
    for parameter in parameters:
        if not isinstance(parameter, Mapping):
            continue
        storage = parameter.get("storage") if isinstance(parameter.get("storage"), Mapping) else {}
        result.append(
            {
                "index": parameter.get("index"),
                "data_type": parameter.get("data_type"),
                "size": parameter.get("size"),
                "is_signed": parameter.get("is_signed"),
                "storage_size_bits": storage.get("size_bits"),
                "storage_role": storage.get("register_name") or storage.get("space_name"),
            }
        )
    return tuple(result)


def _signature_return_type(signature: Any) -> Optional[str]:
    if not isinstance(signature, Mapping):
        return None
    value = signature.get("return_type")
    return str(value) if value is not None else None


def _load_file_hashes(raw_dir: Path, manifest: Mapping[str, Any]) -> Dict[str, str]:
    file_hashes_path = raw_dir / "file_hashes.json"
    if file_hashes_path.is_file():
        payload = _read_json(file_hashes_path)
        return {str(key): str(value) for key, value in payload.items()}
    return {
        str(key): str(value)
        for key, value in (manifest.get("file_content_hashes") or {}).items()
    }


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
    _, pair_label = parse_log_identity(log_path)
    if " ↔ " in pair_label:
        left, right = pair_label.split(" ↔ ", 1)
        return left, right
    return "<missing-left>", "<missing-right>"


def _binary_sort_key(binary_id: str) -> Tuple[str, int, str]:
    text = str(binary_id)
    if len(text) > 1 and text[0].isalpha() and text[1:].isdigit():
        return text[0], int(text[1:]), text
    return text, -1, text


def _oracle_entry_key(category: str, function: str) -> str:
    return f"{category}:{function}"


def _relative_posix(path: Path, base: Path) -> str:
    try:
        return path.resolve().relative_to(base.resolve()).as_posix()
    except ValueError:
        return path.as_posix()


def _stable_json_hash(value: Any) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"), default=str).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


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
