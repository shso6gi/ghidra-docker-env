# -*- coding: utf-8 -*-
"""Freeze Phase 3 lane 2 representatives for return-width bridge work."""

from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Sequence, Tuple

from .result_summary import (
    STATUS_EQ,
    STATUS_TIMEOUT,
    STATUS_UNKNOWN,
    classify_result_payload,
)
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
    coerce_unknown_recovery_actions,
)


MANIFEST_VERSION = 1
TARGET_REASON_IDS = ("return_width_bridge_missing",)
MISSING_SENTINEL = UNKNOWN_TUPLE_MISSING
_REPO_ROOT = Path(__file__).resolve().parents[3]
RETURN_WIDTH_BRIDGE_PROOF_STAGES = ("abi_relation", "high_bit_relation")
RETURN_WIDTH_BRIDGE_REASON_TUPLE = (
    UnknownCountKind.REASON_RECORD.value,
    "return_width_bridge_missing",
    "blocks_equivalence",
    "query",
    "abi_relation_high_bit_proof",
    MISSING_SENTINEL,
    MISSING_SENTINEL,
)
RETURN_WIDTH_BRIDGE_ABI_ACTION_TUPLE = (
    UnknownCountKind.PROOF_ACTION.value,
    "return_width_bridge_missing",
    "blocks_equivalence",
    "query",
    "abi_relation_proof",
    "abi_relation",
    "planned",
)
RETURN_WIDTH_BRIDGE_HIGH_BIT_ACTION_TUPLE = (
    UnknownCountKind.PROOF_ACTION.value,
    "return_width_bridge_missing",
    "blocks_equivalence",
    "query",
    "high_bit_proof",
    "high_bit_relation",
    "planned",
)
RETURN_WIDTH_BRIDGE_ACTION_REQUIREMENTS: Mapping[Tuple[str, str], Mapping[str, Any]] = {
    ("abi_relation_proof", "abi_relation"): {
        "status": "planned",
        "evidence_kind": "calling_convention",
        "required_evidence": (
            "calling_convention",
            "return_storage",
            "narrow_return_width",
        ),
    },
    ("high_bit_proof", "high_bit_relation"): {
        "status": "planned",
        "evidence_kind": "producer_width",
        "required_evidence": (
            "producer_width",
            "extension_semantics",
            "high_bits_irrelevant_or_equal",
        ),
    },
}
ABI_CALLING_CONVENTION_RELATIONS = frozenset({"same_return_abi_family"})
ABI_RETURN_STORAGE_RELATIONS = frozenset({"abi_related_return_storage"})
HIGH_BIT_EXTENSION_RELATIONS = frozenset({"compatible_under_narrow_width"})
HIGH_BIT_PROOF_LABELS = frozenset({"high_bits_do_not_affect_compared_return"})
COMPLETED_PROOF_BLOCKER_FIELDS = (
    "sat_unsafety_reasons",
    "coverage_gap_reasons",
    "unsupported_effect_reasons",
    "active_unsafety_reasons",
    "active_coverage_gaps",
    "active_coverage_gap_reasons",
    "active_unsupported_effects",
    "unsupported_call_effect_reasons",
    "unsupported_memory_effect_reasons",
)
STRUCTURED_EVIDENCE_NODE_ROOTS = {
    "binary",
    "call",
    "const",
    "intrinsic",
    "literal",
    "memory",
    "parameter",
    "phi",
    "unary",
    "variable",
}
FUNCTION_CALL_BINARY_NAMES = {
    "B10": "function_call_test-mips64-clang-O1",
    "B13": "function_call_test-mips64-gcc-O0",
}


def _expected_reason_record(movement_id: str) -> Dict[str, Any]:
    return {
        "id": movement_id,
        "count_kind": UnknownCountKind.REASON_RECORD.value,
        "tuple": list(RETURN_WIDTH_BRIDGE_REASON_TUPLE),
        "aggregation_unit": "pair",
        "stage": "S_PAIRWISE",
        "pair_or_case": MISSING_SENTINEL,
        "expected_evidence_refs": ["return_width_bridge"],
        "required_object_target_kind": "return_width_bridge",
    }


def _expected_proof_action(
    movement_id: str,
    tuple_key: Tuple[str, ...],
    *,
    required_evidence: Sequence[str],
) -> Dict[str, Any]:
    return {
        "id": movement_id,
        "count_kind": UnknownCountKind.PROOF_ACTION.value,
        "tuple": list(tuple_key),
        "aggregation_unit": "pair",
        "stage": "S_PAIRWISE",
        "pair_or_case": MISSING_SENTINEL,
        "expected_evidence_refs": ["return_width_bridge"],
        "required_evidence": list(required_evidence),
        "required_object_target_kind": "return_width_bridge",
        "require_proof_obligation_id": True,
    }


DEFAULT_REPRESENTATIVES: Tuple[Mapping[str, Any], ...] = (
    {
        "id": "representative-return-width-bridge-apply-indirect-width-high-bit-near-miss",
        "category": "function_call",
        "function": "fc_apply_indirect",
        "binary_pair": "B10_B13",
        "expected_observed_binary1_name": FUNCTION_CALL_BINARY_NAMES["B10"],
        "expected_observed_binary2_name": FUNCTION_CALL_BINARY_NAMES["B13"],
        "required_reason_ids": ["return_width_bridge_missing"],
        "role": "width/high-bit near-miss requiring ABI relation plus high-bit proof",
        "expected_movements": [
            _expected_reason_record("width-bridge-reason-record"),
            _expected_proof_action(
                "width-bridge-abi-relation",
                RETURN_WIDTH_BRIDGE_ABI_ACTION_TUPLE,
                required_evidence=(
                    "calling_convention",
                    "return_storage",
                    "narrow_return_width",
                ),
            ),
            _expected_proof_action(
                "width-bridge-high-bit-relation",
                RETURN_WIDTH_BRIDGE_HIGH_BIT_ACTION_TUPLE,
                required_evidence=(
                    "producer_width",
                    "extension_semantics",
                    "high_bits_irrelevant_or_equal",
                ),
            ),
        ],
    },
)


def build_phase3_return_width_bridge_lane2_manifest(
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
    target_keys = tuple(_entry_key(entry) for entry in representatives)
    current_records = _records_by_key(current_log_roots, target_keys=target_keys)
    baseline_records = _records_by_key(baseline_log_roots, target_keys=target_keys)
    entries = [
        _materialize_entry(raw_entry, current_records, baseline_records)
        for raw_entry in representatives
    ]
    readiness = _readiness(entries)
    implementation_manifest = _implementation_manifest(entries)
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase3_return_width_bridge_lane2_representatives",
        "artifact_role": "derived_audit_proof_backlog_gate",
        "baseline_id": baseline_manifest.get("baseline_id") or MISSING_SENTINEL,
        "baseline_git_head": baseline_manifest.get("git_head") or MISSING_SENTINEL,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "target_reason_ids": list(TARGET_REASON_IDS),
        "baseline_raw_artifact_ref": _file_ref(raw_dir / "artifact_manifest.json"),
        "current_log_roots": {
            category: str(path) for category, path in sorted(current_log_roots.items())
        },
        "baseline_log_roots": {
            category: str(path) for category, path in sorted(baseline_log_roots.items())
        },
        "selection_policy": {
            "representative_count": len(entries),
            "criteria": [
                "concrete function x binary_pair ids",
                "baseline/current UNKNOWN result",
                "current return_width_bridge_missing reason records preserve final UNKNOWN",
                "current proof actions carry raw object_target_key and proof_obligation_id",
                "ABI relation and high-bit proof actions are both required per target",
                "no semantic recovery is accepted before both proofs complete",
            ],
        },
        "implementation_manifest": implementation_manifest,
        "readiness": readiness,
        "phase3_lane2_ready": readiness["ready"],
        "entries": entries,
    }
    path = output / "return_width_bridge_lane2_representatives.json"
    _write_json(path, manifest)
    return path


def validate_phase3_return_width_bridge_lane2_manifest(manifest: Mapping[str, Any]) -> None:
    if manifest.get("phase3_lane2_ready") is True:
        return
    readiness = manifest.get("readiness")
    failures = []
    if isinstance(readiness, Mapping):
        failures.extend(str(kind) for kind in readiness.get("failure_kinds") or ())
    if not failures:
        raise ValueError("Phase 3 lane 2 readiness is false without failure details")
    raise ValueError(f"Phase 3 lane 2 representative manifest is not ready: {', '.join(failures)}")


def build_phase3_return_width_bridge_lane2_post_fix_gate(
    *,
    baseline_raw_dir: Path,
    output_dir: Path,
    current_log_roots: Mapping[str, Path],
    baseline_log_roots: Mapping[str, Path],
    phase3_manifest_path: Optional[Path] = None,
    phase3_manifest_sha256: Optional[str] = None,
) -> Path:
    raw_dir = Path(baseline_raw_dir)
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)
    baseline_manifest = _read_json(raw_dir / "artifact_manifest.json")
    phase3_manifest, phase3_ref = _load_phase3_lane2_manifest(
        raw_dir=raw_dir,
        explicit_path=phase3_manifest_path,
    )
    frozen_entries = tuple(phase3_manifest.get("entries") or ())
    target_keys = tuple(_entry_key(entry) for entry in frozen_entries if isinstance(entry, Mapping))
    current_records = _records_by_key(current_log_roots, target_keys=target_keys)
    manifest_checks = _phase3_pre_fix_manifest_checks(
        phase3_manifest=phase3_manifest,
        phase3_manifest_ref=phase3_ref,
        expected_phase3_manifest_sha256=phase3_manifest_sha256,
        frozen_entries=frozen_entries,
    )
    entries = [
        _materialize_post_fix_entry(raw_entry, current_records)
        for raw_entry in frozen_entries
        if isinstance(raw_entry, Mapping)
    ]
    post_fix_gate = _post_fix_regression_gate(
        entries=entries,
        manifest_checks=manifest_checks,
    )
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase3_return_width_bridge_lane2_post_fix_gate",
        "artifact_role": "derived_audit_post_fix_gate",
        "baseline_id": baseline_manifest.get("baseline_id") or MISSING_SENTINEL,
        "baseline_git_head": baseline_manifest.get("git_head") or MISSING_SENTINEL,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "target_reason_ids": list(TARGET_REASON_IDS),
        "baseline_raw_artifact_ref": _file_ref(raw_dir / "artifact_manifest.json"),
        "phase3_pre_fix_manifest_ref": phase3_ref,
        "current_log_roots": {
            category: str(path) for category, path in sorted(current_log_roots.items())
        },
        "baseline_log_roots": {
            category: str(path) for category, path in sorted(baseline_log_roots.items())
        },
        "post_fix_policy": {
            "unknown_with_pending_proof": "accepted_pending_proof",
            "eq_requires_completed_abi_and_high_bit_proofs": True,
            "proof_id_source": "pre_fix_manifest_unknown_recovery_actions",
            "reject_eq_with_pending_width_bridge_reason": True,
            "reject_eq_with_any_width_bridge_proof_action": True,
        },
        "post_fix_regression_gate": post_fix_gate,
        "phase3_lane2_post_fix_ready": post_fix_gate["ready"],
        "entries": entries,
    }
    path = output / "return_width_bridge_lane2_post_fix_gate.json"
    _write_json(path, manifest)
    return path


def validate_phase3_return_width_bridge_lane2_post_fix_gate(manifest: Mapping[str, Any]) -> None:
    if manifest.get("phase3_lane2_post_fix_ready") is True:
        return
    gate = manifest.get("post_fix_regression_gate")
    failures = []
    if isinstance(gate, Mapping):
        summary = gate.get("summary")
        if isinstance(summary, Mapping):
            failures.extend(str(kind) for kind in summary.get("failed_kinds") or ())
    if not failures:
        raise ValueError("Phase 3 lane 2 post-fix gate is false without failure details")
    raise ValueError(f"Phase 3 lane 2 post-fix gate is not ready: {', '.join(failures)}")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Build Phase 3 lane 2 return-width bridge representative gate.",
    )
    parser.add_argument(
        "--gate-stage",
        choices=("pre-fix", "post-fix"),
        default="pre-fix",
    )
    parser.add_argument("--baseline-raw-dir", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument(
        "--current-log-root",
        action="append",
        default=[],
        metavar="CATEGORY=PATH",
    )
    parser.add_argument(
        "--baseline-log-root",
        action="append",
        default=[],
        metavar="CATEGORY=PATH",
    )
    parser.add_argument("--phase3-manifest", default=None)
    parser.add_argument("--phase3-manifest-sha256", default=None)
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)
    if args.gate_stage == "post-fix" and not args.phase3_manifest_sha256:
        parser.error("--phase3-manifest-sha256 is required when --gate-stage=post-fix")
    current_roots = _parse_roots(args.current_log_root)
    baseline_roots = _parse_roots(args.baseline_log_root)
    if args.gate_stage == "post-fix":
        path = build_phase3_return_width_bridge_lane2_post_fix_gate(
            baseline_raw_dir=Path(args.baseline_raw_dir),
            output_dir=Path(args.output_dir),
            current_log_roots=current_roots,
            baseline_log_roots=baseline_roots,
            phase3_manifest_path=Path(args.phase3_manifest) if args.phase3_manifest else None,
            phase3_manifest_sha256=args.phase3_manifest_sha256,
        )
    else:
        path = build_phase3_return_width_bridge_lane2_manifest(
            baseline_raw_dir=Path(args.baseline_raw_dir),
            output_dir=Path(args.output_dir),
            current_log_roots=current_roots,
            baseline_log_roots=baseline_roots,
        )
    if args.require_ready:
        if args.gate_stage == "post-fix":
            validate_phase3_return_width_bridge_lane2_post_fix_gate(_read_json(path))
        else:
            validate_phase3_return_width_bridge_lane2_manifest(_read_json(path))
    print(path)
    return 0


def _implementation_manifest(entries: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    return {
        "lane_id": "phase3_return_width_bridge_lane2",
        "lane_reason_ids": list(TARGET_REASON_IDS),
        "proof_completion_gate": {
            "eq_allowed_without_completed_proof": False,
            "pending_proof_keeps_final_result": STATUS_UNKNOWN,
            "completion_required_for_recovery": list(RETURN_WIDTH_BRIDGE_PROOF_STAGES),
            "required_recovery_actions": [
                "abi_relation",
                "high_bit_relation",
            ],
        },
        "expected_movement_entries": [
            {
                "id": entry.get("id"),
                "category": entry.get("category"),
                "function": entry.get("function"),
                "binary_pair": entry.get("binary_pair"),
                "expected_movements": entry.get("expected_movements") or (),
                "expected_return_width_bridge_targets": _canonical_targets(
                    _current_targets(entry)
                ),
                "required_completion_actions": _canonical_actions(
                    _current_width_actions(entry)
                ),
            }
            for entry in entries
        ],
    }


def _readiness(entries: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    checks: list[Dict[str, Any]] = []
    checks.append(_identity_set_check("phase3_lane2_entries_exact_set", DEFAULT_REPRESENTATIVES, entries))
    for entry in entries:
        checks.extend(_entry_readiness_checks(entry))
    failed = [check for check in checks if check.get("status") == "failed"]
    return {
        "ready": not failed,
        "summary": {
            "total": len(checks),
            "passed": sum(1 for check in checks if check.get("status") == "ok"),
            "failed": len(failed),
            "failed_kinds": sorted({str(check.get("kind")) for check in failed}),
        },
        "failure_kinds": sorted({str(check.get("kind")) for check in failed}),
        "checks": checks,
    }


def _entry_readiness_checks(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    checks: list[Dict[str, Any]] = []
    details = _entry_details(entry)
    baseline = entry.get("baseline_observation") if isinstance(entry.get("baseline_observation"), Mapping) else {}
    current = entry.get("current_observation") if isinstance(entry.get("current_observation"), Mapping) else {}
    checks.append(
        _ok("return_width_bridge_baseline_unknown", **details)
        if baseline.get("final_result") == STATUS_UNKNOWN
        else _failed(
            "return_width_bridge_baseline_unknown",
            current_result=baseline.get("final_result", MISSING_SENTINEL),
            **details,
        )
    )
    checks.append(
        _ok("return_width_bridge_current_unknown", **details)
        if current.get("final_result") == STATUS_UNKNOWN
        else _failed(
            "return_width_bridge_current_unknown",
            current_result=current.get("final_result", MISSING_SENTINEL),
            **details,
        )
    )
    checks.append(
        _ok("return_width_bridge_binary_direction", **details)
        if _binary_direction_matches(entry, current)
        else _failed(
            "return_width_bridge_binary_direction",
            observed_binary1_name=current.get("observed_binary1_name", MISSING_SENTINEL),
            observed_binary2_name=current.get("observed_binary2_name", MISSING_SENTINEL),
            **details,
        )
    )
    current_targets = _current_targets(entry)
    checks.append(
        _ok("return_width_bridge_current_targets_present", count=len(current_targets), **details)
        if current_targets
        else _failed("return_width_bridge_current_targets_present", count=0, **details)
    )
    checks.append(
        _ok(
            "return_width_bridge_current_actions_complete",
            count=len(_current_width_actions(entry)),
            target_count=len(current_targets),
            **details,
        )
        if current_targets and not _missing_width_bridge_actions(entry)
        else _failed(
            "return_width_bridge_current_actions_complete",
            missing=_missing_width_bridge_actions(entry),
            **details,
        )
    )
    checks.append(
        _ok("return_width_bridge_expected_movements_match_definition", **details)
        if _canonical_movements(entry.get("expected_movements"))
        == _canonical_movements(_expected_entry_for(entry).get("expected_movements"))
        else _failed(
            "return_width_bridge_expected_movements_match_definition",
            expected=_canonical_movements(_expected_entry_for(entry).get("expected_movements")),
            actual=_canonical_movements(entry.get("expected_movements")),
            **details,
        )
    )
    return checks


def _phase3_pre_fix_manifest_checks(
    *,
    phase3_manifest: Mapping[str, Any],
    phase3_manifest_ref: Mapping[str, Any],
    expected_phase3_manifest_sha256: Optional[str],
    frozen_entries: Sequence[Any],
) -> Sequence[Dict[str, Any]]:
    checks: list[Dict[str, Any]] = []
    checks.append(
        _ok("phase3_pre_fix_manifest_available", phase3_manifest_ref=dict(phase3_manifest_ref))
        if phase3_manifest_ref.get("sha256") != "__missing__"
        else _failed("phase3_pre_fix_manifest_available", phase3_manifest_ref=dict(phase3_manifest_ref))
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
            _ok("phase3_pre_fix_manifest_sha256", sha256=actual_sha256)
            if actual_sha256 == expected_phase3_manifest_sha256
            else _failed(
                "phase3_pre_fix_manifest_sha256",
                expected_sha256=expected_phase3_manifest_sha256,
                actual_sha256=actual_sha256 or MISSING_SENTINEL,
            )
        )
    checks.append(
        _ok("phase3_pre_fix_manifest_kind")
        if phase3_manifest.get("manifest_kind") == "phase3_return_width_bridge_lane2_representatives"
        else _failed(
            "phase3_pre_fix_manifest_kind",
            manifest_kind=phase3_manifest.get("manifest_kind", MISSING_SENTINEL),
        )
    )
    checks.append(
        _ok("phase3_pre_fix_manifest_ready")
        if phase3_manifest.get("phase3_lane2_ready") is True
        else _failed(
            "phase3_pre_fix_manifest_ready",
            phase3_lane2_ready=phase3_manifest.get("phase3_lane2_ready", MISSING_SENTINEL),
        )
    )
    checks.append(
        _ok("phase3_pre_fix_entries_non_empty", count=len(frozen_entries))
        if frozen_entries
        else _failed("phase3_pre_fix_entries_non_empty", count=0)
    )
    checks.append(_identity_set_check("phase3_pre_fix_entries_exact_set", DEFAULT_REPRESENTATIVES, frozen_entries))
    implementation = phase3_manifest.get("implementation_manifest")
    implementation_entries = ()
    if isinstance(implementation, Mapping):
        checks.append(_ok("phase3_pre_fix_implementation_manifest_available"))
        implementation_entries = implementation.get("expected_movement_entries") or ()
    else:
        checks.append(_failed("phase3_pre_fix_implementation_manifest_available"))
    checks.append(
        _identity_set_check(
            "phase3_pre_fix_implementation_entries_consistent",
            implementation_entries,
            frozen_entries,
        )
    )
    checks.extend(
        _pre_fix_entry_content_checks(
            frozen_entries=frozen_entries,
            implementation_entries=implementation_entries,
        )
    )
    return checks


def _pre_fix_entry_content_checks(
    *,
    frozen_entries: Sequence[Any],
    implementation_entries: Any,
) -> Sequence[Dict[str, Any]]:
    checks: list[Dict[str, Any]] = []
    expected_map = _entry_map(DEFAULT_REPRESENTATIVES)
    actual_map = _entry_map(frozen_entries)
    implementation_map = _entry_map(implementation_entries)
    for identity, expected_entry in sorted(expected_map.items()):
        actual = actual_map.get(identity)
        implementation = implementation_map.get(identity)
        details = {"entry": _identity_to_dict(identity)}
        expected_movements = _canonical_movements(expected_entry.get("expected_movements"))
        actual_movements = _canonical_movements(actual.get("expected_movements") if isinstance(actual, Mapping) else None)
        impl_movements = _canonical_movements(implementation.get("expected_movements") if isinstance(implementation, Mapping) else None)
        checks.append(
            _ok("phase3_pre_fix_entry_expected_movements_match_definition", **details)
            if actual_movements == expected_movements
            else _failed(
                "phase3_pre_fix_entry_expected_movements_match_definition",
                expected=expected_movements,
                actual=actual_movements,
                **details,
            )
        )
        checks.append(
            _ok("phase3_pre_fix_implementation_expected_movements_match_definition", **details)
            if impl_movements == expected_movements
            else _failed(
                "phase3_pre_fix_implementation_expected_movements_match_definition",
                expected=expected_movements,
                actual=impl_movements,
                **details,
            )
        )
        actual_targets = _canonical_targets(_current_targets(actual)) if isinstance(actual, Mapping) else ()
        impl_targets = _canonical_targets(
            implementation.get("expected_return_width_bridge_targets")
            if isinstance(implementation, Mapping)
            else None
        )
        checks.append(
            _ok("phase3_pre_fix_entry_targets_match_implementation", **details)
            if actual_targets and actual_targets == impl_targets
            else _failed(
                "phase3_pre_fix_entry_targets_match_implementation",
                expected=impl_targets,
                actual=actual_targets,
                **details,
            )
        )
        actual_actions = _canonical_actions(_current_width_actions(actual)) if isinstance(actual, Mapping) else ()
        impl_actions = _canonical_actions(
            implementation.get("required_completion_actions")
            if isinstance(implementation, Mapping)
            else None
        )
        checks.append(
            _ok("phase3_pre_fix_entry_actions_match_implementation", **details)
            if actual_actions and actual_actions == impl_actions
            else _failed(
                "phase3_pre_fix_entry_actions_match_implementation",
                expected=impl_actions,
                actual=actual_actions,
                **details,
            )
        )
    return checks


def _post_fix_regression_gate(
    *,
    entries: Sequence[Mapping[str, Any]],
    manifest_checks: Sequence[Mapping[str, Any]],
) -> Dict[str, Any]:
    checks: list[Dict[str, Any]] = [dict(check) for check in manifest_checks]
    for entry in entries:
        checks.append(
            _ok(
                "return_width_bridge_post_fix_expected_movement",
                entry_id=entry.get("id"),
                function=entry.get("function"),
                binary_pair=entry.get("binary_pair"),
                post_fix_status=entry.get("post_fix_status"),
            )
            if entry.get("post_fix_status") in {"pending_proof", "completed_recovery"}
            else _failed(
                "return_width_bridge_post_fix_expected_movement",
                entry_id=entry.get("id"),
                function=entry.get("function"),
                binary_pair=entry.get("binary_pair"),
                failures=entry.get("post_fix_failures") or (),
                current_result=(entry.get("current_observation") or {}).get("final_result"),
            )
        )
    failed = [check for check in checks if check.get("status") == "failed"]
    return {
        "gate_kind": "phase3_return_width_bridge_lane2_post_fix_regression",
        "baseline_mode": "pending_proof_or_completed_proof_against_pre_fix_manifest",
        "ready": not failed,
        "summary": {
            "total": len(checks),
            "passed": sum(1 for check in checks if check.get("status") == "ok"),
            "failed": len(failed),
            "failed_kinds": sorted({str(check.get("kind")) for check in failed}),
            "locked_gates": [
                "phase3_pre_fix_manifest_sha256",
                "return_width_bridge_object_target_key",
                "return_width_bridge_proof_obligation_id",
                "abi_relation_and_high_bit_proofs_required_before_eq",
                "no_pending_proof_gate_on_eq",
                "no_unresolved_width_bridge_proof_action_on_eq",
            ],
        },
        "checks": checks,
    }


def _materialize_entry(
    raw_entry: Mapping[str, Any],
    current_records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
    baseline_records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
) -> Dict[str, Any]:
    entry = dict(raw_entry)
    key = _entry_key(raw_entry)
    entry["baseline_observation"] = _observation(raw_entry, baseline_records.get(key))
    entry["current_observation"] = _observation(raw_entry, current_records.get(key))
    entry["target_object_keys"] = _canonical_targets(_current_targets(entry))
    entry["required_completion_actions"] = _canonical_actions(_current_width_actions(entry))
    return entry


def _materialize_post_fix_entry(
    frozen_entry: Mapping[str, Any],
    current_records: Mapping[Tuple[str, str, str], Mapping[str, Any]],
) -> Dict[str, Any]:
    entry = dict(frozen_entry)
    key = _entry_key(frozen_entry)
    entry["current_observation"] = _observation(frozen_entry, current_records.get(key))
    status, failures = _post_fix_status(entry)
    entry["post_fix_status"] = status
    entry["post_fix_failures"] = failures
    entry["pending_proof_obligations"] = (
        _pending_proof_obligations(entry) if status == "pending_proof" else []
    )
    return entry


def _post_fix_status(entry: Mapping[str, Any]) -> Tuple[str, Sequence[Dict[str, Any]]]:
    failures: list[Dict[str, Any]] = []
    current = entry.get("current_observation") if isinstance(entry.get("current_observation"), Mapping) else {}
    result = current.get("final_result")
    details = _entry_details(entry)
    if result == STATUS_TIMEOUT:
        failures.append(_failed("return_width_bridge_timeout_regression", **details))
        return "failed", failures
    if result == STATUS_EQ:
        failures.extend(_completed_recovery_failures(entry, current))
        if failures:
            return "failed", failures
        return "completed_recovery", ()
    if result != STATUS_UNKNOWN:
        failures.append(
            _failed(
                "return_width_bridge_unexpected_final_result",
                current_result=result or MISSING_SENTINEL,
                **details,
            )
        )
        return "failed", failures
    frozen_targets = _canonical_targets(entry.get("target_object_keys"))
    current_targets = _canonical_targets(_current_targets(entry))
    if not frozen_targets or current_targets != frozen_targets:
        failures.append(
            _failed(
                "return_width_bridge_target_set_changed",
                expected=frozen_targets,
                actual=current_targets,
                **details,
            )
        )
    frozen_actions = _canonical_actions(entry.get("required_completion_actions"))
    current_actions = _canonical_actions(_current_width_actions(entry))
    if not frozen_actions or current_actions != frozen_actions:
        failures.append(
            _failed(
                "return_width_bridge_required_actions_changed",
                expected=frozen_actions,
                actual=current_actions,
                **details,
            )
        )
    missing = _missing_width_bridge_actions(entry)
    if missing:
        failures.append(_failed("return_width_bridge_current_actions_complete", missing=missing, **details))
    if failures:
        return "failed", failures
    return "pending_proof", ()


def _observation(
    entry: Mapping[str, Any],
    record: Optional[Mapping[str, Any]],
) -> Dict[str, Any]:
    if record is None:
        return {
            "log_status": "missing",
            "final_result": "MISSING",
            "observed_reason_ids": [],
            "reason_records": [],
            "proof_actions": [],
            "reason_record_tuples": [],
            "proof_action_tuples": [],
        }
    payload = record.get("payload") if isinstance(record.get("payload"), Mapping) else {}
    reasons = _extract_final_unknown_reasons(payload)
    raw_actions = payload.get("unknown_recovery_actions")
    if not isinstance(raw_actions, Sequence) or isinstance(raw_actions, (str, bytes)):
        raw_actions = ()
    actions = coerce_unknown_recovery_actions(raw_actions)
    return {
        "log_status": "present",
        "log_path": record.get("relative_log_path") or MISSING_SENTINEL,
        "log_sha256": record.get("log_sha256") or MISSING_SENTINEL,
        "final_result": classify_result_payload(payload),
        "observed_function1_name": payload.get("function1_name") or MISSING_SENTINEL,
        "observed_function2_name": payload.get("function2_name") or MISSING_SENTINEL,
        "observed_binary1_name": payload.get("binary1_name") or MISSING_SENTINEL,
        "observed_binary2_name": payload.get("binary2_name") or MISSING_SENTINEL,
        "observed_left_binary_id": record.get("observed_left_binary_id") or MISSING_SENTINEL,
        "observed_right_binary_id": record.get("observed_right_binary_id") or MISSING_SENTINEL,
        "observed_reason_ids": sorted({reason.reason_id for reason in reasons}),
        "decision_gated_by_pending_proof": bool(payload.get("decision_gated_by_pending_proof")),
        "completed_recovery_proof_evidence": _completed_recovery_proof_summaries(payload),
        "reason_record_tuples": [
            list(_global_reason_tuple_from_record(reason, UnknownCountKind.REASON_RECORD.value))
            for reason in reasons
        ],
        "proof_action_tuples": [
            list(_global_reason_tuple_from_action(action))
            for action in actions
        ],
        "reason_records": [_reason_to_dict(reason) for reason in reasons],
        "proof_actions": [
            _action_to_dict(action, raw_actions[index] if index < len(raw_actions) else None)
            for index, action in enumerate(actions)
        ],
    }


def _reason_to_dict(reason: Any) -> Dict[str, Any]:
    return {
        "count_kind": reason.count_kind,
        "reason_id": reason.reason_id,
        "decision_effect": reason.decision_effect,
        "reason_scope": reason.reason_scope,
        "aggregation_unit": reason.aggregation_unit,
        "stage": reason.stage,
        "pair_or_case": reason.pair_or_case,
        "recovery_proof_kind": reason.recovery_proof_kind,
        "proof_stage": reason.proof_stage,
        "evidence_kind": reason.evidence_kind,
        "object_target_key": _jsonable(reason.object_target_key),
        "proof_obligation_id": _jsonable(reason.proof_obligation_id),
        "action_status": reason.action_status,
        "tuple": list(_global_reason_tuple_from_record(reason, UnknownCountKind.REASON_RECORD.value)),
    }


def _action_to_dict(action: Any, raw_action: Any) -> Dict[str, Any]:
    raw_has_proof_id = (
        isinstance(raw_action, Mapping)
        and "proof_obligation_id" in raw_action
        and raw_action.get("proof_obligation_id") is not None
    )
    raw_has_target = (
        isinstance(raw_action, Mapping)
        and "object_target_key" in raw_action
        and raw_action.get("object_target_key") is not None
    )
    return {
        "count_kind": action.count_kind,
        "reason_id": action.reason_id,
        "decision_effect": action.decision_effect,
        "reason_scope": action.reason_scope,
        "aggregation_unit": action.aggregation_unit,
        "stage": action.stage,
        "pair_or_case": action.pair_or_case,
        "proof_kind": action.proof_kind,
        "proof_stage": action.proof_stage,
        "status": action.status,
        "required_evidence": list(action.required_evidence or ()),
        "evidence_kind": action.evidence_kind,
        "object_target_key": _jsonable(action.object_target_key),
        "proof_obligation_id": _jsonable(action.proof_obligation_id),
        "raw_object_target_key_present": raw_has_target,
        "raw_proof_obligation_id_present": raw_has_proof_id,
        "tuple": list(_global_reason_tuple_from_action(action)),
    }


def _current_targets(entry: Any) -> Sequence[Any]:
    if not isinstance(entry, Mapping):
        return ()
    current = entry.get("current_observation")
    if not isinstance(current, Mapping):
        return ()
    targets = []
    for record in current.get("reason_records") or ():
        if not isinstance(record, Mapping):
            continue
        if record.get("reason_id") != "return_width_bridge_missing":
            continue
        target = record.get("object_target_key")
        if _object_target_key_is_specific_width_bridge(target):
            targets.append(target)
    return tuple(targets)


def _current_width_actions(entry: Any) -> Sequence[Mapping[str, Any]]:
    if not isinstance(entry, Mapping):
        return ()
    current = entry.get("current_observation")
    if not isinstance(current, Mapping):
        return ()
    actions = []
    for action in current.get("proof_actions") or ():
        if not isinstance(action, Mapping):
            continue
        if action.get("reason_id") != "return_width_bridge_missing":
            continue
        if action.get("proof_stage") not in RETURN_WIDTH_BRIDGE_PROOF_STAGES:
            continue
        if not _object_target_key_is_specific_width_bridge(action.get("object_target_key")):
            continue
        if action.get("proof_obligation_id") is None:
            continue
        if action.get("raw_proof_obligation_id_present") is not True:
            continue
        if action.get("raw_object_target_key_present") is not True:
            continue
        if not _proof_action_has_expected_id(action):
            continue
        if not _proof_action_matches_lane_definition(action):
            continue
        actions.append(action)
    return tuple(actions)


def _missing_width_bridge_actions(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    current_targets = _canonical_targets(_current_targets(entry))
    actions = _current_width_actions(entry)
    action_keys = {
        (
            _canonical_json(action.get("object_target_key")),
            action.get("proof_kind"),
            action.get("proof_stage"),
        )
        for action in actions
    }
    missing = []
    for target in current_targets:
        target_json = _canonical_json(target)
        for proof_kind, proof_stage in (
            ("abi_relation_proof", "abi_relation"),
            ("high_bit_proof", "high_bit_relation"),
        ):
            if (target_json, proof_kind, proof_stage) not in action_keys:
                missing.append(
                    {
                        "object_target_key": target,
                        "proof_kind": proof_kind,
                        "proof_stage": proof_stage,
                    }
                )
    return missing


def _completed_recovery_failures(
    entry: Mapping[str, Any],
    current: Mapping[str, Any],
) -> Sequence[Dict[str, Any]]:
    failures: list[Dict[str, Any]] = []
    details = _entry_details(entry)
    if current.get("decision_gated_by_pending_proof") is True:
        failures.append(_failed("return_width_bridge_decision_gated_by_pending_proof", **details))
    active_reasons = [
        reason_id
        for reason_id in current.get("observed_reason_ids") or ()
        if reason_id == "return_width_bridge_missing"
    ]
    if active_reasons:
        failures.append(
            _failed(
                "return_width_bridge_active_reason_not_cleared",
                active_reason_ids=active_reasons,
                **details,
            )
        )
    pending_actions = [
        action
        for action in current.get("proof_actions") or ()
        if isinstance(action, Mapping)
        and action.get("reason_id") == "return_width_bridge_missing"
    ]
    if pending_actions:
        failures.append(_failed("return_width_bridge_pending_proof_action_still_active", **details))
    required_actions = _canonical_actions(entry.get("required_completion_actions"))
    if not required_actions:
        failures.append(_failed("return_width_bridge_frozen_proof_actions_missing", **details))
        return failures
    completed = tuple(current.get("completed_recovery_proof_evidence") or ())
    if not completed:
        failures.append(_failed("return_width_bridge_completed_proof_required", **details))
        return failures
    for action in required_actions:
        if not any(_completed_evidence_matches_action(evidence, action) for evidence in completed):
            failures.append(
                _failed(
                    "return_width_bridge_completed_proof_required",
                    proof_stage=action.get("proof_stage") or MISSING_SENTINEL,
                    evidence_kind=action.get("evidence_kind") or MISSING_SENTINEL,
                    proof_kind=action.get("proof_kind") or MISSING_SENTINEL,
                    **details,
                )
            )
    return failures


def _pending_proof_obligations(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    current = entry.get("current_observation") if isinstance(entry.get("current_observation"), Mapping) else {}
    completed = tuple(current.get("completed_recovery_proof_evidence") or ())
    obligations = []
    for action in _canonical_actions(entry.get("required_completion_actions")):
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
                "proof_obligation_id": _jsonable(action.get("proof_obligation_id")),
                "completed_evidence_present": has_completed_evidence,
                "status": "completed_evidence_present" if has_completed_evidence else "pending_evidence",
            }
        )
    return obligations


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
    if not _object_target_key_is_specific_width_bridge(object_target_key):
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
    if not _completed_evidence_has_required_proof_content(
        evidence_summary,
        evidence,
        action,
        object_target_key,
    ):
        return False
    expected_id = _expected_proof_obligation_id(action, object_target_key=object_target_key)
    provided_id = _normalize_nested_tuple(
        evidence_summary.get("proof_obligation_id") or evidence.get("proof_obligation_id")
    )
    return (
        provided_id == expected_id
        and object_target_key == _normalize_nested_tuple(action.get("object_target_key"))
        and expected_id == _normalize_nested_tuple(action.get("proof_obligation_id"))
    )


def _completed_evidence_has_required_proof_content(
    evidence_summary: Mapping[str, Any],
    evidence: Mapping[str, Any],
    action: Mapping[str, Any],
    object_target_key: Any,
) -> bool:
    requirement = RETURN_WIDTH_BRIDGE_ACTION_REQUIREMENTS.get(
        (
            str(action.get("proof_kind") or MISSING_SENTINEL),
            str(action.get("proof_stage") or MISSING_SENTINEL),
        )
    )
    if requirement is None:
        return False
    expected_required = tuple(requirement["required_evidence"])
    actual_required = tuple(
        str(item)
        for item in (
            evidence_summary.get("required_evidence")
            or evidence.get("required_evidence")
            or ()
        )
    )
    if actual_required != expected_required:
        return False
    content = _completed_proof_content(evidence_summary, evidence, str(action.get("proof_kind")))
    if not isinstance(content, Mapping):
        return False
    if _nested_completed_proof_has_active_blocker(content):
        return False
    if str(action.get("proof_kind") or MISSING_SENTINEL) == "abi_relation_proof":
        return _abi_relation_proof_content_is_specific(content, object_target_key)
    if str(action.get("proof_kind") or MISSING_SENTINEL) == "high_bit_proof":
        return _high_bit_proof_content_is_specific(content, object_target_key)
    return False


def _completed_proof_content(
    evidence_summary: Mapping[str, Any],
    evidence: Mapping[str, Any],
    proof_kind: str,
) -> Any:
    for container in (evidence_summary, evidence):
        for field_name in ("proof_content", "proof", "proof_evidence"):
            content = container.get(field_name)
            if isinstance(content, Mapping):
                if proof_kind in content and isinstance(content[proof_kind], Mapping):
                    return content[proof_kind]
                return content
    return None


def _abi_relation_proof_content_is_specific(content: Mapping[str, Any], object_target_key: Any) -> bool:
    target = _normalize_nested_tuple(object_target_key)
    left = _find_width_side(target, "left")
    right = _find_width_side(target, "right")
    if not isinstance(left, tuple) or not isinstance(right, tuple):
        return False
    return (
        _calling_convention_evidence_is_specific(
            content.get("calling_convention"),
            left,
            right,
        )
        and _return_storage_evidence_is_specific(
            content.get("return_storage"),
            left,
            right,
        )
        and _narrow_return_width_evidence_is_specific(
            content.get("narrow_return_width"),
            target,
        )
    )


def _high_bit_proof_content_is_specific(content: Mapping[str, Any], object_target_key: Any) -> bool:
    target = _normalize_nested_tuple(object_target_key)
    return (
        _producer_width_evidence_is_specific(content.get("producer_width"), target)
        and _extension_semantics_evidence_is_specific(content.get("extension_semantics"))
        and _high_bits_evidence_is_specific(
            content.get("high_bits_irrelevant_or_equal"),
            target,
        )
    )


def _calling_convention_evidence_is_specific(value: Any, left: tuple, right: tuple) -> bool:
    if not isinstance(value, Mapping) or value.get("object_derived") is not True:
        return False
    left_function = _find_tagged_entry(left, "function_ref")
    right_function = _find_tagged_entry(right, "function_ref")
    return (
        _normalize_nested_tuple(value.get("left_function_ref")) == _normalize_nested_tuple(left_function)
        and _normalize_nested_tuple(value.get("right_function_ref")) == _normalize_nested_tuple(right_function)
        and value.get("relation") in ABI_CALLING_CONVENTION_RELATIONS
    )


def _return_storage_evidence_is_specific(value: Any, left: tuple, right: tuple) -> bool:
    if not isinstance(value, Mapping) or value.get("object_derived") is not True:
        return False
    left_storage = _find_tagged_entry(left, "return_storage")
    right_storage = _find_tagged_entry(right, "return_storage")
    return (
        _normalize_nested_tuple(value.get("left_return_storage")) == _normalize_nested_tuple(left_storage)
        and _normalize_nested_tuple(value.get("right_return_storage")) == _normalize_nested_tuple(right_storage)
        and value.get("relation") in ABI_RETURN_STORAGE_RELATIONS
    )


def _narrow_return_width_evidence_is_specific(value: Any, target: tuple) -> bool:
    widths = _find_tagged_entry(target, "return_widths")
    if not (
        isinstance(value, Mapping)
        and value.get("object_derived") is True
        and isinstance(widths, tuple)
        and len(widths) == 3
    ):
        return False
    narrow_width = min(int(widths[1]), int(widths[2]))
    return value.get("narrow_width") == narrow_width and value.get("proven") is True


def _producer_width_evidence_is_specific(value: Any, target: tuple) -> bool:
    widths = _find_tagged_entry(target, "return_widths")
    if not (
        isinstance(value, Mapping)
        and value.get("object_derived") is True
        and isinstance(widths, tuple)
        and len(widths) == 3
    ):
        return False
    return value.get("left_width") == widths[1] and value.get("right_width") == widths[2]


def _extension_semantics_evidence_is_specific(value: Any) -> bool:
    return (
        isinstance(value, Mapping)
        and value.get("object_derived") is True
        and _text_identity_is_specific(value.get("left_extension"))
        and _text_identity_is_specific(value.get("right_extension"))
        and value.get("relation") in HIGH_BIT_EXTENSION_RELATIONS
    )


def _high_bits_evidence_is_specific(value: Any, target: tuple) -> bool:
    widths = _find_tagged_entry(target, "return_widths")
    if not (
        isinstance(value, Mapping)
        and value.get("object_derived") is True
        and value.get("proven") is True
        and isinstance(widths, tuple)
        and len(widths) == 3
    ):
        return False
    return (
        value.get("narrow_width") == min(int(widths[1]), int(widths[2]))
        and value.get("wide_width") == max(int(widths[1]), int(widths[2]))
        and value.get("proof") in HIGH_BIT_PROOF_LABELS
    )


def _completed_evidence_has_active_blocker(evidence: Mapping[str, Any]) -> bool:
    for field_name in COMPLETED_PROOF_BLOCKER_FIELDS:
        if evidence.get(field_name):
            return True
    return False


def _nested_completed_proof_has_active_blocker(value: Any) -> bool:
    if isinstance(value, Mapping):
        for field_name in COMPLETED_PROOF_BLOCKER_FIELDS:
            if value.get(field_name):
                return True
        return any(_nested_completed_proof_has_active_blocker(item) for item in value.values())
    if isinstance(value, Sequence) and not isinstance(value, (str, bytes)):
        return any(_nested_completed_proof_has_active_blocker(item) for item in value)
    return False


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


def _proof_action_has_expected_id(action: Mapping[str, Any]) -> bool:
    target = _normalize_nested_tuple(action.get("object_target_key"))
    if not _object_target_key_is_specific_width_bridge(target):
        return False
    return _normalize_nested_tuple(action.get("proof_obligation_id")) == _expected_proof_obligation_id(
        action,
        object_target_key=target,
    )


def _proof_action_matches_lane_definition(action: Mapping[str, Any]) -> bool:
    requirement = RETURN_WIDTH_BRIDGE_ACTION_REQUIREMENTS.get(
        (
            str(action.get("proof_kind") or MISSING_SENTINEL),
            str(action.get("proof_stage") or MISSING_SENTINEL),
        )
    )
    if requirement is None:
        return False
    required_evidence = tuple(str(value) for value in (action.get("required_evidence") or ()))
    return (
        action.get("count_kind") == UnknownCountKind.PROOF_ACTION.value
        and action.get("reason_id") == "return_width_bridge_missing"
        and action.get("decision_effect") == "blocks_equivalence"
        and action.get("reason_scope") == "query"
        and action.get("aggregation_unit") == "pair"
        and str(action.get("status") or MISSING_SENTINEL) == requirement["status"]
        and str(action.get("evidence_kind") or MISSING_SENTINEL) == requirement["evidence_kind"]
        and required_evidence == tuple(requirement["required_evidence"])
    )


def _expected_proof_obligation_id(
    action: Mapping[str, Any],
    *,
    object_target_key: Any,
) -> Tuple[Any, ...]:
    return build_proof_obligation_id(
        action.get("reason_id"),
        action.get("proof_stage"),
        action.get("proof_kind"),
        action.get("evidence_kind"),
        object_target_key,
    )


def _object_target_key_is_specific_width_bridge(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if (
        not isinstance(normalized, tuple)
        or len(normalized) < 5
        or normalized[0] != "return_width_bridge"
        or _nested_contains_missing_sentinel(normalized)
    ):
        return False
    pair = _find_tagged_entry(normalized, "pair")
    widths = _find_tagged_entry(normalized, "return_widths")
    left = _find_width_side(normalized, "left")
    right = _find_width_side(normalized, "right")
    if not (
        isinstance(pair, tuple)
        and len(pair) == 2
        and _text_identity_is_specific(pair[1])
        and isinstance(widths, tuple)
        and len(widths) == 3
        and _is_positive_int(widths[1])
        and _is_positive_int(widths[2])
        and isinstance(left, tuple)
        and isinstance(right, tuple)
    ):
        return False
    return _width_side_is_specific(left, widths[1]) and _width_side_is_specific(
        right,
        widths[2],
    )


def _find_width_side(value: Any, side: str) -> Any:
    if not isinstance(value, tuple):
        return None
    for item in value:
        if isinstance(item, tuple) and len(item) >= 2 and item[0] == "return_width_side" and item[1] == side:
            return item
    return None


def _width_side_is_specific(value: Any, expected_return_size: int) -> bool:
    if not isinstance(value, tuple) or len(value) < 6:
        return False
    function_ref = _find_tagged_entry(value, "function_ref")
    return_size = _find_tagged_entry(value, "return_size")
    return_storage = _find_tagged_entry(value, "return_storage")
    return_case = _find_tagged_entry(value, "return_case_partition_member")
    return (
        isinstance(function_ref, tuple)
        and len(function_ref) >= 2
        and _function_ref_key_is_specific(function_ref[1])
        and isinstance(return_size, tuple)
        and len(return_size) == 2
        and return_size[1] == expected_return_size
        and isinstance(return_storage, tuple)
        and len(return_storage) >= 3
        and return_storage[1] not in {None, "", MISSING_SENTINEL}
        and return_storage[2] == expected_return_size
        and _return_case_partition_member_is_specific(return_case, expected_return_size)
    )


def _return_case_partition_member_is_specific(value: Any, expected_return_size: int) -> bool:
    if not isinstance(value, tuple) or len(value) < 6 or value[0] != "return_case_partition_member":
        return False
    member_index = value[1]
    source_indices = value[2]
    return_case = value[3]
    comparison_surface = value[4]
    value_evidence = value[5]
    return (
        _nonnegative_int_like(member_index)
        and _source_indices_are_specific(source_indices)
        and _return_case_key_is_specific(return_case, expected_member_index=member_index)
        and _comparison_surface_key_is_specific(comparison_surface, expected_return_size)
        and _return_value_evidence_is_specific(value_evidence)
    )


def _source_indices_are_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or not value:
        return False
    return all(_nonnegative_int_like(item) for item in value)


def _return_case_key_is_specific(value: Any, *, expected_member_index: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 8 or value[0] != "return_case":
        return False
    case_index = value[1]
    address = value[2]
    pcode_ref = value[3]
    pcode_identity = value[4]
    return_ordinal = value[5]
    return_value = value[6]
    guards = value[7]
    return (
        _nonnegative_int_like(case_index)
        and int(case_index) == int(expected_member_index)
        and _text_identity_is_specific(address)
        and _pcode_ref_is_specific(pcode_ref)
        and _text_identity_is_specific(pcode_identity)
        and _nonnegative_int_like(return_ordinal)
        and _structured_root_is_specific(return_value, {"expression"})
        and _return_guards_are_specific(guards)
    )


def _comparison_surface_key_is_specific(value: Any, expected_return_size: int) -> bool:
    if not isinstance(value, tuple) or len(value) != 4 or value[0] != "comparison_surface":
        return False
    return (
        value[1] == "return_value"
        and _is_positive_int(value[2])
        and value[2] == expected_return_size
    )


def _return_value_evidence_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 2 or value[0] != "value":
        return False
    return _structured_root_is_specific(value[1], {"expression"})


def _return_guards_are_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or not value:
        return False
    return all(_return_guard_key_is_specific(guard) for guard in value)


def _return_guard_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 4 or value[0] != "return_guard":
        return False
    return (
        isinstance(value[1], bool)
        and _structured_root_is_specific(value[2], {"condition"})
        and _structured_root_is_specific(value[3], {"expression"})
    )


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


def _pcode_address_ref_is_specific(value: Any, expected_kind: str) -> bool:
    if not isinstance(value, tuple) or len(value) != 3 or value[0] != expected_kind:
        return False
    return _text_identity_is_specific(value[1]) and _nonnegative_int_like(value[2])


def _function_ref_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 3:
        return False
    kind, binary_id, address_offset = value[:3]
    if kind not in {"function", "code_address"}:
        return False
    return _binary_id_is_specific(binary_id) and _nonnegative_int_like(address_offset)


def _binary_id_is_specific(value: Any) -> bool:
    return _text_identity_is_specific(value) and not value.strip().isdecimal()


def _nonnegative_int_like(value: Any) -> bool:
    if isinstance(value, bool) or value is None:
        return False
    try:
        return int(value) >= 0
    except (TypeError, ValueError):
        return False


def _int_like(value: Any) -> bool:
    if isinstance(value, bool) or value is None:
        return False
    try:
        int(value)
    except (TypeError, ValueError):
        return False
    return True


def _text_identity_is_specific(value: Any) -> bool:
    return isinstance(value, str) and value.strip() not in {"", MISSING_SENTINEL}


def _structured_evidence_is_specific(value: Any) -> bool:
    return _nested_has_specific_leaf(value) and not _nested_contains_missing(value)


def _structured_root_is_specific(value: Any, allowed_roots: set[str]) -> bool:
    if not isinstance(value, tuple) or len(value) < 2:
        return False
    return value[0] in allowed_roots and _structured_node_is_specific(value[1])


def _structured_node_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 2 or not _text_identity_is_specific(value[0]):
        return False
    root = value[0]
    if root not in STRUCTURED_EVIDENCE_NODE_ROOTS:
        return False
    if root in {"const", "literal"}:
        return _const_or_literal_node_is_specific(value)
    if root in {"parameter", "variable"}:
        return _named_value_node_is_specific(value)
    if root == "binary":
        return _binary_expression_node_is_specific(value)
    if root == "unary":
        return _unary_expression_node_is_specific(value)
    if root == "memory":
        return _memory_expression_node_is_specific(value)
    if root == "call":
        return _call_expression_node_is_specific(value)
    if root == "intrinsic":
        return _intrinsic_expression_node_is_specific(value)
    if root == "phi":
        return _phi_expression_node_is_specific(value)
    return False


def _const_or_literal_node_is_specific(value: tuple) -> bool:
    return (
        len(value) == 3
        and _typed_atom_key_is_specific(value[1])
        and _is_positive_int(value[2])
    )


def _named_value_node_is_specific(value: tuple) -> bool:
    return (
        len(value) == 4
        and _text_identity_is_specific(value[1])
        and _typed_atom_key_is_specific(value[2])
        and _is_positive_int(value[3])
    )


def _binary_expression_node_is_specific(value: tuple) -> bool:
    return (
        len(value) == 5
        and _text_identity_is_specific(value[1])
        and _is_positive_int(value[2])
        and _structured_node_is_specific(value[3])
        and _structured_node_is_specific(value[4])
    )


def _unary_expression_node_is_specific(value: tuple) -> bool:
    return (
        len(value) == 4
        and _text_identity_is_specific(value[1])
        and _is_positive_int(value[2])
        and _structured_node_is_specific(value[3])
    )


def _memory_expression_node_is_specific(value: tuple) -> bool:
    if len(value) < 4 or not _is_positive_int(value[1]):
        return False
    read_order = value[3]
    return (
        _structured_node_is_specific(value[2])
        and isinstance(read_order, tuple)
        and len(read_order) == 2
        and read_order[0] == "read_order"
        and _nonnegative_int_like(read_order[1])
    )


def _call_expression_node_is_specific(value: tuple) -> bool:
    return (
        len(value) == 4
        and _call_callee_key_is_specific(value[1])
        and _is_positive_int(value[2])
        and _structured_node_sequence_is_specific(value[3])
    )


def _intrinsic_expression_node_is_specific(value: tuple) -> bool:
    opcode = value[2] if len(value) >= 3 else None
    return (
        len(value) == 5
        and _text_identity_is_specific(value[1])
        and (opcode is None or _nonnegative_int_like(opcode))
        and _is_positive_int(value[3])
        and _structured_node_sequence_is_specific(value[4])
    )


def _phi_expression_node_is_specific(value: tuple) -> bool:
    if len(value) != 3 or not _is_positive_int(value[1]):
        return False
    branches = value[2]
    if not isinstance(branches, tuple) or not branches:
        return False
    for branch in branches:
        if not isinstance(branch, tuple) or len(branch) != 2:
            return False
        condition, branch_value = branch
        if not (
            _phi_condition_key_is_specific(condition)
            and _structured_node_is_specific(branch_value)
        ):
            return False
    return True


def _phi_condition_key_is_specific(value: Any) -> bool:
    if value == ("none",):
        return True
    return (
        isinstance(value, tuple)
        and len(value) == 3
        and value[0] == "cond"
        and _structured_node_is_specific(value[1])
        and isinstance(value[2], bool)
    )


def _structured_node_sequence_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple):
        return False
    return all(_structured_node_is_specific(item) for item in value)


def _call_callee_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or not value or not _text_identity_is_specific(value[0]):
        return False
    if _nested_contains_missing(value):
        return False
    if value[0] == "function_ref":
        return len(value) == 2 and _function_ref_key_is_specific(value[1])
    if value[0] in {"function", "code_address"}:
        return _function_ref_key_is_specific(value)
    if value[0] == "unknown_indirect_target":
        return _unknown_indirect_callee_key_is_specific(value)
    if value[0] == "call_target":
        return len(value) == 2 and _call_target_ref_key_is_specific(value[1])
    if value[0] == "external_symbol":
        return _external_symbol_key_is_specific(value)
    if value[0] == "import_stub":
        return _import_stub_key_is_specific(value)
    if value[0] == "thunk":
        return _thunk_key_is_specific(value)
    return False


def _unknown_indirect_callee_key_is_specific(value: tuple) -> bool:
    typed_target = _find_tagged_entry(value, "typed_target_expression")
    provenance = _find_tagged_entry(value, "provenance")
    return (
        isinstance(typed_target, tuple)
        and len(typed_target) == 2
        and _typed_target_expression_key_is_specific(typed_target[1])
        and isinstance(provenance, tuple)
        and len(provenance) == 2
        and _target_expression_provenance_is_specific(provenance[1])
    )


def _call_target_ref_key_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    return (
        isinstance(normalized, tuple)
        and len(normalized) >= 3
        and normalized[0] in {"function", "code_address"}
        and _binary_id_is_specific(normalized[1])
        and _nonnegative_int_like(normalized[2])
    )


def _external_symbol_key_is_specific(value: tuple) -> bool:
    library = _find_tagged_entry(value, "library")
    symbol = _find_tagged_entry(value, "symbol") or _find_tagged_entry(value, "name")
    import_address = _find_tagged_entry(value, "import_address")
    return (
        isinstance(library, tuple)
        and len(library) == 2
        and _text_identity_is_specific(library[1])
        and isinstance(symbol, tuple)
        and len(symbol) == 2
        and _text_identity_is_specific(symbol[1])
        and (
            import_address is None
            or (
                isinstance(import_address, tuple)
                and len(import_address) == 2
                and _address_or_offset_key_is_specific(import_address[1])
            )
        )
    )


def _import_stub_key_is_specific(value: tuple) -> bool:
    import_table = _find_tagged_entry(value, "import_table")
    import_address = _find_tagged_entry(value, "import_address")
    target_symbol = _find_tagged_entry(value, "target_symbol")
    return (
        isinstance(import_table, tuple)
        and len(import_table) == 2
        and _text_identity_is_specific(import_table[1])
        and isinstance(import_address, tuple)
        and len(import_address) == 2
        and _address_or_offset_key_is_specific(import_address[1])
        and isinstance(target_symbol, tuple)
        and len(target_symbol) == 2
        and _external_symbol_key_is_specific(_normalize_nested_tuple(target_symbol[1]))
    )


def _thunk_key_is_specific(value: tuple) -> bool:
    thunk_function = _find_tagged_entry(value, "thunk_function")
    resolved_target = _find_tagged_entry(value, "resolved_target")
    return (
        isinstance(thunk_function, tuple)
        and len(thunk_function) == 2
        and _call_target_ref_key_is_specific(thunk_function[1])
        and isinstance(resolved_target, tuple)
        and len(resolved_target) == 2
        and _call_callee_key_is_specific(_normalize_nested_tuple(resolved_target[1]))
    )


def _address_or_offset_key_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if _nonnegative_int_like(normalized):
        return True
    return (
        isinstance(normalized, tuple)
        and len(normalized) == 3
        and _text_identity_is_specific(normalized[0])
        and _text_identity_is_specific(normalized[1])
        and _nonnegative_int_like(normalized[2])
    )


def _target_expression_provenance_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if not isinstance(normalized, tuple) or not normalized or _nested_contains_missing(normalized):
        return False
    root = normalized[0]
    if root == "typed_target_expression":
        return len(normalized) == 2 and _typed_target_expression_key_is_specific(normalized[1])
    if root in {"expression", "condition"}:
        return _structured_root_is_specific(normalized, {root})
    if root in STRUCTURED_EVIDENCE_NODE_ROOTS:
        return _structured_node_is_specific(normalized)
    if root in {"storage", "runtime_ref"}:
        return len(normalized) == 2 and _provenance_payload_key_is_specific(normalized[1])
    if root == "expression_digest":
        return _expression_digest_key_is_specific(normalized)
    return False


def _provenance_payload_key_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    return (
        isinstance(normalized, tuple)
        and len(normalized) >= 2
        and _text_identity_is_specific(normalized[0])
        and not _nested_contains_missing(normalized)
        and not isinstance(normalized[1], str)
    )


def _expression_digest_key_is_specific(value: tuple) -> bool:
    digest = value[1] if len(value) > 1 else None
    complete = _find_tagged_entry(value, "complete")
    root = _find_tagged_entry(value, "root")
    source_atoms = _find_tagged_entry(value, "source_atoms")
    return (
        _hex_digest_is_specific(digest)
        and isinstance(complete, tuple)
        and len(complete) == 2
        and isinstance(complete[1], bool)
        and isinstance(root, tuple)
        and len(root) == 2
        and _provenance_payload_key_is_specific(root[1])
        and isinstance(source_atoms, tuple)
        and len(source_atoms) == 2
        and isinstance(source_atoms[1], tuple)
        and bool(source_atoms[1])
    )


def _hex_digest_is_specific(value: Any) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(char in "0123456789abcdefABCDEF" for char in value)
    )


def _typed_target_expression_key_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if not isinstance(normalized, tuple) or not normalized:
        return False
    if normalized[0] in {"expression", "condition"}:
        return _structured_root_is_specific(normalized, {normalized[0]})
    return _structured_node_is_specific(normalized)


def _typed_atom_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 2 or not _text_identity_is_specific(value[0]):
        return False
    kind, payload = value
    if kind == "int":
        return _int_like(payload)
    if kind == "bool":
        return isinstance(payload, bool) or payload in {0, 1}
    if kind == "bytes":
        return _hex_bytes_text_is_specific(payload)
    return False


def _hex_bytes_text_is_specific(value: Any) -> bool:
    if not _text_identity_is_specific(value) or len(value) % 2 != 0:
        return False
    return all(char in "0123456789abcdefABCDEF" for char in value)


def _nested_has_specific_leaf(value: Any) -> bool:
    if value is None or value == "" or value == MISSING_SENTINEL:
        return False
    if isinstance(value, tuple):
        return any(_nested_has_specific_leaf(item) for item in value)
    if isinstance(value, list):
        return any(_nested_has_specific_leaf(item) for item in value)
    return True


def _nested_contains_missing(value: Any) -> bool:
    if value is None or value == "" or value == MISSING_SENTINEL:
        return True
    if isinstance(value, tuple):
        return any(_nested_contains_missing(item) for item in value)
    if isinstance(value, list):
        return any(_nested_contains_missing(item) for item in value)
    return False


def _nested_contains_missing_sentinel(value: Any) -> bool:
    if value == MISSING_SENTINEL:
        return True
    if isinstance(value, tuple):
        return any(_nested_contains_missing_sentinel(item) for item in value)
    if isinstance(value, list):
        return any(_nested_contains_missing_sentinel(item) for item in value)
    return False


def _is_positive_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value > 0


def _find_tagged_entry(value: Any, tag: str) -> Any:
    if not isinstance(value, tuple):
        return None
    for item in value:
        if isinstance(item, tuple) and item and item[0] == tag:
            return item
    return None


def _canonical_movements(values: Any) -> Tuple[Dict[str, Any], ...]:
    if not isinstance(values, Sequence) or isinstance(values, (str, bytes)):
        return ()
    canonical = []
    for movement in values:
        if not isinstance(movement, Mapping):
            continue
        canonical.append(
            {
                "id": movement.get("id") or MISSING_SENTINEL,
                "count_kind": movement.get("count_kind") or MISSING_SENTINEL,
                "tuple": list(movement.get("tuple") or ()),
                "aggregation_unit": movement.get("aggregation_unit") or MISSING_SENTINEL,
                "stage": movement.get("stage") or MISSING_SENTINEL,
                "pair_or_case": movement.get("pair_or_case") or MISSING_SENTINEL,
                "expected_evidence_refs": list(movement.get("expected_evidence_refs") or ()),
                "expected_evidence_kind": movement.get("expected_evidence_kind") or MISSING_SENTINEL,
                "required_evidence": list(movement.get("required_evidence") or ()),
                "required_object_target_kind": movement.get("required_object_target_kind") or MISSING_SENTINEL,
                "require_proof_obligation_id": bool(movement.get("require_proof_obligation_id")),
            }
        )
    return tuple(sorted(canonical, key=_canonical_json))


def _canonical_targets(values: Any) -> Tuple[Any, ...]:
    if not isinstance(values, Sequence) or isinstance(values, (str, bytes)):
        return ()
    return tuple(sorted((_jsonable(value) for value in values), key=_canonical_json))


def _canonical_actions(values: Any) -> Tuple[Dict[str, Any], ...]:
    if not isinstance(values, Sequence) or isinstance(values, (str, bytes)):
        return ()
    canonical = []
    for action in values:
        if not isinstance(action, Mapping):
            continue
        canonical.append(
            {
                "reason_id": action.get("reason_id") or MISSING_SENTINEL,
                "proof_kind": action.get("proof_kind") or MISSING_SENTINEL,
                "proof_stage": action.get("proof_stage") or MISSING_SENTINEL,
                "status": action.get("status") or MISSING_SENTINEL,
                "evidence_kind": action.get("evidence_kind") or MISSING_SENTINEL,
                "required_evidence": list(action.get("required_evidence") or ()),
                "object_target_key": _jsonable(action.get("object_target_key")),
                "proof_obligation_id": _jsonable(action.get("proof_obligation_id")),
            }
        )
    return tuple(sorted(canonical, key=_canonical_json))


def _records_by_key(
    roots: Mapping[str, Path],
    *,
    target_keys: Optional[Sequence[Tuple[str, str, str]]] = None,
) -> Dict[Tuple[str, str, str], Mapping[str, Any]]:
    records: Dict[Tuple[str, str, str], Mapping[str, Any]] = {}
    target_key_set = set(target_keys or ())
    for category, root in roots.items():
        paths = _target_log_paths(str(category), Path(root), target_key_set) if target_key_set else sorted(Path(root).glob("*/*.log"))
        for path in paths:
            _add_record_from_path(records, str(category), path)
    return records


def _target_log_paths(
    category: str,
    root: Path,
    target_keys: Sequence[Tuple[str, str, str]],
) -> Sequence[Path]:
    paths = []
    for key_category, function, binary_pair in sorted(target_keys):
        if key_category != category:
            continue
        parts = binary_pair.split("_")
        if len(parts) != 2:
            continue
        left, right = parts
        candidates = (
            root / function / f"{function}_{left}_{right}.log",
            root / function / f"{function}_{right}_{left}.log",
        )
        for candidate in candidates:
            if candidate.is_file():
                paths.append(candidate)
                break
    return tuple(paths)


def _add_record_from_path(
    records: Dict[Tuple[str, str, str], Mapping[str, Any]],
    category: str,
    path: Path,
) -> None:
    function, binary_pair = _identity_from_path(path)
    observed_left, observed_right = _directed_binary_pair_from_path(path)
    payloads = extract_result_payloads_from_text(path.read_text(errors="replace"))
    if not payloads:
        return
    records[(category, function, _canonical_binary_pair(binary_pair))] = {
        "payload": payloads[-1],
        "relative_log_path": _display_path(path),
        "log_sha256": _sha256_file(path),
        "observed_left_binary_id": observed_left,
        "observed_right_binary_id": observed_right,
    }


def _load_phase3_lane2_manifest(
    *,
    raw_dir: Path,
    explicit_path: Optional[Path],
) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    candidates = []
    if explicit_path is not None:
        candidates.append(Path(explicit_path))
    else:
        candidates.append(
            raw_dir.parent
            / "audit"
            / "phase3_return_width_bridge_lane2"
            / "return_width_bridge_lane2_representatives.json"
        )
    for path in candidates:
        if path.is_file():
            return _read_json(path), _file_ref(path)
    fallback = candidates[0]
    return {}, {"path": str(fallback), "sha256": "__missing__"}


def _identity_set_check(kind: str, expected_entries: Any, actual_entries: Any) -> Dict[str, Any]:
    expected = sorted(_entry_map(expected_entries))
    actual = sorted(_entry_map(actual_entries))
    details = {
        "expected": [_identity_to_dict(identity) for identity in expected],
        "actual": [_identity_to_dict(identity) for identity in actual],
    }
    if expected == actual:
        return _ok(kind, **details)
    return _failed(kind, **details)


def _entry_map(entries: Any) -> Dict[Tuple[str, str, str], Mapping[str, Any]]:
    if not isinstance(entries, Sequence) or isinstance(entries, (str, bytes)):
        return {}
    result = {}
    for entry in entries:
        if not isinstance(entry, Mapping):
            continue
        result[_entry_key(entry)] = entry
    return result


def _entry_key(entry: Mapping[str, Any]) -> Tuple[str, str, str]:
    return (
        str(entry.get("category") or MISSING_SENTINEL),
        str(entry.get("function") or MISSING_SENTINEL),
        _canonical_binary_pair(str(entry.get("binary_pair") or MISSING_SENTINEL)),
    )


def _expected_entry_for(entry: Mapping[str, Any]) -> Mapping[str, Any]:
    return _entry_map(DEFAULT_REPRESENTATIVES).get(_entry_key(entry), {})


def _identity_to_dict(identity: Tuple[str, str, str]) -> Dict[str, str]:
    return {
        "category": identity[0],
        "function": identity[1],
        "binary_pair": identity[2],
    }


def _entry_details(entry: Mapping[str, Any]) -> Dict[str, Any]:
    return {
        "entry_id": entry.get("id"),
        "function": entry.get("function"),
        "binary_pair": entry.get("binary_pair"),
    }


def _binary_direction_matches(entry: Mapping[str, Any], observation: Mapping[str, Any]) -> bool:
    return (
        observation.get("observed_binary1_name") == entry.get("expected_observed_binary1_name")
        and observation.get("observed_binary2_name") == entry.get("expected_observed_binary2_name")
    )


def _identity_from_path(path: Path) -> Tuple[str, str]:
    stem = path.stem
    parts = stem.rsplit("_", 2)
    if len(parts) == 3:
        return parts[0], _canonical_binary_pair(f"{parts[1]}_{parts[2]}")
    return stem, stem


def _directed_binary_pair_from_path(path: Path) -> Tuple[str, str]:
    stem = path.stem
    parts = stem.rsplit("_", 2)
    if len(parts) == 3:
        return parts[1], parts[2]
    return MISSING_SENTINEL, MISSING_SENTINEL


def _canonical_binary_pair(value: str) -> str:
    parts = [part.strip() for part in value.replace("↔", "_").split("_") if part.strip()]
    if len(parts) == 2:
        return "_".join(sorted(parts))
    return value


def _jsonable(value: Any) -> Any:
    if isinstance(value, tuple):
        return [_jsonable(item) for item in value]
    if isinstance(value, list):
        return [_jsonable(item) for item in value]
    if isinstance(value, Mapping):
        return {str(key): _jsonable(val) for key, val in sorted(value.items(), key=lambda item: str(item[0]))}
    return value


def _normalize_nested_tuple(value: Any) -> Any:
    if isinstance(value, tuple):
        return tuple(_normalize_nested_tuple(item) for item in value)
    if isinstance(value, list):
        return tuple(_normalize_nested_tuple(item) for item in value)
    if isinstance(value, Mapping):
        return tuple(
            (str(key), _normalize_nested_tuple(val))
            for key, val in sorted(value.items(), key=lambda item: str(item[0]))
        )
    return value


def _canonical_json(value: Any) -> str:
    return json.dumps(_jsonable(value), sort_keys=True, separators=(",", ":"))


def _parse_roots(values: Sequence[str]) -> Dict[str, Path]:
    roots = {}
    for value in values:
        if "=" not in value:
            raise ValueError(f"expected CATEGORY=PATH root, got: {value}")
        category, path = value.split("=", 1)
        roots[category] = Path(path)
    return roots


def _read_json(path: Path) -> Dict[str, Any]:
    return json.loads(Path(path).read_text())


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with Path(path).open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _file_ref(path: Path) -> Dict[str, str]:
    return {
        "path": _display_path(path),
        "sha256": _sha256_file(path) if path.is_file() else "__missing__",
    }


def _display_path(path: Path) -> str:
    raw_path = Path(path)
    try:
        resolved = raw_path.resolve(strict=False)
        repo_root = _REPO_ROOT.resolve(strict=False)
    except OSError:
        return str(raw_path)
    try:
        return resolved.relative_to(repo_root).as_posix()
    except ValueError:
        pass
    resolved_text = resolved.as_posix()
    repo_text = repo_root.as_posix().rstrip("/")
    prefix = f"{repo_text}/"
    if resolved_text.casefold().startswith(prefix.casefold()):
        return resolved_text[len(prefix):]
    return str(raw_path)


def _ok(kind: str, **details: Any) -> Dict[str, Any]:
    result = {"kind": kind, "status": "ok"}
    result.update(details)
    return result


def _failed(kind: str, **details: Any) -> Dict[str, Any]:
    result = {"kind": kind, "status": "failed"}
    result.update(details)
    return result


if __name__ == "__main__":
    raise SystemExit(main())
