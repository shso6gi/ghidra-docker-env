# -*- coding: utf-8 -*-
"""Freeze Phase 3 lane 4 representatives for Method-B closure proof work."""

from __future__ import annotations

import argparse
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
)
from .phase3_return_width_bridge_lane2 import (
    _binary_direction_matches,
    _call_callee_key_is_specific,
    _canonical_json,
    _canonical_movements,
    _canonical_targets,
    _entry_details,
    _entry_key,
    _entry_map,
    _failed,
    _file_ref,
    _identity_set_check,
    _identity_to_dict,
    _jsonable,
    _nonnegative_int_like,
    _normalize_nested_tuple,
    _ok,
    _parse_roots,
    _read_json,
    _records_by_key,
    _sha256_file,
    _text_identity_is_specific,
    _write_json,
)
from .phase3_readonly_identity_lane3 import (
    _analysis_entry_key_is_specific,
    _comparison_surface_is_specific,
    _completed_evidence_has_active_blocker,
    _completed_recovery_proof_summaries,
    _guards_key_is_specific,
    _nested_completed_proof_has_active_blocker,
    _nested_contains_diagnostic_reason,
    _pcode_op_ref_is_specific,
    _readonly_value_entry_is_specific,
    _readonly_return_case_member_is_specific,
)
from ..equivalence.unknown_reason import (
    UNKNOWN_TUPLE_MISSING,
    UnknownCountKind,
    build_proof_obligation_id,
    coerce_unknown_recovery_actions,
)


MANIFEST_VERSION = 1
TARGET_REASON_IDS = ("method_b_closure_blocked",)
MISSING_SENTINEL = UNKNOWN_TUPLE_MISSING
METHOD_B_COVERING_PROOF_KIND = "proof_backed_covering_case"
METHOD_B_COVERING_PROOF_STAGE = "method_b_covering_case"
METHOD_B_COVERING_EVIDENCE_KIND = "seed_compensation"
METHOD_B_COVERING_REQUIRED_EVIDENCE = (
    "seed_compensation",
    "term_sequence",
    "pure_side_effect_profile",
)
METHOD_B_GUARD_PROOF_KIND = "guard_partition_completion"
METHOD_B_GUARD_PROOF_STAGE = "method_b_guard_partition"
METHOD_B_GUARD_EVIDENCE_KIND = "guard_partition"
METHOD_B_GUARD_REQUIRED_EVIDENCE = (
    "guard_partition",
    "partition_coverage_proof",
)
METHOD_B_ACTION_SPECS = (
    {
        "proof_kind": METHOD_B_COVERING_PROOF_KIND,
        "proof_stage": METHOD_B_COVERING_PROOF_STAGE,
        "evidence_kind": METHOD_B_COVERING_EVIDENCE_KIND,
        "required_evidence": METHOD_B_COVERING_REQUIRED_EVIDENCE,
    },
    {
        "proof_kind": METHOD_B_GUARD_PROOF_KIND,
        "proof_stage": METHOD_B_GUARD_PROOF_STAGE,
        "evidence_kind": METHOD_B_GUARD_EVIDENCE_KIND,
        "required_evidence": METHOD_B_GUARD_REQUIRED_EVIDENCE,
    },
)
METHOD_B_REASON_TUPLE = (
    UnknownCountKind.REASON_RECORD.value,
    "method_b_closure_blocked",
    "blocks_equivalence",
    "stage",
    METHOD_B_COVERING_PROOF_KIND,
    MISSING_SENTINEL,
    MISSING_SENTINEL,
)
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
LOOP_BINARY_NAMES = {
    "B10": "loop_method_b_test-mips64-clang-O1",
    "B13": "loop_method_b_test-mips64-gcc-O0",
}


def _method_b_action_tuple(spec: Mapping[str, Any]) -> Tuple[str, ...]:
    return (
        UnknownCountKind.PROOF_ACTION.value,
        "method_b_closure_blocked",
        "blocks_equivalence",
        "stage",
        str(spec["proof_kind"]),
        str(spec["proof_stage"]),
        "planned",
    )


def _expected_reason_record(movement_id: str) -> Dict[str, Any]:
    return {
        "id": movement_id,
        "count_kind": UnknownCountKind.REASON_RECORD.value,
        "tuple": list(METHOD_B_REASON_TUPLE),
        "aggregation_unit": "pair",
        "stage": "S_PAIRWISE",
        "pair_or_case": MISSING_SENTINEL,
        "expected_evidence_refs": ["loop_summary_guard_mismatch", "loop_summary_unproven"],
        "required_object_target_kind": "method_b_closure",
    }


def _expected_proof_action(movement_id: str, spec: Mapping[str, Any]) -> Dict[str, Any]:
    return {
        "id": movement_id,
        "count_kind": UnknownCountKind.PROOF_ACTION.value,
        "tuple": list(_method_b_action_tuple(spec)),
        "aggregation_unit": "pair",
        "stage": "S_PAIRWISE",
        "pair_or_case": MISSING_SENTINEL,
        "expected_evidence_refs": [str(spec["evidence_kind"])],
        "required_evidence": list(spec["required_evidence"]),
        "required_object_target_kind": "method_b_closure",
        "require_proof_obligation_id": True,
    }


DEFAULT_REPRESENTATIVES: Tuple[Mapping[str, Any], ...] = (
    {
        "id": "representative-method-b-even-index-step2-covering-guard",
        "category": "loop",
        "function": "lmb_sum_even_index_step2",
        "binary_pair": "B10_B13",
        "expected_observed_binary1_name": LOOP_BINARY_NAMES["B10"],
        "expected_observed_binary2_name": LOOP_BINARY_NAMES["B13"],
        "required_reason_ids": ["method_b_closure_blocked"],
        "role": "Method-B covering case and guard partition proof backlog",
        "expected_movements": [
            _expected_reason_record("method-b-closure-reason-record"),
            _expected_proof_action("method-b-covering-case-proof", METHOD_B_ACTION_SPECS[0]),
            _expected_proof_action("method-b-guard-partition-proof", METHOD_B_ACTION_SPECS[1]),
        ],
    },
)


def build_phase3_method_b_closure_lane4_manifest(
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
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "manifest_kind": "phase3_method_b_closure_lane4_representatives",
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
                "concrete loop function x binary_pair ids",
                "baseline/current UNKNOWN result",
                "current method_b_closure_blocked record preserves final UNKNOWN",
                "current proof actions carry raw object_target_key and proof_obligation_id",
                "method-b target is object-derived and excludes diagnostic reason prose",
                "covering-case and guard-partition proofs are both required before recovery",
            ],
        },
        "implementation_manifest": _implementation_manifest(entries),
        "readiness": readiness,
        "phase3_lane4_ready": readiness["ready"],
        "entries": entries,
    }
    path = output / "method_b_closure_lane4_representatives.json"
    _write_json(path, manifest)
    return path


def validate_phase3_method_b_closure_lane4_manifest(manifest: Mapping[str, Any]) -> None:
    if manifest.get("phase3_lane4_ready") is True:
        return
    readiness = manifest.get("readiness")
    failures = []
    if isinstance(readiness, Mapping):
        failures.extend(str(kind) for kind in readiness.get("failure_kinds") or ())
    if not failures:
        raise ValueError("Phase 3 lane 4 readiness is false without failure details")
    raise ValueError(f"Phase 3 lane 4 representative manifest is not ready: {', '.join(failures)}")


def build_phase3_method_b_closure_lane4_post_fix_gate(
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
    phase3_manifest, phase3_ref = _load_phase3_manifest(
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
        "manifest_kind": "phase3_method_b_closure_lane4_post_fix_gate",
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
            "eq_requires_completed_method_b_proofs": True,
            "proof_id_source": "pre_fix_manifest_unknown_recovery_actions",
            "reject_eq_with_pending_method_b_reason": True,
            "reject_eq_with_any_method_b_proof_action": True,
        },
        "post_fix_regression_gate": post_fix_gate,
        "phase3_lane4_post_fix_ready": post_fix_gate["ready"],
        "entries": entries,
    }
    path = output / "method_b_closure_lane4_post_fix_gate.json"
    _write_json(path, manifest)
    return path


def validate_phase3_method_b_closure_lane4_post_fix_gate(manifest: Mapping[str, Any]) -> None:
    if manifest.get("phase3_lane4_post_fix_ready") is True:
        return
    gate = manifest.get("post_fix_regression_gate")
    failures = []
    if isinstance(gate, Mapping):
        summary = gate.get("summary")
        if isinstance(summary, Mapping):
            failures.extend(str(kind) for kind in summary.get("failed_kinds") or ())
    if not failures:
        raise ValueError("Phase 3 lane 4 post-fix gate is false without failure details")
    raise ValueError(f"Phase 3 lane 4 post-fix gate is not ready: {', '.join(failures)}")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Build Phase 3 lane 4 Method-B closure representative gate.",
    )
    parser.add_argument("--gate-stage", choices=("pre-fix", "post-fix"), default="pre-fix")
    parser.add_argument("--baseline-raw-dir", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--current-log-root", action="append", default=[], metavar="CATEGORY=PATH")
    parser.add_argument("--baseline-log-root", action="append", default=[], metavar="CATEGORY=PATH")
    parser.add_argument("--phase3-manifest", default=None)
    parser.add_argument("--phase3-manifest-sha256", default=None)
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)
    if args.gate_stage == "post-fix" and not args.phase3_manifest_sha256:
        parser.error("--phase3-manifest-sha256 is required when --gate-stage=post-fix")
    current_roots = _parse_roots(args.current_log_root)
    baseline_roots = _parse_roots(args.baseline_log_root)
    if args.gate_stage == "post-fix":
        path = build_phase3_method_b_closure_lane4_post_fix_gate(
            baseline_raw_dir=Path(args.baseline_raw_dir),
            output_dir=Path(args.output_dir),
            current_log_roots=current_roots,
            baseline_log_roots=baseline_roots,
            phase3_manifest_path=Path(args.phase3_manifest) if args.phase3_manifest else None,
            phase3_manifest_sha256=args.phase3_manifest_sha256,
        )
    else:
        path = build_phase3_method_b_closure_lane4_manifest(
            baseline_raw_dir=Path(args.baseline_raw_dir),
            output_dir=Path(args.output_dir),
            current_log_roots=current_roots,
            baseline_log_roots=baseline_roots,
        )
    if args.require_ready:
        if args.gate_stage == "post-fix":
            validate_phase3_method_b_closure_lane4_post_fix_gate(_read_json(path))
        else:
            validate_phase3_method_b_closure_lane4_manifest(_read_json(path))
    print(path)
    return 0


def _implementation_manifest(entries: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    return {
        "lane_id": "phase3_method_b_closure_lane4",
        "lane_reason_ids": list(TARGET_REASON_IDS),
        "proof_completion_gate": {
            "eq_allowed_without_completed_proof": False,
            "pending_proof_keeps_final_result": STATUS_UNKNOWN,
            "completion_required_for_recovery": [
                METHOD_B_COVERING_PROOF_STAGE,
                METHOD_B_GUARD_PROOF_STAGE,
            ],
            "required_recovery_actions": [
                METHOD_B_COVERING_PROOF_STAGE,
                METHOD_B_GUARD_PROOF_STAGE,
            ],
        },
        "expected_movement_entries": [
            {
                "id": entry.get("id"),
                "category": entry.get("category"),
                "function": entry.get("function"),
                "binary_pair": entry.get("binary_pair"),
                "expected_movements": entry.get("expected_movements") or (),
                "expected_method_b_closure_targets": _canonical_targets(_current_targets(entry)),
                "required_completion_actions": _canonical_actions(_current_method_b_actions(entry)),
            }
            for entry in entries
        ],
    }


def _readiness(entries: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    checks: list[Dict[str, Any]] = []
    checks.append(_identity_set_check("phase3_lane4_entries_exact_set", DEFAULT_REPRESENTATIVES, entries))
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
        _ok("method_b_closure_baseline_unknown", **details)
        if baseline.get("final_result") == STATUS_UNKNOWN
        else _failed(
            "method_b_closure_baseline_unknown",
            current_result=baseline.get("final_result", MISSING_SENTINEL),
            **details,
        )
    )
    checks.append(
        _ok("method_b_closure_current_unknown", **details)
        if current.get("final_result") == STATUS_UNKNOWN
        else _failed(
            "method_b_closure_current_unknown",
            current_result=current.get("final_result", MISSING_SENTINEL),
            **details,
        )
    )
    checks.append(
        _ok("method_b_closure_binary_direction", **details)
        if _binary_direction_matches(entry, current)
        else _failed(
            "method_b_closure_binary_direction",
            observed_binary1_name=current.get("observed_binary1_name", MISSING_SENTINEL),
            observed_binary2_name=current.get("observed_binary2_name", MISSING_SENTINEL),
            **details,
        )
    )
    current_targets = _current_targets(entry)
    checks.append(
        _ok("method_b_closure_current_targets_present", count=len(current_targets), **details)
        if current_targets
        else _failed("method_b_closure_current_targets_present", count=0, **details)
    )
    checks.append(
        _ok(
            "method_b_closure_current_actions_complete",
            count=len(_current_method_b_actions(entry)),
            target_count=len(current_targets),
            **details,
        )
        if current_targets and not _missing_method_b_actions(entry)
        else _failed(
            "method_b_closure_current_actions_complete",
            missing=_missing_method_b_actions(entry),
            **details,
        )
    )
    checks.append(
        _ok("method_b_closure_expected_movements_match_definition", **details)
        if _canonical_movements(entry.get("expected_movements"))
        == _canonical_movements(_expected_entry_for(entry).get("expected_movements"))
        else _failed(
            "method_b_closure_expected_movements_match_definition",
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
        if phase3_manifest.get("manifest_kind") == "phase3_method_b_closure_lane4_representatives"
        else _failed(
            "phase3_pre_fix_manifest_kind",
            manifest_kind=phase3_manifest.get("manifest_kind", MISSING_SENTINEL),
        )
    )
    checks.append(
        _ok("phase3_pre_fix_manifest_ready")
        if phase3_manifest.get("phase3_lane4_ready") is True
        else _failed(
            "phase3_pre_fix_manifest_ready",
            phase3_lane4_ready=phase3_manifest.get("phase3_lane4_ready", MISSING_SENTINEL),
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
            implementation.get("expected_method_b_closure_targets")
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
        actual_actions = _canonical_actions(_current_method_b_actions(actual)) if isinstance(actual, Mapping) else ()
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
                "method_b_closure_post_fix_expected_movement",
                entry_id=entry.get("id"),
                function=entry.get("function"),
                binary_pair=entry.get("binary_pair"),
                post_fix_status=entry.get("post_fix_status"),
            )
            if entry.get("post_fix_status") in {"pending_proof", "completed_recovery"}
            else _failed(
                "method_b_closure_post_fix_expected_movement",
                entry_id=entry.get("id"),
                function=entry.get("function"),
                binary_pair=entry.get("binary_pair"),
                failures=entry.get("post_fix_failures") or (),
                current_result=(entry.get("current_observation") or {}).get("final_result"),
            )
        )
    failed = [check for check in checks if check.get("status") == "failed"]
    return {
        "gate_kind": "phase3_method_b_closure_lane4_post_fix_regression",
        "baseline_mode": "pending_proof_or_completed_proof_against_pre_fix_manifest",
        "ready": not failed,
        "summary": {
            "total": len(checks),
            "passed": sum(1 for check in checks if check.get("status") == "ok"),
            "failed": len(failed),
            "failed_kinds": sorted({str(check.get("kind")) for check in failed}),
            "locked_gates": [
                "phase3_pre_fix_manifest_sha256",
                "method_b_closure_object_target_key",
                "method_b_closure_proof_obligation_id",
                "method_b_completed_proof_required_before_eq",
                "no_pending_proof_gate_on_eq",
                "no_unresolved_method_b_proof_action_on_eq",
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
    entry["required_completion_actions"] = _canonical_actions(_current_method_b_actions(entry))
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
    return entry


def _post_fix_status(entry: Mapping[str, Any]) -> Tuple[str, Sequence[Dict[str, Any]]]:
    failures: list[Dict[str, Any]] = []
    current = entry.get("current_observation") if isinstance(entry.get("current_observation"), Mapping) else {}
    result = current.get("final_result")
    details = _entry_details(entry)
    if result == STATUS_TIMEOUT:
        failures.append(_failed("method_b_closure_timeout_regression", **details))
        return "failed", failures
    if result == STATUS_EQ:
        failures.extend(_completed_recovery_failures(entry, current))
        if failures:
            return "failed", failures
        return "completed_recovery", ()
    if result != STATUS_UNKNOWN:
        failures.append(
            _failed(
                "method_b_closure_unexpected_final_result",
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
                "method_b_closure_target_set_changed",
                expected=frozen_targets,
                actual=current_targets,
                **details,
            )
        )
    frozen_actions = _canonical_actions(entry.get("required_completion_actions"))
    current_actions = _canonical_actions(_current_method_b_actions(entry))
    if not frozen_actions or current_actions != frozen_actions:
        failures.append(
            _failed(
                "method_b_closure_required_actions_changed",
                expected=frozen_actions,
                actual=current_actions,
                **details,
            )
        )
    missing = _missing_method_b_actions(entry)
    if missing:
        failures.append(_failed("method_b_closure_current_actions_complete", missing=missing, **details))
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
        if record.get("reason_id") != "method_b_closure_blocked":
            continue
        target = record.get("object_target_key")
        if _object_target_key_is_specific_method_b_closure(target):
            targets.append(target)
    return tuple(targets)


def _current_method_b_actions(entry: Any) -> Sequence[Mapping[str, Any]]:
    if not isinstance(entry, Mapping):
        return ()
    current = entry.get("current_observation")
    if not isinstance(current, Mapping):
        return ()
    actions = []
    for action in current.get("proof_actions") or ():
        if not isinstance(action, Mapping):
            continue
        if action.get("reason_id") != "method_b_closure_blocked":
            continue
        if not _method_b_action_spec_for(action):
            continue
        if not _object_target_key_is_specific_method_b_closure(action.get("object_target_key")):
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


def _missing_method_b_actions(entry: Mapping[str, Any]) -> Sequence[Dict[str, Any]]:
    current_targets = _canonical_targets(_current_targets(entry))
    actions = _current_method_b_actions(entry)
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
        for spec in METHOD_B_ACTION_SPECS:
            key = (target_json, spec["proof_kind"], spec["proof_stage"])
            if key not in action_keys:
                missing.append(
                    {
                        "object_target_key": target,
                        "proof_kind": spec["proof_kind"],
                        "proof_stage": spec["proof_stage"],
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
        failures.append(_failed("method_b_closure_decision_gated_by_pending_proof", **details))
    active_reasons = [
        reason_id
        for reason_id in current.get("observed_reason_ids") or ()
        if _text_identity_is_specific(reason_id)
    ]
    if active_reasons:
        failures.append(
            _failed(
                "method_b_closure_active_reason_not_cleared",
                active_reason_ids=active_reasons,
                **details,
            )
        )
    pending_actions = [
        action
        for action in current.get("proof_actions") or ()
        if isinstance(action, Mapping)
    ]
    if pending_actions:
        failures.append(_failed("method_b_closure_pending_proof_action_still_active", **details))
    required_actions = _canonical_actions(entry.get("required_completion_actions"))
    if not required_actions:
        failures.append(_failed("method_b_closure_frozen_proof_actions_missing", **details))
        return failures
    completed = tuple(current.get("completed_recovery_proof_evidence") or ())
    if not completed:
        failures.append(_failed("method_b_closure_completed_proof_required", **details))
        return failures
    for action in required_actions:
        if not any(_completed_evidence_matches_action(evidence, action) for evidence in completed):
            failures.append(
                _failed(
                    "method_b_closure_completed_proof_required",
                    proof_stage=action.get("proof_stage") or MISSING_SENTINEL,
                    evidence_kind=action.get("evidence_kind") or MISSING_SENTINEL,
                    proof_kind=action.get("proof_kind") or MISSING_SENTINEL,
                    **details,
                )
            )
    return failures


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
    object_target_key = _normalize_nested_tuple(
        evidence_summary.get("object_target_key") or evidence.get("object_target_key")
    )
    if not _object_target_key_is_specific_method_b_closure(object_target_key):
        return False
    if (
        str(evidence_summary.get("reason_id") or evidence.get("reason_id") or MISSING_SENTINEL)
        != str(action.get("reason_id") or MISSING_SENTINEL)
        or str(evidence_summary.get("proof_stage") or evidence.get("proof_stage") or MISSING_SENTINEL)
        != str(action.get("proof_stage") or MISSING_SENTINEL)
        or str(evidence_summary.get("proof_kind") or evidence.get("proof_kind") or MISSING_SENTINEL)
        != str(action.get("proof_kind") or MISSING_SENTINEL)
        or str(evidence_summary.get("evidence_kind") or evidence.get("evidence_kind") or MISSING_SENTINEL)
        != str(action.get("evidence_kind") or MISSING_SENTINEL)
    ):
        return False
    if _completed_evidence_has_active_blocker(evidence):
        return False
    if not _completed_evidence_has_required_proof_content(evidence_summary, evidence, action, object_target_key):
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
    spec = _method_b_action_spec_for(action)
    if not spec:
        return False
    actual_required = tuple(
        str(item)
        for item in (
            evidence_summary.get("required_evidence")
            or evidence.get("required_evidence")
            or ()
        )
    )
    if actual_required != tuple(spec["required_evidence"]):
        return False
    content = _completed_proof_content(evidence_summary, evidence)
    if not isinstance(content, Mapping):
        return False
    if _nested_completed_proof_has_active_blocker(content):
        return False
    return _method_b_proof_content_is_specific(content, action, object_target_key)


def _completed_proof_content(evidence_summary: Mapping[str, Any], evidence: Mapping[str, Any]) -> Any:
    for container in (evidence_summary, evidence):
        for field_name in ("proof_content", "proof", "proof_evidence"):
            content = container.get(field_name)
            if isinstance(content, Mapping):
                proof_kind = evidence_summary.get("proof_kind") or evidence.get("proof_kind")
                if proof_kind in content and isinstance(content[proof_kind], Mapping):
                    return content[proof_kind]
                return content
    return None


def _method_b_proof_content_is_specific(
    content: Mapping[str, Any],
    action: Mapping[str, Any],
    object_target_key: Any,
) -> bool:
    target = _normalize_nested_tuple(object_target_key)
    if (
        content.get("object_derived") is not True
        or _normalize_nested_tuple(content.get("object_target_key")) != target
    ):
        return False
    proof_stage = str(action.get("proof_stage") or "")
    if proof_stage == METHOD_B_COVERING_PROOF_STAGE:
        return (
            _proof_status_value_is_complete(content.get("seed_compensation"))
            and _proof_status_value_is_complete(content.get("term_sequence"))
            and _proof_status_value_is_complete(content.get("pure_side_effect_profile"))
        )
    if proof_stage == METHOD_B_GUARD_PROOF_STAGE:
        return (
            _proof_status_value_is_complete(content.get("guard_partition"))
            and _proof_status_value_is_complete(content.get("partition_coverage_proof"))
        )
    return False


def _proof_status_value_is_complete(value: Any) -> bool:
    return str(value or "") in {"complete", "completed", "covered", "matched", "proven", "checked", "vacuous"}


def _object_target_key_is_specific_method_b_closure(value: Any) -> bool:
    target = _normalize_nested_tuple(value)
    if not isinstance(target, tuple) or len(target) != 4 or target[0] != "method_b_closure":
        return False
    pair = target[1]
    if not (
        isinstance(pair, tuple)
        and len(pair) == 2
        and pair[0] == "pair"
        and _text_identity_is_specific(pair[1])
    ):
        return False
    if _nested_contains_diagnostic_reason(target):
        return False
    return _method_b_side_is_specific(target[2], "left") and _method_b_side_is_specific(target[3], "right")


def _method_b_side_is_specific(value: Any, expected_side: str) -> bool:
    side = _normalize_nested_tuple(value)
    if not isinstance(side, tuple) or len(side) != 6:
        return False
    if side[0] != "method_b_closure_side" or side[1] != expected_side:
        return False
    return (
        _analysis_entry_key_is_specific(side[2])
        and _method_b_return_case_member_is_specific(side[3])
        and _method_b_loop_value_entry_is_specific(side[4])
        and _guards_key_is_specific(side[5], allow_empty=True)
    )


def _method_b_return_case_member_is_specific(value: Any) -> bool:
    if _readonly_return_case_member_is_specific(value):
        return True
    member = _normalize_nested_tuple(value)
    if not isinstance(member, tuple) or len(member) != 7 or member[0] != "readonly_return_case_partition_member":
        return False
    case_index, source_indices = member[1], member[2]
    return_case, comparison_surface, value_entry, guards = member[3], member[4], member[5], member[6]
    if not (_nonnegative_int_like(case_index) and _method_b_source_indices_are_specific(source_indices)):
        return False
    return (
        _method_b_return_case_key_is_specific(return_case, case_index)
        and _comparison_surface_is_specific(comparison_surface)
        and _method_b_return_value_entry_is_specific(value_entry)
        and _guards_key_is_specific(guards, allow_empty=True)
    )


def _method_b_source_indices_are_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    return isinstance(normalized, tuple) and bool(normalized) and all(_nonnegative_int_like(item) for item in normalized)


def _method_b_return_case_key_is_specific(value: Any, case_index: Any) -> bool:
    case = _normalize_nested_tuple(value)
    return (
        isinstance(case, tuple)
        and len(case) == 6
        and case[0] == "return_case"
        and case[1] == case_index
        and _text_identity_is_specific(case[2])
        and _pcode_op_ref_is_specific(case[3])
        and _text_identity_is_specific(case[4])
        and _nonnegative_int_like(case[5])
    )


def _method_b_return_value_entry_is_specific(value: Any) -> bool:
    if _readonly_value_entry_is_specific(value):
        return True
    normalized = _normalize_nested_tuple(value)
    return (
        isinstance(normalized, tuple)
        and len(normalized) == 2
        and normalized[0] == "value"
        and _method_b_expression_key_is_specific(normalized[1])
    )


def _method_b_loop_value_entry_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    return (
        isinstance(normalized, tuple)
        and len(normalized) == 2
        and normalized[0] == "loop_value"
        and _method_b_loop_value_is_specific(normalized[1])
    )


def _method_b_loop_value_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if not isinstance(normalized, tuple) or len(normalized) != 4 or normalized[0] != "method_b_loop_value":
        return False
    runtime_ref, loop_summary, expression_key = normalized[1], normalized[2], normalized[3]
    if runtime_ref is not None and not _method_b_runtime_ref_key_is_specific(runtime_ref):
        return False
    if loop_summary is not None and not _method_b_loop_summary_key_is_specific(loop_summary):
        return False
    return _method_b_expression_key_is_specific(expression_key)


def _method_b_expression_key_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if not isinstance(normalized, tuple) or len(normalized) != 2:
        return False
    if _nested_contains_missing_sentinel_or_empty(normalized) or _nested_contains_diagnostic_reason(normalized):
        return False
    root = normalized[0]
    payload = normalized[1]
    if root == "expression":
        return _method_b_expression_payload_is_specific(payload)
    if root == "runtime_ref":
        return _method_b_runtime_ref_key_is_specific(payload)
    return False


def _method_b_expression_payload_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    if not isinstance(normalized, tuple) or not normalized or not _text_identity_is_specific(normalized[0]):
        return False
    if _nested_contains_missing_sentinel_or_empty(normalized) or _nested_contains_diagnostic_reason(normalized):
        return False
    root = normalized[0]
    allowed_roots = {
        "expression",
        "condition",
        "const",
        "literal",
        "parameter",
        "variable",
        "binary",
        "unary",
        "memory",
        "call",
        "intrinsic",
        "phi",
    }
    if root not in allowed_roots:
        return False
    if root in {"expression", "condition"}:
        return len(normalized) >= 2 and _method_b_expression_payload_is_specific(normalized[1])
    if root in {"const", "literal"}:
        return (
            len(normalized) == 3
            and _method_b_typed_atom_key_is_specific(normalized[1])
            and _positive_int_like(normalized[2])
        )
    if root in {"parameter", "variable"}:
        return (
            len(normalized) == 4
            and _text_identity_is_specific(normalized[1])
            and _method_b_typed_atom_key_is_specific(normalized[2])
            and _positive_int_like(normalized[3])
        )
    if root == "binary":
        return (
            len(normalized) == 5
            and _text_identity_is_specific(normalized[1])
            and _positive_int_like(normalized[2])
            and _method_b_expression_payload_is_specific(normalized[3])
            and _method_b_expression_payload_is_specific(normalized[4])
        )
    if root == "unary":
        return (
            len(normalized) == 4
            and _text_identity_is_specific(normalized[1])
            and _positive_int_like(normalized[2])
            and _method_b_expression_payload_is_specific(normalized[3])
        )
    if root == "memory":
        if len(normalized) < 4 or not _positive_int_like(normalized[1]):
            return False
        read_order = normalized[3]
        return (
            _method_b_expression_payload_is_specific(normalized[2])
            and isinstance(read_order, tuple)
            and len(read_order) == 2
            and read_order[0] == "read_order"
            and (read_order[1] is None or _nonnegative_int_like(read_order[1]))
        )
    if root == "call":
        return (
            len(normalized) == 4
            and _call_callee_key_is_specific(normalized[1])
            and _positive_int_like(normalized[2])
            and _method_b_expression_sequence_is_specific(normalized[3])
        )
    if root == "intrinsic":
        opcode = normalized[2] if len(normalized) >= 3 else None
        return (
            len(normalized) == 5
            and _text_identity_is_specific(normalized[1])
            and (opcode is None or _nonnegative_int_like(opcode))
            and _positive_int_like(normalized[3])
            and _method_b_expression_sequence_is_specific(normalized[4])
        )
    if root == "phi":
        if len(normalized) != 3 or not _positive_int_like(normalized[1]):
            return False
        branches = normalized[2]
        if not isinstance(branches, tuple) or not branches:
            return False
        return all(_method_b_phi_branch_is_specific(branch) for branch in branches)
    return False


def _method_b_typed_atom_key_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    return (
        isinstance(normalized, tuple)
        and len(normalized) == 2
        and _text_identity_is_specific(normalized[0])
        and not _nested_contains_missing_sentinel_or_empty(normalized)
        and not _nested_contains_diagnostic_reason(normalized)
    )


def _method_b_expression_sequence_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    return isinstance(normalized, tuple) and all(_method_b_expression_payload_is_specific(item) for item in normalized)


def _method_b_phi_branch_is_specific(value: Any) -> bool:
    branch = _normalize_nested_tuple(value)
    if not isinstance(branch, tuple) or len(branch) != 2:
        return False
    condition, branch_value = branch
    if condition != ("none",) and not (
        isinstance(condition, tuple)
        and len(condition) == 3
        and condition[0] == "cond"
        and _method_b_expression_payload_is_specific(condition[1])
        and isinstance(condition[2], bool)
    ):
        return False
    return _method_b_expression_payload_is_specific(branch_value)


def _positive_int_like(value: Any) -> bool:
    return _nonnegative_int_like(value) and int(value) > 0


def _method_b_runtime_ref_key_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    return (
        isinstance(normalized, tuple)
        and len(normalized) >= 2
        and normalized[0] in {
            "readonly_reduction",
            "readonly_reduction_proof_semantic",
            "readonly_reduction_loop_semantic",
            "readonly_reduction_semantic",
            "counted_loop_summary",
            "counted_loop_summary_loop_semantic",
            "counted_loop_summary_semantic",
        }
        and not _nested_contains_missing_sentinel_or_empty(normalized)
        and not _nested_contains_diagnostic_reason(normalized)
    )


def _method_b_loop_summary_key_is_specific(value: Any) -> bool:
    normalized = _normalize_nested_tuple(value)
    return (
        isinstance(normalized, tuple)
        and len(normalized) >= 2
        and normalized[0] in {"loop_summary", "loop_summary_method_b"}
        and not _nested_contains_missing_sentinel_or_empty(normalized)
        and not _nested_contains_diagnostic_reason(normalized)
    )


def _nested_contains_missing_sentinel_or_empty(value: Any) -> bool:
    if value == "" or value == MISSING_SENTINEL:
        return True
    if isinstance(value, tuple):
        return any(_nested_contains_missing_sentinel_or_empty(item) for item in value)
    if isinstance(value, list):
        return any(_nested_contains_missing_sentinel_or_empty(item) for item in value)
    return False


def _method_b_action_spec_for(action: Mapping[str, Any]) -> Optional[Mapping[str, Any]]:
    for spec in METHOD_B_ACTION_SPECS:
        if action.get("proof_kind") == spec["proof_kind"] and action.get("proof_stage") == spec["proof_stage"]:
            return spec
    return None


def _proof_action_has_expected_id(action: Mapping[str, Any]) -> bool:
    target = _normalize_nested_tuple(action.get("object_target_key"))
    provided = _normalize_nested_tuple(action.get("proof_obligation_id"))
    return provided == _expected_proof_obligation_id(action, object_target_key=target)


def _expected_proof_obligation_id(action: Mapping[str, Any], *, object_target_key: Any) -> Tuple[Any, ...]:
    return build_proof_obligation_id(
        str(action.get("reason_id") or MISSING_SENTINEL),
        str(action.get("proof_stage") or MISSING_SENTINEL),
        str(action.get("proof_kind") or MISSING_SENTINEL),
        str(action.get("evidence_kind") or MISSING_SENTINEL),
        _normalize_nested_tuple(object_target_key),
    )


def _proof_action_matches_lane_definition(action: Mapping[str, Any]) -> bool:
    spec = _method_b_action_spec_for(action)
    if not spec:
        return False
    return (
        action.get("count_kind") == UnknownCountKind.PROOF_ACTION.value
        and action.get("decision_effect") == "blocks_equivalence"
        and action.get("reason_scope") == "stage"
        and action.get("aggregation_unit") == "pair"
        and action.get("stage") == "S_PAIRWISE"
        and action.get("status") == "planned"
        and action.get("evidence_kind") == spec["evidence_kind"]
        and tuple(action.get("required_evidence") or ()) == tuple(spec["required_evidence"])
        and tuple(action.get("tuple") or ()) == _method_b_action_tuple(spec)
    )


def _canonical_actions(values: Any) -> Tuple[Dict[str, Any], ...]:
    if not isinstance(values, Sequence) or isinstance(values, (str, bytes)):
        return ()
    canonical = []
    for action in values:
        if not isinstance(action, Mapping):
            continue
        canonical.append(
            {
                "count_kind": action.get("count_kind") or MISSING_SENTINEL,
                "reason_id": action.get("reason_id") or MISSING_SENTINEL,
                "decision_effect": action.get("decision_effect") or MISSING_SENTINEL,
                "reason_scope": action.get("reason_scope") or MISSING_SENTINEL,
                "aggregation_unit": action.get("aggregation_unit") or MISSING_SENTINEL,
                "stage": action.get("stage") or MISSING_SENTINEL,
                "pair_or_case": action.get("pair_or_case") or MISSING_SENTINEL,
                "proof_kind": action.get("proof_kind") or MISSING_SENTINEL,
                "proof_stage": action.get("proof_stage") or MISSING_SENTINEL,
                "status": action.get("status") or MISSING_SENTINEL,
                "evidence_kind": action.get("evidence_kind") or MISSING_SENTINEL,
                "required_evidence": list(action.get("required_evidence") or ()),
                "object_target_key": _jsonable(action.get("object_target_key")),
                "proof_obligation_id": _jsonable(action.get("proof_obligation_id")),
                "tuple": list(action.get("tuple") or ()),
            }
        )
    return tuple(sorted(canonical, key=_canonical_json))


def _expected_entry_for(entry: Mapping[str, Any]) -> Mapping[str, Any]:
    return _entry_map(DEFAULT_REPRESENTATIVES).get(_entry_key(entry), {})


def _load_phase3_manifest(
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
            / "phase3_method_b_closure_lane4"
            / "method_b_closure_lane4_representatives.json"
        )
    for path in candidates:
        if path.is_file():
            return _read_json(path), _file_ref(path)
    fallback = candidates[0]
    return {}, {"path": str(fallback), "sha256": "__missing__"}


if __name__ == "__main__":
    raise SystemExit(main())
