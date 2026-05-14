# -*- coding: utf-8 -*-
"""Validate Phase 2 expected movement for equivalence_blocking_unsafety."""

from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence, Tuple

from ..equivalence.unknown_reason import (
    UNKNOWN_TUPLE_MISSING,
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    build_proof_obligation_id,
    coerce_unknown_reason_records,
)
from .result_summary import (
    STATUS_EQ,
    STATUS_UNKNOWN,
    ValidationLogRecord,
    aggregate_validation_logs,
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


def build_phase2_equivalence_blocking_unsafety_movement(
    *,
    phase1_dir: Path,
    output_dir: Path,
    current_log_roots: Mapping[str, Path],
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
    summary = _movement_summary(entries)
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
        "movement_summary": summary,
        "phase2_ready": summary["failed"] == 0,
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
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args(argv)
    path = build_phase2_equivalence_blocking_unsafety_movement(
        phase1_dir=Path(args.phase1_dir),
        output_dir=Path(args.output_dir),
        current_log_roots=_parse_current_log_roots(args.current_log_root or ()),
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


def _movement_summary(entries: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
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
    )
    failed_entries = sum(1 for entry in entries if entry.get("movement_status") != "expected_movement")
    return {
        "target_reason_id": TARGET_REASON_ID,
        "total": len(entries),
        "passed": sum(1 for entry in entries if entry.get("movement_status") == "expected_movement"),
        "failed": failed_entries + len(missing_representatives) + len(unexpected_representatives),
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
