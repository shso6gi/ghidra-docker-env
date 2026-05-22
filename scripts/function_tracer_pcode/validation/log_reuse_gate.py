# -*- coding: utf-8 -*-
"""Decide whether an existing validation log is safe to reuse."""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any, Iterable, Mapping, Optional, Sequence, Tuple

from ..equivalence.unknown_reason import (
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    build_proof_obligation_id,
    coerce_unknown_reason_record,
)
from .phase2_equivalence_blocking_unsafety import (
    EXPECTED_RECOVERY_ACTION,
    EXPECTED_PROOF_STAGE,
    TARGET_REASON_ID,
    _object_target_key_is_specific,
)
from .unknown_reason_summary import (
    RESULT_JSON_END,
    extract_result_payloads_from_text,
)


EXPECTED_PHASE2_EVIDENCE_KINDS = frozenset(
    {
        "call_effect_summary",
        "runtime_ref",
        "callsite_storage",
    }
)


def validation_log_reuse_failures(
    path: Path,
    *,
    require_phase2_object_keys: bool = False,
) -> Tuple[str, ...]:
    """Return failure reasons that make an existing log unsuitable for reuse."""

    log_path = Path(path)
    if not log_path.is_file():
        return ("log_missing",)
    text = log_path.read_text(errors="replace")
    if RESULT_JSON_END not in text:
        return ("result_json_incomplete",)
    payloads = extract_result_payloads_from_text(text)
    if not payloads:
        return ("result_json_missing_or_unparseable",)
    if not require_phase2_object_keys:
        return ()
    return _phase2_object_key_failures(payloads[-1])


def validation_log_is_reusable(
    path: Path,
    *,
    require_phase2_object_keys: bool = False,
) -> bool:
    return not validation_log_reuse_failures(
        path,
        require_phase2_object_keys=require_phase2_object_keys,
    )


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Validate an existing log before skip/reuse.")
    parser.add_argument("--log", required=True, help="validation log path")
    parser.add_argument(
        "--require-phase2-object-keys",
        action="store_true",
        help=(
            "require equivalence_blocking_unsafety call-effect proof records "
            "to carry canonical object_target_key/proof_obligation_id"
        ),
    )
    args = parser.parse_args(argv)

    failures = validation_log_reuse_failures(
        Path(args.log),
        require_phase2_object_keys=args.require_phase2_object_keys,
    )
    if failures:
        print("\n".join(failures))
        return 1
    return 0


def _phase2_object_key_failures(payload: Mapping[str, Any]) -> Tuple[str, ...]:
    failures = []
    for raw_reason in payload.get("unknown_reasons") or ():
        reason = coerce_unknown_reason_record(raw_reason)
        if reason.reason_id != TARGET_REASON_ID:
            continue
        if not _is_phase2_call_effect_blocker(reason):
            continue
        failures.extend(_raw_phase2_reason_failures(raw_reason))
        failures.extend(_phase2_reason_failures(reason))
    return tuple(dict.fromkeys(failures))


def _is_phase2_call_effect_blocker(reason: Any) -> bool:
    if reason.recovery_proof_kind == UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value:
        return True
    evidence_refs = tuple(str(ref) for ref in (reason.evidence_refs or ()))
    detail = str(reason.detail or "")
    return any("unsupported_call_effect_summary" in ref for ref in evidence_refs) or (
        "unsupported_call_effect_summary" in detail
    )


def _raw_phase2_reason_failures(raw_reason: Any) -> Iterable[str]:
    if not isinstance(raw_reason, Mapping):
        yield "phase2_proof_obligation_id_missing"
        return
    if "proof_obligation_id" not in raw_reason or raw_reason.get("proof_obligation_id") is None:
        yield "phase2_proof_obligation_id_missing"


def _phase2_reason_failures(reason: Any) -> Iterable[str]:
    if reason.recovery_proof_kind != UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value:
        yield "phase2_recovery_proof_kind_missing"
    if reason.proof_stage != EXPECTED_PROOF_STAGE:
        yield "phase2_proof_stage_missing"
    if reason.action_status != UnknownRecoveryActionStatus.PENDING_PROOF.value:
        yield "phase2_action_status_missing"
    if reason.recovery_action != EXPECTED_RECOVERY_ACTION:
        yield "phase2_recovery_action_missing"
    if reason.evidence_kind is None:
        yield "phase2_evidence_kind_missing"
    elif reason.evidence_kind not in EXPECTED_PHASE2_EVIDENCE_KINDS:
        yield "phase2_evidence_kind_mismatch"
    if not _object_target_key_is_specific(reason.object_target_key):
        yield "phase2_object_target_key_missing_or_not_specific"

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
        yield "phase2_proof_obligation_id_mismatch"


if __name__ == "__main__":
    raise SystemExit(main())
