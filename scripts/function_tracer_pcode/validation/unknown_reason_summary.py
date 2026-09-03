# -*- coding: utf-8 -*-
"""Typed UNKNOWN reason aggregation for validation before/after reports.

This module intentionally consumes machine-readable EquivalenceResult/debug_trace
payloads instead of parsing human log text. Human logs are diagnostics; plan16
needs stable typed dimensions: reason_id, decision_effect, reason_scope, and the
recovery-proof backlog created from those reasons.
"""

from __future__ import annotations

import argparse
import json
from collections.abc import Sequence as SequenceABC
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence, Tuple

from ..equivalence.unknown_reason import (
    UNKNOWN_TUPLE_MISSING,
    UnknownCountKind,
    UnknownDecisionEffect,
    UnknownRecoveryActionStatus,
    UnknownReasonClass,
    UnknownReasonId,
    UnknownReasonRecord,
    build_unknown_recovery_actions,
    coerce_unknown_reason_records,
    make_unknown_reason,
)
from .root_blocker_summary import compare_root_blocker_summaries, summarize_root_blockers


_FINAL_UNKNOWN_TRANSITIONS = {"UNKNOWN", "TIMEOUT"}
_PROOF_BACKLOG_CLASSES = {
    UnknownReasonClass.PROOF_OBLIGATION.value,
    UnknownReasonClass.COVERAGE_GAP.value,
}
_PRIMARY_DECISION_EFFECT_PRIORITY = {
    UnknownDecisionEffect.BLOCKS_EQUIVALENCE.value: 0,
    UnknownDecisionEffect.BLOCKS_DISEQUIVALENCE.value: 1,
    UnknownDecisionEffect.BLOCKS_DECISION.value: 2,
    UnknownDecisionEffect.RETRYABLE.value: 3,
    UnknownDecisionEffect.DIAGNOSTIC_ONLY.value: 4,
}
RESULT_JSON_BEGIN = "=== EQUIVALENCE_RESULT_JSON_BEGIN ==="
RESULT_JSON_END = "=== EQUIVALENCE_RESULT_JSON_END ==="
_GLOBAL_REASON_TUPLE_WIDTH = 7
_GLOBAL_REASON_COUNT_KINDS = {
    UnknownCountKind.FINAL_RESULT.value,
    UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value,
    UnknownCountKind.REASON_RECORD.value,
    UnknownCountKind.PROOF_ACTION.value,
}
_CORRESPONDENCE_RAW_LOG_MISSING_KEY = (
    UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value,
    UnknownReasonId.UNKNOWN.value,
    UNKNOWN_TUPLE_MISSING,
    UNKNOWN_TUPLE_MISSING,
    UNKNOWN_TUPLE_MISSING,
    UNKNOWN_TUPLE_MISSING,
    UNKNOWN_TUPLE_MISSING,
)


@dataclass(frozen=True)
class UnknownReasonCorrespondenceDiagnostic:
    classification: str
    tuple_key: Tuple[str, ...]
    validation_unknown_units: int = 0
    reason_records: int = 0
    proof_actions: int = 0

    def to_dict(self) -> Dict[str, Any]:
        return {
            "classification": self.classification,
            "tuple_key": list(self.tuple_key),
            "validation_unknown_units": self.validation_unknown_units,
            "reason_records": self.reason_records,
            "proof_actions": self.proof_actions,
        }


@dataclass(frozen=True)
class UnknownValidationSummary:
    total_results: int = 0
    unknown_results: int = 0
    unknown_units: int = 0
    final_result_counts: Dict[str, int] = field(default_factory=dict)
    validation_unknown_unit_multiset: Dict[Tuple[str, ...], int] = field(default_factory=dict)
    reason_record_multiset: Dict[Tuple[str, ...], int] = field(default_factory=dict)
    proof_action_multiset: Dict[Tuple[str, ...], int] = field(default_factory=dict)
    unknown_by_reason: Dict[str, int] = field(default_factory=dict)
    unknown_by_decision_effect: Dict[str, int] = field(default_factory=dict)
    unknown_by_reason_scope: Dict[str, int] = field(default_factory=dict)
    proof_backlog_by_reason: Dict[str, int] = field(default_factory=dict)
    proof_backlog_by_proof_kind: Dict[str, int] = field(default_factory=dict)
    proof_backlog_by_recovery_action: Dict[str, int] = field(default_factory=dict)
    proof_backlog_by_action_status: Dict[str, int] = field(default_factory=dict)
    operational_unknown_by_reason: Dict[str, int] = field(default_factory=dict)
    operational_unknown_by_class: Dict[str, int] = field(default_factory=dict)
    root_blocker_summary: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "total_results": self.total_results,
            "unknown_results": self.unknown_results,
            "unknown_units": self.unknown_units,
            "final_result_counts": dict(self.final_result_counts),
            "validation_unknown_unit_multiset": _tuple_multiset_to_dict(
                self.validation_unknown_unit_multiset
            ),
            "reason_record_multiset": _tuple_multiset_to_dict(self.reason_record_multiset),
            "proof_action_multiset": _tuple_multiset_to_dict(self.proof_action_multiset),
            "unknown_by_reason": dict(self.unknown_by_reason),
            "unknown_by_decision_effect": dict(self.unknown_by_decision_effect),
            "unknown_by_reason_scope": dict(self.unknown_by_reason_scope),
            "proof_backlog_by_reason": dict(self.proof_backlog_by_reason),
            "proof_backlog_by_proof_kind": dict(self.proof_backlog_by_proof_kind),
            "proof_backlog_by_recovery_action": dict(self.proof_backlog_by_recovery_action),
            "proof_backlog_by_action_status": dict(self.proof_backlog_by_action_status),
            "operational_unknown_by_reason": dict(self.operational_unknown_by_reason),
            "operational_unknown_by_class": dict(self.operational_unknown_by_class),
            "root_blocker_summary": dict(self.root_blocker_summary),
            "reason_record_correspondence": [
                diagnostic.to_dict()
                for diagnostic in diagnose_unknown_reason_correspondence(self)
            ],
        }


@dataclass(frozen=True)
class UnknownValidationDiff:
    before: UnknownValidationSummary
    after: UnknownValidationSummary
    delta_unknown_results: int
    delta_unknown_units: int
    unknown_by_reason_delta: Dict[str, int]
    unknown_by_decision_effect_delta: Dict[str, int]
    unknown_by_reason_scope_delta: Dict[str, int]
    proof_backlog_by_reason_delta: Dict[str, int]
    proof_backlog_by_proof_kind_delta: Dict[str, int]
    proof_backlog_by_recovery_action_delta: Dict[str, int]
    proof_backlog_by_action_status_delta: Dict[str, int]
    final_result_counts_delta: Dict[str, int]
    validation_unknown_unit_multiset_delta: Dict[Tuple[str, ...], int]
    reason_record_multiset_delta: Dict[Tuple[str, ...], int]
    proof_action_multiset_delta: Dict[Tuple[str, ...], int]
    operational_unknown_by_reason_delta: Dict[str, int]
    operational_unknown_by_class_delta: Dict[str, int]
    root_blocker_diff: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "before": self.before.to_dict(),
            "after": self.after.to_dict(),
            "delta_unknown_results": self.delta_unknown_results,
            "delta_unknown_units": self.delta_unknown_units,
            "unknown_by_reason_delta": dict(self.unknown_by_reason_delta),
            "unknown_by_decision_effect_delta": dict(self.unknown_by_decision_effect_delta),
            "unknown_by_reason_scope_delta": dict(self.unknown_by_reason_scope_delta),
            "proof_backlog_by_reason_delta": dict(self.proof_backlog_by_reason_delta),
            "proof_backlog_by_proof_kind_delta": dict(self.proof_backlog_by_proof_kind_delta),
            "proof_backlog_by_recovery_action_delta": dict(self.proof_backlog_by_recovery_action_delta),
            "proof_backlog_by_action_status_delta": dict(self.proof_backlog_by_action_status_delta),
            "final_result_counts_delta": dict(self.final_result_counts_delta),
            "validation_unknown_unit_multiset_delta": _tuple_multiset_to_dict(
                self.validation_unknown_unit_multiset_delta
            ),
            "reason_record_multiset_delta": _tuple_multiset_to_dict(
                self.reason_record_multiset_delta
            ),
            "proof_action_multiset_delta": _tuple_multiset_to_dict(
                self.proof_action_multiset_delta
            ),
            "operational_unknown_by_reason_delta": dict(self.operational_unknown_by_reason_delta),
            "operational_unknown_by_class_delta": dict(self.operational_unknown_by_class_delta),
            "root_blocker_diff": dict(self.root_blocker_diff),
        }


def summarize_validation_unknowns(
    result_payloads: Iterable[Any],
    *,
    target_cases: Optional[Sequence[str]] = None,
) -> UnknownValidationSummary:
    target_filter = tuple(str(target) for target in (target_cases or ()))
    payload_list = [_coerce_payload(raw_payload) for raw_payload in result_payloads]
    selected_payloads = [
        payload
        for payload in payload_list
        if not target_filter or _payload_matches_targets(payload, target_filter)
    ]
    total_results = 0
    unknown_results = 0
    unknown_units = 0
    final_result_counts: Dict[str, int] = {}
    validation_unknown_unit_multiset: Dict[Tuple[str, ...], int] = {}
    reason_record_multiset: Dict[Tuple[str, ...], int] = {}
    proof_action_multiset: Dict[Tuple[str, ...], int] = {}
    unknown_by_reason: Dict[str, int] = {}
    unknown_by_decision_effect: Dict[str, int] = {}
    unknown_by_reason_scope: Dict[str, int] = {}
    proof_backlog_by_reason: Dict[str, int] = {}
    proof_backlog_by_proof_kind: Dict[str, int] = {}
    proof_backlog_by_recovery_action: Dict[str, int] = {}
    proof_backlog_by_action_status: Dict[str, int] = {}
    operational_unknown_by_reason: Dict[str, int] = {}
    operational_unknown_by_class: Dict[str, int] = {}

    for payload in selected_payloads:
        total_results += 1
        _inc(final_result_counts, _payload_final_result(payload))
        if not _payload_is_unknown(payload):
            continue
        unknown_results += 1

        extracted_records = _extract_final_unknown_reasons(payload)
        records = _select_primary_records_by_aggregation_unit(extracted_records)
        if not records:
            records = (
                make_unknown_reason(
                    UnknownReasonId.UNKNOWN,
                    stage=_payload_stage(payload),
                    pair_or_case=_payload_pair_or_case(payload),
                ),
            )
        unknown_units += len(records)

        for record in extracted_records or records:
            _inc(
                reason_record_multiset,
                _global_reason_tuple_from_record(
                    record,
                    UnknownCountKind.REASON_RECORD.value,
                ),
            )
            for action in build_unknown_recovery_actions((record,)):
                _inc(proof_action_multiset, _global_reason_tuple_from_action(action))

        for record in records:
            _inc(
                validation_unknown_unit_multiset,
                _global_reason_tuple_from_record(
                    record,
                    UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value,
                ),
            )
            _inc(unknown_by_reason, record.reason_id)
            _inc(unknown_by_decision_effect, record.decision_effect)
            _inc(unknown_by_reason_scope, record.reason_scope)
            actions = build_unknown_recovery_actions((record,))
            if _is_proof_backlog(record, actions):
                _inc(proof_backlog_by_reason, record.reason_id)
                for action in actions:
                    _inc(proof_backlog_by_proof_kind, action.proof_kind)
                    _inc(proof_backlog_by_recovery_action, _recovery_action_key(action))
                    _inc(proof_backlog_by_action_status, action.status)
            else:
                _inc(operational_unknown_by_reason, record.reason_id)
                _inc(operational_unknown_by_class, record.reason_class)

    return UnknownValidationSummary(
        total_results=total_results,
        unknown_results=unknown_results,
        unknown_units=unknown_units,
        final_result_counts=final_result_counts,
        validation_unknown_unit_multiset=validation_unknown_unit_multiset,
        reason_record_multiset=reason_record_multiset,
        proof_action_multiset=proof_action_multiset,
        unknown_by_reason=unknown_by_reason,
        unknown_by_decision_effect=unknown_by_decision_effect,
        unknown_by_reason_scope=unknown_by_reason_scope,
        proof_backlog_by_reason=proof_backlog_by_reason,
        proof_backlog_by_proof_kind=proof_backlog_by_proof_kind,
        proof_backlog_by_recovery_action=proof_backlog_by_recovery_action,
        proof_backlog_by_action_status=proof_backlog_by_action_status,
        operational_unknown_by_reason=operational_unknown_by_reason,
        operational_unknown_by_class=operational_unknown_by_class,
        root_blocker_summary=summarize_root_blockers(selected_payloads).to_dict(),
    )


def compare_validation_unknowns(
    before_payloads: Iterable[Any],
    after_payloads: Iterable[Any],
    *,
    target_cases: Optional[Sequence[str]] = None,
) -> UnknownValidationDiff:
    before_payloads_list = [_coerce_payload(item) for item in before_payloads]
    after_payloads_list = [_coerce_payload(item) for item in after_payloads]
    target_filter = tuple(str(target) for target in (target_cases or ()))
    root_before = summarize_root_blockers(
        item for item in before_payloads_list
        if not target_filter or _payload_matches_targets(item, target_filter)
    )
    root_after = summarize_root_blockers(
        item for item in after_payloads_list
        if not target_filter or _payload_matches_targets(item, target_filter)
    )
    before = summarize_validation_unknowns(before_payloads_list, target_cases=target_cases)
    after = summarize_validation_unknowns(after_payloads_list, target_cases=target_cases)
    return UnknownValidationDiff(
        before=before,
        after=after,
        delta_unknown_results=after.unknown_results - before.unknown_results,
        delta_unknown_units=after.unknown_units - before.unknown_units,
        unknown_by_reason_delta=_diff_counts(before.unknown_by_reason, after.unknown_by_reason),
        unknown_by_decision_effect_delta=_diff_counts(
            before.unknown_by_decision_effect,
            after.unknown_by_decision_effect,
        ),
        unknown_by_reason_scope_delta=_diff_counts(
            before.unknown_by_reason_scope,
            after.unknown_by_reason_scope,
        ),
        proof_backlog_by_reason_delta=_diff_counts(
            before.proof_backlog_by_reason,
            after.proof_backlog_by_reason,
        ),
        proof_backlog_by_proof_kind_delta=_diff_counts(
            before.proof_backlog_by_proof_kind,
            after.proof_backlog_by_proof_kind,
        ),
        proof_backlog_by_recovery_action_delta=_diff_counts(
            before.proof_backlog_by_recovery_action,
            after.proof_backlog_by_recovery_action,
        ),
        proof_backlog_by_action_status_delta=_diff_counts(
            before.proof_backlog_by_action_status,
            after.proof_backlog_by_action_status,
        ),
        final_result_counts_delta=_diff_counts(
            before.final_result_counts,
            after.final_result_counts,
        ),
        validation_unknown_unit_multiset_delta=_diff_counts(
            before.validation_unknown_unit_multiset,
            after.validation_unknown_unit_multiset,
        ),
        reason_record_multiset_delta=_diff_counts(
            before.reason_record_multiset,
            after.reason_record_multiset,
        ),
        proof_action_multiset_delta=_diff_counts(
            before.proof_action_multiset,
            after.proof_action_multiset,
        ),
        operational_unknown_by_reason_delta=_diff_counts(
            before.operational_unknown_by_reason,
            after.operational_unknown_by_reason,
        ),
        operational_unknown_by_class_delta=_diff_counts(
            before.operational_unknown_by_class,
            after.operational_unknown_by_class,
        ),
        root_blocker_diff=compare_root_blocker_summaries(root_before, root_after).to_dict(),
    )


def diagnose_unknown_reason_correspondence(
    summary: UnknownValidationSummary,
) -> Tuple[UnknownReasonCorrespondenceDiagnostic, ...]:
    """Classify validation-unit, detail-record, and proof-action count drift.

    The comparison key intentionally mirrors the global reason tuple minus
    ``count_kind``. Optional tuple fields are normalized to
    ``UNKNOWN_TUPLE_MISSING`` so callers can compare v0/v1 artifacts without
    prose-derived fallbacks.
    """

    validation_by_signature = _reason_signature_counts(
        summary.validation_unknown_unit_multiset,
        UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value,
    )
    reason_by_signature = _reason_signature_counts(
        summary.reason_record_multiset,
        UnknownCountKind.REASON_RECORD.value,
    )
    proof_action_by_signature = _reason_signature_counts(
        summary.proof_action_multiset,
        UnknownCountKind.PROOF_ACTION.value,
    )
    diagnostics = []

    if (
        summary.unknown_results > 0
        and not validation_by_signature
        and not reason_by_signature
    ):
        diagnostics.append(
            UnknownReasonCorrespondenceDiagnostic(
                classification="raw_log_missing",
                tuple_key=_CORRESPONDENCE_RAW_LOG_MISSING_KEY,
                validation_unknown_units=0,
                reason_records=0,
                proof_actions=0,
            )
        )

    for signature in sorted(set(validation_by_signature) | set(reason_by_signature)):
        validation_count = int(validation_by_signature.get(signature, 0) or 0)
        reason_count = int(reason_by_signature.get(signature, 0) or 0)
        if validation_count == reason_count:
            continue
        if reason_count > validation_count:
            classification = "aggregation_difference"
        elif reason_count == 0:
            classification = "detail_missing"
        else:
            classification = "parser_bug"
        diagnostics.append(
            UnknownReasonCorrespondenceDiagnostic(
                classification=classification,
                tuple_key=_reason_tuple_from_signature(
                    UnknownCountKind.REASON_RECORD.value,
                    signature,
                ),
                validation_unknown_units=validation_count,
                reason_records=reason_count,
                proof_actions=int(proof_action_by_signature.get(signature, 0) or 0),
            )
        )

    for signature, action_count in sorted(proof_action_by_signature.items()):
        validation_count = int(validation_by_signature.get(signature, 0) or 0)
        reason_count = int(reason_by_signature.get(signature, 0) or 0)
        if action_count == reason_count and action_count == validation_count:
            continue
        diagnostics.append(
            UnknownReasonCorrespondenceDiagnostic(
                classification="proof_action_expansion",
                tuple_key=_reason_tuple_from_signature(
                    UnknownCountKind.PROOF_ACTION.value,
                    signature,
                ),
                validation_unknown_units=validation_count,
                reason_records=reason_count,
                proof_actions=int(action_count or 0),
            )
        )

    return tuple(
        sorted(
            diagnostics,
            key=lambda diagnostic: (
                diagnostic.classification,
                diagnostic.tuple_key,
                diagnostic.validation_unknown_units,
                diagnostic.reason_records,
                diagnostic.proof_actions,
            ),
        )
    )


def format_validation_unknown_summary(
    summary: UnknownValidationSummary,
    *,
    indent: str = "",
    compact: bool = False,
    max_items: Optional[int] = None,
) -> str:
    lines = [
        f"{indent}UNKNOWN validation summary:",
        f"{indent}  Total results : {summary.total_results}",
        f"{indent}  Unknown results: {summary.unknown_results}",
        f"{indent}  Unknown units  : {summary.unknown_units}",
    ]
    max_items = _summary_max_items(compact=compact, max_items=max_items)
    _append_count_block(lines, "Final results", summary.final_result_counts, indent, max_items=max_items)
    _append_count_block(
        lines,
        "Validation UNKNOWN unit tuples",
        summary.validation_unknown_unit_multiset,
        indent,
        max_items=max_items,
    )
    if not compact:
        _append_count_block(
            lines,
            "Reason record tuples",
            summary.reason_record_multiset,
            indent,
            max_items=max_items,
        )
        _append_count_block(
            lines,
            "Proof action tuples",
            summary.proof_action_multiset,
            indent,
            max_items=max_items,
        )
    _append_count_block(lines, "UNKNOWN by reason", summary.unknown_by_reason, indent, max_items=max_items)
    _append_count_block(
        lines,
        "UNKNOWN by decision_effect",
        summary.unknown_by_decision_effect,
        indent,
        max_items=max_items,
    )
    _append_count_block(
        lines,
        "UNKNOWN by reason_scope",
        summary.unknown_by_reason_scope,
        indent,
        max_items=max_items,
    )
    _append_count_block(lines, "Proof backlog by reason", summary.proof_backlog_by_reason, indent, max_items=max_items)
    _append_count_block(
        lines,
        "Proof backlog by proof_kind",
        summary.proof_backlog_by_proof_kind,
        indent,
        max_items=max_items,
    )
    _append_count_block(
        lines,
        "Proof backlog by recovery_action",
        summary.proof_backlog_by_recovery_action,
        indent,
        max_items=max_items,
    )
    _append_count_block(
        lines,
        "Proof backlog by action_status",
        summary.proof_backlog_by_action_status,
        indent,
        max_items=max_items,
    )
    _append_count_block(
        lines,
        "Operational UNKNOWN by reason",
        summary.operational_unknown_by_reason,
        indent,
        max_items=max_items,
    )
    if not compact:
        _append_correspondence_diagnostics(
            lines,
            diagnose_unknown_reason_correspondence(summary),
            indent,
        )
    root = summary.root_blocker_summary
    if root:
        lines.extend(
            [
                f"{indent}Root blockers:",
                f"{indent}  Active unique blockers : {root.get('active_root_blocker_count', 0)}",
                f"{indent}  Observed candidates     : {root.get('candidate_root_blocker_count', 0)}",
                f"{indent}  Required unique proofs  : "
                + (
                    str(root.get("required_unique_proof_count"))
                    if root.get("required_unique_proof_count") is not None
                    else "unknown (incomplete identity)"
                ),
            ]
        )
    return "\n".join(lines)


def format_validation_unknown_diff(
    diff: UnknownValidationDiff,
    *,
    indent: str = "",
    compact: bool = False,
    max_items: Optional[int] = None,
) -> str:
    lines = [
        f"{indent}UNKNOWN validation before/after delta:",
        f"{indent}  Unknown results delta: {_format_delta(diff.delta_unknown_results)}",
        f"{indent}  Unknown units delta  : {_format_delta(diff.delta_unknown_units)}",
    ]
    root_diff = diff.root_blocker_diff
    if root_diff:
        lines.extend(
            [
                f"{indent}  Active root blocker delta: {_format_delta(root_diff.get('active_root_blocker_delta', 0))}",
                f"{indent}  Unique proof delta       : "
                + (
                    _format_delta(root_diff.get("required_unique_proof_delta", 0))
                    if root_diff.get("proof_requirement_comparison_complete", True)
                    else "unknown (incomplete requirement identity)"
                ),
            ]
        )
    max_items = _summary_max_items(compact=compact, max_items=max_items)
    _append_count_block(lines, "Final results delta", diff.final_result_counts_delta, indent, max_items=max_items)
    _append_count_block(
        lines,
        "Validation UNKNOWN unit tuple delta",
        diff.validation_unknown_unit_multiset_delta,
        indent,
        max_items=max_items,
    )
    if not compact:
        _append_count_block(
            lines,
            "Reason record tuple delta",
            diff.reason_record_multiset_delta,
            indent,
            max_items=max_items,
        )
        _append_count_block(
            lines,
            "Proof action tuple delta",
            diff.proof_action_multiset_delta,
            indent,
            max_items=max_items,
        )
    _append_count_block(lines, "UNKNOWN by reason delta", diff.unknown_by_reason_delta, indent, max_items=max_items)
    _append_count_block(
        lines,
        "UNKNOWN by decision_effect delta",
        diff.unknown_by_decision_effect_delta,
        indent,
        max_items=max_items,
    )
    _append_count_block(
        lines,
        "UNKNOWN by reason_scope delta",
        diff.unknown_by_reason_scope_delta,
        indent,
        max_items=max_items,
    )
    _append_count_block(
        lines,
        "Proof backlog by reason delta",
        diff.proof_backlog_by_reason_delta,
        indent,
        max_items=max_items,
    )
    _append_count_block(
        lines,
        "Proof backlog by proof_kind delta",
        diff.proof_backlog_by_proof_kind_delta,
        indent,
        max_items=max_items,
    )
    _append_count_block(
        lines,
        "Proof backlog by recovery_action delta",
        diff.proof_backlog_by_recovery_action_delta,
        indent,
        max_items=max_items,
    )
    _append_count_block(
        lines,
        "Proof backlog by action_status delta",
        diff.proof_backlog_by_action_status_delta,
        indent,
        max_items=max_items,
    )
    _append_count_block(
        lines,
        "Operational UNKNOWN by reason delta",
        diff.operational_unknown_by_reason_delta,
        indent,
        max_items=max_items,
    )
    _append_count_block(
        lines,
        "Operational UNKNOWN by class delta",
        diff.operational_unknown_by_class_delta,
        indent,
        max_items=max_items,
    )
    return "\n".join(lines)


def format_validation_unknown_diff_unavailable(
    summary: UnknownValidationSummary,
    *,
    indent: str = "",
    baseline_hint: str = "--before-dir or VALIDATION_BEFORE_DIR",
) -> str:
    lines = [
        f"{indent}UNKNOWN validation before/after delta:",
        f"{indent}  Baseline: unavailable; set {baseline_hint} to enable deltas.",
        f"{indent}  Current unknown results: {summary.unknown_results}",
        f"{indent}  Current unknown units  : {summary.unknown_units}",
    ]
    _append_count_block(
        lines,
        "Final results delta",
        {},
        indent,
        empty_label="baseline unavailable",
    )
    _append_count_block(
        lines,
        "Validation UNKNOWN unit tuple delta",
        {},
        indent,
        empty_label="baseline unavailable",
    )
    _append_count_block(
        lines,
        "Reason record tuple delta",
        {},
        indent,
        empty_label="baseline unavailable",
    )
    _append_count_block(
        lines,
        "Proof action tuple delta",
        {},
        indent,
        empty_label="baseline unavailable",
    )
    _append_count_block(
        lines,
        "UNKNOWN by reason delta",
        {},
        indent,
        empty_label="baseline unavailable",
    )
    _append_count_block(
        lines,
        "UNKNOWN by decision_effect delta",
        {},
        indent,
        empty_label="baseline unavailable",
    )
    _append_count_block(
        lines,
        "UNKNOWN by reason_scope delta",
        {},
        indent,
        empty_label="baseline unavailable",
    )
    _append_count_block(
        lines,
        "Proof backlog by reason delta",
        {},
        indent,
        empty_label="baseline unavailable",
    )
    _append_count_block(
        lines,
        "Proof backlog by proof_kind delta",
        {},
        indent,
        empty_label="baseline unavailable",
    )
    _append_count_block(
        lines,
        "Proof backlog by recovery_action delta",
        {},
        indent,
        empty_label="baseline unavailable",
    )
    _append_count_block(
        lines,
        "Proof backlog by action_status delta",
        {},
        indent,
        empty_label="baseline unavailable",
    )
    _append_count_block(
        lines,
        "Operational UNKNOWN by reason delta",
        {},
        indent,
        empty_label="baseline unavailable",
    )
    _append_count_block(
        lines,
        "Operational UNKNOWN by class delta",
        {},
        indent,
        empty_label="baseline unavailable",
    )
    return "\n".join(lines)


def extract_result_payloads_from_text(text: str) -> Tuple[Mapping[str, Any], ...]:
    payloads = []
    current_lines = []
    in_payload = False
    for line in text.splitlines():
        stripped = line.strip()
        if stripped == RESULT_JSON_BEGIN:
            in_payload = True
            current_lines = []
            continue
        if stripped == RESULT_JSON_END and in_payload:
            raw_json = "\n".join(current_lines).strip()
            if raw_json:
                payload = json.loads(raw_json)
                if isinstance(payload, Mapping):
                    payloads.append(payload)
            in_payload = False
            current_lines = []
            continue
        if in_payload:
            current_lines.append(line)
    return tuple(payloads)


def extract_result_payloads_from_logs(log_paths: Iterable[Any]) -> Tuple[Mapping[str, Any], ...]:
    payloads = []
    for raw_path in log_paths:
        path = Path(raw_path)
        if not path.is_file():
            continue
        payloads.extend(extract_result_payloads_from_text(path.read_text(errors="replace")))
    return tuple(payloads)


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Summarize typed UNKNOWN reasons from equivalence validation logs.",
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--summary", action="store_true", help="print UNKNOWN reason summary")
    mode.add_argument("--diff", action="store_true", help="print before/after UNKNOWN reason delta")
    parser.add_argument("--before-dir", default=None, help="directory containing baseline *.log files")
    parser.add_argument("--indent", default="", help="prefix to add to each output line")
    parser.add_argument(
        "--target-case",
        action="append",
        default=None,
        help="target function/case substring to include; may be repeated",
    )
    parser.add_argument("logs", nargs="*", help="after/current equivalence log files")
    args = parser.parse_args(argv)

    after_payloads = extract_result_payloads_from_logs(args.logs)
    if args.diff or args.before_dir:
        before_logs = sorted(Path(args.before_dir or "").glob("*.log")) if args.before_dir else ()
        before_payloads = extract_result_payloads_from_logs(before_logs)
        print(
            format_validation_unknown_diff(
                compare_validation_unknowns(
                    before_payloads,
                    after_payloads,
                    target_cases=args.target_case,
                ),
                indent=args.indent,
            )
        )
        return 0
    print(
        format_validation_unknown_summary(
            summarize_validation_unknowns(after_payloads, target_cases=args.target_case),
            indent=args.indent,
        )
    )
    return 0


def _coerce_payload(value: Any) -> Mapping[str, Any]:
    if isinstance(value, Mapping):
        return value
    to_dict = getattr(value, "to_dict", None)
    if callable(to_dict):
        payload = to_dict()
        if isinstance(payload, Mapping):
            return payload
    raise TypeError(f"validation result payload must be a mapping or expose to_dict(), got {type(value)!r}")


def _payload_is_unknown(payload: Mapping[str, Any]) -> bool:
    if payload.get("decision_receipt") is not None:
        from ..equivalence.v2.phase8_cutover import outcome_from_payload

        return outcome_from_payload(payload).value in {"UNKNOWN", "TIMEOUT"}
    if payload.get("is_equivalent") is not None:
        return False
    debug_trace = payload.get("debug_trace")
    if isinstance(debug_trace, Mapping) and debug_trace.get("final_result") is not None:
        return False
    return payload.get("error_message") is None


def _payload_final_result(payload: Mapping[str, Any]) -> str:
    if payload.get("decision_receipt") is not None:
        from ..equivalence.v2.phase8_cutover import outcome_from_payload

        return outcome_from_payload(payload).value
    debug_trace = payload.get("debug_trace")
    if isinstance(debug_trace, Mapping):
        final_result = debug_trace.get("final_result")
        if final_result is not None:
            if final_result is True:
                return "EQUIVALENT"
            if final_result is False:
                return "NOT_EQ"
            return str(final_result)
    is_equivalent = payload.get("is_equivalent")
    if is_equivalent is True:
        return "EQUIVALENT"
    if is_equivalent is False:
        return "NOT_EQ"
    if payload.get("error_message") is not None:
        return "ERROR"
    if _payload_is_timeout(payload):
        return "TIMEOUT"
    return "UNKNOWN"


def _payload_is_timeout(payload: Mapping[str, Any]) -> bool:
    if payload.get("decision_receipt") is not None:
        from ..equivalence.v2.phase8_cutover import outcome_from_payload

        return outcome_from_payload(payload).value == "TIMEOUT"
    if payload.get("is_timeout") is True:
        return True
    solver_results = payload.get("solver_results")
    if isinstance(solver_results, Mapping):
        all_results = solver_results.get("all_results") or solver_results.get("results") or ()
        for solver_result in all_results:
            if isinstance(solver_result, Mapping) and str(solver_result.get("status")) == "TIMEOUT":
                return True
    return False


def _payload_matches_targets(payload: Mapping[str, Any], targets: Sequence[str]) -> bool:
    haystack = " ".join(
        str(value)
        for value in (
            payload.get("case_id"),
            payload.get("function_name"),
            payload.get("function1_name"),
            payload.get("function2_name"),
            payload.get("binary1_name"),
            payload.get("binary2_name"),
        )
        if value is not None
    )
    return any(target in haystack for target in targets)


def _extract_final_unknown_reasons(payload: Mapping[str, Any]) -> Tuple[UnknownReasonRecord, ...]:
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
                return coerce_unknown_reason_records(attempt.get("unknown_reasons") or ())
    return coerce_unknown_reason_records(payload.get("unknown_reasons") or ())


def _select_primary_records_by_aggregation_unit(
    records: Iterable[UnknownReasonRecord],
) -> Tuple[UnknownReasonRecord, ...]:
    grouped_records: Dict[Tuple[str, str], list[UnknownReasonRecord]] = {}
    fallback_index = 0
    for record in records:
        aggregation_key = str(record.aggregation_unit or "result")
        unit_key = record.pair_or_case or record.stage
        if unit_key is None:
            unit_key = f"record:{fallback_index}"
            fallback_index += 1
        grouped_records.setdefault((aggregation_key, unit_key), []).append(record)
    return tuple(
        min(group, key=_primary_unknown_record_sort_key)
        for group in grouped_records.values()
    )


def _primary_unknown_record_sort_key(record: UnknownReasonRecord) -> Tuple[Any, ...]:
    return (
        _PRIMARY_DECISION_EFFECT_PRIORITY.get(str(record.decision_effect), 99),
        str(record.reason_id),
        str(record.reason_scope),
        str(record.recovery_proof_kind),
        str(record.proof_stage or ""),
        str(record.action_status or ""),
        tuple(str(ref) for ref in (record.evidence_refs or ())),
        str(record.detail or ""),
    )


def _is_proof_backlog(record: UnknownReasonRecord, actions: Sequence[Any] = ()) -> bool:
    action_statuses = {str(getattr(action, "status", "")) for action in actions}
    return (
        record.reason_class in _PROOF_BACKLOG_CLASSES
        or record.action_status
        in {
            UnknownRecoveryActionStatus.PENDING_PROOF.value,
            UnknownRecoveryActionStatus.PLANNED.value,
        }
        or (
            record.object_target_key is not None
            and bool(
                action_statuses
                & {
                    UnknownRecoveryActionStatus.PENDING_PROOF.value,
                    UnknownRecoveryActionStatus.PLANNED.value,
                }
            )
        )
    )


def _global_reason_tuple_from_record(
    record: UnknownReasonRecord,
    count_kind: str,
) -> Tuple[str, ...]:
    return (
        str(count_kind),
        str(record.reason_id),
        str(record.decision_effect),
        str(record.reason_scope),
        str(record.recovery_proof_kind or UNKNOWN_TUPLE_MISSING),
        str(record.proof_stage or UNKNOWN_TUPLE_MISSING),
        str(record.action_status or UNKNOWN_TUPLE_MISSING),
    )


def _global_reason_tuple_from_action(action: Any) -> Tuple[str, ...]:
    return (
        str(getattr(action, "count_kind", UnknownCountKind.PROOF_ACTION.value)),
        str(getattr(action, "reason_id", UnknownReasonId.UNKNOWN.value)),
        str(getattr(action, "decision_effect", UNKNOWN_TUPLE_MISSING)),
        str(getattr(action, "reason_scope", UNKNOWN_TUPLE_MISSING)),
        str(getattr(action, "proof_kind", UNKNOWN_TUPLE_MISSING)),
        str(getattr(action, "proof_stage", UNKNOWN_TUPLE_MISSING)),
        str(getattr(action, "status", UNKNOWN_TUPLE_MISSING)),
    )


def _payload_stage(payload: Mapping[str, Any]) -> Optional[str]:
    stage_path = payload.get("stage_path")
    if isinstance(stage_path, SequenceABC) and not isinstance(stage_path, (str, bytes)) and stage_path:
        return str(stage_path[-1])
    return None


def _payload_pair_or_case(payload: Mapping[str, Any]) -> Optional[str]:
    pair_info = payload.get("pairwise_stats")
    if isinstance(pair_info, Mapping):
        total_pairs = pair_info.get("total_pairs")
        unknown_pairs = pair_info.get("unknown_pairs")
        if total_pairs is not None or unknown_pairs is not None:
            return f"pairs:{unknown_pairs or 0}/{total_pairs or 0}"
    return None


def _reason_signature_counts(
    counts: Mapping[Tuple[Any, ...], int],
    default_count_kind: str,
) -> Dict[Tuple[str, ...], int]:
    signatures: Dict[Tuple[str, ...], int] = {}
    for raw_key, count in counts.items():
        normalized = _normalize_global_reason_tuple(raw_key, default_count_kind)
        signature = normalized[1:]
        _inc(signatures, signature, int(count or 0))
    return signatures


def _normalize_global_reason_tuple(
    raw_key: Tuple[Any, ...],
    default_count_kind: str,
) -> Tuple[str, ...]:
    parts = tuple(str(part) for part in (raw_key or ()))
    if parts and parts[0] in _GLOBAL_REASON_COUNT_KINDS:
        normalized = parts
    else:
        normalized = (str(default_count_kind),) + parts
    if len(normalized) >= _GLOBAL_REASON_TUPLE_WIDTH:
        return normalized[:_GLOBAL_REASON_TUPLE_WIDTH]
    return normalized + (UNKNOWN_TUPLE_MISSING,) * (
        _GLOBAL_REASON_TUPLE_WIDTH - len(normalized)
    )


def _reason_tuple_from_signature(
    count_kind: str,
    signature: Tuple[str, ...],
) -> Tuple[str, ...]:
    parts = (str(count_kind),) + tuple(str(part) for part in signature)
    if len(parts) >= _GLOBAL_REASON_TUPLE_WIDTH:
        return parts[:_GLOBAL_REASON_TUPLE_WIDTH]
    return parts + (UNKNOWN_TUPLE_MISSING,) * (_GLOBAL_REASON_TUPLE_WIDTH - len(parts))


def _inc(counts: Dict[str, int], key: Any, amount: int = 1) -> None:
    count_key = key if isinstance(key, tuple) else str(key)
    counts[count_key] = int(counts.get(count_key, 0) or 0) + int(amount)


def _recovery_action_key(action: Any) -> str:
    return " | ".join(
        str(value)
        for value in (
            getattr(action, "reason_id", "unknown"),
            getattr(action, "proof_kind", "none"),
            getattr(action, "proof_stage", "unspecified"),
            getattr(action, "status", "unspecified"),
        )
    )


def _diff_counts(before: Mapping[str, int], after: Mapping[str, int]) -> Dict[str, int]:
    keys = set(before.keys()) | set(after.keys())
    return {
        key: int(after.get(key, 0) or 0) - int(before.get(key, 0) or 0)
        for key in sorted(keys)
        if int(after.get(key, 0) or 0) - int(before.get(key, 0) or 0) != 0
    }


def _tuple_multiset_to_dict(counts: Mapping[Tuple[Any, ...], int]) -> Dict[str, int]:
    return {
        " | ".join(_format_tuple_value(part) for part in key): value
        for key, value in counts.items()
    }


def _format_tuple_value(value: Any) -> str:
    if isinstance(value, tuple):
        return "(" + ", ".join(_format_tuple_value(part) for part in value) + ")"
    return str(value)


def _append_count_block(
    lines: list,
    title: str,
    counts: Mapping[Any, int],
    indent: str,
    *,
    empty_label: str = "(none)",
    max_items: Optional[int] = None,
) -> None:
    lines.append(f"{indent}  {title}:")
    if not counts:
        lines.append(f"{indent}    {empty_label}")
        return
    sorted_keys = sorted(counts, key=lambda key: (-abs(int(counts[key])), str(key)))
    shown_keys = sorted_keys[:max_items] if max_items is not None and max_items >= 0 else sorted_keys
    for key in shown_keys:
        lines.append(f"{indent}    - {key}: {counts[key]}")
    if len(shown_keys) < len(sorted_keys):
        hidden = len(sorted_keys) - len(shown_keys)
        hidden_total = sum(int(counts[key]) for key in sorted_keys[len(shown_keys):])
        lines.append(f"{indent}    - ... {hidden} more entries (sum={hidden_total})")


def _summary_max_items(*, compact: bool, max_items: Optional[int]) -> Optional[int]:
    if max_items is not None:
        return max_items
    return 20 if compact else None


def _append_correspondence_diagnostics(
    lines: list,
    diagnostics: Sequence[UnknownReasonCorrespondenceDiagnostic],
    indent: str,
) -> None:
    lines.append(f"{indent}  Validation UNKNOWN unit / reason record correspondence:")
    if not diagnostics:
        lines.append(f"{indent}    - ok")
        return
    for diagnostic in diagnostics:
        lines.append(
            f"{indent}    - {diagnostic.classification}: "
            f"{_format_tuple_value(diagnostic.tuple_key)} "
            f"(validation_unknown_unit={diagnostic.validation_unknown_units}, "
            f"reason_record={diagnostic.reason_records}, "
            f"proof_action={diagnostic.proof_actions})"
        )


def _format_delta(value: int) -> str:
    if value > 0:
        return f"+{value}"
    return str(value)


if __name__ == "__main__":
    raise SystemExit(main())
