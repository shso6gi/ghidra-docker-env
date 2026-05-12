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
    UnknownReasonClass,
    UnknownReasonId,
    UnknownReasonRecord,
    build_unknown_recovery_actions,
    coerce_unknown_reason_records,
    make_unknown_reason,
)


_FINAL_UNKNOWN_TRANSITIONS = {"UNKNOWN", "TIMEOUT"}
_PROOF_BACKLOG_CLASSES = {
    UnknownReasonClass.PROOF_OBLIGATION.value,
    UnknownReasonClass.COVERAGE_GAP.value,
}
RESULT_JSON_BEGIN = "=== EQUIVALENCE_RESULT_JSON_BEGIN ==="
RESULT_JSON_END = "=== EQUIVALENCE_RESULT_JSON_END ==="


@dataclass(frozen=True)
class UnknownValidationSummary:
    total_results: int = 0
    unknown_results: int = 0
    unknown_units: int = 0
    unknown_by_reason: Dict[str, int] = field(default_factory=dict)
    unknown_by_decision_effect: Dict[str, int] = field(default_factory=dict)
    unknown_by_reason_scope: Dict[str, int] = field(default_factory=dict)
    proof_backlog_by_reason: Dict[str, int] = field(default_factory=dict)
    proof_backlog_by_proof_kind: Dict[str, int] = field(default_factory=dict)
    operational_unknown_by_reason: Dict[str, int] = field(default_factory=dict)
    operational_unknown_by_class: Dict[str, int] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "total_results": self.total_results,
            "unknown_results": self.unknown_results,
            "unknown_units": self.unknown_units,
            "unknown_by_reason": dict(self.unknown_by_reason),
            "unknown_by_decision_effect": dict(self.unknown_by_decision_effect),
            "unknown_by_reason_scope": dict(self.unknown_by_reason_scope),
            "proof_backlog_by_reason": dict(self.proof_backlog_by_reason),
            "proof_backlog_by_proof_kind": dict(self.proof_backlog_by_proof_kind),
            "operational_unknown_by_reason": dict(self.operational_unknown_by_reason),
            "operational_unknown_by_class": dict(self.operational_unknown_by_class),
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
    operational_unknown_by_reason_delta: Dict[str, int]
    operational_unknown_by_class_delta: Dict[str, int]

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
            "operational_unknown_by_reason_delta": dict(self.operational_unknown_by_reason_delta),
            "operational_unknown_by_class_delta": dict(self.operational_unknown_by_class_delta),
        }


def summarize_validation_unknowns(
    result_payloads: Iterable[Any],
    *,
    target_cases: Optional[Sequence[str]] = None,
) -> UnknownValidationSummary:
    target_filter = tuple(str(target) for target in (target_cases or ()))
    total_results = 0
    unknown_results = 0
    unknown_units = 0
    unknown_by_reason: Dict[str, int] = {}
    unknown_by_decision_effect: Dict[str, int] = {}
    unknown_by_reason_scope: Dict[str, int] = {}
    proof_backlog_by_reason: Dict[str, int] = {}
    proof_backlog_by_proof_kind: Dict[str, int] = {}
    operational_unknown_by_reason: Dict[str, int] = {}
    operational_unknown_by_class: Dict[str, int] = {}

    for raw_payload in result_payloads:
        payload = _coerce_payload(raw_payload)
        if target_filter and not _payload_matches_targets(payload, target_filter):
            continue
        total_results += 1
        if not _payload_is_unknown(payload):
            continue
        unknown_results += 1

        records = _select_primary_records_by_aggregation_unit(
            _extract_final_unknown_reasons(payload)
        )
        if not records:
            records = (
                make_unknown_reason(
                    UnknownReasonId.UNKNOWN,
                    stage=_payload_stage(payload),
                    pair_or_case=_payload_pair_or_case(payload),
                ),
            )
        unknown_units += len(records)

        for record in records:
            _inc(unknown_by_reason, record.reason_id)
            _inc(unknown_by_decision_effect, record.decision_effect)
            _inc(unknown_by_reason_scope, record.reason_scope)
            if _is_proof_backlog(record):
                _inc(proof_backlog_by_reason, record.reason_id)
                for action in build_unknown_recovery_actions((record,)):
                    _inc(proof_backlog_by_proof_kind, action.proof_kind)
            else:
                _inc(operational_unknown_by_reason, record.reason_id)
                _inc(operational_unknown_by_class, record.reason_class)

    return UnknownValidationSummary(
        total_results=total_results,
        unknown_results=unknown_results,
        unknown_units=unknown_units,
        unknown_by_reason=unknown_by_reason,
        unknown_by_decision_effect=unknown_by_decision_effect,
        unknown_by_reason_scope=unknown_by_reason_scope,
        proof_backlog_by_reason=proof_backlog_by_reason,
        proof_backlog_by_proof_kind=proof_backlog_by_proof_kind,
        operational_unknown_by_reason=operational_unknown_by_reason,
        operational_unknown_by_class=operational_unknown_by_class,
    )


def compare_validation_unknowns(
    before_payloads: Iterable[Any],
    after_payloads: Iterable[Any],
    *,
    target_cases: Optional[Sequence[str]] = None,
) -> UnknownValidationDiff:
    before = summarize_validation_unknowns(before_payloads, target_cases=target_cases)
    after = summarize_validation_unknowns(after_payloads, target_cases=target_cases)
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
        operational_unknown_by_reason_delta=_diff_counts(
            before.operational_unknown_by_reason,
            after.operational_unknown_by_reason,
        ),
        operational_unknown_by_class_delta=_diff_counts(
            before.operational_unknown_by_class,
            after.operational_unknown_by_class,
        ),
    )


def format_validation_unknown_summary(
    summary: UnknownValidationSummary,
    *,
    indent: str = "",
) -> str:
    lines = [
        f"{indent}UNKNOWN validation summary:",
        f"{indent}  Total results : {summary.total_results}",
        f"{indent}  Unknown results: {summary.unknown_results}",
        f"{indent}  Unknown units  : {summary.unknown_units}",
    ]
    _append_count_block(lines, "UNKNOWN by reason", summary.unknown_by_reason, indent)
    _append_count_block(
        lines,
        "UNKNOWN by decision_effect",
        summary.unknown_by_decision_effect,
        indent,
    )
    _append_count_block(
        lines,
        "UNKNOWN by reason_scope",
        summary.unknown_by_reason_scope,
        indent,
    )
    _append_count_block(lines, "Proof backlog by reason", summary.proof_backlog_by_reason, indent)
    _append_count_block(
        lines,
        "Proof backlog by proof_kind",
        summary.proof_backlog_by_proof_kind,
        indent,
    )
    _append_count_block(
        lines,
        "Operational UNKNOWN by reason",
        summary.operational_unknown_by_reason,
        indent,
    )
    return "\n".join(lines)


def format_validation_unknown_diff(
    diff: UnknownValidationDiff,
    *,
    indent: str = "",
) -> str:
    lines = [
        f"{indent}UNKNOWN validation before/after delta:",
        f"{indent}  Unknown results delta: {_format_delta(diff.delta_unknown_results)}",
        f"{indent}  Unknown units delta  : {_format_delta(diff.delta_unknown_units)}",
    ]
    _append_count_block(lines, "UNKNOWN by reason delta", diff.unknown_by_reason_delta, indent)
    _append_count_block(
        lines,
        "UNKNOWN by decision_effect delta",
        diff.unknown_by_decision_effect_delta,
        indent,
    )
    _append_count_block(
        lines,
        "UNKNOWN by reason_scope delta",
        diff.unknown_by_reason_scope_delta,
        indent,
    )
    _append_count_block(
        lines,
        "Proof backlog by reason delta",
        diff.proof_backlog_by_reason_delta,
        indent,
    )
    _append_count_block(
        lines,
        "Proof backlog by proof_kind delta",
        diff.proof_backlog_by_proof_kind_delta,
        indent,
    )
    _append_count_block(
        lines,
        "Operational UNKNOWN by reason delta",
        diff.operational_unknown_by_reason_delta,
        indent,
    )
    _append_count_block(
        lines,
        "Operational UNKNOWN by class delta",
        diff.operational_unknown_by_class_delta,
        indent,
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
    if payload.get("is_equivalent") is not None:
        return False
    debug_trace = payload.get("debug_trace")
    if isinstance(debug_trace, Mapping) and debug_trace.get("final_result") is not None:
        return False
    return payload.get("error_message") is None


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
    primary_records: Dict[Tuple[str, str], UnknownReasonRecord] = {}
    fallback_index = 0
    for record in records:
        aggregation_key = str(record.aggregation_unit or "result")
        unit_key = record.pair_or_case or record.stage
        if unit_key is None:
            unit_key = f"record:{fallback_index}"
            fallback_index += 1
        primary_records.setdefault((aggregation_key, unit_key), record)
    return tuple(primary_records.values())


def _is_proof_backlog(record: UnknownReasonRecord) -> bool:
    return record.reason_class in _PROOF_BACKLOG_CLASSES


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


def _inc(counts: Dict[str, int], key: Any, amount: int = 1) -> None:
    text_key = str(key)
    counts[text_key] = int(counts.get(text_key, 0) or 0) + int(amount)


def _diff_counts(before: Mapping[str, int], after: Mapping[str, int]) -> Dict[str, int]:
    keys = set(before.keys()) | set(after.keys())
    return {
        key: int(after.get(key, 0) or 0) - int(before.get(key, 0) or 0)
        for key in sorted(keys)
        if int(after.get(key, 0) or 0) - int(before.get(key, 0) or 0) != 0
    }


def _append_count_block(
    lines: list,
    title: str,
    counts: Mapping[str, int],
    indent: str,
) -> None:
    lines.append(f"{indent}  {title}:")
    if not counts:
        lines.append(f"{indent}    (none)")
        return
    for key in sorted(counts):
        lines.append(f"{indent}    - {key}: {counts[key]}")


def _format_delta(value: int) -> str:
    if value > 0:
        return f"+{value}"
    return str(value)


if __name__ == "__main__":
    raise SystemExit(main())
