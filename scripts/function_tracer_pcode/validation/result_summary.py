# -*- coding: utf-8 -*-
"""Shared validation result classifier and summary formatter.

Both per-function ``results_summary.txt`` and top-level ``overall_summary.txt``
should be generated from this module so their counts cannot drift.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence, Tuple

from ..equivalence.unknown_reason import (
    UNKNOWN_TUPLE_MISSING,
    coerce_unknown_reason_records,
)
from .unknown_reason_summary import (
    compare_validation_unknowns,
    extract_result_payloads_from_text,
    format_validation_unknown_diff,
    format_validation_unknown_diff_unavailable,
    format_validation_unknown_summary,
    summarize_validation_unknowns,
)


STATUS_EQ = "EQ"
STATUS_NOT_EQ = "NOT_EQ"
STATUS_ERROR = "ERROR"
STATUS_TIMEOUT = "TIMEOUT"
STATUS_UNKNOWN = "UNKNOWN"
STATUS_INCOMPLETE = "INCOMPLETE"
STATUS_ORDER = (
    STATUS_EQ,
    STATUS_NOT_EQ,
    STATUS_ERROR,
    STATUS_UNKNOWN,
    STATUS_TIMEOUT,
    STATUS_INCOMPLETE,
)
BASELINE_MATCH_SCOPE_ALL = "all"
BASELINE_MATCH_SCOPE_AFTER_PAIRS = "after-pairs"
BASELINE_MATCH_LEVEL_EXACT = "exact"
BASELINE_MATCH_LEVEL_FINAL_RESULTS = "final-results"


@dataclass(frozen=True)
class ValidationLogRecord:
    path: str
    function_name: str
    pair_label: str
    status: str
    payloads: Tuple[Mapping[str, Any], ...] = ()


@dataclass(frozen=True)
class ValidationResultAggregate:
    records: Tuple[ValidationLogRecord, ...] = ()
    counts: Dict[str, int] = field(default_factory=dict)
    pairs_by_status: Dict[str, Tuple[str, ...]] = field(default_factory=dict)

    @property
    def total_pairs(self) -> int:
        return len(self.records)

    def count(self, status: str) -> int:
        return int(self.counts.get(status, 0) or 0)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "total_pairs": self.total_pairs,
            "counts": dict(self.counts),
            "pairs_by_status": {
                status: list(pairs)
                for status, pairs in self.pairs_by_status.items()
            },
        }


@dataclass(frozen=True)
class OverallValidationSummary:
    function_summaries: Dict[str, ValidationResultAggregate]
    overall: ValidationResultAggregate

    def to_dict(self) -> Dict[str, Any]:
        return {
            "functions": {
                function: summary.to_dict()
                for function, summary in self.function_summaries.items()
            },
            "overall": self.overall.to_dict(),
        }


@dataclass(frozen=True)
class ValidationBaselineComparison:
    before_total_results: int = 0
    after_total_results: int = 0
    final_result_counts_delta: Dict[str, int] = field(default_factory=dict)
    unknown_final_results_delta: int = 0
    timeout_final_results_delta: int = 0
    timeout_class_multiset_delta: Dict[str, int] = field(default_factory=dict)
    validation_unknown_unit_multiset_delta: Dict[Tuple[str, ...], int] = field(default_factory=dict)
    reason_record_multiset_delta: Dict[Tuple[str, ...], int] = field(default_factory=dict)
    proof_action_multiset_delta: Dict[Tuple[str, ...], int] = field(default_factory=dict)
    pair_final_result_multiset_delta: Dict[Tuple[str, ...], int] = field(default_factory=dict)
    pair_result_multiset_delta: Dict[Tuple[str, ...], int] = field(default_factory=dict)
    missing_pair_identities: Tuple[Tuple[str, str], ...] = ()
    added_pair_identities: Tuple[Tuple[str, str], ...] = ()

    def has_differences(self) -> bool:
        return any(
            (
                self.before_total_results != self.after_total_results,
                bool(self.final_result_counts_delta),
                self.unknown_final_results_delta != 0,
                self.timeout_final_results_delta != 0,
                bool(self.timeout_class_multiset_delta),
                bool(self.validation_unknown_unit_multiset_delta),
                bool(self.reason_record_multiset_delta),
                bool(self.proof_action_multiset_delta),
                bool(self.pair_final_result_multiset_delta),
                bool(self.pair_result_multiset_delta),
                bool(self.missing_pair_identities),
                bool(self.added_pair_identities),
            )
        )

    def has_final_result_differences(self) -> bool:
        return any(
            (
                self.before_total_results != self.after_total_results,
                bool(self.final_result_counts_delta),
                self.unknown_final_results_delta != 0,
                self.timeout_final_results_delta != 0,
                bool(self.pair_final_result_multiset_delta),
                bool(self.missing_pair_identities),
                bool(self.added_pair_identities),
            )
        )


def classify_result_payload(payload: Mapping[str, Any]) -> str:
    if payload.get("error_message"):
        return STATUS_ERROR
    is_equivalent = payload.get("is_equivalent")
    if is_equivalent is True:
        return STATUS_EQ
    if is_equivalent is False:
        return STATUS_NOT_EQ
    if payload.get("is_timeout") is True:
        return STATUS_TIMEOUT
    solver_results = payload.get("solver_results")
    if isinstance(solver_results, Mapping):
        all_results = solver_results.get("all_results") or solver_results.get("results") or ()
        for solver_result in all_results:
            if isinstance(solver_result, Mapping) and str(solver_result.get("status")) == "TIMEOUT":
                return STATUS_TIMEOUT
    return STATUS_UNKNOWN


def classify_log_text(text: str) -> str:
    payloads = extract_result_payloads_from_text(text)
    if payloads:
        return classify_result_payload(payloads[-1])
    for line in text.splitlines():
        if line.startswith("Result: EQUIVALENT"):
            return STATUS_EQ
        if line.startswith("Result: NOT EQUIVALENT"):
            return STATUS_NOT_EQ
        if line.startswith("Result: ERROR"):
            return STATUS_ERROR
        if line.startswith("Result: TIMEOUT"):
            return STATUS_TIMEOUT
        if line.startswith("Result: UNKNOWN"):
            return STATUS_UNKNOWN
    return STATUS_INCOMPLETE


def read_validation_log_record(path: Any) -> ValidationLogRecord:
    log_path = Path(path)
    text = log_path.read_text(errors="replace") if log_path.is_file() else ""
    payloads = extract_result_payloads_from_text(text)
    function_name, pair_label = parse_log_identity(log_path)
    if payloads:
        payload = payloads[-1]
        function_name = str(
            payload.get("function1_name")
            or payload.get("function_name")
            or function_name
        )
    return ValidationLogRecord(
        path=str(log_path),
        function_name=function_name,
        pair_label=pair_label,
        status=classify_log_text(text),
        payloads=payloads,
    )


def parse_log_identity(path: Path) -> Tuple[str, str]:
    stem = path.stem
    parts = stem.rsplit("_", 2)
    if len(parts) == 3:
        return parts[0], f"{parts[1]} ↔ {parts[2]}"
    return stem, stem


def aggregate_validation_records(records: Iterable[ValidationLogRecord]) -> ValidationResultAggregate:
    record_tuple = tuple(records)
    counts = {status: 0 for status in STATUS_ORDER}
    pairs_by_status = {status: [] for status in STATUS_ORDER}
    for record in record_tuple:
        status = record.status if record.status in counts else STATUS_UNKNOWN
        counts[status] += 1
        pairs_by_status[status].append(record.pair_label)
    return ValidationResultAggregate(
        records=record_tuple,
        counts=counts,
        pairs_by_status={
            status: tuple(sorted(pairs))
            for status, pairs in pairs_by_status.items()
        },
    )


def aggregate_validation_logs(log_paths: Iterable[Any]) -> ValidationResultAggregate:
    return aggregate_validation_records(read_validation_log_record(path) for path in log_paths)


def aggregate_validation_logs_by_function(log_paths: Iterable[Any]) -> OverallValidationSummary:
    records = tuple(read_validation_log_record(path) for path in log_paths)
    grouped: Dict[str, list] = {}
    for record in records:
        grouped.setdefault(record.function_name, []).append(record)
    function_summaries = {
        function: aggregate_validation_records(function_records)
        for function, function_records in sorted(grouped.items())
    }
    return OverallValidationSummary(
        function_summaries=function_summaries,
        overall=aggregate_validation_records(records),
    )


def compare_validation_baseline_records(
    before_records: Iterable[ValidationLogRecord],
    after_records: Iterable[ValidationLogRecord],
) -> ValidationBaselineComparison:
    before_record_tuple = tuple(before_records)
    after_record_tuple = tuple(after_records)
    before_unknown_payloads = _payloads_from_records(before_record_tuple)
    after_unknown_payloads = _payloads_from_records(after_record_tuple)
    unknown_diff = compare_validation_unknowns(
        before_unknown_payloads,
        after_unknown_payloads,
    )
    before_counts = _status_counts(before_record_tuple)
    after_counts = _status_counts(after_record_tuple)
    before_pair_identities = _pair_identity_set(before_record_tuple)
    after_pair_identities = _pair_identity_set(after_record_tuple)
    return ValidationBaselineComparison(
        before_total_results=len(before_record_tuple),
        after_total_results=len(after_record_tuple),
        final_result_counts_delta=_diff_counts(before_counts, after_counts),
        unknown_final_results_delta=(
            int(after_counts.get(STATUS_UNKNOWN, 0) or 0)
            - int(before_counts.get(STATUS_UNKNOWN, 0) or 0)
        ),
        timeout_final_results_delta=(
            int(after_counts.get(STATUS_TIMEOUT, 0) or 0)
            - int(before_counts.get(STATUS_TIMEOUT, 0) or 0)
        ),
        timeout_class_multiset_delta=_diff_counts(
            _timeout_class_multiset(before_record_tuple),
            _timeout_class_multiset(after_record_tuple),
        ),
        validation_unknown_unit_multiset_delta=unknown_diff.validation_unknown_unit_multiset_delta,
        reason_record_multiset_delta=unknown_diff.reason_record_multiset_delta,
        proof_action_multiset_delta=unknown_diff.proof_action_multiset_delta,
        pair_final_result_multiset_delta=_diff_counts(
            _pair_final_result_multiset(before_record_tuple),
            _pair_final_result_multiset(after_record_tuple),
        ),
        pair_result_multiset_delta=_diff_counts(
            _pair_result_multiset(before_record_tuple),
            _pair_result_multiset(after_record_tuple),
        ),
        missing_pair_identities=tuple(sorted(before_pair_identities - after_pair_identities)),
        added_pair_identities=tuple(sorted(after_pair_identities - before_pair_identities)),
    )


def canonical_validation_surface(records: Iterable[ValidationLogRecord]) -> Dict[str, Any]:
    """Return the deterministic comparison surface for validation log records."""

    record_tuple = tuple(records)
    unknown_summary = summarize_validation_unknowns(_payloads_from_records(record_tuple))
    return {
        "total_results": len(record_tuple),
        "final_result_counts": _status_counts(record_tuple),
        "unknown_final_results": _status_counts(record_tuple).get(STATUS_UNKNOWN, 0),
        "timeout_final_results": _status_counts(record_tuple).get(STATUS_TIMEOUT, 0),
        "timeout_class_multiset": _string_count_items(_timeout_class_multiset(record_tuple)),
        "validation_unknown_unit_multiset": _tuple_count_items(
            unknown_summary.validation_unknown_unit_multiset
        ),
        "reason_record_multiset": _tuple_count_items(unknown_summary.reason_record_multiset),
        "proof_action_multiset": _tuple_count_items(unknown_summary.proof_action_multiset),
        "pair_final_result_multiset": _tuple_count_items(_pair_final_result_multiset(record_tuple)),
        "pair_result_multiset": _tuple_count_items(_pair_result_multiset(record_tuple)),
        "pair_identities": [list(item) for item in sorted(_pair_identity_set(record_tuple))],
    }


def canonical_validation_surface_hash(records: Iterable[ValidationLogRecord]) -> str:
    payload = json.dumps(
        canonical_validation_surface(records),
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def scope_baseline_records_for_after_pairs(
    before_records: Iterable[ValidationLogRecord],
    after_records: Iterable[ValidationLogRecord],
) -> Tuple[ValidationLogRecord, ...]:
    after_record_tuple = tuple(after_records)
    before_record_tuple = tuple(before_records)
    if not after_record_tuple:
        return before_record_tuple
    after_pair_identities = _pair_identity_set(after_record_tuple)
    return tuple(
        record
        for record in before_record_tuple
        if _canonical_pair_result_tuple(record)[:2] in after_pair_identities
    )


def format_function_results_summary(
    function_name: str,
    aggregate: ValidationResultAggregate,
    *,
    elapsed_seconds: Optional[float] = None,
    include_unknown_reason_summary: bool = True,
    before_log_paths: Sequence[Any] = (),
    baseline_match_scope: str = BASELINE_MATCH_SCOPE_ALL,
) -> str:
    lines = [f"--- Results for {function_name} ---"]
    lines.append(f"  Total pairs     : {aggregate.total_pairs}")
    if elapsed_seconds is not None:
        lines.append(f"  Elapsed wall time: {format_duration(elapsed_seconds)}")
    lines.extend(_format_count_lines("  ", aggregate))
    lines.extend(_format_pair_list_sections("  ", aggregate))
    if all(
        aggregate.count(status) == 0
        for status in (STATUS_NOT_EQ, STATUS_ERROR, STATUS_UNKNOWN, STATUS_TIMEOUT, STATUS_INCOMPLETE)
    ):
        lines.append("")
        lines.append("  ✓ All compared pairs are EQUIVALENT.")
    if include_unknown_reason_summary:
        payloads = _payloads_from_records(aggregate.records)
        unknown_summary = summarize_validation_unknowns(payloads)
        lines.append("")
        lines.append(format_validation_unknown_summary(unknown_summary, indent="  "))
        lines.append("")
        if before_log_paths:
            before_records = aggregate_validation_logs(before_log_paths).records
            before_records = _apply_baseline_match_scope(
                before_records,
                aggregate.records,
                baseline_match_scope,
            )
            before_payloads = _payloads_from_records(before_records)
            lines.append(
                format_validation_unknown_diff(
                    compare_validation_unknowns(before_payloads, payloads),
                    indent="  ",
                )
            )
            lines.append("")
            lines.append(
                format_validation_baseline_comparison(
                    compare_validation_baseline_records(
                        before_records,
                        aggregate.records,
                    ),
                    indent="  ",
                )
            )
        else:
            lines.append(format_validation_unknown_diff_unavailable(unknown_summary, indent="  "))
    lines.append("")
    return "\n".join(lines)


def format_overall_results_summary(
    summary: OverallValidationSummary,
    *,
    function_wall_times: Optional[Mapping[str, float]] = None,
    before_log_paths: Sequence[Any] = (),
    baseline_match_scope: str = BASELINE_MATCH_SCOPE_ALL,
) -> str:
    function_wall_times = function_wall_times or {}
    lines = [
        "============================================================",
        f"  All functions processed: {len(summary.function_summaries)} function(s)",
        "============================================================",
    ]
    for function_name, aggregate in summary.function_summaries.items():
        lines.append(
            "  {name:<30s} : TOTAL={total:3d}, EQ={eq:3d}, NOT_EQ={not_eq:3d}, "
            "ERROR={error:3d}, UNKNOWN={unknown:3d}, TIMEOUT={timeout:3d}, INCOMPLETE={incomplete:3d}, WALL={wall}".format(
                name=function_name,
                total=aggregate.total_pairs,
                eq=aggregate.count(STATUS_EQ),
                not_eq=aggregate.count(STATUS_NOT_EQ),
                error=aggregate.count(STATUS_ERROR),
                unknown=aggregate.count(STATUS_UNKNOWN),
                timeout=aggregate.count(STATUS_TIMEOUT),
                incomplete=aggregate.count(STATUS_INCOMPLETE),
                wall=format_duration(function_wall_times.get(function_name, 0.0)),
            )
        )
    lines.append("")
    lines.append(
        "  Overall totals              : TOTAL={total:3d}, EQ={eq:3d}, NOT_EQ={not_eq:3d}, "
        "ERROR={error:3d}, UNKNOWN={unknown:3d}, TIMEOUT={timeout:3d}, INCOMPLETE={incomplete:3d}".format(
            total=summary.overall.total_pairs,
            eq=summary.overall.count(STATUS_EQ),
            not_eq=summary.overall.count(STATUS_NOT_EQ),
            error=summary.overall.count(STATUS_ERROR),
            unknown=summary.overall.count(STATUS_UNKNOWN),
            timeout=summary.overall.count(STATUS_TIMEOUT),
            incomplete=summary.overall.count(STATUS_INCOMPLETE),
        )
    )
    payloads = _payloads_from_records(summary.overall.records)
    unknown_summary = summarize_validation_unknowns(payloads)
    lines.append("")
    lines.append(format_validation_unknown_summary(unknown_summary, indent="  "))
    lines.append("")
    if before_log_paths:
        before_records = aggregate_validation_logs(before_log_paths).records
        before_records = _apply_baseline_match_scope(
            before_records,
            summary.overall.records,
            baseline_match_scope,
        )
        before_payloads = _payloads_from_records(before_records)
        lines.append(
            format_validation_unknown_diff(
                compare_validation_unknowns(before_payloads, payloads),
                indent="  ",
            )
        )
        lines.append("")
        lines.append(
            format_validation_baseline_comparison(
                compare_validation_baseline_records(
                    before_records,
                    summary.overall.records,
                ),
                indent="  ",
            )
        )
    else:
        lines.append(format_validation_unknown_diff_unavailable(unknown_summary, indent="  "))
    lines.append("============================================================")
    return "\n".join(lines)


def format_validation_baseline_comparison(
    comparison: ValidationBaselineComparison,
    *,
    indent: str = "",
) -> str:
    lines = [
        f"{indent}Canonical baseline comparison:",
        f"{indent}  Total results delta      : {_format_delta(comparison.after_total_results - comparison.before_total_results)}",
        f"{indent}  UNKNOWN final result delta: {_format_delta(comparison.unknown_final_results_delta)}",
        f"{indent}  TIMEOUT final result delta: {_format_delta(comparison.timeout_final_results_delta)}",
    ]
    _append_delta_block(lines, "Final result count delta", comparison.final_result_counts_delta, indent)
    _append_delta_block(
        lines,
        "Timeout class tuple delta",
        comparison.timeout_class_multiset_delta,
        indent,
    )
    _append_delta_block(
        lines,
        "Validation UNKNOWN unit tuple delta",
        comparison.validation_unknown_unit_multiset_delta,
        indent,
    )
    _append_delta_block(
        lines,
        "Reason record tuple delta",
        comparison.reason_record_multiset_delta,
        indent,
    )
    _append_delta_block(
        lines,
        "Proof action tuple delta",
        comparison.proof_action_multiset_delta,
        indent,
    )
    _append_delta_block(
        lines,
        "Pair final result tuple delta",
        comparison.pair_final_result_multiset_delta,
        indent,
    )
    lines.extend(_format_pair_final_result_movement_lines(comparison, indent))
    _append_delta_block(
        lines,
        "Pair result tuple delta",
        comparison.pair_result_multiset_delta,
        indent,
    )
    _append_identity_block(
        lines,
        "Missing pair identities",
        comparison.missing_pair_identities,
        indent,
    )
    _append_identity_block(
        lines,
        "Added pair identities",
        comparison.added_pair_identities,
        indent,
    )
    return "\n".join(lines)


def format_validation_baseline_movement_summary(
    comparison: ValidationBaselineComparison,
    *,
    indent: str = "",
) -> str:
    lines = _format_pair_final_result_movement_lines(comparison, indent)
    if not lines:
        return f"{indent}Final result movements by function: ok"
    return "\n".join(lines)


def assert_aggregation_invariant(summary: OverallValidationSummary) -> None:
    expected_total = sum(function_summary.total_pairs for function_summary in summary.function_summaries.values())
    if summary.overall.total_pairs != expected_total:
        raise AssertionError(
            f"overall total {summary.overall.total_pairs} != function total {expected_total}"
        )
    for status in STATUS_ORDER:
        expected = sum(function_summary.count(status) for function_summary in summary.function_summaries.values())
        actual = summary.overall.count(status)
        if actual != expected:
            raise AssertionError(f"{status} total {actual} != function total {expected}")


def format_duration(total_seconds: Optional[float]) -> str:
    total = max(float(total_seconds or 0.0), 0.0)
    hours = int(total // 3600)
    minutes = int((total - hours * 3600) // 60)
    seconds = total - hours * 3600 - minutes * 60
    if hours > 0:
        return f"{hours}h {minutes:02d}m {seconds:06.3f}s"
    if minutes > 0:
        return f"{minutes}m {seconds:06.3f}s"
    return f"{seconds:.3f}s"


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Generate validation results summaries from logs.")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--function-summary", action="store_true")
    mode.add_argument("--overall-summary", action="store_true")
    parser.add_argument("--function-name", default=None)
    parser.add_argument("--elapsed-seconds", type=float, default=None)
    parser.add_argument("--before-dir", default=None)
    parser.add_argument(
        "--require-before-dir",
        action="store_true",
        help="fail instead of emitting baseline-unavailable delta sections",
    )
    parser.add_argument(
        "--require-baseline-match",
        action="store_true",
        help="fail when canonical before/after baseline comparison has any delta",
    )
    parser.add_argument(
        "--baseline-match-scope",
        choices=(BASELINE_MATCH_SCOPE_ALL, BASELINE_MATCH_SCOPE_AFTER_PAIRS),
        default=BASELINE_MATCH_SCOPE_ALL,
        help=(
            "baseline comparison scope; use after-pairs for filtered representative "
            "reruns where only executed pairs should be compared"
        ),
    )
    parser.add_argument(
        "--baseline-match-level",
        choices=(BASELINE_MATCH_LEVEL_EXACT, BASELINE_MATCH_LEVEL_FINAL_RESULTS),
        default=BASELINE_MATCH_LEVEL_EXACT,
        help=(
            "baseline comparison strictness; final-results ignores reason/action tuple "
            "movement after pair identities and final result counts match"
        ),
    )
    parser.add_argument(
        "--function-wall-time",
        action="append",
        default=None,
        help="function=seconds; may be repeated for overall summaries",
    )
    parser.add_argument("logs", nargs="*")
    args = parser.parse_args(argv)

    if args.function_summary:
        aggregate = aggregate_validation_logs(args.logs)
        function_name = args.function_name or _single_function_name(aggregate.records) or "(unknown)"
        before_logs = sorted(Path(args.before_dir).glob("*.log")) if args.before_dir else ()
        _require_before_logs(before_logs, args.require_before_dir)
        output = format_function_results_summary(
            function_name,
            aggregate,
            elapsed_seconds=args.elapsed_seconds,
            before_log_paths=before_logs,
            baseline_match_scope=args.baseline_match_scope,
        )
        print(output)
        _require_baseline_match(
            before_logs,
            aggregate.records,
            args.require_baseline_match,
            args.baseline_match_scope,
            args.baseline_match_level,
        )
        return 0

    overall = aggregate_validation_logs_by_function(args.logs)
    assert_aggregation_invariant(overall)
    before_logs = sorted(Path(args.before_dir).glob("*/*.log")) if args.before_dir else ()
    _require_before_logs(before_logs, args.require_before_dir)
    output = format_overall_results_summary(
        overall,
        function_wall_times=_parse_function_wall_times(args.function_wall_time or ()),
        before_log_paths=before_logs,
        baseline_match_scope=args.baseline_match_scope,
    )
    print(output)
    _require_baseline_match(
        before_logs,
        overall.overall.records,
        args.require_baseline_match,
        args.baseline_match_scope,
        args.baseline_match_level,
    )
    return 0


def _require_before_logs(before_logs: Sequence[Any], require_before_dir: bool) -> None:
    if require_before_dir and not before_logs:
        raise SystemExit(
            "--require-before-dir requires --before-dir with baseline *.log files"
        )


def _require_baseline_match(
    before_logs: Sequence[Any],
    after_records: Sequence[ValidationLogRecord],
    require_baseline_match: bool,
    baseline_match_scope: str,
    baseline_match_level: str,
) -> None:
    if not require_baseline_match:
        return
    before_records = aggregate_validation_logs(before_logs).records if before_logs else ()
    before_records = _apply_baseline_match_scope(
        before_records,
        after_records,
        baseline_match_scope,
    )
    comparison = compare_validation_baseline_records(before_records, after_records)
    if baseline_match_level == BASELINE_MATCH_LEVEL_FINAL_RESULTS:
        failed = comparison.has_final_result_differences()
    else:
        failed = comparison.has_differences()
    if failed:
        raise SystemExit(
            "baseline comparison mismatch\n"
            + format_validation_baseline_movement_summary(comparison)
        )


def _apply_baseline_match_scope(
    before_records: Iterable[ValidationLogRecord],
    after_records: Iterable[ValidationLogRecord],
    baseline_match_scope: str,
) -> Tuple[ValidationLogRecord, ...]:
    before_record_tuple = tuple(before_records)
    if baseline_match_scope == BASELINE_MATCH_SCOPE_AFTER_PAIRS:
        return scope_baseline_records_for_after_pairs(before_record_tuple, after_records)
    return before_record_tuple


def _format_count_lines(indent: str, aggregate: ValidationResultAggregate) -> Tuple[str, ...]:
    return (
        f"{indent}Equivalent     : {aggregate.count(STATUS_EQ)}",
        f"{indent}Not equivalent : {aggregate.count(STATUS_NOT_EQ)}",
        f"{indent}Error          : {aggregate.count(STATUS_ERROR)}",
        f"{indent}Unknown        : {aggregate.count(STATUS_UNKNOWN)}",
        f"{indent}Timeout        : {aggregate.count(STATUS_TIMEOUT)}",
        f"{indent}Incomplete     : {aggregate.count(STATUS_INCOMPLETE)}",
    )


def _format_pair_list_sections(indent: str, aggregate: ValidationResultAggregate) -> Tuple[str, ...]:
    lines = []
    for status, title in (
        (STATUS_NOT_EQ, "NOT EQUIVALENT pairs"),
        (STATUS_ERROR, "ERROR pairs"),
        (STATUS_UNKNOWN, "UNKNOWN pairs"),
        (STATUS_TIMEOUT, "TIMEOUT pairs"),
        (STATUS_INCOMPLETE, "INCOMPLETE logs"),
    ):
        pairs = aggregate.pairs_by_status.get(status) or ()
        if not pairs:
            continue
        lines.append("")
        lines.append(f"{indent}{title}:")
        for pair in pairs:
            lines.append(f"{indent}  - {pair}")
    return tuple(lines)


def _payloads_from_records(records: Iterable[ValidationLogRecord]) -> Tuple[Mapping[str, Any], ...]:
    payloads = []
    for record in records:
        payloads.extend(record.payloads)
    return tuple(payloads)


def _status_counts(records: Iterable[ValidationLogRecord]) -> Dict[str, int]:
    counts = {status: 0 for status in STATUS_ORDER}
    for record in records:
        status = record.status if record.status in counts else STATUS_UNKNOWN
        counts[status] += 1
    return counts


def _string_count_items(counts: Mapping[str, int]) -> Sequence[Dict[str, Any]]:
    return [
        {"key": str(key), "count": int(value)}
        for key, value in sorted(counts.items(), key=lambda item: str(item[0]))
    ]


def _tuple_count_items(counts: Mapping[Any, int]) -> Sequence[Dict[str, Any]]:
    return [
        {"key": list(key) if isinstance(key, tuple) else key, "count": int(value)}
        for key, value in sorted(counts.items(), key=lambda item: str(item[0]))
    ]


def _pair_result_multiset(records: Iterable[ValidationLogRecord]) -> Dict[Tuple[str, ...], int]:
    counts: Dict[Tuple[str, ...], int] = {}
    for record in records:
        key = _canonical_pair_result_tuple(record)
        counts[key] = int(counts.get(key, 0) or 0) + 1
    return counts


def _pair_final_result_multiset(records: Iterable[ValidationLogRecord]) -> Dict[Tuple[str, ...], int]:
    counts: Dict[Tuple[str, ...], int] = {}
    for record in records:
        key = _canonical_pair_result_tuple(record)[:3]
        counts[key] = int(counts.get(key, 0) or 0) + 1
    return counts


def _pair_identity_set(records: Iterable[ValidationLogRecord]) -> set:
    return {
        _canonical_pair_result_tuple(record)[:2]
        for record in records
    }


def _timeout_class_multiset(records: Iterable[ValidationLogRecord]) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    for record in records:
        payload = record.payloads[-1] if record.payloads else {}
        timeout_class = _canonical_timeout_class(payload, record.status)
        if timeout_class == UNKNOWN_TUPLE_MISSING:
            continue
        counts[timeout_class] = int(counts.get(timeout_class, 0) or 0) + 1
    return counts


def _canonical_pair_result_tuple(record: ValidationLogRecord) -> Tuple[str, ...]:
    payload = record.payloads[-1] if record.payloads else {}
    function_name = str(
        payload.get("function1_name")
        or payload.get("function_name")
        or record.function_name
    )
    left_binary, right_binary = _payload_or_record_binary_ids(payload, record)
    binary_pair = " ↔ ".join(sorted((left_binary, right_binary)))
    return (
        function_name,
        binary_pair,
        record.status if record.status in STATUS_ORDER else STATUS_UNKNOWN,
        _canonical_blocking_reason(payload, record.status),
        _canonical_timeout_class(payload, record.status),
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
    return Path(text).name if text else UNKNOWN_TUPLE_MISSING


def _canonical_blocking_reason(payload: Mapping[str, Any], status: str) -> str:
    explicit = payload.get("blocking_reason")
    if explicit:
        return str(explicit)
    records = tuple(coerce_unknown_reason_records(payload.get("unknown_reasons") or ()))
    if records:
        return ",".join(sorted({str(record.reason_id) for record in records}))
    if status == STATUS_TIMEOUT:
        return _canonical_timeout_class(payload, status)
    return UNKNOWN_TUPLE_MISSING


def _canonical_timeout_class(payload: Mapping[str, Any], status: str) -> str:
    if status != STATUS_TIMEOUT:
        return UNKNOWN_TUPLE_MISSING
    for key in ("timeout_class", "timeout_reason"):
        value = payload.get(key)
        if value:
            return str(value)
    solver_results = payload.get("solver_results")
    if isinstance(solver_results, Mapping):
        all_results = solver_results.get("all_results") or solver_results.get("results") or ()
        for solver_result in all_results:
            if isinstance(solver_result, Mapping) and str(solver_result.get("status")) == "TIMEOUT":
                return "solver_timeout"
    if payload.get("is_timeout") is True:
        return "timeout"
    return UNKNOWN_TUPLE_MISSING


def _diff_counts(before: Mapping[Any, int], after: Mapping[Any, int]) -> Dict[Any, int]:
    keys = set(before.keys()) | set(after.keys())
    return {
        key: int(after.get(key, 0) or 0) - int(before.get(key, 0) or 0)
        for key in sorted(keys)
        if int(after.get(key, 0) or 0) - int(before.get(key, 0) or 0) != 0
    }


def _append_delta_block(
    lines: list,
    title: str,
    counts: Mapping[Any, int],
    indent: str,
) -> None:
    lines.append(f"{indent}  {title}:")
    if not counts:
        lines.append(f"{indent}    ok")
        return
    for key in sorted(counts):
        lines.append(f"{indent}    - {_format_key(key)}: {_format_delta(counts[key])}")


def _append_identity_block(
    lines: list,
    title: str,
    identities: Sequence[Tuple[str, str]],
    indent: str,
) -> None:
    lines.append(f"{indent}  {title}:")
    if not identities:
        lines.append(f"{indent}    ok")
        return
    for function_name, binary_pair in identities:
        lines.append(f"{indent}    - {function_name} | {binary_pair}")


def _format_pair_final_result_movement_lines(
    comparison: ValidationBaselineComparison,
    indent: str,
) -> list:
    movements = _pair_final_result_movements(
        comparison.pair_final_result_multiset_delta
    )
    lines = [f"{indent}  Final result movements by function:"]
    if not movements:
        lines.append(f"{indent}    ok")
        return lines
    for before_status, after_status, function_name in sorted(movements):
        lines.append(
            f"{indent}    - {before_status}->{after_status} | "
            f"{function_name}: {movements[(before_status, after_status, function_name)]}"
        )
    return lines


def _pair_final_result_movements(
    delta: Mapping[Tuple[str, ...], int],
) -> Dict[Tuple[str, str, str], int]:
    removed: Dict[Tuple[str, str], Dict[str, int]] = {}
    added: Dict[Tuple[str, str], Dict[str, int]] = {}
    for key, count in delta.items():
        if len(key) < 3:
            continue
        function_name, binary_pair, status = key[:3]
        bucket = added if count > 0 else removed
        status_counts = bucket.setdefault((function_name, binary_pair), {})
        status_counts[status] = int(status_counts.get(status, 0) or 0) + abs(int(count))

    movements: Dict[Tuple[str, str, str], int] = {}
    for pair_identity in sorted(set(removed) & set(added)):
        removed_statuses = removed[pair_identity]
        added_statuses = added[pair_identity]
        for before_status in sorted(removed_statuses):
            before_count = removed_statuses[before_status]
            if before_count <= 0:
                continue
            for after_status in sorted(added_statuses):
                after_count = added_statuses[after_status]
                if after_count <= 0:
                    continue
                moved = min(before_count, after_count)
                if moved <= 0:
                    continue
                function_name, _binary_pair = pair_identity
                movement_key = (before_status, after_status, function_name)
                movements[movement_key] = int(movements.get(movement_key, 0) or 0) + moved
                removed_statuses[before_status] -= moved
                added_statuses[after_status] -= moved
                before_count -= moved
                if before_count <= 0:
                    break
    return movements


def _format_key(key: Any) -> str:
    if isinstance(key, tuple):
        return " | ".join(str(part) for part in key)
    return str(key)


def _format_delta(value: int) -> str:
    value = int(value or 0)
    if value > 0:
        return f"+{value}"
    return str(value)


def _single_function_name(records: Sequence[ValidationLogRecord]) -> Optional[str]:
    names = {record.function_name for record in records}
    if len(names) == 1:
        return next(iter(names))
    return None


def _parse_function_wall_times(values: Iterable[str]) -> Dict[str, float]:
    parsed = {}
    for value in values:
        if "=" not in value:
            continue
        name, raw_seconds = value.split("=", 1)
        try:
            parsed[name] = float(raw_seconds)
        except ValueError:
            parsed[name] = 0.0
    return parsed


if __name__ == "__main__":
    raise SystemExit(main())
