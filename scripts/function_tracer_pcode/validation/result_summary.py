# -*- coding: utf-8 -*-
"""Shared validation result classifier and summary formatter.

Both per-function ``results_summary.txt`` and top-level ``overall_summary.txt``
should be generated from this module so their counts cannot drift.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence, Tuple

from .unknown_reason_summary import (
    compare_validation_unknowns,
    extract_result_payloads_from_logs,
    extract_result_payloads_from_text,
    format_validation_unknown_diff,
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


def format_function_results_summary(
    function_name: str,
    aggregate: ValidationResultAggregate,
    *,
    elapsed_seconds: Optional[float] = None,
    include_unknown_reason_summary: bool = True,
    before_log_paths: Sequence[Any] = (),
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
        lines.append("")
        lines.append(format_validation_unknown_summary(summarize_validation_unknowns(payloads), indent="  "))
        if before_log_paths:
            before_payloads = extract_result_payloads_from_logs(before_log_paths)
            lines.append("")
            lines.append(
                format_validation_unknown_diff(
                    compare_validation_unknowns(before_payloads, payloads),
                    indent="  ",
                )
            )
    lines.append("")
    return "\n".join(lines)


def format_overall_results_summary(
    summary: OverallValidationSummary,
    *,
    function_wall_times: Optional[Mapping[str, float]] = None,
    before_log_paths: Sequence[Any] = (),
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
    lines.append("")
    lines.append(format_validation_unknown_summary(summarize_validation_unknowns(payloads), indent="  "))
    if before_log_paths:
        before_payloads = extract_result_payloads_from_logs(before_log_paths)
        lines.append("")
        lines.append(
            format_validation_unknown_diff(
                compare_validation_unknowns(before_payloads, payloads),
                indent="  ",
            )
        )
    lines.append("============================================================")
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
        print(
            format_function_results_summary(
                function_name,
                aggregate,
                elapsed_seconds=args.elapsed_seconds,
                before_log_paths=before_logs,
            )
        )
        return 0

    overall = aggregate_validation_logs_by_function(args.logs)
    assert_aggregation_invariant(overall)
    before_logs = sorted(Path(args.before_dir).glob("*/*.log")) if args.before_dir else ()
    print(
        format_overall_results_summary(
            overall,
            function_wall_times=_parse_function_wall_times(args.function_wall_time or ()),
            before_log_paths=before_logs,
        )
    )
    return 0


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
