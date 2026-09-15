# -*- coding: utf-8 -*-
"""Shared validation result classifier and summary formatter.

Both per-function ``results_summary.txt`` and top-level ``overall_summary.txt``
should be generated from this module so their counts cannot drift.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.authority.decision.pair_status_authority import (
    find_pair_status_public_key,
    pair_status_operational_diagnostic,
    validate_signed_pair_status,
)
from scripts.function_tracer_pcode.authority.decision.production_cutover import (
    conditional_outcome_from_payload,
)
from scripts.function_tracer_pcode.checker.diagnostics import (
    FAILURE_INTERNAL_EXCEPTION as INTERNAL_EXCEPTION_KEY,
    FAILURE_SWALLOWED_EXCEPTIONS as SWALLOWED_LEDGER_KEY,
)
from scripts.function_tracer_pcode.checker.unknown_reason import (
    coerce_unknown_reason_records,
)
from scripts.function_tracer_pcode.proof.unknown_reason import (
    UNKNOWN_TUPLE_MISSING,
)
from scripts.function_tracer_pcode.reporting.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
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
# Issue #125 PR-125-B: typed failure 診断（`diagnostics["failures"]`）の集計。
# 見出しは `run_health_summary.parse_overall_summary_health` の `section_titles`
# に登録してあるので、名前を変えるときは両方を変える。
FAILURE_SWALLOWED_BY_TYPE_TITLE = "Swallowed exceptions by type"
FAILURE_INTERNAL_BY_SITE_TITLE = "Internal exceptions by site"
FAILURE_SWALLOWED_BY_TYPE_KEY = "swallowed_exceptions_by_type"
FAILURE_SWALLOWED_BY_SITE_KEY = "swallowed_exceptions_by_site"
FAILURE_INTERNAL_BY_SITE_KEY = "internal_exception_by_site"
FAILURE_EVIDENCE_KEY = "failure_diagnostic_evidence"
FAILURE_SWALLOWED_TOTAL_KEY = "swallowed_exception_total"
FAILURE_SWALLOWED_OBSERVED_TOTAL_KEY = "swallowed_exception_observed_total"
#: `diagnostics["failures"]` block の 3 値（key 欠落 / 壊れた値 / 正常）。
#: `is` で比較するので intern 済みの literal をそのまま使う。
FAILURE_BLOCK_MISSING = "block_missing"
FAILURE_BLOCK_BROKEN = "block_broken"
FAILURE_BLOCK_PRESENT = "block_present"
#: evidence は surface ごと。片方が壊れても、もう片方の観測は有効なまま残す。
FAILURE_SWALLOWED_SURFACE = "swallowed_exceptions"
FAILURE_INTERNAL_SURFACE = "internal_exception"
#: surface ごとの evidence の状態。`(none)` / exact total を名乗れるのは complete だけ。
EVIDENCE_COMPLETE = "complete"
EVIDENCE_PARTIAL = "partial"
EVIDENCE_UNKNOWN = "unknown"

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
    pair_status_metadata: Optional[Mapping[str, Any]] = None
    # Issue #20: the assumption-dependent column.  ``status`` stays the
    # unconditional classification; this one is aggregated separately and is
    # ``None`` for every pair that carries no conditional decision.
    conditional_status: Optional[str] = None


@dataclass(frozen=True)
class ValidationResultAggregate:
    records: Tuple[ValidationLogRecord, ...] = ()
    counts: Dict[str, int] = field(default_factory=dict)
    pairs_by_status: Dict[str, Tuple[str, ...]] = field(default_factory=dict)
    # Issue #20: conditional (assumption-dependent) results are counted in
    # their own column.  ``counts`` never sees them, so the unconditional
    # totals of a run cannot move because a conditional proof succeeded.
    conditional_counts: Dict[str, int] = field(default_factory=dict)
    conditional_pairs_by_status: Dict[str, Tuple[str, ...]] = field(default_factory=dict)

    @property
    def total_pairs(self) -> int:
        return len(self.records)

    def count(self, status: str) -> int:
        return int(self.counts.get(status, 0) or 0)

    def conditional_count(self, status: str) -> int:
        return int(self.conditional_counts.get(status, 0) or 0)

    @property
    def total_conditional_pairs(self) -> int:
        return sum(int(value or 0) for value in self.conditional_counts.values())

    def to_dict(self) -> Dict[str, Any]:
        return {
            "total_pairs": self.total_pairs,
            "counts": dict(self.counts),
            "pairs_by_status": {
                status: list(pairs)
                for status, pairs in self.pairs_by_status.items()
            },
            "conditional_counts": dict(self.conditional_counts),
            "conditional_pairs_by_status": {
                status: list(pairs)
                for status, pairs in self.conditional_pairs_by_status.items()
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


def classify_result_payload(payload: Mapping[str, Any], *, matrix_context: bool = False) -> str:
    if payload.get("decision_receipt") is not None:
        from scripts.function_tracer_pcode.authority.decision.production_cutover import (
            outcome_from_payload,
        )

        outcome = outcome_from_payload(payload).value
        return STATUS_EQ if outcome == "EQUIVALENT" else outcome
    failure_status = str(payload.get("failure_status") or "")
    if matrix_context and failure_status == "function_lookup_miss":
        return STATUS_INCOMPLETE
    if payload.get("error_message"):
        return STATUS_ERROR
    if failure_status in {"decompilation_failed", "high_function_missing"}:
        return STATUS_UNKNOWN
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


def classify_log_text(text: str, *, matrix_context: bool = False) -> str:
    final_events = _extract_final_result_events(text, matrix_context=matrix_context)
    if final_events:
        return final_events[-1][1]
    return STATUS_INCOMPLETE


def classify_canonical_log_text(text: str, *, matrix_context: bool = False) -> str:
    """Classify one cutover log only when its final event is receipt-bound JSON."""

    events = _extract_final_result_events(text, matrix_context=matrix_context)
    if not events:
        return STATUS_INCOMPLETE
    _line, status, payload = events[-1]
    if payload is None or payload.get("decision_receipt") is None:
        return STATUS_INCOMPLETE
    return status


def _extract_final_result_events(
    text: str,
    *,
    matrix_context: bool = False,
) -> Tuple[Tuple[int, str, Optional[Mapping[str, Any]]], ...]:
    events = []
    current_lines = []
    in_payload = False
    for index, line in enumerate(text.splitlines()):
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
                    events.append(
                        (
                            index,
                            classify_result_payload(payload, matrix_context=matrix_context),
                            payload,
                        )
                    )
            in_payload = False
            current_lines = []
            continue
        if in_payload:
            current_lines.append(line)
            continue
        status = _classify_result_line(line)
        if status is not None:
            events.append((index, status, None))
    return tuple(sorted(events, key=lambda event: event[0]))


def _classify_result_line(line: str) -> Optional[str]:
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
    return None


def read_validation_log_record(
    path: Any, *, canonical_only: bool = False,
) -> ValidationLogRecord:
    log_path = Path(path)
    text = log_path.read_text(errors="replace") if log_path.is_file() else ""
    payloads = extract_result_payloads_from_text(text)
    pair_status = None
    operational_invalid = None
    if canonical_only:
        pair_status_path = log_path.with_suffix(".pair-status.json")
        if pair_status_path.is_file():
            pair_status_payload = json.loads(
                pair_status_path.read_text(encoding="utf-8")
            )
            # Operational diagnostics are deliberately outside signed authority.
            # They preserve the primary classifier exception when sealing could
            # not begin, and therefore cannot make any canonical outcome claim.
            # Recognize only the shared exact schema before signature validation.
            # Any extension, missing detail, or different error kind continues
            # into signed validation and is rejected fail-closed.  Keeping this
            # boundary explicit also prevents an unsigned diagnostic from being
            # accepted as a resumable or publication-grade pair-status record.
            operational_invalid = pair_status_operational_diagnostic(
                pair_status_payload
            )
            if operational_invalid is None:
                pair_status = validate_signed_pair_status(
                    pair_status_payload,
                    public_key_path=find_pair_status_public_key(pair_status_path),
                )
        events = _extract_final_result_events(text, matrix_context=True)
        final_payload = events[-1][2] if events else None
        payloads = (
            (final_payload,)
            if final_payload is not None
            and final_payload.get("decision_receipt") is not None
            and (
                pair_status is None
                or classify_result_payload(final_payload, matrix_context=True)
                == (
                    STATUS_EQ
                    if pair_status["canonical_outcome"] == "EQUIVALENT"
                    else pair_status["canonical_outcome"]
                )
            )
            else ()
        )
        if pair_status is None:
            payloads = ()
    function_name, pair_label = parse_log_identity(log_path)
    conditional_status = None
    if payloads:
        payload = payloads[-1]
        function_name = str(
            payload.get("function1_name")
            or payload.get("function_name")
            or function_name
        )
        # Issue #20: the conditional column is validated against its own
        # receipt.  It is aggregated separately and never feeds ``status``.
        conditional = conditional_outcome_from_payload(payload)
        conditional_status = None if conditional is None else conditional.value
    if pair_status is not None:
        # In canonical mode the signed body is the authority for this column
        # too; the log payload may only agree with it.
        signed_conditional = pair_status.get("conditional_outcome")
        if payloads and conditional_status != signed_conditional:
            raise ValueError(
                "pair-status conditional column differs from the result payload"
            )
        conditional_status = signed_conditional
    return ValidationLogRecord(
        path=str(log_path),
        function_name=function_name,
        pair_label=pair_label,
        status=(
            (
                STATUS_EQ
                if pair_status["canonical_outcome"] == "EQUIVALENT"
                else pair_status["canonical_outcome"]
            )
            if pair_status is not None
            else STATUS_ERROR
            if operational_invalid is not None
            else STATUS_INCOMPLETE
            if canonical_only
            else classify_log_text(text, matrix_context=True)
        ),
        payloads=payloads,
        conditional_status=conditional_status,
        pair_status_metadata=(
            {
                "error_kind": pair_status["error_kind"],
                "child_returncode": pair_status["child_returncode"],
                "supervisor_status": pair_status["supervisor_status"],
            }
            if pair_status is not None
            else {
                "error_kind": operational_invalid["error_kind"],
                "child_returncode": None,
                "supervisor_status": "INVALID",
                "classification_valid": False,
                "detail": operational_invalid["detail"],
            }
            if operational_invalid is not None
            else None
        ),
    )


def parse_log_identity(path: Path) -> Tuple[str, str]:
    stem = path.stem
    matrix_identity = re.fullmatch(
        r"(?P<function>.+)_N_(?P<left>B\d+)_O_(?P<right>B\d+)",
        stem,
    )
    if matrix_identity is not None:
        return (
            matrix_identity.group("function"),
            f"{matrix_identity.group('left')} ↔ {matrix_identity.group('right')}",
        )
    parts = stem.rsplit("_", 2)
    if len(parts) == 3:
        return parts[0], f"{parts[1]} ↔ {parts[2]}"
    return stem, stem


def error_pairs_from_summary(path: Path, *, matrix: str) -> Tuple[str, ...]:
    """Read only the ERROR pair section from a function summary.

    ERROR-only reruns use this historical, human-readable census as the
    scheduling authority.  ``matrix`` controls the pair key format emitted
    for the Eq (``B1_B2``) and Neq (``N_B1_O_B2``) runners.
    """

    if matrix not in {"EQ", "NEQ"}:
        raise ValueError("matrix must be EQ or NEQ")
    lines = path.read_text(encoding="utf-8").splitlines()
    in_errors = False
    pairs = []
    for line in lines:
        stripped = line.strip()
        if stripped == "ERROR pairs:":
            in_errors = True
            continue
        if in_errors and (not stripped or stripped.endswith("pairs:")
                          or stripped.endswith("logs:")):
            break
        if not in_errors:
            continue
        match = re.fullmatch(r"-\s+(?P<left>\S+)\s+↔\s+(?P<right>\S+)", stripped)
        if match is None:
            continue
        left, right = match.group("left"), match.group("right")
        if matrix == "EQ":
            if not (re.fullmatch(r"B\d+", left) and re.fullmatch(r"B\d+", right)):
                raise ValueError("Eq ERROR pair identity is malformed")
            pairs.append(f"{left}_{right}")
        else:
            if not (re.fullmatch(r"N_B\d+", left)
                    and re.fullmatch(r"O_B\d+", right)):
                raise ValueError("Neq ERROR pair identity is malformed")
            pairs.append(f"{left}_{right}")
    return tuple(dict.fromkeys(pairs))


def aggregate_validation_records(records: Iterable[ValidationLogRecord]) -> ValidationResultAggregate:
    record_tuple = tuple(records)
    counts = {status: 0 for status in STATUS_ORDER}
    pairs_by_status = {status: [] for status in STATUS_ORDER}
    conditional_counts: Dict[str, int] = {}
    conditional_pairs: Dict[str, list] = {}
    for record in record_tuple:
        status = record.status if record.status in counts else STATUS_UNKNOWN
        counts[status] += 1
        pairs_by_status[status].append(record.pair_label)
        conditional = record.conditional_status
        if conditional is None:
            continue
        conditional_counts[conditional] = conditional_counts.get(conditional, 0) + 1
        conditional_pairs.setdefault(conditional, []).append(record.pair_label)
    return ValidationResultAggregate(
        records=record_tuple,
        counts=counts,
        pairs_by_status={
            status: tuple(sorted(pairs))
            for status, pairs in pairs_by_status.items()
        },
        conditional_counts={
            status: conditional_counts[status] for status in sorted(conditional_counts)
        },
        conditional_pairs_by_status={
            status: tuple(sorted(conditional_pairs[status]))
            for status in sorted(conditional_pairs)
        },
    )


def aggregate_validation_logs(
    log_paths: Iterable[Any], *, canonical_only: bool = False,
) -> ValidationResultAggregate:
    return aggregate_validation_records(
        read_validation_log_record(path, canonical_only=canonical_only)
        for path in log_paths
    )


def aggregate_validation_logs_by_function(
    log_paths: Iterable[Any], *, canonical_only: bool = False,
) -> OverallValidationSummary:
    records = tuple(
        read_validation_log_record(path, canonical_only=canonical_only)
        for path in log_paths
    )
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


@dataclass(frozen=True)
class FailureEvidence:
    """1 つの診断 surface を、何 pair 分読めたか（Issue #125）。

    ``observed`` / ``missing`` / ``malformed`` は排他で、合計が run の pair 数。

    * ``observed``  … その surface を読めた pair
    * ``missing``   … ``diagnostics["failures"]`` ごと無い pair（PR-125-A 以前の
      log、結果 payload の無い pair）。surface が読めたわけではない。
    * ``malformed`` … block はあるがその surface が契約から外れていた pair。
    """

    observed: int = 0
    missing: int = 0
    malformed: int = 0

    @property
    def state(self) -> str:
        # 未観測が 1 pair でもあれば「run 全体で 0 件」とは言えない。
        if not self.missing and not self.malformed:
            return EVIDENCE_COMPLETE
        if not self.observed:
            return EVIDENCE_UNKNOWN
        return EVIDENCE_PARTIAL

    @property
    def is_complete(self) -> bool:
        return self.state == EVIDENCE_COMPLETE

    def to_dict(self) -> Dict[str, Any]:
        return {
            "state": self.state,
            "observed": self.observed,
            "missing": self.missing,
            "malformed": self.malformed,
        }


@dataclass(frozen=True)
class FailureDiagnosticsSummary:
    """1 run 分の typed failure 診断（Issue #125）。

    源は結果 payload の ``diagnostics["failures"]`` だけで、**判定には一切
    触れない**。`unknown_cause_aggregate` / canonical unknown reason の集計とは
    別経路で、reason 語彙も共有しない（診断を decision authority へ接続しない）。

    evidence は **surface ごと**に持つ。``internal_exception`` が書かれていない
    ことは、正常な failure block の中では「観測して 0 件」だが、block 自体が
    無ければ「未観測」で意味が違う。同じ理由で、握り潰し台帳が壊れている pair
    があっても内部エラーの観測結果までは捨てない。

    件数の読み方:

    * ``swallowed_observed_total`` は **観測できた分の合計（下限）**。常に整数。
    * ``swallowed_exact_total`` は run 全体の正確な合計。evidence が complete
      でなければ ``None``（0 と主張しない）。
    * ``*_by_type`` / ``*_by_site`` は観測できた行だけ。evidence が complete で
      なければ下限であって「run 全体の内訳」ではない。
    """

    swallowed_evidence: FailureEvidence = field(default_factory=FailureEvidence)
    internal_evidence: FailureEvidence = field(default_factory=FailureEvidence)
    swallowed_observed_total: int = 0
    swallowed_exceptions_by_type: Dict[str, int] = field(default_factory=dict)
    swallowed_exceptions_by_site: Dict[str, int] = field(default_factory=dict)
    internal_exception_by_site: Dict[str, int] = field(default_factory=dict)

    @property
    def swallowed_exact_total(self) -> Optional[int]:
        """evidence が complete のときだけ run 全体の正確な合計。"""

        if self.swallowed_evidence.is_complete:
            return self.swallowed_observed_total
        return None

    def to_dict(self) -> Dict[str, Any]:
        return {
            FAILURE_EVIDENCE_KEY: {
                FAILURE_SWALLOWED_SURFACE: self.swallowed_evidence.to_dict(),
                FAILURE_INTERNAL_SURFACE: self.internal_evidence.to_dict(),
            },
            FAILURE_SWALLOWED_TOTAL_KEY: self.swallowed_exact_total,
            FAILURE_SWALLOWED_OBSERVED_TOTAL_KEY: self.swallowed_observed_total,
            FAILURE_SWALLOWED_BY_TYPE_KEY: dict(self.swallowed_exceptions_by_type),
            FAILURE_SWALLOWED_BY_SITE_KEY: dict(self.swallowed_exceptions_by_site),
            FAILURE_INTERNAL_BY_SITE_KEY: dict(self.internal_exception_by_site),
        }


#: `dict.get()` では「key が無い」と「値が None」を区別できないので、その 2 つを
#: 分けたい読み取りではこの番兵を既定値にする。
_ABSENT = object()


def _is_count(value: Any) -> bool:
    """件数として受理できる値か（bool は int だが件数ではない）。"""

    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def _failure_diagnostics_block(
    payload: Mapping[str, Any],
) -> Tuple[str, Mapping[str, Any]]:
    """1 つの結果 payload から ``diagnostics["failures"]`` を 3 値で取り出す。

    * ``FAILURE_BLOCK_MISSING`` — ``diagnostics`` / ``failures`` の **key 自体が
      無い**。PR-125-A 以前の log。**未観測**であって 0 件ではない。
    * ``FAILURE_BLOCK_BROKEN`` — key はあるが値が mapping でない（``None`` /
      文字列 / list …）。log は PR-125-A 以降だが、観測 surface が **壊れて
      いる**。未観測と混同しない。
    * ``FAILURE_BLOCK_PRESENT`` — mapping。surface ごとの検証へ進む。空の
      mapping もここに入り、どちらの surface も読めないので malformed になる。
    """

    if not isinstance(payload, Mapping) or "diagnostics" not in payload:
        return FAILURE_BLOCK_MISSING, {}
    diagnostics = payload["diagnostics"]
    if not isinstance(diagnostics, Mapping):
        return FAILURE_BLOCK_BROKEN, {}
    if "failures" not in diagnostics:
        return FAILURE_BLOCK_MISSING, {}
    failures = diagnostics["failures"]
    if not isinstance(failures, Mapping):
        return FAILURE_BLOCK_BROKEN, {}
    return FAILURE_BLOCK_PRESENT, failures


def _bump_count(counts: Dict[str, int], key: str, amount: int) -> None:
    counts[key] = counts.get(key, 0) + amount


def _read_swallowed_surface(
    failures: Mapping[str, Any],
    by_type: Dict[str, int],
    by_site: Dict[str, int],
) -> Tuple[bool, int]:
    """握り潰し台帳を 1 pair 分読む。``(読み切れたか, 観測した件数)``。

    PR-125-A の producer 契約は ``{"total": <非負 int>, "by_site": [...]}``。
    readable と言えるのは **その契約を全部満たしたときだけ**:

    * ``by_site`` key があり、str/bytes でない sequence
    * ``total`` key が **存在**し、bool でない非負 int
    * 各行が mapping で、``count`` が bool でない非負 int
    * 宣言された ``total`` が読めた行の合計と一致

    1 つでも欠けたら readable にしない（``total`` が無い payload から
    「全行を観測できた」= exact total は導けない）。ただし **そこまでに読めた
    行は捨てない**。読み切れなかった pair は呼び出し側が ``malformed`` に
    数えるので、surface が complete を主張することはなく、読めた分は
    observed lower bound として残る。
    """

    swallowed = failures.get(SWALLOWED_LEDGER_KEY, _ABSENT)
    if not isinstance(swallowed, Mapping):
        # `attach_failure_diagnostics` は全 pair でこの key を書く。無い block も
        # 値が mapping でない block も、この surface は読めていない。
        return False, 0
    rows = swallowed.get("by_site", _ABSENT)
    declared = swallowed.get("total", _ABSENT)
    readable = True
    row_total = 0
    if not isinstance(rows, Sequence) or isinstance(rows, (str, bytes)):
        # key 欠落（`_ABSENT`）も非 sequence もここに落ちる。
        readable = False
        rows = ()
    for row in rows:
        if not isinstance(row, Mapping):
            readable = False
            continue
        count = row.get("count", _ABSENT)
        if not _is_count(count):
            readable = False
            continue
        row_total += count
        _bump_count(by_type, str(row.get("exception_type") or UNKNOWN_TUPLE_MISSING), count)
        _bump_count(by_site, str(row.get("site") or UNKNOWN_TUPLE_MISSING), count)
    # `total` は producer の必須 key。欠落・None・bool・非 int・負数・行の合計との
    # 不一致は、どれも「全行を観測できた」ことを保証しない。
    if not _is_count(declared) or declared != row_total:
        readable = False
    return readable, row_total


def _read_internal_surface(
    failures: Mapping[str, Any], by_site: Dict[str, int],
) -> bool:
    """内部エラーを 1 pair 分読む。読み切れたら ``True``。

    ``internal_exception`` key が無いことを「その pair では内部エラーが起きな
    かった」= 観測済み 0 件と読めるのは、その block が attach 経路で作られたと
    分かるときだけ。marker は ``swallowed_exceptions`` **key の存在**で、
    `attach_failure_diagnostics` が全 pair で必ず書く。marker は key の有無だけ
    を見るので、握り潰し台帳の **値** が壊れていても、こちらの観測は有効なまま
    残る（surface 間で壊れを伝播させない）。
    """

    internal = failures.get(INTERNAL_EXCEPTION_KEY, _ABSENT)
    if internal is _ABSENT:
        return SWALLOWED_LEDGER_KEY in failures
    if not isinstance(internal, Mapping):
        # 明示的な `None` もここ。key 欠落と混同しない。
        return False
    # 1 pair は 1 回しか内部エラーで終われないので 1 件で数える。
    _bump_count(by_site, str(internal.get("site") or UNKNOWN_TUPLE_MISSING), 1)
    return True


def summarize_failure_diagnostics(
    records: Iterable[ValidationLogRecord],
) -> FailureDiagnosticsSummary:
    """pair ごとの最終結果 payload から typed failure 診断を集計する。

    1 pair = 1 log = 1 record。log に結果 payload が複数あっても **最後の 1 つ**
    （その pair の最終結果）だけを読むので、同じ pair を複数経路から二重に
    数えない。読めなかった pair は surface ごとに数えるだけで、集計全体を
    落とさない（fail-open）。読めなかった分を 0 件として数えることはしない。
    """

    swallowed = {"observed": 0, "missing": 0, "malformed": 0}
    internal = {"observed": 0, "missing": 0, "malformed": 0}
    observed_total = 0
    by_type: Dict[str, int] = {}
    by_site: Dict[str, int] = {}
    internal_by_site: Dict[str, int] = {}
    for record in records:
        payloads = tuple(record.payloads)
        block_state, failures = (
            _failure_diagnostics_block(payloads[-1]) if payloads
            # 結果 payload が 1 つも無い pair（TIMEOUT / 無 payload）は未観測。
            else (FAILURE_BLOCK_MISSING, {})
        )
        if block_state is FAILURE_BLOCK_MISSING:
            swallowed["missing"] += 1
            internal["missing"] += 1
            continue
        if block_state is FAILURE_BLOCK_BROKEN:
            # key はあるので未観測ではない。両 surface とも読めていない。
            swallowed["malformed"] += 1
            internal["malformed"] += 1
            continue
        readable, row_total = _read_swallowed_surface(failures, by_type, by_site)
        swallowed["observed" if readable else "malformed"] += 1
        observed_total += row_total
        internal_readable = _read_internal_surface(failures, internal_by_site)
        internal["observed" if internal_readable else "malformed"] += 1
    return FailureDiagnosticsSummary(
        swallowed_evidence=FailureEvidence(**swallowed),
        internal_evidence=FailureEvidence(**internal),
        swallowed_observed_total=observed_total,
        swallowed_exceptions_by_type=dict(sorted(by_type.items())),
        swallowed_exceptions_by_site=dict(sorted(by_site.items())),
        internal_exception_by_site=dict(sorted(internal_by_site.items())),
    )


def format_failure_evidence_value(evidence: FailureEvidence) -> str:
    return (
        f"{evidence.state} (observed {evidence.observed}"
        f" / missing {evidence.missing} / malformed {evidence.malformed})"
    )


def format_swallowed_total_value(summary: FailureDiagnosticsSummary) -> str:
    """正確な合計と「観測できた下限」を表示で分ける。"""

    exact = summary.swallowed_exact_total
    if exact is None:
        return f"unknown (observed {summary.swallowed_observed_total})"
    return str(exact)


def format_failure_diagnostics_summary(
    summary: FailureDiagnosticsSummary,
    *,
    indent: str = "",
    compact: bool = False,
    max_items: Optional[int] = None,
) -> str:
    """Issue #125 の 2 節を既存の count block と同じ形で描画する。

    空の節は #128 と同じ語彙で書き分ける: その surface の evidence が complete
    なら ``(none)``（観測して 0 件）、そうでなければ ``(unknown)``。未観測の
    pair がある run を「run 全体で 0 件」と読ませないための区別。
    """

    if max_items is None and compact:
        # compact の既定（`unknown_reason_summary` の count block と同じ 20 件）。
        max_items = 20
    lines = [
        f"{indent}Failure diagnostics:",
        f"{indent}  Swallowed exception evidence: "
        + format_failure_evidence_value(summary.swallowed_evidence),
        f"{indent}  Internal exception evidence : "
        + format_failure_evidence_value(summary.internal_evidence),
        f"{indent}  Swallowed exceptions total  : "
        + format_swallowed_total_value(summary),
    ]
    _append_failure_count_block(
        lines,
        FAILURE_SWALLOWED_BY_TYPE_TITLE,
        summary.swallowed_exceptions_by_type,
        indent,
        empty_label=_evidence_empty_label(summary.swallowed_evidence),
        max_items=max_items,
    )
    _append_failure_count_block(
        lines,
        FAILURE_INTERNAL_BY_SITE_TITLE,
        summary.internal_exception_by_site,
        indent,
        empty_label=_evidence_empty_label(summary.internal_evidence),
        max_items=max_items,
    )
    return "\n".join(lines)


def _evidence_empty_label(evidence: Optional[FailureEvidence]) -> str:
    """空の集計を `(none)`（観測して 0 件）と `(unknown)`（未観測）に分ける。"""

    return "(none)" if evidence is not None and evidence.is_complete else "(unknown)"


def _append_failure_count_block(
    lines: list,
    title: str,
    counts: Mapping[str, int],
    indent: str,
    *,
    empty_label: str,
    max_items: Optional[int] = None,
) -> None:
    """`unknown_reason_summary` の count block と **同じ行の形**で出す。

    `run_health_summary.parse_overall_summary_health` は見出しと `- key: count`
    の 2 つの形だけで section を読むので、ここを別形にすると parser が割れる。
    """

    lines.append(f"{indent}  {title}:")
    if not counts:
        lines.append(f"{indent}    {empty_label}")
        return
    ordered = sorted(counts, key=lambda key: (-int(counts[key]), str(key)))
    shown = ordered[:max_items] if max_items is not None and max_items >= 0 else ordered
    for key in shown:
        lines.append(f"{indent}    - {key}: {counts[key]}")
    if len(shown) < len(ordered):
        hidden = ordered[len(shown):]
        lines.append(
            f"{indent}    - ... {len(hidden)} more entries "
            f"(sum={sum(int(counts[key]) for key in hidden)})"
        )


def format_function_results_summary(
    function_name: str,
    aggregate: ValidationResultAggregate,
    *,
    elapsed_seconds: Optional[float] = None,
    include_unknown_reason_summary: bool = True,
    before_log_paths: Sequence[Any] = (),
    baseline_match_scope: str = BASELINE_MATCH_SCOPE_ALL,
    compact: bool = False,
    max_items: Optional[int] = None,
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
        lines.append(
            format_validation_unknown_summary(
                unknown_summary,
                indent="  ",
                compact=compact,
                max_items=max_items,
            )
        )
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
                    compact=compact,
                    max_items=max_items,
                )
            )
            if not compact:
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
    compact: bool = False,
    max_items: Optional[int] = None,
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
    lines.append(
        format_validation_unknown_summary(
            unknown_summary,
            indent="  ",
            compact=compact,
            max_items=max_items,
        )
    )
    # Issue #125 PR-125-B: typed failure 診断。UNKNOWN の集計（authority 由来の
    # reason）とは別源なので、その block の後ろに独立した節として置く。
    lines.append("")
    lines.append(
        format_failure_diagnostics_summary(
            summarize_failure_diagnostics(summary.overall.records),
            indent="  ",
            compact=compact,
            max_items=max_items,
        )
    )
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
                compact=compact,
                max_items=max_items,
            )
        )
        if not compact:
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
    mode.add_argument("--classify-log", action="store_true")
    mode.add_argument("--error-pairs", action="store_true")
    parser.add_argument("--matrix", choices=("EQ", "NEQ"))
    parser.add_argument(
        "--allow-legacy-log",
        action="store_true",
        help="classify terminal Result lines without requiring receipt-bound JSON",
    )
    parser.add_argument("--function-name", default=None)
    parser.add_argument(
        "--canonical-only",
        action="store_true",
        help="require receipt-bound five-value result JSON; legacy logs become INCOMPLETE",
    )
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
    parser.add_argument(
        "--summary-level",
        choices=("compact", "normal", "verbose"),
        default=os.environ.get("VALIDATION_SUMMARY_LEVEL", "normal"),
        help="summary verbosity; compact suppresses large tuple sections",
    )
    parser.add_argument(
        "--summary-max-items",
        type=int,
        default=_env_int("VALIDATION_SUMMARY_MAX_ITEMS"),
        help="maximum entries per count block; compact defaults to 20",
    )
    parser.add_argument(
        "--health-summary-json",
        default=os.environ.get("VALIDATION_HEALTH_SUMMARY_JSON"),
        help="optional path for a compact machine-readable run health summary",
    )
    parser.add_argument(
        "--health-summary-text",
        default=os.environ.get("VALIDATION_HEALTH_SUMMARY_TEXT"),
        help="optional path for a compact human-readable run health summary",
    )
    parser.add_argument(
        "--log-list0",
        action="append",
        default=[],
        metavar="PATH",
        help=(
            "read additional log paths from a NUL-delimited file; may be repeated "
            "to avoid operating-system command-line length limits"
        ),
    )
    parser.add_argument("logs", nargs="*")
    args = parser.parse_args(argv)
    logs = list(args.logs)
    for list_path_text in args.log_list0:
        list_path = Path(list_path_text)
        try:
            raw_paths = list_path.read_bytes().split(b"\0")
        except OSError as exc:
            parser.error(f"cannot read --log-list0 {list_path}: {exc}")
        logs.extend(os.fsdecode(raw_path) for raw_path in raw_paths if raw_path)
    compact = args.summary_level == "compact"

    if args.classify_log:
        if len(logs) != 1:
            parser.error("--classify-log requires exactly one log")
        print(read_validation_log_record(
            logs[0], canonical_only=not args.allow_legacy_log
        ).status)
        return 0

    if args.error_pairs:
        if len(logs) != 1 or args.matrix is None:
            parser.error("--error-pairs requires one summary path and --matrix")
        for pair in error_pairs_from_summary(Path(logs[0]), matrix=args.matrix):
            print(pair)
        return 0

    if args.function_summary:
        aggregate = aggregate_validation_logs(
            logs, canonical_only=args.canonical_only
        )
        function_name = args.function_name or _single_function_name(aggregate.records) or "(unknown)"
        before_logs = sorted(Path(args.before_dir).glob("*.log")) if args.before_dir else ()
        _require_before_logs(before_logs, args.require_before_dir)
        output = format_function_results_summary(
            function_name,
            aggregate,
            elapsed_seconds=args.elapsed_seconds,
            before_log_paths=before_logs,
            baseline_match_scope=args.baseline_match_scope,
            compact=compact,
            max_items=args.summary_max_items,
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

    overall = aggregate_validation_logs_by_function(
        logs, canonical_only=args.canonical_only
    )
    assert_aggregation_invariant(overall)
    before_logs = sorted(Path(args.before_dir).glob("*/*.log")) if args.before_dir else ()
    _require_before_logs(before_logs, args.require_before_dir)
    output = format_overall_results_summary(
        overall,
        function_wall_times=_parse_function_wall_times(args.function_wall_time or ()),
        before_log_paths=before_logs,
        baseline_match_scope=args.baseline_match_scope,
        compact=compact,
        max_items=args.summary_max_items,
    )
    print(output)
    if args.health_summary_json or args.health_summary_text:
        before_records = aggregate_validation_logs(
            before_logs, canonical_only=args.canonical_only
        ).records if before_logs else ()
        health = build_run_health_summary(
            overall,
            before_records=before_records,
            baseline_match_scope=args.baseline_match_scope,
        )
        if args.health_summary_json:
            _write_json_file(Path(args.health_summary_json), health)
        if args.health_summary_text:
            _write_text_file(Path(args.health_summary_text), format_run_health_summary(health))
    _require_baseline_match(
        before_logs,
        overall.overall.records,
        args.require_baseline_match,
        args.baseline_match_scope,
        args.baseline_match_level,
    )
    return 0


def build_run_health_summary(
    summary: OverallValidationSummary,
    *,
    before_records: Sequence[ValidationLogRecord] = (),
    baseline_match_scope: str = BASELINE_MATCH_SCOPE_ALL,
) -> Dict[str, Any]:
    payloads = _payloads_from_records(summary.overall.records)
    unknown_summary = summarize_validation_unknowns(payloads)
    metadata_counts = {
        "error_kind_counts": {},
        "child_returncode_counts": {},
        "supervisor_status_counts": {},
    }
    for record in summary.overall.records:
        metadata = record.pair_status_metadata
        if metadata is None:
            continue
        values = {
            "error_kind_counts": (
                "<none>" if metadata["error_kind"] is None
                else str(metadata["error_kind"])
            ),
            "child_returncode_counts": (
                "null" if metadata["child_returncode"] is None
                else str(metadata["child_returncode"])
            ),
            "supervisor_status_counts": str(metadata["supervisor_status"]),
        }
        for field, value in values.items():
            counts = metadata_counts[field]
            counts[value] = counts.get(value, 0) + 1
    health: Dict[str, Any] = {
        "total_results": summary.overall.total_pairs,
        "final_result_counts": {status: summary.overall.count(status) for status in STATUS_ORDER},
        "unknown_results": unknown_summary.unknown_results,
        "unknown_units": unknown_summary.unknown_units,
        "unknown_by_reason": dict(unknown_summary.unknown_by_reason),
        "proof_backlog_by_reason": dict(unknown_summary.proof_backlog_by_reason),
        "proof_backlog_by_proof_kind": dict(unknown_summary.proof_backlog_by_proof_kind),
        "operational_unknown_by_reason": dict(unknown_summary.operational_unknown_by_reason),
        # Issue #125 PR-125-B: 診断専用の次元。canonical unknown reason の集計
        # 契約とは独立で、decision authority へは接続しない。
        **summarize_failure_diagnostics(summary.overall.records).to_dict(),
        **metadata_counts,
        "functions": {
            function_name: {
                "total": aggregate.total_pairs,
                STATUS_EQ: aggregate.count(STATUS_EQ),
                STATUS_NOT_EQ: aggregate.count(STATUS_NOT_EQ),
                STATUS_ERROR: aggregate.count(STATUS_ERROR),
                STATUS_UNKNOWN: aggregate.count(STATUS_UNKNOWN),
                STATUS_TIMEOUT: aggregate.count(STATUS_TIMEOUT),
                STATUS_INCOMPLETE: aggregate.count(STATUS_INCOMPLETE),
            }
            for function_name, aggregate in summary.function_summaries.items()
        },
    }
    if before_records:
        scoped_before = _apply_baseline_match_scope(
            before_records,
            summary.overall.records,
            baseline_match_scope,
        )
        comparison = compare_validation_baseline_records(scoped_before, summary.overall.records)
        health["baseline_comparison"] = {
            "before_total_results": comparison.before_total_results,
            "after_total_results": comparison.after_total_results,
            "final_result_counts_delta": dict(comparison.final_result_counts_delta),
            "unknown_final_results_delta": comparison.unknown_final_results_delta,
            "timeout_final_results_delta": comparison.timeout_final_results_delta,
            "missing_pair_identity_count": len(comparison.missing_pair_identities),
            "added_pair_identity_count": len(comparison.added_pair_identities),
        }
    return health


def format_run_health_summary(health: Mapping[str, Any]) -> str:
    counts = health.get("final_result_counts") if isinstance(health, Mapping) else {}
    if not isinstance(counts, Mapping):
        counts = {}
    lines = [
        "Run health summary:",
        f"  total_results: {health.get('total_results', 0)}",
        (
            "  final_results: "
            f"EQ={counts.get(STATUS_EQ, 0)} "
            f"NOT_EQ={counts.get(STATUS_NOT_EQ, 0)} "
            f"UNKNOWN={counts.get(STATUS_UNKNOWN, 0)} "
            f"TIMEOUT={counts.get(STATUS_TIMEOUT, 0)} "
            f"ERROR={counts.get(STATUS_ERROR, 0)} "
            f"INCOMPLETE={counts.get(STATUS_INCOMPLETE, 0)}"
        ),
        f"  unknown_units: {health.get('unknown_units', 0)}",
    ]
    baseline = health.get("baseline_comparison")
    if isinstance(baseline, Mapping):
        lines.extend(
            [
                "  baseline_delta:",
                f"    UNKNOWN final results: {_format_delta(int(baseline.get('unknown_final_results_delta', 0)))}",
                f"    TIMEOUT final results: {_format_delta(int(baseline.get('timeout_final_results_delta', 0)))}",
                f"    missing pairs: {baseline.get('missing_pair_identity_count', 0)}",
                f"    added pairs: {baseline.get('added_pair_identity_count', 0)}",
            ]
        )
    # Issue #128: 証拠が無い section は `(unknown)`。実際に 0 件の `(none)` と
    # 潰さない（`run_health_summary.parse_overall_summary_health` が往復させる）。
    evidence_missing = health.get("evidence_missing_sections")
    evidence_missing = set(evidence_missing) if isinstance(evidence_missing, (list, tuple, set)) else set()
    for title in (
        "unknown_by_reason",
        "proof_backlog_by_reason",
        "operational_unknown_by_reason",
    ):
        values = health.get(title)
        lines.append(f"  {title}:")
        if not isinstance(values, Mapping) or not values:
            lines.append("    (unknown)" if title in evidence_missing else "    (none)")
            continue
        for name, count in sorted(values.items(), key=lambda item: (-int(item[1]), str(item[0])))[:20]:
            lines.append(f"    - {name}: {count}")
    # Issue #125 PR-125-B: typed failure 診断の 2 節。証拠が 1 件も無い run は
    # `(unknown)`、読めた上で 0 件なら `(none)`（#128 と同じ語彙）。
    lines.extend(format_failure_health_lines(health))
    benchmark = health.get(BENCHMARK_VALIDATION_KEY)
    if isinstance(benchmark, Mapping):
        lines.extend(format_benchmark_validation_lines(benchmark))
    # Issue #124 PR-124-C: TIMEOUT の診断（`timeout_hotspot_summary` が merge する）。
    # key が無い run（このツールを流していない / PR-124-C 以前）では 1 行も出さない。
    # 「0 件」と書くと、観測していないことを観測して 0 だったことにしてしまう。
    timeout_diagnostics = health.get(TIMEOUT_DIAGNOSTICS_KEY)
    if isinstance(timeout_diagnostics, Mapping):
        lines.extend(format_timeout_health_lines(timeout_diagnostics))
    return "\n".join(lines)


def failure_evidence_from_health(
    health: Mapping[str, Any], surface: str,
) -> Optional[FailureEvidence]:
    """health mapping から 1 surface の evidence を復元する。

    key が無い（PR-125-B 以前に作った JSON / summary）場合は ``None``。
    これを「観測して 0 件」に読み替えてはいけない。
    """

    evidence = health.get(FAILURE_EVIDENCE_KEY)
    if not isinstance(evidence, Mapping):
        return None
    row = evidence.get(surface)
    if not isinstance(row, Mapping):
        return None
    counts = [row.get(name, _ABSENT) for name in ("observed", "missing", "malformed")]
    # 3 つとも揃っていなければ復元しない。欠けた次元を 0 で埋めると、
    # 未観測の run が complete に見えてしまう。
    if not all(_is_count(value) for value in counts):
        return None
    restored = FailureEvidence(*counts)
    declared_state = row.get("state", _ABSENT)
    if declared_state is not _ABSENT and declared_state != restored.state:
        # 書かれている state と件数が矛盾する health は信用しない（fail-closed）。
        return None
    # 3 次元は run の pair 全部を排他に分類したもの。`total_results` が分かる
    # health では合計が一致していなければならない。一致しない evidence からは
    # complete も exact total も導けないので信用しない。`total_results` を
    # 持たない legacy health では推測しない（勝手に 0 を仮定しない）。
    total_results = health.get("total_results", _ABSENT)
    if total_results is not _ABSENT:
        if not _is_count(total_results):
            return None
        if restored.observed + restored.missing + restored.malformed != total_results:
            return None
    return restored


def format_failure_health_lines(health: Mapping[str, Any]) -> List[str]:
    """Issue #125 の evidence と 2 節を health summary にも出す。

    空の節の書き分けは #128 と同じ語彙。**観測記録そのものが無い** health
    （PR-125-B 以前に作った JSON / summary）は「0 件」ではなく `(unknown)`。
    合計も、evidence が complete でなければ exact 0 を名乗らない。
    """

    # どの集計がどの surface の evidence に従うか。
    surfaces = {
        FAILURE_SWALLOWED_BY_TYPE_KEY: FAILURE_SWALLOWED_SURFACE,
        FAILURE_INTERNAL_BY_SITE_KEY: FAILURE_INTERNAL_SURFACE,
    }
    evidences = {
        surface: failure_evidence_from_health(health, surface)
        for surface in (FAILURE_SWALLOWED_SURFACE, FAILURE_INTERNAL_SURFACE)
    }
    lines: List[str] = [f"  {FAILURE_EVIDENCE_KEY}:"]
    for surface in (FAILURE_SWALLOWED_SURFACE, FAILURE_INTERNAL_SURFACE):
        evidence = evidences[surface]
        lines.append(
            f"    - {surface}: "
            + (EVIDENCE_UNKNOWN if evidence is None
               else format_failure_evidence_value(evidence))
        )
    exact = health.get(FAILURE_SWALLOWED_TOTAL_KEY)
    observed_total = health.get(FAILURE_SWALLOWED_OBSERVED_TOTAL_KEY)
    swallowed_complete = (
        evidences[FAILURE_SWALLOWED_SURFACE] is not None
        and evidences[FAILURE_SWALLOWED_SURFACE].is_complete
    )
    if swallowed_complete and _is_count(exact):
        lines.append(f"  {FAILURE_SWALLOWED_TOTAL_KEY}: {exact}")
    elif _is_count(observed_total):
        lines.append(
            f"  {FAILURE_SWALLOWED_TOTAL_KEY}: "
            f"{EVIDENCE_UNKNOWN} (observed {observed_total})"
        )
    else:
        lines.append(f"  {FAILURE_SWALLOWED_TOTAL_KEY}: {EVIDENCE_UNKNOWN}")
    # `overall_summary.txt` から読み戻した health は `(unknown)` marker を
    # `evidence_missing_sections` に持つので、そちらも尊重して往復させる。
    marked = health.get("evidence_missing_sections")
    marked = set(marked) if isinstance(marked, (list, tuple, set)) else set()
    for key in (FAILURE_SWALLOWED_BY_TYPE_KEY, FAILURE_INTERNAL_BY_SITE_KEY):
        values = health.get(key)
        lines.append(f"  {key}:")
        if not isinstance(values, Mapping) or not values:
            empty_label = _evidence_empty_label(evidences[surfaces[key]])
            lines.append(f"    {'(unknown)' if key in marked else empty_label}")
            continue
        for name, count in sorted(values.items(), key=lambda item: (-int(item[1]), str(item[0])))[:20]:
            lines.append(f"    - {name}: {count}")
    return lines


# Issue #124 PR-124-C: TIMEOUT 診断（``reporting.timeout_hotspot_summary``）が
# merge する節。gate と同じく、runner 経路と offline 再集計で同じ描画を使う。
TIMEOUT_DIAGNOSTICS_KEY = "timeout_diagnostics"

#: text に出す counting 次元と、その見出し。`timeout_kind` と `timeout_hotspots`
#: は Issue #124 の AC が名指ししている 2 節。
TIMEOUT_HEALTH_SECTIONS = (
    "timeout_kind",
    "handler_registered",
    "signal_sent",
    "signal_start_state",
    "dump_observed",
    "sent_but_unobserved",
    "unavailable_reason",
    "artifact_status",
    "last_completed_stage",
    "in_progress_stage",
    "in_progress_stage_basis",
    "longest_completed_stage",
    "timeout_hotspots",
)


def timeout_diagnostics_from_health(
    health: Mapping[str, Any],
) -> Optional[Mapping[str, Any]]:
    """health から TIMEOUT 診断の節を取り出す。無ければ `None`。

    `None` は「この run では集計していない」であって「TIMEOUT が 0 件」ではない。
    0 件の run は `pairs: 0` を持つ mapping を返す。
    """

    section = health.get(TIMEOUT_DIAGNOSTICS_KEY)
    if not isinstance(section, Mapping):
        return None
    return section


def format_timeout_health_lines(section: Mapping[str, Any]) -> List[str]:
    """TIMEOUT 診断の節。件数はすべて TIMEOUT pair 数と総和が一致する。

    値が観測できなかった pair は ``(unknown)`` bucket に入っているので、
    ここで 0 件へ潰さない。section 自体が無い health では呼ばれない。
    """

    pairs = section.get("pairs")
    total = section.get("total_pairs")
    header = f"  timeout_diagnostics: pairs={pairs if _is_count(pairs) else EVIDENCE_UNKNOWN}"
    if _is_count(total):
        header += f" / {total}"
    lines: List[str] = [header]
    evidence = section.get("evidence")
    if isinstance(evidence, Mapping):
        lines.append(
            "  timeout_diagnostic_evidence: "
            + " ".join(
                f"{name}={evidence.get(name, 0)}"
                for name in sorted(evidence)
            )
        )
    for title in TIMEOUT_HEALTH_SECTIONS:
        values = section.get(title)
        lines.append(f"  {title}:")
        if not isinstance(values, Mapping) or not values:
            # 集計自体はあるが次元が空 = TIMEOUT pair が 0 件。
            lines.append("    (none)")
            continue
        for name, count in sorted(
            values.items(), key=lambda item: (-int(item[1]), str(item[0]))
        )[:20]:
            lines.append(f"    - {name}: {count}")
    note = section.get("candidate_frames_note")
    if isinstance(note, str) and note:
        lines.append(f"  timeout_candidate_frames_note: {note}")
    return lines


# Issue #104: the runner benchmark gate (``reporting.benchmark_validation_gate``)
# merges its section into the health summary under this key; rendering lives
# here so the runner path and the offline ``run_health_summary`` path agree.
BENCHMARK_VALIDATION_KEY = "benchmark_validation"


def format_benchmark_validation_lines(section: Mapping[str, Any]) -> List[str]:
    def _counts(name: str) -> Mapping[str, Any]:
        values = section.get(name)
        return values if isinstance(values, Mapping) else {}

    hard = _counts("hard_violations")
    lines = [
        "  soundness_violations: "
        f"eq_not_eq={hard.get('eq_not_eq', 0)} "
        f"neq_equivalent={hard.get('neq_confirmed_not_eq_equivalent', 0)} "
        f"neq_not_eq_on_confirmed_eq={hard.get('neq_confirmed_eq_not_eq', 0)} "
        f"neq_equivalent_unmapped={hard.get('neq_equivalent_unmapped', 0)}",
    ]
    for group in ("suspicious", "benign"):
        for kind, count in sorted(_counts(group).items()):
            lines.append(f"  {kind}: {count}")
    lines.append(
        f"  benchmark_gate: {section.get('gate', 'EMPTY')} (pairs={section.get('pairs', 0)})"
    )
    # Issue #20: the assumption-dependent column, printed only when the run
    # produced one so existing summaries are byte-identical without it.
    conditional = section.get("conditional")
    if isinstance(conditional, Mapping) and int(conditional.get("pairs", 0) or 0):
        conditional_hard = conditional.get("hard_violations")
        conditional_hard = conditional_hard if isinstance(conditional_hard, Mapping) else {}
        lines.append(
            "  conditional_soundness_violations: "
            f"eq_not_eq={conditional_hard.get('eq_not_eq', 0)} "
            f"neq_equivalent={conditional_hard.get('neq_confirmed_not_eq_equivalent', 0)} "
            f"neq_not_eq_on_confirmed_eq={conditional_hard.get('neq_confirmed_eq_not_eq', 0)} "
            f"neq_equivalent_unmapped={conditional_hard.get('neq_equivalent_unmapped', 0)}"
        )
        lines.append(f"  conditional_pairs: {conditional.get('pairs', 0)}")
    return lines


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


def _env_int(name: str) -> Optional[int]:
    raw = os.environ.get(name)
    if raw is None or raw == "":
        return None
    try:
        return int(raw)
    except ValueError:
        raise SystemExit(f"{name} must be an integer, got {raw!r}") from None


def _write_json_file(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def _write_text_file(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text.rstrip() + "\n")


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
    lines = (
        f"{indent}Equivalent     : {aggregate.count(STATUS_EQ)}",
        f"{indent}Not equivalent : {aggregate.count(STATUS_NOT_EQ)}",
        f"{indent}Error          : {aggregate.count(STATUS_ERROR)}",
        f"{indent}Unknown        : {aggregate.count(STATUS_UNKNOWN)}",
        f"{indent}Timeout        : {aggregate.count(STATUS_TIMEOUT)}",
        f"{indent}Incomplete     : {aggregate.count(STATUS_INCOMPLETE)}",
    )
    return lines + _format_conditional_count_lines(indent, aggregate)


def _format_conditional_count_lines(
    indent: str, aggregate: ValidationResultAggregate,
) -> Tuple[str, ...]:
    """Render the assumption-dependent column, and only when it has rows.

    A run without a conditional lane prints exactly what it printed before, so
    the unconditional summary of an existing run cannot move.
    """
    if not aggregate.conditional_counts:
        return ()
    body = " ".join(
        f"{status}={aggregate.conditional_count(status)}"
        for status in sorted(aggregate.conditional_counts)
    )
    return (
        f"{indent}Conditional (assumption-dependent), reported separately: {body}",
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
