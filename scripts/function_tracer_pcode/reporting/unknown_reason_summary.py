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

from scripts.function_tracer_pcode.checker.unknown_reason import (
    UnknownReasonRecord,
    coerce_unknown_reason_records,
    make_unknown_reason,
)
# Issue #128 PR-128-A: 集計の次元・単位選択・backlog 判定は checker 側の
# `cause_aggregate` が正本。`unknown_cause_aggregate` を作る producer と同じ
# 関数を使うので、aggregate 経路と debug_trace 経路の数が構造的に一致する。
from scripts.function_tracer_pcode.checker.cause_aggregate import (
    FINAL_UNKNOWN_TRANSITIONS,
    GLOBAL_REASON_TUPLE_WIDTH as _GLOBAL_REASON_TUPLE_WIDTH,
    aggregate_is_usable,
    build_reason_view,
    completion_counts,
    multiset_from_rows,
    transition_counts,
)
from scripts.function_tracer_pcode.proof.unknown_reason import (
    UNKNOWN_TUPLE_MISSING,
    UnknownCountKind,
    UnknownReasonId,
)
from scripts.function_tracer_pcode.reporting.root_blocker_summary import (
    compare_root_blocker_summaries,
    extract_reason_occurrences,
    summarize_root_blockers,
)


# 集計は 2 系統あり、源も契約も別。混ぜて加算しない。
#
# (1) final reason authority -- 「この結果の最終 UNKNOWN reason は何だったか」。
#     `decision_receipt` があれば canonical `unknown_reasons` が正本。
#     Issue #128 の A（意図的な語彙・件数変更）はこの系統にだけ現れる。
SOURCE_CANONICAL = "canonical"
SOURCE_LEGACY_TRACE = "legacy_trace"
SOURCE_AGGREGATE_LEGACY = "aggregate_legacy"
SOURCE_PAYLOAD = "payload"
SOURCE_SYNTHESIZED = "synthesized"
# (2) diagnostic reporting source -- 「原因分析の材料」。`debug_trace` が持っていた
#     legacy record 由来の集計で、aggregate はそれを保つためにある（B）。
#     canonical 化でこちらの件数を 0 にしてはいけない。
DIAGNOSTIC_SOURCE_AGGREGATE = "unknown_cause_aggregate"
DIAGNOSTIC_SOURCE_TRACE = "debug_trace"
# 診断源がどちらも無い結果。payload の record から作れる値は出すが、それが
# 「trace があったときの legacy 集計」と同じである保証は無いので、観測できた
# 結果としては数えない（run 全体が partial になる）。
DIAGNOSTIC_SOURCE_PAYLOAD_FALLBACK = "payload_fallback"
# 最終 UNKNOWN/TIMEOUT attempt の 3 状態。`EMPTY`（観測して 0 件）を `ABSENT`
# （最終 attempt が無い）と同じに扱うと、trace を省いた途端に最終 reason が
# payload の record へすり替わる。
LEGACY_FINAL_ATTEMPT_RECORDS = "observed_records"
LEGACY_FINAL_ATTEMPT_EMPTY = "observed_empty"
LEGACY_FINAL_ATTEMPT_ABSENT = "absent"
# completion / causal transition の集計単位。block ごとに観測可否が別。
CAUSAL_BLOCKS = ("proof_completions", "reason_completions", "causal_transitions")

# final reason authority が決める集計。証拠が無いことは起こらない
# （最後は「record を持たない結果」として 1 件合成する）。
FINAL_REASON_SURFACES = (
    "unknown_by_reason",
    "unknown_by_reason_detail",
    "unknown_by_decision_effect",
    "unknown_by_reason_scope",
)
# diagnostic source が決める集計。1 結果でも源が無ければ
# 「0 件（none）」ではなく「観測できなかった（unknown）」になる。
DIAGNOSTIC_SURFACES = (
    "validation_unknown_unit_multiset",
    "reason_record_multiset",
    "proof_action_multiset",
    "proof_backlog_by_reason",
    "proof_backlog_by_proof_kind",
    "proof_backlog_by_recovery_action",
    "proof_backlog_by_action_status",
    "operational_unknown_by_reason",
    "operational_unknown_by_class",
)
RESULT_JSON_BEGIN = "=== EQUIVALENCE_RESULT_JSON_BEGIN ==="
RESULT_JSON_END = "=== EQUIVALENCE_RESULT_JSON_END ==="
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
    unknown_by_reason_detail: Dict[str, int] = field(default_factory=dict)
    diagnostics_stats: Dict[str, Any] = field(default_factory=dict)
    # Issue #128: 集計の 2 系統それぞれの出所と、診断源の観測状況。
    # `evidence_missing` に載った集計は、空でも「0 件」ではなく「観測できなかった」。
    # `diagnostic_evidence` は一部だけ欠測した run（partial）を見分けるために持つ。
    final_reason_sources: Tuple[str, ...] = ()
    diagnostic_sources: Tuple[str, ...] = ()
    diagnostic_evidence: Dict[str, int] = field(default_factory=dict)
    # completion / causal transition の集計。診断源から作るので、`debug_trace` を
    # 省いても aggregate 側から同じ値が出る（oracle の比較対象）。
    causal_evidence: Dict[str, Any] = field(default_factory=dict)
    # block ごとの観測件数。`causal_evidence[name] is None` は「観測できなかった」で、
    # `{"total": 0, ...}` は「観測して 0 件」。両者を潰さないための対。
    causal_evidence_counts: Dict[str, Dict[str, int]] = field(default_factory=dict)
    evidence_missing: Tuple[str, ...] = ()

    def to_dict(self) -> Dict[str, Any]:
        return {
            "total_results": self.total_results,
            "unknown_results": self.unknown_results,
            "unknown_units": self.unknown_units,
            "final_result_counts": dict(self.final_result_counts),
            "unknown_by_reason_detail": dict(self.unknown_by_reason_detail),
            "diagnostics_stats": dict(self.diagnostics_stats),
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
            "final_reason_sources": list(self.final_reason_sources),
            "diagnostic_sources": list(self.diagnostic_sources),
            "diagnostic_evidence": dict(self.diagnostic_evidence),
            "causal_evidence": dict(self.causal_evidence),
            "causal_evidence_counts": dict(self.causal_evidence_counts),
            "evidence_missing": list(self.evidence_missing),
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
    merged = _empty_merge_target()
    final_sources: set = set()
    diagnostic_sources: set = set()
    diagnostic_observed = 0
    diagnostic_missing = 0
    causal_evidence: Dict[str, Any] = {}
    causal_evidence_counts: Dict[str, Dict[str, int]] = {}
    diagnostics_collector = _DiagnosticsCollector()

    for payload in selected_payloads:
        total_results += 1
        _inc(final_result_counts, _payload_final_result(payload))
        diagnostics_collector.add(payload)
        if not _payload_is_unknown(payload):
            continue
        unknown_results += 1
        # (1) 最終 reason は authority から、(2) 診断は診断源から。別々に取る。
        final_view, final_source = _final_reason_view(payload)
        final_sources.add(final_source)
        unknown_units += int(final_view.get("unit_count") or 0)
        _merge_final_reason_view(merged, final_view)

        diagnostic_view, diagnostic_source = _diagnostic_reason_view(payload)
        diagnostic_sources.add(diagnostic_source)
        if diagnostic_source == DIAGNOSTIC_SOURCE_PAYLOAD_FALLBACK:
            diagnostic_missing += 1
        else:
            diagnostic_observed += 1
        _merge_diagnostic_view(merged, diagnostic_view)
        _merge_causal_evidence(
            causal_evidence, causal_evidence_counts, _diagnostic_causal_evidence(payload)
        )

    # 1 結果でも診断源が無ければ、診断集計は「完全に観測できた値」ではない。
    # 全欠測でも一部欠測でも `unknown` 扱いにし、静かに確定値へ潰さない。
    evidence_missing: Tuple[str, ...] = DIAGNOSTIC_SURFACES if diagnostic_missing else ()

    return UnknownValidationSummary(
        total_results=total_results,
        unknown_results=unknown_results,
        unknown_units=unknown_units,
        final_result_counts=final_result_counts,
        validation_unknown_unit_multiset=merged["validation_unknown_unit_multiset"],
        reason_record_multiset=merged["reason_record_multiset"],
        proof_action_multiset=merged["proof_action_multiset"],
        unknown_by_reason=merged["by_reason"],
        unknown_by_decision_effect=merged["by_decision_effect"],
        unknown_by_reason_scope=merged["by_reason_scope"],
        proof_backlog_by_reason=merged["backlog"]["by_reason"],
        proof_backlog_by_proof_kind=merged["backlog"]["by_proof_kind"],
        proof_backlog_by_recovery_action=merged["backlog"]["by_recovery_action"],
        proof_backlog_by_action_status=merged["backlog"]["by_action_status"],
        operational_unknown_by_reason=merged["operational"]["by_reason"],
        operational_unknown_by_class=merged["operational"]["by_class"],
        root_blocker_summary=summarize_root_blockers(selected_payloads).to_dict(),
        unknown_by_reason_detail=merged["by_reason_detail"],
        diagnostics_stats=diagnostics_collector.snapshot(),
        final_reason_sources=tuple(sorted(final_sources)),
        diagnostic_sources=tuple(sorted(diagnostic_sources)),
        diagnostic_evidence={
            "observed": diagnostic_observed,
            "missing": diagnostic_missing,
        },
        causal_evidence={
            # 1 件も観測できなかった block は `None`（= unknown）。空 dict にしない。
            name: causal_evidence.get(name)
            if causal_evidence_counts.get(name, {}).get("observed")
            else None
            for name in CAUSAL_BLOCKS
        },
        causal_evidence_counts=causal_evidence_counts,
        evidence_missing=evidence_missing,
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
    # Issue #128: 最終 reason の authority と、診断集計の源は別。どちらから
    # 読んだかと、診断源が何件観測できたかを出力に残す（partial を隠さない）。
    evidence = summary.diagnostic_evidence or {}
    lines.append(
        f"{indent}  Final reason sources: "
        + (", ".join(summary.final_reason_sources) or "(none)")
    )
    lines.append(
        f"{indent}  Diagnostic sources  : "
        + (", ".join(summary.diagnostic_sources) or "(none)")
        + f" (observed {int(evidence.get('observed', 0))}"
        + f" / missing {int(evidence.get('missing', 0))})"
    )
    # completion / causal transition は block ごとに観測可否が違う。
    # 「観測して 0 件」と「観測できなかった」を text でも取り違えないよう並べる。
    lines.append(
        f"{indent}  Causal evidence     : "
        + "; ".join(
            "{name} observed {observed} / missing {missing}".format(
                name=name,
                observed=int((summary.causal_evidence_counts.get(name) or {}).get("observed", 0)),
                missing=int((summary.causal_evidence_counts.get(name) or {}).get("missing", 0)),
            )
            for name in CAUSAL_BLOCKS
        )
    )
    missing = frozenset(summary.evidence_missing)

    def _empty(surface: str) -> str:
        # 空の集計が「0 件（none）」なのか「観測できなかった（unknown）」なのか。
        return "(unknown)" if surface in missing else "(none)"

    max_items = _summary_max_items(compact=compact, max_items=max_items)
    _append_count_block(lines, "Final results", summary.final_result_counts, indent, max_items=max_items)
    _append_count_block(
        lines,
        "Validation UNKNOWN unit tuples",
        summary.validation_unknown_unit_multiset,
        indent,
        empty_label=_empty("validation_unknown_unit_multiset"),
        max_items=max_items,
    )
    if not compact:
        _append_count_block(
            lines,
            "Reason record tuples",
            summary.reason_record_multiset,
            indent,
            empty_label=_empty("reason_record_multiset"),
            max_items=max_items,
        )
        _append_count_block(
            lines,
            "Proof action tuples",
            summary.proof_action_multiset,
            indent,
            empty_label=_empty("proof_action_multiset"),
            max_items=max_items,
        )
    _append_count_block(lines, "UNKNOWN by reason", summary.unknown_by_reason, indent, empty_label=_empty("unknown_by_reason"), max_items=max_items)
    _append_count_block(
        lines,
        "UNKNOWN by reason detail",
        summary.unknown_by_reason_detail,
        indent,
        empty_label=_empty("unknown_by_reason_detail"),
        max_items=max_items,
    )
    _append_diagnostics_block(lines, summary.diagnostics_stats, indent)
    _append_count_block(
        lines,
        "UNKNOWN by decision_effect",
        summary.unknown_by_decision_effect,
        indent,
        empty_label=_empty("unknown_by_decision_effect"),
        max_items=max_items,
    )
    _append_count_block(
        lines,
        "UNKNOWN by reason_scope",
        summary.unknown_by_reason_scope,
        indent,
        empty_label=_empty("unknown_by_reason_scope"),
        max_items=max_items,
    )
    _append_count_block(lines, "Proof backlog by reason", summary.proof_backlog_by_reason, indent, empty_label=_empty("proof_backlog_by_reason"), max_items=max_items)
    _append_count_block(
        lines,
        "Proof backlog by proof_kind",
        summary.proof_backlog_by_proof_kind,
        indent,
        empty_label=_empty("proof_backlog_by_proof_kind"),
        max_items=max_items,
    )
    _append_count_block(
        lines,
        "Proof backlog by recovery_action",
        summary.proof_backlog_by_recovery_action,
        indent,
        empty_label=_empty("proof_backlog_by_recovery_action"),
        max_items=max_items,
    )
    _append_count_block(
        lines,
        "Proof backlog by action_status",
        summary.proof_backlog_by_action_status,
        indent,
        empty_label=_empty("proof_backlog_by_action_status"),
        max_items=max_items,
    )
    _append_count_block(
        lines,
        "Operational UNKNOWN by reason",
        summary.operational_unknown_by_reason,
        indent,
        empty_label=_empty("operational_unknown_by_reason"),
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
        from scripts.function_tracer_pcode.authority.decision.production_cutover import (
            outcome_from_payload,
        )

        return outcome_from_payload(payload).value in {"UNKNOWN", "TIMEOUT"}
    if payload.get("is_equivalent") is not None:
        return False
    debug_trace = payload.get("debug_trace")
    if isinstance(debug_trace, Mapping) and debug_trace.get("final_result") is not None:
        return False
    return payload.get("error_message") is None


def _payload_final_result(payload: Mapping[str, Any]) -> str:
    if payload.get("decision_receipt") is not None:
        from scripts.function_tracer_pcode.authority.decision.production_cutover import (
            outcome_from_payload,
        )

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
        from scripts.function_tracer_pcode.authority.decision.production_cutover import (
            outcome_from_payload,
        )

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


def _legacy_trace_records(
    payload: Mapping[str, Any],
) -> Optional[Tuple[UnknownReasonRecord, ...]]:
    """最終 UNKNOWN/TIMEOUT attempt の legacy record。

    `None` は「最終 attempt が無い」、空 tuple は「最終 attempt はあるが record を
    持たない」。後者は結果単位の合成 record へ進む従来の挙動なので、両者を
    同じ falsy 値へ潰さない。
    """
    debug_trace = payload.get("debug_trace")
    if not isinstance(debug_trace, Mapping) or debug_trace.get("final_result") is not None:
        return None
    for attempt in reversed(tuple(debug_trace.get("attempts") or ())):
        if not isinstance(attempt, Mapping):
            continue
        if (
            attempt.get("result") is None
            and str(attempt.get("transition_reason")) in FINAL_UNKNOWN_TRANSITIONS
        ):
            return coerce_unknown_reason_records(attempt.get("unknown_reasons") or ())
    return None


def _extract_final_unknown_reasons(payload: Mapping[str, Any]) -> Tuple[UnknownReasonRecord, ...]:
    """最終 UNKNOWN reason の record 集合（正本 = canonical payload）。

    Issue #128: `decision_receipt` を持つ canonical payload では top-level
    `unknown_reasons` が最終 reason の authority で、legacy trace を優先しない。
    receipt を持たない古い log だけが従来どおり最終 attempt の legacy record を
    使う。どちらか一方だけを使い、両方を足し合わせることはしない。
    """
    if payload.get("decision_receipt") is not None:
        return coerce_unknown_reason_records(payload.get("unknown_reasons") or ())
    legacy = _legacy_trace_records(payload)
    if legacy is not None:
        return legacy
    return coerce_unknown_reason_records(payload.get("unknown_reasons") or ())


def _synthesized_reason_view(payload: Mapping[str, Any]) -> Dict[str, Any]:
    """record を 1 件も持たない結果の扱い（従来どおり合成 record 1 件）。"""
    return build_reason_view((
        make_unknown_reason(
            UnknownReasonId.UNKNOWN,
            stage=_payload_stage(payload),
            pair_or_case=_payload_pair_or_case(payload),
            detail="result payload carries no unknown_reasons record",
        ),
    ))


def _legacy_final_attempt_state(
    payload: Mapping[str, Any],
) -> Tuple[str, Optional[Dict[str, Any]], Optional[str]]:
    """最終 UNKNOWN/TIMEOUT attempt の 3 状態を、経路に依らず同じに決める。

    * `LEGACY_FINAL_ATTEMPT_RECORDS` — 観測し、record があった（view を返す）
    * `LEGACY_FINAL_ATTEMPT_EMPTY`   — 観測したが record が 0 件だった
    * `LEGACY_FINAL_ATTEMPT_ABSENT`  — そもそも最終 attempt が無かった

    **`EMPTY` と `ABSENT` は別**。前者は「見た上で 0 件」なので次の源へ進まず
    結果単位の合成 record 1 件になり、後者だけが次の源（payload）へ進む。
    full `debug_trace` からも `unknown_cause_aggregate.legacy_view` からも同じ
    3 状態が出ることが、trace を省いても最終 reason が変わらない条件。
    """
    legacy = _legacy_trace_records(payload)
    if legacy is not None:
        if legacy:
            return LEGACY_FINAL_ATTEMPT_RECORDS, build_reason_view(legacy), SOURCE_LEGACY_TRACE
        return LEGACY_FINAL_ATTEMPT_EMPTY, None, SOURCE_LEGACY_TRACE
    aggregate = payload.get("unknown_cause_aggregate")
    if aggregate_is_usable(aggregate):
        legacy_view = aggregate.get("legacy_view")
        # 最終 attempt の record 集合として作られた view だけが legacy authority の
        # 代用になる。`payload_records` 形は「最終 attempt が無かった」ことの記録
        # なので ABSENT として扱い、payload を読む分岐へ落とす。
        if (
            (aggregate.get("evidence_present") or {}).get("legacy_records")
            and isinstance(legacy_view, Mapping)
            and legacy_view.get("source") == "final_attempt"
        ):
            if int(legacy_view.get("record_count") or 0):
                return (
                    LEGACY_FINAL_ATTEMPT_RECORDS,
                    dict(legacy_view),
                    SOURCE_AGGREGATE_LEGACY,
                )
            return LEGACY_FINAL_ATTEMPT_EMPTY, None, SOURCE_AGGREGATE_LEGACY
    return LEGACY_FINAL_ATTEMPT_ABSENT, None, None


def _final_reason_view(payload: Mapping[str, Any]) -> Tuple[Dict[str, Any], str]:
    """(1) final reason authority: この結果の最終 UNKNOWN reason そのもの。

    優先順:

    1. canonical payload（`decision_receipt` あり）の `unknown_reasons`
    2. 最終 UNKNOWN/TIMEOUT attempt — full `debug_trace` から、無ければ
       `unknown_cause_aggregate.legacy_view` から（`_legacy_final_attempt_state`）。
       **観測したが 0 件**なら合成 1 件で確定し、次の源へは進まない。
    3. 最終 attempt が無かったときだけ payload の `unknown_reasons`
    4. どれも無い -> record を持たない結果として 1 件合成する（従来どおり）

    2 が 3 より前にあるのが要点: trace を省いた log でも payload の
    `unknown_reasons` は残るので、先に payload を読むと legacy 件数が静かに
    canonical 件数へすり替わる。ここが返すのは最終 reason だけで、診断集計は
    `_diagnostic_reason_view` が別に決める。
    """
    if payload.get("decision_receipt") is not None:
        records = coerce_unknown_reason_records(payload.get("unknown_reasons") or ())
        if records:
            return build_reason_view(records), SOURCE_CANONICAL
    else:
        state, view, source = _legacy_final_attempt_state(payload)
        if state == LEGACY_FINAL_ATTEMPT_RECORDS:
            return view, source
        if state == LEGACY_FINAL_ATTEMPT_ABSENT:
            records = coerce_unknown_reason_records(payload.get("unknown_reasons") or ())
            if records:
                return build_reason_view(records), SOURCE_PAYLOAD
        # EMPTY は次の源を見ずにここへ落ちる（trace 経路と同じ答え）。
    return _synthesized_reason_view(payload), SOURCE_SYNTHESIZED


def _diagnostic_reason_view(payload: Mapping[str, Any]) -> Tuple[Dict[str, Any], str]:
    """(2) diagnostic reporting source: 原因分析の材料（multiset / backlog / operational）。

    **aggregate が在ることと、診断の証拠が在ることは別**。usable な aggregate でも
    `legacy_view` が `null`（= producer が trace を観測できていない）なら、その結果の
    診断は観測できていない。値は payload の record から作るが、それは補助値であって
    「観測済み」ではないので `payload_fallback` として返し、run 全体を partial にする。

    順序:

    * usable aggregate で `legacy_view` が在る -> 観測済み（aggregate）
    * usable aggregate だが `legacy_view` が `null` -> 欠測（payload fallback）
    * full `debug_trace` が在る -> 観測済み（従来経路）
    * どちらも無い -> 欠測（payload fallback）
    """
    aggregate = payload.get("unknown_cause_aggregate")
    if aggregate_is_usable(aggregate):
        # block の中身より先に「観測できたか」の証言を見る（他の block と同じ順）。
        observed = (aggregate.get("evidence_present") or {}).get("legacy_records")
        legacy_view = aggregate.get("legacy_view")
        if observed and isinstance(legacy_view, Mapping):
            if int(legacy_view.get("record_count") or 0):
                return dict(legacy_view), DIAGNOSTIC_SOURCE_AGGREGATE
            # record を 1 件も持たない集合。従来経路と同じく合成 1 件にする。
            return _synthesized_reason_view(payload), DIAGNOSTIC_SOURCE_AGGREGATE
        return _payload_fallback_reason_view(payload)
    if isinstance(payload.get("debug_trace"), Mapping):
        legacy = _legacy_trace_records(payload)
        if legacy is None:
            legacy = coerce_unknown_reason_records(payload.get("unknown_reasons") or ())
        view = build_reason_view(legacy) if legacy else _synthesized_reason_view(payload)
        return view, DIAGNOSTIC_SOURCE_TRACE
    return _payload_fallback_reason_view(payload)


def _payload_fallback_reason_view(payload: Mapping[str, Any]) -> Tuple[Dict[str, Any], str]:
    """診断源が無いときの補助値。古い artifact を壊さないが観測済みとは数えない。"""
    records = coerce_unknown_reason_records(payload.get("unknown_reasons") or ())
    view = build_reason_view(records) if records else _synthesized_reason_view(payload)
    return view, DIAGNOSTIC_SOURCE_PAYLOAD_FALLBACK


def _diagnostic_causal_evidence(
    payload: Mapping[str, Any],
) -> Dict[str, Optional[Dict[str, Any]]]:
    """completion / causal transition の集計。block ごとに観測可否を返す。

    `None` は「観測できなかった」で、`{"total": 0, ...}` は「観測して 0 件」。
    aggregate は `evidence_present.completion_events` / `causal_transitions` で
    どちらだったかを証言するので、それを `{}` に潰さない。
    """
    empty: Dict[str, Optional[Dict[str, Any]]] = {name: None for name in CAUSAL_BLOCKS}
    aggregate = payload.get("unknown_cause_aggregate")
    if aggregate_is_usable(aggregate):
        evidence = aggregate.get("evidence_present") or {}
        blocks = dict(empty)
        completions = aggregate.get("completions")
        if evidence.get("completion_events") and isinstance(completions, Mapping):
            for name in ("proof_completions", "reason_completions"):
                value = completions.get(name)
                if isinstance(value, Mapping):
                    blocks[name] = dict(value)
        transitions = aggregate.get("transitions")
        if evidence.get("causal_transitions") and isinstance(transitions, Mapping):
            value = transitions.get("causal_transitions")
            if isinstance(value, Mapping):
                blocks["causal_transitions"] = dict(value)
        return blocks
    if isinstance(payload.get("debug_trace"), Mapping):
        occurrences, trace_transitions, completions, reason_completions = (
            extract_reason_occurrences(payload)
        )
        counted = dict(completion_counts(completions, reason_completions, occurrences))
        counted.update(transition_counts(trace_transitions, occurrences))
        return {name: dict(counted[name]) for name in CAUSAL_BLOCKS}
    return empty


def _merge_causal_evidence(
    target: Dict[str, Any],
    counts: Dict[str, Dict[str, int]],
    blocks: Mapping[str, Optional[Mapping[str, Any]]],
) -> None:
    """block ごとに観測できたものだけ足し、観測できなかった件数を別に数える。"""
    for name in CAUSAL_BLOCKS:
        block = blocks.get(name)
        tally = counts.setdefault(name, {"observed": 0, "missing": 0})
        if block is None:
            tally["missing"] += 1
            continue
        tally["observed"] += 1
        bucket = target.setdefault(name, {})
        for key, value in block.items():
            if isinstance(value, Mapping):
                inner = bucket.setdefault(key, {})
                for inner_key, inner_value in value.items():
                    _inc(inner, inner_key, int(inner_value or 0))
            else:
                _inc(bucket, key, int(value or 0))


def _merge_final_reason_view(target: Dict[str, Any], view: Mapping[str, Any]) -> None:
    """final reason authority の次元だけ足し込む。"""
    for name in ("by_reason", "by_decision_effect", "by_reason_scope", "by_reason_detail"):
        for key, value in (view.get(name) or {}).items():
            _inc(target[name], key, int(value or 0))


def _merge_diagnostic_view(target: Dict[str, Any], view: Mapping[str, Any]) -> None:
    """diagnostic source の次元だけ足し込む（final reason の次元には触れない）。"""
    for name in (
        "validation_unknown_unit_multiset",
        "reason_record_multiset",
        "proof_action_multiset",
    ):
        for key, value in multiset_from_rows(view.get(name)).items():
            _inc(target[name], key, int(value or 0))
    for name in ("by_reason", "by_proof_kind", "by_recovery_action", "by_action_status"):
        for key, value in ((view.get("backlog") or {}).get(name) or {}).items():
            _inc(target["backlog"][name], key, int(value or 0))
    for name in ("by_reason", "by_class"):
        for key, value in ((view.get("operational") or {}).get(name) or {}).items():
            _inc(target["operational"][name], key, int(value or 0))


def _empty_merge_target() -> Dict[str, Any]:
    return {
        "by_reason": {},
        "by_decision_effect": {},
        "by_reason_scope": {},
        "by_reason_detail": {},
        "validation_unknown_unit_multiset": {},
        "reason_record_multiset": {},
        "proof_action_multiset": {},
        "backlog": {
            "by_reason": {},
            "by_proof_kind": {},
            "by_recovery_action": {},
            "by_action_status": {},
        },
        "operational": {"by_reason": {}, "by_class": {}},
    }


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


class _DiagnosticsCollector:
    """Aggregate the non-signed `diagnostics` block across result payloads."""

    def __init__(self) -> None:
        self.count = 0
        self.total_seconds: list = []
        self.analysis_seconds: list = []
        self.solver_seconds: list = []
        self.node_counts: list = []
        self.max_depths: list = []

    def add(self, payload: Mapping[str, Any]) -> None:
        diagnostics = payload.get("diagnostics") if isinstance(payload, Mapping) else None
        if not isinstance(diagnostics, Mapping):
            return
        self.count += 1
        timings = diagnostics.get("timings") or {}
        self._push(self.total_seconds, timings.get("total_seconds"))
        analysis = timings.get("analysis_seconds") or {}
        if analysis:
            self._push(self.analysis_seconds, sum(float(v or 0) for v in analysis.values()))
        self._push(self.solver_seconds, timings.get("solver_seconds"))
        for stats in (diagnostics.get("expressions") or {}).values():
            self._push(self.node_counts, (stats or {}).get("node_count"))
            self._push(self.max_depths, (stats or {}).get("max_depth"))

    @staticmethod
    def _push(bucket: list, value: Any) -> None:
        try:
            if value is not None:
                bucket.append(float(value))
        except (TypeError, ValueError):
            return

    @staticmethod
    def _stats(values: list) -> Dict[str, float]:
        if not values:
            return {}
        return {
            "count": len(values),
            "mean": round(sum(values) / len(values), 6),
            "max": round(max(values), 6),
        }

    def snapshot(self) -> Dict[str, Any]:
        if not self.count:
            return {}
        return {
            "results_with_diagnostics": self.count,
            "total_seconds": self._stats(self.total_seconds),
            "analysis_seconds": self._stats(self.analysis_seconds),
            "solver_seconds": self._stats(self.solver_seconds),
            "expression_node_count": self._stats(self.node_counts),
            "expression_max_depth": self._stats(self.max_depths),
        }


def _append_diagnostics_block(lines: list, stats: Mapping[str, Any], indent: str) -> None:
    lines.append(f"{indent}  Diagnostics (per-result timings / expression size):")
    if not stats:
        lines.append(f"{indent}    (none)")
        return
    lines.append(f"{indent}    results with diagnostics: {stats.get('results_with_diagnostics', 0)}")
    for key in (
        "total_seconds", "analysis_seconds", "solver_seconds",
        "expression_node_count", "expression_max_depth",
    ):
        item = stats.get(key) or {}
        if item:
            lines.append(
                f"{indent}    {key}: mean={item.get('mean')} max={item.get('max')} (n={item.get('count')})"
            )



if __name__ == "__main__":
    raise SystemExit(main())
