# -*- coding: utf-8 -*-
"""Root-cause aggregation for final UNKNOWN/TIMEOUT results.

The aggregator is observational: it never changes an equivalence decision.
Typed cause keys are accepted without semantic rewriting.  Legacy tuple keys
are preserved in full and therefore may over-partition, but never over-merge.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, Iterable, Mapping, Optional, Tuple

from scripts.function_tracer_pcode.checker.unknown_reason import build_unknown_recovery_actions
# Issue #128 PR-128-A: cause identity / causal status の決め方は checker 側の
# `cause_aggregate` が正本。`unknown_cause_aggregate` を作る producer と、
# ここ（consumer）が同じ関数を使うことで、`debug_trace` 経路と aggregate 経路の
# identity が一致する（= 経路が違っても before/after 比較が成立する）。
from scripts.function_tracer_pcode.checker.cause_aggregate import (
    BLOCKING_DECISION_EFFECTS as _BLOCKING_EFFECTS,
    FINAL_UNKNOWN_TRANSITIONS as _FINAL_TRANSITIONS,
    aggregate_is_usable,
    freeze_identity as _freeze,
    identity_tuple as _tuple,
    resolve_cause_identity,
    resolve_occurrence_transitions as _resolve_transitions,
    resolve_pool_refs,
    resolve_required_proofs,
)


ROOT_BLOCKER_SCHEMA_VERSION = 1


@dataclass(frozen=True)
class ComparisonDomainKey:
    left_binary_identity: Tuple[Any, ...]
    right_binary_identity: Tuple[Any, ...]
    architecture_identity: Tuple[Any, ...] = ()
    abi_fingerprint: Tuple[Any, ...] = ()
    calling_convention_fingerprint: Tuple[Any, ...] = ()
    comparison_policy_fingerprint: Tuple[Any, ...] = ()
    schema_version: int = 1

    def to_key(self) -> Tuple[Any, ...]:
        return _freeze(self.__dict__)


@dataclass(frozen=True)
class StableResultRef:
    logical_case_identity: Tuple[Any, ...]
    left_function_identity: Tuple[Any, ...]
    right_function_identity: Tuple[Any, ...]
    comparison_domain: ComparisonDomainKey
    artifact_schema_version: int = 1
    identity_certainty: str = "verified"

    def to_key(self) -> Tuple[Any, ...]:
        return (
            self.artifact_schema_version,
            self.logical_case_identity,
            self.left_function_identity,
            self.right_function_identity,
            self.comparison_domain.to_key(),
            self.identity_certainty,
        )


@dataclass(frozen=True)
class ResultProvenanceRef:
    run_identity: Tuple[Any, ...]
    artifact_identity: Tuple[Any, ...]
    source_path: Optional[str] = None
    observed_at: Optional[str] = None

    def to_key(self) -> Tuple[Any, ...]:
        return _freeze(self.__dict__)


@dataclass(frozen=True)
class StableCasePairRef:
    stable_result_ref: StableResultRef
    strategy_identity: str
    left_case_identity: Tuple[Any, ...]
    right_case_identity: Tuple[Any, ...]

    def to_key(self) -> Tuple[Any, ...]:
        return (
            self.stable_result_ref.to_key(),
            self.strategy_identity,
            self.left_case_identity,
            self.right_case_identity,
        )


@dataclass(frozen=True)
class AggregationSnapshot:
    snapshot_id: str
    selected_result_occurrences: Tuple[Tuple[Any, ...], ...] = ()
    allow_legacy_unverified_identity: bool = False


@dataclass(frozen=True)
class RootBlockerId:
    identity_scope: str
    cause_kind: str
    canonical_cause_key: Tuple[Any, ...]
    schema_version: int = ROOT_BLOCKER_SCHEMA_VERSION

    def to_key(self) -> Tuple[Any, ...]:
        return (
            self.schema_version,
            self.identity_scope,
            self.cause_kind,
            self.canonical_cause_key,
        )


@dataclass(frozen=True)
class RootBlocker:
    blocker_id: RootBlockerId
    legacy_proof_obligation_ids: Tuple[Tuple[Any, ...], ...]
    required_proof_ids: Tuple[Tuple[Any, ...], ...]
    affected_case_pairs: Tuple[Tuple[Any, ...], ...]
    affected_unknown_results: Tuple[Tuple[Any, ...], ...]
    affected_result_occurrences: Tuple[Tuple[Any, ...], ...]
    observed_reason_ids: Tuple[str, ...]
    observed_occurrence_ids: Tuple[Tuple[Any, ...], ...]
    evidence_refs: Tuple[str, ...]
    causal_certainties: Tuple[str, ...]
    proof_requirements_complete: bool = True

    def to_dict(self) -> Dict[str, Any]:
        return {
            "blocker_id": self.blocker_id.to_key(),
            "identity_scope": self.blocker_id.identity_scope,
            "cause_kind": self.blocker_id.cause_kind,
            "legacy_proof_obligation_ids": self.legacy_proof_obligation_ids,
            "required_proof_ids": self.required_proof_ids,
            "affected_case_pairs": self.affected_case_pairs,
            "affected_unknown_results": self.affected_unknown_results,
            "affected_result_occurrences": self.affected_result_occurrences,
            "observed_reason_ids": self.observed_reason_ids,
            "observed_occurrence_ids": self.observed_occurrence_ids,
            "evidence_refs": self.evidence_refs,
            "causal_certainties": self.causal_certainties,
            "proof_requirements_complete": self.proof_requirements_complete,
        }


@dataclass(frozen=True)
class RootBlockerSummary:
    snapshot_id: str
    active_root_blockers: Tuple[RootBlocker, ...] = ()
    observed_candidate_blockers: Tuple[RootBlocker, ...] = ()
    diagnostics: Dict[str, int] = field(default_factory=dict)
    # ``None`` = causal evidence was not observable (distinct from "all zero").
    coverage: Optional[Dict[str, float]] = field(default_factory=dict)
    aggregate_pair_count_hints: Tuple[str, ...] = ()

    @property
    def active_root_blocker_count(self) -> int:
        return len(self.active_root_blockers)

    @property
    def candidate_root_blocker_count(self) -> int:
        return len(self.observed_candidate_blockers)

    @property
    def required_unique_proof_count(self) -> Optional[int]:
        if any(
            not blocker.proof_requirements_complete
            for blocker in self.active_root_blockers
        ):
            return None
        return len(
            {
                proof
                for blocker in self.active_root_blockers
                for proof in blocker.required_proof_ids
            }
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "snapshot_id": self.snapshot_id,
            "active_root_blockers": [item.to_dict() for item in self.active_root_blockers],
            "observed_candidate_blockers": [
                item.to_dict() for item in self.observed_candidate_blockers
            ],
            "active_root_blocker_count": self.active_root_blocker_count,
            "candidate_root_blocker_count": self.candidate_root_blocker_count,
            "required_unique_proof_count": self.required_unique_proof_count,
            "diagnostics": dict(self.diagnostics),
            "coverage": dict(self.coverage) if self.coverage is not None else None,
            "aggregate_pair_count_hints": self.aggregate_pair_count_hints,
        }


@dataclass(frozen=True)
class RootBlockerDiff:
    new_blocker_ids: Tuple[Tuple[Any, ...], ...]
    resolved_blocker_ids: Tuple[Tuple[Any, ...], ...]
    persisting_blocker_ids: Tuple[Tuple[Any, ...], ...]
    new_proof_requirement_ids: Tuple[Tuple[Any, ...], ...]
    resolved_proof_requirement_ids: Tuple[Tuple[Any, ...], ...]
    active_root_blocker_delta: int
    required_unique_proof_delta: Optional[int]
    proof_requirement_comparison_complete: bool

    def to_dict(self) -> Dict[str, Any]:
        return dict(self.__dict__)


def compare_root_blocker_summaries(
    before: RootBlockerSummary,
    after: RootBlockerSummary,
) -> RootBlockerDiff:
    before_ids = {item.blocker_id.to_key() for item in before.active_root_blockers}
    after_ids = {item.blocker_id.to_key() for item in after.active_root_blockers}
    complete = (
        before.required_unique_proof_count is not None
        and after.required_unique_proof_count is not None
    )
    before_proofs = {
        proof for item in before.active_root_blockers for proof in item.required_proof_ids
    }
    after_proofs = {
        proof for item in after.active_root_blockers for proof in item.required_proof_ids
    }
    ordered = lambda values: tuple(sorted(values, key=repr))
    return RootBlockerDiff(
        new_blocker_ids=ordered(after_ids - before_ids),
        resolved_blocker_ids=ordered(before_ids - after_ids),
        persisting_blocker_ids=ordered(before_ids & after_ids),
        new_proof_requirement_ids=ordered(after_proofs - before_proofs) if complete else (),
        resolved_proof_requirement_ids=ordered(before_proofs - after_proofs) if complete else (),
        active_root_blocker_delta=after.active_root_blocker_count - before.active_root_blocker_count,
        required_unique_proof_delta=(
            after.required_unique_proof_count - before.required_unique_proof_count
            if complete
            else None
        ),
        proof_requirement_comparison_complete=complete,
    )


@dataclass
class _BlockerBuilder:
    blocker_id: RootBlockerId
    legacy: set = field(default_factory=set)
    required: set = field(default_factory=set)
    pairs: set = field(default_factory=set)
    results: set = field(default_factory=set)
    result_occurrences: set = field(default_factory=set)
    reasons: set = field(default_factory=set)
    occurrences: set = field(default_factory=set)
    evidence: set = field(default_factory=set)
    certainties: set = field(default_factory=set)
    proof_requirements_complete: bool = True

    def freeze(self) -> RootBlocker:
        ordered = lambda values: tuple(sorted(values, key=repr))
        return RootBlocker(
            self.blocker_id,
            ordered(self.legacy),
            ordered(self.required),
            ordered(self.pairs),
            ordered(self.results),
            ordered(self.result_occurrences),
            ordered(self.reasons),
            ordered(self.occurrences),
            ordered(self.evidence),
            ordered(self.certainties),
            self.proof_requirements_complete,
        )


def summarize_root_blockers(
    result_payloads: Iterable[Mapping[str, Any]],
    *,
    snapshot: Optional[AggregationSnapshot] = None,
) -> RootBlockerSummary:
    """Aggregate blockers for one explicitly selected current snapshot.

    If duplicate stable results occur without an explicit occurrence selection,
    none of those ambiguous results contribute to the active ranking.  They are
    retained in the candidate history and diagnosed.
    """

    payloads = [dict(payload) for payload in result_payloads]
    snapshot = snapshot or AggregationSnapshot("implicit-single-occurrence")
    diagnostics: Dict[str, int] = {}
    hints = []
    entries = []
    by_stable: Dict[Tuple[Any, ...], list] = {}
    selected = set(snapshot.selected_result_occurrences)

    for index, payload in enumerate(payloads):
        provenance = _provenance_ref(payload, index)
        stable = _stable_result_ref(
            payload,
            provenance=provenance,
            allow_legacy_unverified=snapshot.allow_legacy_unverified_identity,
        )
        if stable is None:
            if not payload.get("binary1_content_identity") or not payload.get("binary2_content_identity"):
                _inc(diagnostics, "missing_binary_content_identity")
                _inc(diagnostics, "missing_comparison_domain_identity")
            if not payload.get("function1_identity") or not payload.get("function2_identity"):
                _inc(diagnostics, "missing_function_identity")
            continue
        entry = (payload, stable, provenance)
        entries.append(entry)
        by_stable.setdefault(stable.to_key(), []).append(entry)
        pair_info = payload.get("pairwise_stats")
        if isinstance(pair_info, Mapping):
            hints.append(
                f"unknown {int(pair_info.get('unknown_pairs') or 0)} / "
                f"total {int(pair_info.get('total_pairs') or 0)}"
            )

    active_occurrence_keys = set()
    for stable_key, group in by_stable.items():
        if len(group) == 1:
            active_occurrence_keys.add(group[0][2].to_key())
            continue
        explicitly_selected = [item for item in group if item[2].to_key() in selected]
        if len(explicitly_selected) == 1:
            active_occurrence_keys.add(explicitly_selected[0][2].to_key())
        else:
            _inc(diagnostics, "duplicate_current_result_occurrence")
            _inc(diagnostics, "ambiguous_snapshot_membership")

    candidate: Dict[Tuple[Any, ...], _BlockerBuilder] = {}
    active: Dict[Tuple[Any, ...], _BlockerBuilder] = {}
    total_reasons = typed_reasons = explicit_status = pair_identified = 0
    transition_target_count = proof_completion_count = linked_completion_count = 0
    causal_evidence_present = False

    for payload, stable, provenance in entries:
        final_unknown = _is_final_unknown(payload)
        active_result_occurrence = (
            final_unknown
            and provenance.to_key() in active_occurrence_keys
            and stable.identity_certainty == "verified"
        )
        # Issue #128: 診断の入力は (1) unknown_cause_aggregate -> (2) full
        # debug_trace -> (3) evidence 無し の順。aggregate があるときは trace を
        # 集計に使わない（同じ occurrence を二重計上しないため）。
        aggregate = payload.get("unknown_cause_aggregate")
        if aggregate_is_usable(aggregate) and isinstance(aggregate.get("root_causes"), list):
            stats = aggregate.get("root_cause_stats") or {}
            total_reasons += int(stats.get("total_reasons") or 0)
            typed_reasons += int(stats.get("typed_reasons") or 0)
            explicit_status += int(stats.get("explicit_causal_status") or 0)
            pair_identified += int(stats.get("pair_identified") or 0)
            transition_target_count += int(stats.get("transition_target_count") or 0)
            proof_completion_count += int(stats.get("proof_completion_count") or 0)
            linked_completion_count += int(stats.get("linked_completion_count") or 0)
            for name, value in (stats.get("diagnostics") or {}).items():
                _inc(diagnostics, str(name), int(value or 0))
            evidence = aggregate.get("evidence_present") or {}
            if evidence.get("causal_transitions") or evidence.get("completion_events"):
                causal_evidence_present = True
            identity_pool = aggregate.get("identity_pool") or ()
            for cause in aggregate.get("root_causes") or ():
                if not isinstance(cause, Mapping) or cause.get("canonical_cause_key") is None:
                    continue
                blocker_id = RootBlockerId(
                    str(cause.get("identity_scope") or ""),
                    str(cause.get("cause_kind") or ""),
                    _freeze(cause.get("canonical_cause_key")),
                )
                _add_cause_group(
                    candidate, blocker_id, cause.get("all") or {}, stable, provenance, identity_pool
                )
                active_group = cause.get("active")
                if active_result_occurrence and active_group:
                    _add_cause_group(
                        active, blocker_id, active_group, stable, provenance, identity_pool
                    )
            continue
        if isinstance(payload.get("debug_trace"), Mapping):
            causal_evidence_present = True
        occurrences, transitions, completions, reason_completions = _extract_occurrences(payload)
        transition_target_count += len(
            {
                _freeze(item.get("target_occurrence_id"))
                for item in transitions
                if isinstance(item, Mapping) and item.get("target_occurrence_id")
            }
        )
        proof_completion_ids = {
            _freeze(item.get("completion_id"))
            for item in completions
            if isinstance(item, Mapping) and item.get("completion_id")
        }
        proof_completion_count += len(proof_completion_ids)
        linked_completion_count += len(
            {
                _freeze(item.get("cause_ref"))
                for item in transitions
                if isinstance(item, Mapping)
                and item.get("cause_kind") == "proof_completion"
                and _freeze(item.get("cause_ref")) in proof_completion_ids
            }
        )
        transition_state = _resolve_transitions(
            occurrences,
            transitions,
            completions,
            diagnostics,
            reason_completions=reason_completions,
        )
        final_occurrence_ids = _final_attempt_occurrence_ids(payload, occurrences)
        for occurrence in occurrences:
            record = occurrence.get("reason_record") or {}
            total_reasons += 1
            status = str(occurrence.get("initial_causal_status") or "unclassified")
            if status != "unclassified":
                explicit_status += 1
            occurrence_id = _freeze(occurrence.get("occurrence_id"))
            effective = transition_state.get(occurrence_id, status)
            blocker_id, typed = _blocker_id(record, stable, diagnostics)
            if blocker_id is None:
                _inc(diagnostics, "unkeyed_reason_record")
                continue
            typed_reasons += int(typed)
            pair_ref = _case_pair_ref(payload, stable, occurrence, record)
            if pair_ref is not None:
                pair_identified += 1
            certainty = "explicit" if status != "unclassified" else "unclassified"
            is_final_occurrence = occurrence_id in final_occurrence_ids
            if status == "unclassified" and is_final_occurrence:
                effect = str(record.get("decision_effect") or "")
                action_status = str(record.get("action_status") or "")
                if effect in _BLOCKING_EFFECTS and action_status != "proof_complete":
                    certainty = "inferred_final_attempt"
                    effective = "active_final_blocker"
            _add_occurrence(
                candidate,
                blocker_id,
                record,
                occurrence_id,
                stable,
                provenance,
                pair_ref,
                certainty,
                diagnostics,
            )
            active_status_allowed = (
                effective == "active_final_blocker" and is_final_occurrence
            ) or (
                effective == "contributing_blocker"
                and is_final_occurrence
            )
            if active_result_occurrence and active_status_allowed:
                _add_occurrence(
                    active,
                    blocker_id,
                    record,
                    occurrence_id,
                    stable,
                    provenance,
                    pair_ref,
                    certainty,
                    None,
                )

    # Issue #128: aggregate も trace も無ければ coverage は `unknown`（= None）。
    # 「全部 0 件だった」と「観測できなかった」を同じ 0.0 で潰さない。
    coverage = None
    if causal_evidence_present:
        coverage = {
            "typed_cause_coverage": _ratio(typed_reasons, total_reasons),
            "explicit_causal_status_coverage": _ratio(explicit_status, total_reasons),
            "case_pair_identity_coverage": _ratio(pair_identified, total_reasons),
            "transition_emission_coverage": _ratio(transition_target_count, total_reasons),
            "proof_completion_linkage_coverage": _ratio(
                linked_completion_count, proof_completion_count
            ) if proof_completion_count else 0.0,
        }
    blocker_sort = lambda item: (
        -len(item.results),
        repr(item.blocker_id.to_key()),
    )
    active_values = tuple(
        item.freeze() for item in sorted(active.values(), key=blocker_sort)
    )
    candidate_values = tuple(
        item.freeze() for item in sorted(candidate.values(), key=blocker_sort)
    )
    return RootBlockerSummary(
        snapshot.snapshot_id,
        active_values,
        candidate_values,
        diagnostics,
        coverage,
        tuple(sorted(set(hints))),
    )


def _stable_result_ref(
    payload: Mapping[str, Any],
    *,
    provenance: ResultProvenanceRef,
    allow_legacy_unverified: bool,
) -> Optional[StableResultRef]:
    left_content = payload.get("binary1_content_identity")
    right_content = payload.get("binary2_content_identity")
    left_function = payload.get("function1_identity")
    right_function = payload.get("function2_identity")
    certainty = "verified"
    if not left_content or not right_content or not left_function or not right_function:
        if not allow_legacy_unverified:
            return None
        certainty = "legacy_unverified"
        left_content = (
            "legacy_snapshot_binary",
            provenance.to_key(),
            payload.get("binary1_name") or "<missing>",
        )
        right_content = (
            "legacy_snapshot_binary",
            provenance.to_key(),
            payload.get("binary2_name") or "<missing>",
        )
        left_function = (
            "legacy_snapshot_function",
            provenance.to_key(),
            payload.get("function1_name") or payload.get("function_name") or "<missing>",
        )
        right_function = (
            "legacy_snapshot_function",
            provenance.to_key(),
            payload.get("function2_name") or payload.get("function_name") or "<missing>",
        )
    domain = ComparisonDomainKey(
        left_binary_identity=_tuple(left_content),
        right_binary_identity=_tuple(right_content),
        architecture_identity=_tuple(payload.get("architecture_identity")),
        abi_fingerprint=_tuple(payload.get("abi_fingerprint")),
        calling_convention_fingerprint=_tuple(payload.get("calling_convention_fingerprint")),
        comparison_policy_fingerprint=_tuple(payload.get("comparison_policy_fingerprint")),
    )
    case = payload.get("logical_case_identity") or payload.get("case_id") or payload.get("function_name")
    left = left_function
    right = right_function
    return StableResultRef(
        _tuple(case or "<missing>"),
        _tuple(left or "<missing>"),
        _tuple(right or "<missing>"),
        domain,
        identity_certainty=certainty,
    )


def _provenance_ref(payload: Mapping[str, Any], index: int) -> ResultProvenanceRef:
    return ResultProvenanceRef(
        _tuple(payload.get("run_identity") or ("input_ordinal", index)),
        _tuple(payload.get("artifact_identity") or payload.get("result_artifact_identity") or ("payload", index)),
        payload.get("source_path"),
        payload.get("observed_at"),
    )


def _is_final_unknown(payload: Mapping[str, Any]) -> bool:
    if payload.get("decision_receipt") is not None:
        from scripts.function_tracer_pcode.authority.decision.production_cutover import (
            outcome_from_payload,
        )

        return outcome_from_payload(payload).value in {"UNKNOWN", "TIMEOUT"}
    if payload.get("error_message") is not None:
        return False
    trace = payload.get("debug_trace")
    if isinstance(trace, Mapping):
        if trace.get("error_message") is not None:
            return False
        attempts = tuple(trace.get("attempts") or ())
        if attempts:
            final_unknown_attempt = next(
                (
                    attempt
                    for attempt in reversed(attempts)
                    if isinstance(attempt, Mapping)
                    and attempt.get("result") is None
                    and str(attempt.get("transition_reason") or "")
                    in _FINAL_TRANSITIONS
                ),
                None,
            )
            if final_unknown_attempt is None:
                return False
    if isinstance(trace, Mapping) and trace.get("final_result") is not None:
        return False
    value = payload.get("is_equivalent")
    if value is None:
        value = payload.get("final_result")
    if value is not None:
        return False
    return True


def _extract_occurrences(payload: Mapping[str, Any]):
    trace = payload.get("debug_trace") if isinstance(payload.get("debug_trace"), Mapping) else {}
    occurrences = []
    for attempt_index, attempt in enumerate(trace.get("attempts") or ()):
        if not isinstance(attempt, Mapping):
            continue
        attempt_occurrences = attempt.get("reason_occurrences") or ()
        if attempt_occurrences:
            occurrences.extend(dict(item) for item in attempt_occurrences if isinstance(item, Mapping))
            continue
        attempt_identity = {
            "trace_schema_version": 1,
            "strategy_identity": str(attempt.get("strategy") or attempt.get("phase") or "unknown"),
            "attempt_ordinal": int(attempt.get("attempt_id", attempt_index)),
        }
        for reason_index, reason in enumerate(attempt.get("unknown_reasons") or ()):
            occurrences.append({
                "occurrence_id": {
                    "occurrence_schema_version": 1,
                    "attempt_identity": attempt_identity,
                    "reason_ordinal": reason_index,
                },
                "attempt_identity": attempt_identity,
                "reason_record": reason,
                "initial_causal_status": "unclassified",
            })
    if not occurrences:
        for reason_index, reason in enumerate(payload.get("unknown_reasons") or ()):
            attempt_identity = {"trace_schema_version": 1, "strategy_identity": "payload", "attempt_ordinal": 0}
            occurrences.append({
                "occurrence_id": {"occurrence_schema_version": 1, "attempt_identity": attempt_identity, "reason_ordinal": reason_index},
                "attempt_identity": attempt_identity,
                "reason_record": reason,
                "initial_causal_status": "unclassified",
            })
    return (
        occurrences,
        list(trace.get("causal_transitions") or ()),
        list(trace.get("proof_completion_events") or ()),
        list(trace.get("reason_completion_events") or ()),
    )


def _final_attempt_occurrence_ids(payload, occurrences):
    trace = payload.get("debug_trace") if isinstance(payload.get("debug_trace"), Mapping) else {}
    final_attempt = None
    for attempt in reversed(tuple(trace.get("attempts") or ())):
        if isinstance(attempt, Mapping) and attempt.get("result") is None and str(attempt.get("transition_reason")) in _FINAL_TRANSITIONS:
            final_attempt = _freeze({
                "trace_schema_version": 1,
                "strategy_identity": str(attempt.get("strategy") or attempt.get("phase") or "unknown"),
                "attempt_ordinal": int(attempt.get("attempt_id", 0)),
            })
            break
    if final_attempt is None and occurrences:
        final_attempt = _freeze(occurrences[-1].get("attempt_identity"))
    return {
        _freeze(item.get("occurrence_id"))
        for item in occurrences
        if _freeze(item.get("attempt_identity")) == final_attempt
    }


def _blocker_id(record, stable, diagnostics):
    """reason record -> RootBlockerId。identity の判定は共有 resolver に委ねる。"""
    resolution = resolve_cause_identity(
        typed_cause_key=record.get("typed_cause_key"),
        object_target_key=record.get("object_target_key"),
        left_binary_identity=stable.comparison_domain.left_binary_identity,
        right_binary_identity=stable.comparison_domain.right_binary_identity,
    )
    if resolution.diagnostic:
        _inc(diagnostics, resolution.diagnostic)
    if not resolution.resolved:
        return None, False
    return (
        RootBlockerId(
            resolution.identity_scope,
            resolution.cause_kind,
            resolution.canonical_cause_key,
        ),
        resolution.typed,
    )


def _case_pair_ref(payload, stable, occurrence, record):
    pair = record.get("pair_or_case")
    if isinstance(pair, (tuple, list)) and len(pair) == 2:
        strategy = str((occurrence.get("attempt_identity") or {}).get("strategy_identity") or "unknown")
        return StableCasePairRef(stable, strategy, _tuple(pair[0]), _tuple(pair[1])).to_key()
    return None


def _add_occurrence(builders, blocker_id, record, occurrence_id, stable, provenance, pair_ref, certainty, diagnostics):
    builder = builders.setdefault(blocker_id.to_key(), _BlockerBuilder(blocker_id))
    legacy = record.get("proof_obligation_id")
    if legacy:
        builder.legacy.add(_freeze(legacy))
    # Requirement derivation (including the conservative legacy migration for
    # artifacts that only carry an ``object_target_key``) is shared with the
    # ``unknown_cause_aggregate`` producer so both paths yield the same keys.
    proofs = resolve_required_proofs(
        proof_requirement_ids=record.get("proof_requirement_ids") or (),
        object_target_key=record.get("object_target_key"),
        identity_scope=blocker_id.identity_scope,
        canonical_cause_key=blocker_id.canonical_cause_key,
        recovery_actions=build_unknown_recovery_actions((record,)),
    )
    builder.required.update(proofs.keys)
    if not proofs.complete:
        builder.proof_requirements_complete = False
    if diagnostics is not None:
        for name in proofs.diagnostics:
            _inc(diagnostics, name)
    if pair_ref is not None:
        builder.pairs.add(pair_ref)
    builder.results.add(stable.to_key())
    builder.result_occurrences.add(provenance.to_key())
    builder.reasons.add(str(record.get("reason_id") or "unknown"))
    builder.occurrences.add((stable.to_key(), occurrence_id))
    builder.evidence.update(str(item) for item in (record.get("evidence_refs") or ()))
    builder.certainties.add(certainty)


def _add_cause_group(builders, blocker_id, group, stable, provenance, pool=()):
    """``unknown_cause_aggregate`` の 1 原因分をそのまま builder へ足す。

    aggregate は occurrence ごとの record を持たないので、producer 側で
    union 済みの集合（proof requirement / case pair / evidence …）を受け取る。
    ``all`` と ``active`` は producer が別々に union しているため、active 判定に
    使われなかった occurrence の情報が active 側へ混ざらない。繰り返す identity
    は ``identity_pool`` へ畳まれているので index から戻す。
    """
    builder = builders.setdefault(blocker_id.to_key(), _BlockerBuilder(blocker_id))
    builder.legacy.update(
        _freeze(item)
        for item in resolve_pool_refs(pool, group.get("legacy_proof_obligation_id_refs"))
    )
    builder.required.update(
        _freeze(item) for item in resolve_pool_refs(pool, group.get("required_proof_id_refs"))
    )
    if not group.get("proof_requirements_complete", True):
        builder.proof_requirements_complete = False
    for case_pair in group.get("case_pairs") or ():
        frozen = _freeze(case_pair)
        if not isinstance(frozen, tuple) or len(frozen) != 3:
            continue
        strategy, left_case, right_case = frozen
        builder.pairs.add(
            StableCasePairRef(stable, str(strategy), _tuple(left_case), _tuple(right_case)).to_key()
        )
    builder.results.add(stable.to_key())
    builder.result_occurrences.add(provenance.to_key())
    builder.reasons.update(str(item) for item in (group.get("reason_ids") or ()))
    for occurrence_id in group.get("occurrence_ids") or ():
        builder.occurrences.add((stable.to_key(), _freeze(occurrence_id)))
    builder.evidence.update(str(item) for item in (group.get("evidence_refs") or ()))
    builder.certainties.update(str(item) for item in (group.get("certainties") or ()))


def _ratio(numerator, denominator):
    return float(numerator) / float(denominator) if denominator else 1.0


def _inc(counts, key, amount: int = 1):
    counts[key] = counts.get(key, 0) + amount


def format_root_blocker_summary(summary: RootBlockerSummary, *, max_items: int = 20) -> str:
    proof_count = summary.required_unique_proof_count
    lines = [
        "Root blockers:",
        f"  snapshot: {summary.snapshot_id}",
        f"  active unique blockers: {summary.active_root_blocker_count}",
        f"  observed candidates: {summary.candidate_root_blocker_count}",
        "  required unique proofs: "
        + (str(proof_count) if proof_count is not None else "unknown (incomplete identity)"),
    ]
    for index, blocker in enumerate(summary.active_root_blockers[:max_items], 1):
        lines.append(
            f"  {index}. {blocker.blocker_id.cause_kind}: "
            f"results={len(blocker.affected_unknown_results)}, "
            f"pairs={len(blocker.affected_case_pairs)}, "
            f"proofs={len(blocker.required_proof_ids)}"
        )
    if summary.diagnostics:
        lines.append("  diagnostics: " + ", ".join(
            f"{key}={value}" for key, value in sorted(summary.diagnostics.items())
        ))
    return "\n".join(lines)
