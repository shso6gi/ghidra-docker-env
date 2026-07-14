# -*- coding: utf-8 -*-
"""Root-cause aggregation for final UNKNOWN/TIMEOUT results.

The aggregator is observational: it never changes an equivalence decision.
Typed cause keys are accepted without semantic rewriting.  Legacy tuple keys
are preserved in full and therefore may over-partition, but never over-merge.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence, Tuple

from ..equivalence.cause_identity import (
    CAUSE_IDENTITY_SCHEMA_VERSION,
    CauseKey,
    IdentityScope,
    ProofRequirementId,
    canonical_cause_tuple,
    cause_key_from_dict,
)
from ..equivalence.unknown_reason import build_unknown_recovery_actions


ROOT_BLOCKER_SCHEMA_VERSION = 1
_FINAL_TRANSITIONS = {"UNKNOWN", "TIMEOUT"}
_BLOCKING_EFFECTS = {
    "blocks_equivalence",
    "blocks_disequivalence",
    "blocks_decision",
    "retryable",
}
_LEGACY_CAUSE_SCOPES = {
    "return_coverage": (IdentityScope.UNARY.value, "return_coverage_v3"),
    "call_argument_evidence": (IdentityScope.UNARY.value, "call_evidence_v1"),
    "call_target_resolution_evidence": (IdentityScope.UNARY.value, "call_evidence_v1"),
    "deferred_call_site": (IdentityScope.UNARY.value, "deferred_call_v1"),
    "return_width_bridge": (IdentityScope.RELATIONAL.value, "return_width_v1"),
    "solver_timeout": (IdentityScope.EXECUTION.value, "solver_timeout_v1"),
}


def _freeze(value: Any) -> Any:
    if isinstance(value, Mapping):
        return tuple(
            (str(key), _freeze(item))
            for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
        )
    if isinstance(value, (list, tuple)):
        return tuple(_freeze(item) for item in value)
    return value


def _tuple(value: Any) -> Tuple[Any, ...]:
    frozen = _freeze(value)
    if frozen is None:
        return ()
    return frozen if isinstance(frozen, tuple) else (frozen,)


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
    coverage: Dict[str, float] = field(default_factory=dict)
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
            "coverage": dict(self.coverage),
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

    for payload, stable, provenance in entries:
        final_unknown = _is_final_unknown(payload)
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
            if (
                final_unknown
                and provenance.to_key() in active_occurrence_keys
                and stable.identity_certainty == "verified"
                and active_status_allowed
            ):
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


def _resolve_transitions(
    occurrences,
    transitions,
    completions,
    diagnostics,
    *,
    reason_completions=(),
):
    occurrence_by_id = {
        _freeze(item.get("occurrence_id")): item for item in occurrences
    }
    occurrence_ids = set(occurrence_by_id)
    proven_completions = {
        _freeze(item.get("completion_id")): item
        for item in completions
        if (
            isinstance(item, Mapping)
            and str(item.get("proof_status")) == "proven"
            and bool(item.get("proof_artifact_ref"))
        )
    }
    result = {}
    for completion in reason_completions:
        if not isinstance(completion, Mapping):
            continue
        target = _freeze(completion.get("completed_occurrence_id"))
        if str(completion.get("applicability_status")) != "APPLICABLE":
            _inc(diagnostics, "inapplicable_reason_completion")
            continue
        if target not in occurrence_ids:
            _inc(diagnostics, "dangling_reason_completion_target")
            continue
        record = occurrence_by_id[target].get("reason_record") or {}
        expected_target = _freeze(record.get("object_target_key"))
        observed_target = _freeze(completion.get("exact_target_id"))
        expected_slots = {
            str(item.get("proof_kind") or "")
            for item in (record.get("proof_requirement_ids") or ())
            if isinstance(item, Mapping)
        }
        observed_slot = str(
            completion.get("exact_missing_fact_or_proof_slot") or ""
        )
        if (
            (expected_target and expected_target != observed_target)
            or (expected_slots and observed_slot not in expected_slots)
            or not completion.get("source_snapshot_fingerprint")
            or not completion.get("semantic_seed_or_premise_digest")
            or not completion.get("evidence_or_artifact_digest")
            or not completion.get("recognizing_stage")
        ):
            _inc(diagnostics, "invalid_reason_completion_applicability")
            continue
        completed_ordinal = _attempt_ordinal(completion.get("completed_at_attempt"))
        target_ordinal = _attempt_ordinal(occurrence_by_id[target].get("attempt_identity"))
        if (
            completed_ordinal is None
            or target_ordinal is None
            or completed_ordinal <= target_ordinal
        ):
            _inc(diagnostics, "non_forward_reason_completion")
            continue
        result[target] = "discharged"
    seen = set()
    by_target = {}
    for transition in sorted(transitions, key=lambda item: repr(_freeze(item))):
        if not isinstance(transition, Mapping):
            continue
        transition_id = _freeze(transition.get("transition_id"))
        if transition_id in seen:
            continue
        seen.add(transition_id)
        target = _freeze(transition.get("target_occurrence_id"))
        if target not in occurrence_ids:
            _inc(diagnostics, "dangling_transition_target")
            continue
        kind = str(transition.get("transition_kind") or "")
        cause_kind = str(transition.get("cause_kind") or "")
        cause_ref = _freeze(transition.get("cause_ref"))
        valid = False
        emitted_ordinal = _attempt_ordinal(transition.get("emitted_at_attempt"))
        target_ordinal = _attempt_ordinal(
            occurrence_by_id[target].get("attempt_identity")
        )
        if emitted_ordinal is None or target_ordinal is None or emitted_ordinal <= target_ordinal:
            _inc(diagnostics, "non_forward_causal_transition")
            continue
        if kind == "superseded" and cause_kind == "reason_occurrence":
            valid = cause_ref in occurrence_ids
        if not valid:
            _inc(diagnostics, "dangling_transition_cause")
            continue
        by_target.setdefault(target, set()).add((kind, cause_kind, cause_ref))
    for target, values in by_target.items():
        if len(values) != 1:
            _inc(diagnostics, "conflicting_causal_transitions")
            continue
        kind = next(iter(values))[0]
        prior = result.get(target)
        if prior is not None and prior != kind:
            _inc(diagnostics, "conflicting_causal_transitions")
            result.pop(target, None)
            continue
        result[target] = kind
    supersession_edges = {
        target: next(iter(values))[2]
        for target, values in by_target.items()
        if len(values) == 1 and next(iter(values))[0] == "superseded"
    }
    cyclic = _cyclic_nodes(supersession_edges)
    for target in cyclic:
        result.pop(target, None)
    if cyclic:
        diagnostics["causal_transition_cycle"] = len(cyclic)
    return result


def _attempt_ordinal(value: Any) -> Optional[int]:
    if not isinstance(value, Mapping):
        return None
    raw = value.get("attempt_ordinal")
    try:
        return int(raw)
    except (TypeError, ValueError):
        return None


def _cyclic_nodes(edges: Mapping[Any, Any]) -> set:
    cyclic = set()
    for start in edges:
        path = []
        positions = {}
        current = start
        while current in edges:
            if current in positions:
                cyclic.update(path[positions[current]:])
                break
            positions[current] = len(path)
            path.append(current)
            current = edges[current]
    return cyclic


def _blocker_id(record, stable, diagnostics):
    typed = record.get("typed_cause_key")
    if isinstance(typed, Mapping):
        try:
            cause: CauseKey = cause_key_from_dict(typed)
        except ValueError as exc:
            message = str(exc)
            if "unsupported typed cause schema" in message:
                _inc(diagnostics, "unknown_typed_cause_schema")
            elif "unsupported identity scope" in message:
                _inc(diagnostics, "unsupported_identity_scope")
            else:
                _inc(diagnostics, "incomplete_typed_cause_key")
            return None, False
        return RootBlockerId(cause.identity_scope, cause.cause_kind, canonical_cause_tuple(cause)), True
    legacy = record.get("object_target_key")
    if not legacy:
        return None, False
    discriminator = str(_tuple(legacy)[0])
    spec = _LEGACY_CAUSE_SCOPES.get(discriminator)
    if spec is None:
        _inc(diagnostics, "legacy_adapter_missing")
        return None, False
    scope, schema = spec
    validation = _validate_legacy_cause_key(schema, _tuple(legacy))
    if validation == "schema_invalid":
        _inc(diagnostics, "legacy_cause_schema_invalid")
        return None, False
    if validation == "identity_incomplete":
        _inc(diagnostics, "legacy_cause_identity_incomplete")
        return None, False
    # A registered adapter asserts that the complete tuple schema already
    # carries the semantic object/comparison/query identity for its scope.
    # No display name or enclosing result domain is added to the blocker key.
    canonical = (
        "legacy_known_canonical",
        _canonicalize_legacy_cause_key(schema, _tuple(legacy), stable),
    )
    return RootBlockerId(scope, discriminator, canonical), False


def _canonicalize_legacy_cause_key(
    schema: str,
    key: Tuple[Any, ...],
    stable: StableResultRef,
) -> Tuple[Any, ...]:
    if schema == "return_coverage_v3":
        # key[2] is only the presentation side within the current comparison.
        return _freeze(
            (
                key[0],
                ("local_binary_content", _local_binary_identity(stable, key[2])),
                key[1],
                *key[3:],
            )
        )
    if schema == "call_evidence_v1":
        # key[1] is function1/function2; function_ref and pcode identity remain.
        return _freeze(
            (
                key[0],
                ("local_binary_content", _local_binary_identity(stable, key[1])),
                *key[2:],
            )
        )
    return _freeze(key)


def _local_binary_identity(stable: StableResultRef, side: str) -> Tuple[Any, ...]:
    if side == "function1":
        return stable.comparison_domain.left_binary_identity
    if side == "function2":
        return stable.comparison_domain.right_binary_identity
    raise ValueError(f"unsupported unary cause side: {side}")


def _validate_legacy_cause_key(schema: str, key: Tuple[Any, ...]) -> str:
    if schema == "return_coverage_v3":
        if len(key) < 8 or key[0] != "return_coverage":
            return "schema_invalid"
        if key[1] != ("target_schema_version", 3):
            return "schema_invalid"
        if key[2] not in {"function1", "function2"}:
            return "identity_incomplete"
        required_tags = ("function_identity", "return_partition_identity", "guard_disjunction_identity")
        if not all(
            isinstance(value, tuple) and value and value[0] == tag
            for value, tag in ((key[3], required_tags[0]), (key[6], required_tags[1]), (key[7], required_tags[2]))
        ):
            return "identity_incomplete"
        if not _contains_tagged_identity(key[3], "binary_identity"):
            return "identity_incomplete"
        return "valid"
    if schema == "return_width_v1":
        if len(key) != 5 or key[0] != "return_width_bridge":
            return "schema_invalid"
        if not (isinstance(key[1], tuple) and key[1][:1] == ("pair",) and key[1][1]):
            return "identity_incomplete"
        widths = key[2]
        if not (
            isinstance(widths, tuple)
            and len(widths) == 3
            and widths[0] == "return_widths"
            and all(isinstance(value, int) and value > 0 for value in widths[1:])
        ):
            return "identity_incomplete"
        if not all(isinstance(value, tuple) and len(value) >= 3 for value in key[3:]):
            return "identity_incomplete"
        return "valid"
    if schema == "solver_timeout_v1":
        if len(key) != 8 or key[0] != "solver_timeout":
            return "schema_invalid"
        required = {
            "pair": key[1],
            "stage": key[2],
            "query_hash": key[3],
            "timeout_budget_seconds": key[4],
            "solver_options": key[5],
        }
        if any(not isinstance(value, tuple) or not value for value in required.values()):
            return "schema_invalid"
        if any(value[0] != tag for tag, value in required.items()):
            return "schema_invalid"
        if not key[3][1] or not key[4][1] or not key[5][1:]:
            return "identity_incomplete"
        if not all(isinstance(value, tuple) and len(value) >= 2 for value in key[6:]):
            return "identity_incomplete"
        return "valid"
    if schema == "call_evidence_v1":
        if len(key) < 5 or key[0] not in {
            "call_argument_evidence",
            "call_target_resolution_evidence",
        }:
            return "schema_invalid"
        if key[1] not in {"function1", "function2"}:
            return "identity_incomplete"
        if not all(isinstance(value, tuple) and value for value in key[2:5]):
            return "identity_incomplete"
        if key[2][0] != "function_ref" or key[3][0] != "pcode_op":
            return "identity_incomplete"
        return "valid"
    if schema == "deferred_call_v1":
        if len(key) < 4 or key[0] != "deferred_call_site":
            return "schema_invalid"
        if not all(isinstance(value, tuple) and value for value in key[1:4]):
            return "identity_incomplete"
        return "valid"
    return "schema_invalid"


def _contains_tagged_identity(value: Any, tag: str) -> bool:
    if isinstance(value, tuple):
        if value and value[0] == tag:
            return True
        return any(_contains_tagged_identity(item, tag) for item in value)
    return False


def _case_pair_ref(payload, stable, occurrence, record):
    pair = record.get("pair_or_case")
    if isinstance(pair, (tuple, list)) and len(pair) == 2:
        strategy = str((occurrence.get("attempt_identity") or {}).get("strategy_identity") or "unknown")
        return StableCasePairRef(stable, strategy, _tuple(pair[0]), _tuple(pair[1])).to_key()
    return None


def _add_occurrence(builders, blocker_id, record, occurrence_id, stable, provenance, pair_ref, certainty, diagnostics):
    key = blocker_id.to_key()
    builder = builders.setdefault(key, _BlockerBuilder(blocker_id))
    legacy = record.get("proof_obligation_id")
    if legacy:
        builder.legacy.add(_freeze(legacy))
    explicit_requirements = record.get("proof_requirement_ids") or ()
    for requirement in explicit_requirements:
        try:
            builder.required.add(ProofRequirementId.from_dict(requirement).to_key())
        except (TypeError, ValueError) as exc:
            builder.proof_requirements_complete = False
            message = str(exc)
            if diagnostics is not None:
                if "unsupported proof requirement schema" in message:
                    _inc(diagnostics, "unknown_proof_requirement_schema")
                elif "requires kind, target, and contract" in message:
                    _inc(diagnostics, "proof_requirement_identity_incomplete")
                else:
                    _inc(diagnostics, "invalid_proof_requirement")
    if not explicit_requirements and record.get("object_target_key"):
        # Conservative migration for old artifacts.  The full legacy target and
        # comparison domain remain in the target key; reason_id and observed
        # stage are intentionally absent so the same proposition can collapse
        # across reason buckets.
        for action in build_unknown_recovery_actions((record,)):
            if str(getattr(action, "proof_kind", "none")) == "none":
                continue
            contract = (
                "legacy_recovery_contract",
                str(getattr(action, "proof_kind", "")),
                _freeze(getattr(action, "required_evidence", ()) or ()),
            )
            try:
                requirement = ProofRequirementId.create(
                    getattr(action, "proof_kind", ""),
                    (
                        "legacy_scope_aware_target",
                        blocker_id.identity_scope,
                        blocker_id.canonical_cause_key,
                    ),
                    contract,
                )
            except ValueError:
                continue
            builder.required.add(requirement.to_key())
    if pair_ref is not None:
        builder.pairs.add(pair_ref)
    builder.results.add(stable.to_key())
    builder.result_occurrences.add(provenance.to_key())
    builder.reasons.add(str(record.get("reason_id") or "unknown"))
    builder.occurrences.add((stable.to_key(), occurrence_id))
    builder.evidence.update(str(item) for item in (record.get("evidence_refs") or ()))
    builder.certainties.add(certainty)


def _ratio(numerator, denominator):
    return float(numerator) / float(denominator) if denominator else 1.0


def _inc(counts, key):
    counts[key] = counts.get(key, 0) + 1


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
