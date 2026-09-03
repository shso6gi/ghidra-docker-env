"""Entry-bound census contracts, joins, metrics, and all-or-nothing gates."""

from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.authority.decision.candidate import CandidateDecisionProjection
from scripts.function_tracer_pcode.authority.contracts import (
    BlockerEligibilityBaseRow,
    CActiveBaseRow,
    CensusMode,
    Outcome,
    QOpenBaseRow,
    RecoveryAddressability,
    ResultKind,
    VerifiedLifecycleProjection,
    SCHEMA_VERSION,
    authority_digest,
    canonical_value,
)
from scripts.function_tracer_pcode.authority.decision.decision import DecisionReceipt
from scripts.function_tracer_pcode.authority.lifecycle.stream import EventType, SealedEventStream


class CensusStatus(str, Enum):
    VALID = "VALID"
    INVALID = "INVALID"


@dataclass(frozen=True)
class CensusComputation:
    status: CensusStatus
    authoritative: bool
    canonical_metrics: Optional[Mapping[str, Any]]
    diagnostic_errors: Tuple[str, ...]


@dataclass(frozen=True)
class CensusEntry:
    result_occurrence_id: str
    result_kind: ResultKind
    comparison_domain_identity: Any
    binary_content_identities: Any
    function_identities: Any
    event_stream_authority_digest: Optional[str]
    lifecycle_projection_digest: Optional[str]
    decision_receipt_digest: Optional[str]
    result_artifact_digest: str
    migration_pair_id: Optional[str] = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "result_kind", ResultKind(self.result_kind))
        for field_name in (
            "comparison_domain_identity",
            "binary_content_identities",
            "function_identities",
        ):
            object.__setattr__(self, field_name, canonical_value(getattr(self, field_name)))
        if not self.result_occurrence_id or not self.result_artifact_digest:
            raise ValueError("census entry identity is incomplete")
        v2_digests = (
            self.event_stream_authority_digest,
            self.lifecycle_projection_digest,
            self.decision_receipt_digest,
        )
        if self.result_kind == ResultKind.V2_NATIVE and not all(v2_digests):
            raise ValueError("v2 census entry lacks authority digest")
        if self.result_kind == ResultKind.LEGACY and any(v2_digests):
            raise ValueError("legacy census entry cannot claim v2 authority digests")


@dataclass(frozen=True)
class CensusManifest:
    manifest_id: str
    census_mode: CensusMode
    repository_commit: str
    analysis_config_digest: str
    entries: Tuple[CensusEntry, ...]
    manifest_authority_digest: str = field(init=False)
    generated_at: Optional[str] = None
    schema_version: int = SCHEMA_VERSION

    def __post_init__(self) -> None:
        if type(self.schema_version) is not int or self.schema_version != SCHEMA_VERSION:
            raise ValueError("unsupported census manifest schema")
        object.__setattr__(self, "census_mode", CensusMode(self.census_mode))
        entries = tuple(sorted(tuple(self.entries), key=lambda item: item.result_occurrence_id))
        if len({entry.result_occurrence_id for entry in entries}) != len(entries):
            raise ValueError("duplicate census result occurrence")
        if self.census_mode == CensusMode.V2_CANONICAL and any(
            entry.result_kind != ResultKind.V2_NATIVE for entry in entries
        ):
            raise ValueError("canonical census cannot contain legacy entries")
        if self.census_mode == CensusMode.LEGACY_DIAGNOSTIC and any(
            entry.result_kind != ResultKind.LEGACY for entry in entries
        ):
            raise ValueError("legacy census cannot contain v2-native entries")
        if self.census_mode == CensusMode.MIGRATION_COMPARISON:
            by_pair: dict[str, list[CensusEntry]] = defaultdict(list)
            for entry in entries:
                if not entry.migration_pair_id:
                    raise ValueError("migration comparison entry lacks pair identity")
                by_pair[entry.migration_pair_id].append(entry)
            if not by_pair or any(
                len(pair) != 2
                or {entry.result_kind for entry in pair}
                != {ResultKind.V2_NATIVE, ResultKind.LEGACY}
                for pair in by_pair.values()
            ):
                raise ValueError("migration comparison requires exact v1/v2 entry pairs")
            for pair in by_pair.values():
                left, right = pair
                if (
                    left.comparison_domain_identity != right.comparison_domain_identity
                    or left.binary_content_identities != right.binary_content_identities
                    or left.function_identities != right.function_identities
                ):
                    raise ValueError("migration pair comparison identities differ")
        elif any(entry.migration_pair_id for entry in entries):
            raise ValueError("migration pair identity is forbidden outside comparison mode")
        object.__setattr__(self, "entries", entries)
        object.__setattr__(
            self,
            "manifest_authority_digest",
            authority_digest(
                {
                    "manifest_id": self.manifest_id,
                    "schema_version": self.schema_version,
                    "census_mode": self.census_mode.value,
                    "repository_commit": self.repository_commit,
                    "analysis_config_digest": self.analysis_config_digest,
                    "entries": entries,
                }
            ),
        )


@dataclass(frozen=True)
class ActiveOccurrenceMaterialization:
    result_occurrence_id: str
    occurrence_id: str
    cause_id: str
    recovery_addressability: RecoveryAddressability

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "recovery_addressability",
            RecoveryAddressability(self.recovery_addressability),
        )

    @property
    def key(self) -> Tuple[str, str, str]:
        return self.result_occurrence_id, self.occurrence_id, self.cause_id


@dataclass(frozen=True)
class CoverageInputs:
    active_occurrences: Tuple[ActiveOccurrenceMaterialization, ...]

    def __post_init__(self) -> None:
        object.__setattr__(self, "active_occurrences", tuple(self.active_occurrences))
        if len({item.key for item in self.active_occurrences}) != len(self.active_occurrences):
            raise ValueError("duplicate active occurrence materialization input")


def coverage_ratio(numerator: int, denominator: int) -> Optional[float]:
    if numerator < 0 or denominator < 0 or numerator > denominator:
        raise ValueError("invalid coverage numerator/denominator")
    return None if denominator == 0 else numerator / denominator


def materialization_metrics(
    active: Sequence[ActiveOccurrenceMaterialization],
    q_open_base: Sequence[QOpenBaseRow],
) -> Mapping[str, Any]:
    open_keys = {
        (row.result_occurrence_id, row.occurrence_id, row.cause_id)
        for row in q_open_base
    }
    categories = Counter()
    required_total = required_materialized = optional_total = optional_materialized = 0
    for item in active:
        materialized = item.key in open_keys
        if item.recovery_addressability == RecoveryAddressability.REQUIREMENT_REQUIRED:
            required_total += 1
            required_materialized += int(materialized)
            if not materialized:
                categories["required_missing"] += 1
        elif item.recovery_addressability == RecoveryAddressability.REQUIREMENT_OPTIONAL:
            optional_total += 1
            optional_materialized += int(materialized)
            if not materialized:
                categories["optional_not_materialized"] += 1
        else:
            if materialized:
                raise ValueError("NO_PROOF_RECOVERY occurrence has an open requirement")
            categories["no_proof_recovery"] += 1
    return {
        "required_requirement_materialization_coverage": coverage_ratio(
            required_materialized, required_total
        ),
        "optional_requirement_materialization_rate": coverage_ratio(
            optional_materialized, optional_total
        ),
        "active_causes_without_materialized_requirement": {
            key: categories.get(key, 0)
            for key in (
                "required_missing",
                "optional_not_materialized",
                "no_proof_recovery",
            )
        },
    }


def join_outcome_relations(
    manifest: CensusManifest,
    decisions: Sequence[DecisionReceipt],
    projections: Sequence[VerifiedLifecycleProjection],
) -> Mapping[str, Any]:
    if manifest.census_mode != CensusMode.V2_CANONICAL:
        raise ValueError("outcome authority join requires V2_CANONICAL mode")
    if any(type(projection) is not VerifiedLifecycleProjection for projection in projections):
        raise TypeError("canonical census requires FINAL lifecycle authorities")
    manifest_ids = {entry.result_occurrence_id for entry in manifest.entries}
    decision_by_id = {receipt.result_occurrence_id: receipt for receipt in decisions}
    projection_by_id = {
        projection.result_occurrence_id: projection for projection in projections
    }
    if len(decision_by_id) != len(decisions) or set(decision_by_id) != manifest_ids:
        raise ValueError("decision receipt key set differs from census manifest")
    if len(projection_by_id) != len(projections) or set(projection_by_id) != manifest_ids:
        raise ValueError("lifecycle projection key set differs from census manifest")
    entry_by_id = {entry.result_occurrence_id: entry for entry in manifest.entries}
    for result_id in sorted(manifest_ids):
        receipt = decision_by_id[result_id]
        projection = projection_by_id[result_id]
        receipt.validate()
        projection.validate()
        entry = entry_by_id[result_id]
        if entry.decision_receipt_digest != receipt.receipt_digest:
            raise ValueError("decision receipt digest differs from census entry")
        if entry.lifecycle_projection_digest != receipt.lifecycle_projection_digest:
            raise ValueError("decision lifecycle digest differs from census entry")
        if entry.lifecycle_projection_digest != projection.lifecycle_projection_digest:
            raise ValueError("verified lifecycle digest differs from census entry")
    causes = tuple(
        row for result_id in sorted(manifest_ids)
        for row in projection_by_id[result_id].c_active_base
    )
    requirements = tuple(
        row for result_id in sorted(manifest_ids)
        for row in projection_by_id[result_id].q_open_base
    )
    eligibility = tuple(
        row for result_id in sorted(manifest_ids)
        for row in projection_by_id[result_id].blocker_eligibility_base
    )
    if len(causes) != len(set(causes)) or len(requirements) != len(set(requirements)):
        raise ValueError("duplicate base relation row")
    cause_keys = {
        (row.result_occurrence_id, row.occurrence_id, row.cause_id) for row in causes
    }
    for row in requirements:
        if (row.result_occurrence_id, row.occurrence_id, row.cause_id) not in cause_keys:
            raise ValueError("open requirement lacks active cause foreign key")
    c_by_outcome = tuple(
        (row, decision_by_id[row.result_occurrence_id].outcome) for row in causes
    )
    q_by_outcome = tuple(
        (row, decision_by_id[row.result_occurrence_id].outcome) for row in requirements
    )
    observed_decision_counts = Counter(receipt.outcome.value for receipt in decisions)
    decision_counts = {
        outcome.value: observed_decision_counts.get(outcome.value, 0)
        for outcome in Outcome
    }
    if sum(decision_counts.values()) != len(manifest.entries):
        raise ValueError("decision conservation law failed")
    return {
        "decision_by_id": decision_by_id,
        "c_active_base": causes,
        "q_open_base": requirements,
        "blocker_eligibility_base": eligibility,
        "decision_counts": decision_counts,
        "c_active_by_outcome": c_by_outcome,
        "q_open_by_outcome": q_by_outcome,
    }


def compute_canonical_census(
    manifest: CensusManifest,
    candidates: Sequence[CandidateDecisionProjection],
    projections: Sequence[VerifiedLifecycleProjection],
    event_streams: Sequence[SealedEventStream],
    *,
    coverage_inputs: CoverageInputs,
) -> CensusComputation:
    try:
        exact_candidates = tuple(candidates)
        if any(type(item) is not CandidateDecisionProjection for item in exact_candidates):
            raise TypeError("canonical census requires exact candidate authorities")
        for candidate in exact_candidates:
            candidate.validate()
        candidate_by_id = {
            item.decision_receipt.result_occurrence_id: item
            for item in exact_candidates
        }
        if len(candidate_by_id) != len(exact_candidates):
            raise ValueError("duplicate candidate result occurrence")
        decisions = tuple(item.decision_receipt for item in exact_candidates)
        joined = join_outcome_relations(manifest, decisions, projections)
        manifest_ids = {entry.result_occurrence_id for entry in manifest.entries}
        if set(candidate_by_id) != manifest_ids:
            raise ValueError("candidate key set differs from census manifest")
        projection_by_id = {
            item.result_occurrence_id: item for item in projections
        }
        exact_streams = tuple(event_streams)
        if any(type(item) is not SealedEventStream for item in exact_streams):
            raise TypeError("canonical census requires exact sealed event streams")
        for stream in exact_streams:
            stream.validate()
        stream_by_id = {
            item.envelope.result_occurrence_id: item for item in exact_streams
        }
        if len(stream_by_id) != len(exact_streams) or set(stream_by_id) != manifest_ids:
            raise ValueError("sealed event-stream key set differs from census manifest")
        entry_by_id = {
            item.result_occurrence_id: item for item in manifest.entries
        }
        terminal_timeout_event_counts: dict[str, int] = {}
        observed_nonterminal_timeout_event_counts: dict[str, int] = {}
        for result_id in sorted(manifest_ids):
            candidate = candidate_by_id[result_id]
            projection = projection_by_id[result_id]
            entry = entry_by_id[result_id]
            stream = stream_by_id[result_id]
            if candidate.decision_receipt.lifecycle_projection_digest != (
                projection.lifecycle_projection_digest
            ):
                raise ValueError("candidate decision is not bound to lifecycle projection")
            if candidate.lifecycle_snapshot_digest != projection.snapshot_digest:
                raise ValueError("candidate snapshot is not bound to lifecycle projection")
            if candidate.event_stream_authority_digest != (
                entry.event_stream_authority_digest
            ):
                raise ValueError("candidate event stream differs from census manifest")
            if stream.envelope.authority_chain_digest != (
                entry.event_stream_authority_digest
            ):
                raise ValueError("sealed event stream differs from census manifest")
            observed_timeout_digests = tuple(sorted(
                item.authority_digest
                for item in stream.events
                if item.header.event_type in {
                    EventType.SOLVER_TIMEOUT, EventType.PROCESS_TIMEOUT,
                }
            ))
            if observed_timeout_digests != candidate.observed_timeout_event_digests:
                raise ValueError(
                    "candidate timeout projection differs from sealed event stream"
                )
            terminal = len(candidate.terminal_execution_event_digests)
            observed = len(candidate.observed_timeout_event_digests)
            if terminal > observed:
                raise ValueError("terminal timeout count exceeds observed timeout events")
            terminal_timeout_event_counts[result_id] = terminal
            observed_nonterminal_timeout_event_counts[result_id] = observed - terminal
        causes: Tuple[CActiveBaseRow, ...] = joined["c_active_base"]
        requirements: Tuple[QOpenBaseRow, ...] = joined["q_open_base"]
        eligibility: Tuple[BlockerEligibilityBaseRow, ...] = joined[
            "blocker_eligibility_base"
        ]
        decision_by_id: Mapping[str, DecisionReceipt] = joined["decision_by_id"]
        causes_by_result: dict[str, list[CActiveBaseRow]] = defaultdict(list)
        requirements_by_result: dict[str, list[QOpenBaseRow]] = defaultdict(list)
        for row in causes:
            causes_by_result[row.result_occurrence_id].append(row)
        for row in requirements:
            requirements_by_result[row.result_occurrence_id].append(row)
        unknown_timeout_results = 0
        unknown_timeout_with_authority = 0
        for result_id, receipt in decision_by_id.items():
            active = causes_by_result.get(result_id, ())
            open_requirements = requirements_by_result.get(result_id, ())
            terminal_count = int(terminal_timeout_event_counts.get(result_id, 0))
            if receipt.outcome in {Outcome.UNKNOWN, Outcome.TIMEOUT}:
                unknown_timeout_results += 1
                unknown_timeout_with_authority += int(bool(active))
            if receipt.outcome == Outcome.UNKNOWN and not active:
                raise ValueError("UNKNOWN result lacks active semantic cause")
            if receipt.outcome == Outcome.TIMEOUT:
                if not active or not open_requirements or terminal_count != 1:
                    raise ValueError("TIMEOUT result lacks cause, requirement, or terminal event")
            elif terminal_count:
                raise ValueError("non-TIMEOUT result has terminal timeout authority")
            if receipt.outcome == Outcome.EQUIVALENT and any(
                row.decision_effect in {"blocks_equivalence", "blocks_decision"}
                for row in active
            ):
                raise ValueError("EQUIVALENT result retains a blocking active cause")
            if receipt.outcome == Outcome.NOT_EQ and any(
                row.decision_effect in {"blocks_disequivalence", "blocks_decision"}
                for row in active
            ):
                raise ValueError("NOT_EQ result retains a blocking active cause")
        active_keys = {
            (row.result_occurrence_id, row.occurrence_id, row.cause_id) for row in causes
        }
        if {item.key for item in coverage_inputs.active_occurrences} != active_keys:
            raise ValueError("materialization input key set differs from active relation")
        materialization = materialization_metrics(
            coverage_inputs.active_occurrences, requirements
        )
        required_coverage = materialization[
            "required_requirement_materialization_coverage"
        ]
        if required_coverage is not None and required_coverage != 1.0:
            raise ValueError("required requirement materialization coverage is below 1.0")
        affected_unknown: dict[str, set[str]] = defaultdict(set)
        affected_timeout: dict[str, set[str]] = defaultdict(set)
        semantic_groupings: dict[str, Counter] = {
            key: Counter()
            for key in ("reason", "cause", "domain", "decision_effect", "target_kind", "final_outcome")
        }
        for row, outcome in joined["c_active_by_outcome"]:
            if outcome == Outcome.UNKNOWN:
                affected_unknown[row.reason_id].add(row.result_occurrence_id)
            if outcome == Outcome.TIMEOUT:
                affected_timeout[row.reason_id].add(row.result_occurrence_id)
            for key, value in (
                ("reason", row.reason_id),
                ("cause", row.cause_id),
                ("domain", row.domain),
                ("decision_effect", row.decision_effect),
                ("target_kind", row.target_kind),
                ("final_outcome", outcome.value),
            ):
                semantic_groupings[key][value] += 1
        proof_groupings: dict[str, Counter] = {
            "proof_kind": Counter(), "cause": Counter(), "final_outcome": Counter()
        }
        for row, outcome in joined["q_open_by_outcome"]:
            proof_groupings["proof_kind"][row.proof_kind] += 1
            proof_groupings["cause"][row.cause_id] += 1
            proof_groupings["final_outcome"][outcome.value] += 1
        metrics = {
            "decision_counts": joined["decision_counts"],
            "final_unknown_results": joined["decision_counts"][Outcome.UNKNOWN.value],
            "final_timeout_results": joined["decision_counts"][Outcome.TIMEOUT.value],
            "active_blocker_occurrences": len(causes),
            "unique_active_causes": len({row.cause_id for row in causes}),
            "affected_unknown_results_by_reason": {
                reason: len(result_ids) for reason, result_ids in sorted(affected_unknown.items())
            },
            "affected_timeout_results_by_reason": {
                reason: len(result_ids) for reason, result_ids in sorted(affected_timeout.items())
            },
            "semantic_backlog": {
                key: dict(sorted(counts.items())) for key, counts in semantic_groupings.items()
            },
            "unique_open_requirements": len(
                {row.proof_requirement_id for row in requirements}
            ),
            "proof_backlog": {
                key: dict(sorted(counts.items())) for key, counts in proof_groupings.items()
            },
            "terminal_timeout_events": sum(terminal_timeout_event_counts.values()),
            "observed_nonterminal_timeout_events": sum(
                observed_nonterminal_timeout_event_counts.values()
            ),
            "v2_native_typed_cause_coverage": coverage_ratio(
                sum(row.cause_id is not None for row in eligibility),
                len(eligibility),
            ),
            "final_blocker_authority_coverage": coverage_ratio(
                unknown_timeout_with_authority, unknown_timeout_results
            ),
            **materialization,
        }
        if sum(metrics["decision_counts"].values()) != len(manifest.entries):
            raise ValueError("canonical decision-count conservation law failed")
        if metrics["terminal_timeout_events"] != metrics["final_timeout_results"]:
            raise ValueError("terminal timeout/final TIMEOUT conservation law failed")
        return CensusComputation(CensusStatus.VALID, True, metrics, ())
    except (TypeError, ValueError) as exc:
        return CensusComputation(CensusStatus.INVALID, False, None, (str(exc),))
