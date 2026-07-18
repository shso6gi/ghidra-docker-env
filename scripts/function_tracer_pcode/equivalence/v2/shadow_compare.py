"""Post-finalization legacy comparison and shadow census preview."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Optional, Sequence, Tuple

from .candidate import CandidateDecisionProjection
from .census_contract import (
    CensusComputation,
    CensusManifest,
    CoverageInputs,
    compute_canonical_census,
)
from .contracts import Outcome, VerifiedLifecycleProjection, canonical_value
from .stream import SealedEventStream


class ShadowComparisonKind(str, Enum):
    MATCH = "MATCH"
    SHADOW_EVIDENCE_INCOMPLETE = "SHADOW_EVIDENCE_INCOMPLETE"
    MISMATCH_DECISION_AUTHORITY = "MISMATCH_DECISION_AUTHORITY"
    MISMATCH_LIFECYCLE = "MISMATCH_LIFECYCLE"
    MISMATCH_EXECUTION_EVENT = "MISMATCH_EXECUTION_EVENT"
    MISMATCH_FALLBACK_POLICY = "MISMATCH_FALLBACK_POLICY"
    MISMATCH_LEGACY_AMBIGUITY = "MISMATCH_LEGACY_AMBIGUITY"


@dataclass(frozen=True)
class LegacyExpectedProjection:
    outcome: Outcome
    decisive_proof_receipt_digests: Tuple[str, ...]
    decisive_proof_artifact_digests: Tuple[str, ...]
    active_cause_ids: Tuple[str, ...]
    proof_backlog_keys: Tuple[Tuple[str, int, str], ...]
    terminal_execution_event_digests: Tuple[str, ...]
    retry_fallback_projection: Any
    cli_batch_projection: Any
    ambiguity: bool = False

    def __post_init__(self) -> None:
        object.__setattr__(self, "outcome", Outcome(self.outcome))
        object.__setattr__(self, "decisive_proof_receipt_digests", tuple(sorted(self.decisive_proof_receipt_digests)))
        object.__setattr__(self, "decisive_proof_artifact_digests", tuple(sorted(self.decisive_proof_artifact_digests)))
        object.__setattr__(self, "active_cause_ids", tuple(sorted(self.active_cause_ids)))
        object.__setattr__(self, "proof_backlog_keys", tuple(sorted(self.proof_backlog_keys)))
        object.__setattr__(self, "terminal_execution_event_digests", tuple(sorted(self.terminal_execution_event_digests)))
        object.__setattr__(self, "retry_fallback_projection", canonical_value(self.retry_fallback_projection))
        object.__setattr__(self, "cli_batch_projection", canonical_value(self.cli_batch_projection))
        if type(self.ambiguity) is not bool:
            raise TypeError("legacy ambiguity flag must be exact boolean")


def compare_shadow(
    legacy: Optional[LegacyExpectedProjection],
    candidate: Optional[CandidateDecisionProjection],
    *,
    evidence_incomplete: bool = False,
) -> ShadowComparisonKind:
    if evidence_incomplete or candidate is None:
        return ShadowComparisonKind.SHADOW_EVIDENCE_INCOMPLETE
    candidate.validate()
    if legacy is None or legacy.ambiguity:
        return ShadowComparisonKind.MISMATCH_LEGACY_AMBIGUITY
    if (
        legacy.outcome != candidate.decision_receipt.outcome
        or legacy.decisive_proof_receipt_digests
        != candidate.decisive_proof_receipt_digests
        or legacy.decisive_proof_artifact_digests
        != candidate.decisive_proof_artifact_digests
    ):
        return ShadowComparisonKind.MISMATCH_DECISION_AUTHORITY
    if (
        legacy.active_cause_ids != candidate.active_cause_ids
        or legacy.proof_backlog_keys != candidate.proof_backlog_keys
    ):
        return ShadowComparisonKind.MISMATCH_LIFECYCLE
    if legacy.terminal_execution_event_digests != candidate.terminal_execution_event_digests:
        return ShadowComparisonKind.MISMATCH_EXECUTION_EVENT
    if legacy.retry_fallback_projection != candidate.retry_fallback_projection:
        return ShadowComparisonKind.MISMATCH_FALLBACK_POLICY
    if legacy.cli_batch_projection != candidate.cli_batch_projection:
        return ShadowComparisonKind.MISMATCH_DECISION_AUTHORITY
    return ShadowComparisonKind.MATCH


def build_shadow_census_preview(
    manifest: CensusManifest,
    candidates: Sequence[CandidateDecisionProjection],
    projections: Sequence[VerifiedLifecycleProjection],
    event_streams: Sequence[SealedEventStream],
    *,
    coverage_inputs: CoverageInputs,
) -> CensusComputation:
    for candidate in candidates:
        candidate.validate()
    return compute_canonical_census(
        manifest,
        candidates,
        projections,
        event_streams,
        coverage_inputs=coverage_inputs,
    )
