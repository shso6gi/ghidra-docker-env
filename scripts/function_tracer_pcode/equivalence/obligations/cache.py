"""Process-local caches with proof/attempt separation."""

from __future__ import annotations

from dataclasses import dataclass, field
from collections import OrderedDict
from threading import RLock
from typing import Any, Dict, Generic, Iterable, Mapping, Optional, Tuple, TypeVar

from .model import AttemptKey, ProofArtifact
from .proof import (
    ArtifactApplicabilityRecord,
    ValidatedProofClosure,
    ViewPremiseRecord,
    validate_artifact_applicability,
    validate_proof_closure,
)

T = TypeVar("T")


@dataclass(frozen=True)
class AttemptCacheEntry(Generic[T]):
    outcome: T
    query_digest: str
    query_size: int
    elapsed_time: float
    artifact_validation_status: str = "not_applicable"
    retry_eligible: bool = False


class AttemptCache(Generic[T]):
    def __init__(self, max_entries: int = 4096) -> None:
        if max_entries <= 0:
            raise ValueError("AttemptCache max_entries must be positive")
        self.max_entries = int(max_entries)
        self._entries: "OrderedDict[Tuple[Any, ...], AttemptCacheEntry[T]]" = OrderedDict()
        self._lock = RLock()
        self.hits = 0
        self.misses = 0

    def get(self, key: AttemptKey) -> Optional[AttemptCacheEntry[T]]:
        with self._lock:
            value = self._entries.get(key.to_key())
            if value is None:
                self.misses += 1
            else:
                self.hits += 1
                self._entries.move_to_end(key.to_key())
            return value

    def put(self, key: AttemptKey, entry: AttemptCacheEntry[T]) -> None:
        with self._lock:
            frozen_key = key.to_key()
            self._entries[frozen_key] = entry
            self._entries.move_to_end(frozen_key)
            while len(self._entries) > self.max_entries:
                self._entries.popitem(last=False)

    def __len__(self) -> int:
        return len(self._entries)


@dataclass(frozen=True)
class ProofCacheEntry:
    artifact: ProofArtifact
    validation_record: ArtifactApplicabilityRecord


class ProofCache:
    """Stores only validated proof or counterexample artifacts."""

    def __init__(self) -> None:
        self._entries: Dict[Tuple[Any, ...], ProofCacheEntry] = {}

    @staticmethod
    def key(entry: ProofCacheEntry) -> Tuple[Any, ...]:
        artifact = entry.artifact
        record = entry.validation_record
        return (
            artifact.requirement_id.to_key(), artifact.premise_digest,
            artifact.producer_version, artifact.encoding_version,
            record.target_view_id, record.premise_digest,
        )

    def put(
        self,
        artifact: ProofArtifact,
        *,
        artifacts: Iterable[ProofArtifact],
        root_artifact_ids: Iterable[Tuple[object, ...]],
        view_records: Mapping[Tuple[object, ...], ViewPremiseRecord],
        target_view: ViewPremiseRecord,
        candidate_independent_premise_digest: str,
    ) -> ProofCacheEntry:
        """Validate provenance and applicability inside the cache trust boundary."""

        if not artifact.is_validated:
            raise ValueError("ProofCache accepts only validated artifacts")
        materialized_artifacts = tuple(artifacts)
        matching_artifacts = tuple(
            candidate
            for candidate in materialized_artifacts
            if candidate.artifact_id == artifact.artifact_id
        )
        if len(matching_artifacts) != 1:
            raise ValueError(
                "ProofCache requires exactly one validated artifact with the target id"
            )
        if matching_artifacts[0] is not artifact:
            raise ValueError(
                "ProofCache target must be the exact process-local artifact validated in the closure"
            )
        closure = validate_proof_closure(
            materialized_artifacts,
            tuple(root_artifact_ids),
            view_records,
        )
        if artifact.artifact_id not in closure.topological_order:
            raise ValueError("proof artifact is absent from validated closure")
        source_view = view_records.get(artifact.produced_from_view_id)
        if source_view is None:
            raise ValueError("proof artifact source view is unavailable")
        record = validate_artifact_applicability(
            artifact,
            source_view=source_view,
            target_view=target_view,
            candidate_independent_premise_digest=candidate_independent_premise_digest,
            validated_closure_id=closure.closure_id,
        )
        if record.status != "applicable" or not record.candidate_independent:
            raise ValueError("ProofCache requires candidate-independent applicability")
        entry = ProofCacheEntry(artifact, record)
        self._entries[self.key(entry)] = entry
        return entry

    def get(self, key: Tuple[Any, ...]) -> Optional[ProofCacheEntry]:
        return self._entries.get(key)


@dataclass(frozen=True)
class ValidatedUnaryArtifactEntry:
    artifact: ProofArtifact
    function_premise_digest: str
    function_snapshot_fingerprint: str
    outcome_seed_digest: str
    attempt_candidate_independent: bool
    pair_independent: bool
    closure_artifacts: Tuple[ProofArtifact, ...] = ()
    source_view_records: Mapping[Tuple[Any, ...], ViewPremiseRecord] = field(
        default_factory=dict, compare=False, hash=False
    )


class ValidatedUnaryArtifactCache:
    """Process-local cache for function-scoped, pair-independent proof artifacts."""

    def __init__(self, max_entries: int = 2048) -> None:
        if max_entries <= 0:
            raise ValueError("ValidatedUnaryArtifactCache max_entries must be positive")
        self.max_entries = int(max_entries)
        self._entries: "OrderedDict[Tuple[Any, ...], ValidatedUnaryArtifactEntry]" = OrderedDict()
        self._lock = RLock()

    @staticmethod
    def key(requirement_key: Tuple[Any, ...], function_premise_digest: str) -> Tuple[Any, ...]:
        return ("validated_unary_artifact_v1", requirement_key, function_premise_digest)

    def put(self, entry: ValidatedUnaryArtifactEntry) -> None:
        if not entry.artifact.is_validated:
            raise ValueError("unary cache accepts only validated artifacts")
        if not entry.attempt_candidate_independent:
            raise ValueError("unary artifact depends on an attempt/counterexample candidate")
        if not entry.pair_independent:
            raise ValueError("unary artifact depends on a pair peer or side label")
        key = self.key(entry.artifact.requirement_id.to_key(), entry.function_premise_digest)
        with self._lock:
            self._entries[key] = entry
            self._entries.move_to_end(key)
            while len(self._entries) > self.max_entries:
                self._entries.popitem(last=False)

    def get(
        self,
        requirement_key: Tuple[Any, ...],
        function_premise_digest: str,
        *,
        function_snapshot_fingerprint: str,
        outcome_seed_digest: str,
        producer_version: str,
        encoding_version: str,
    ) -> Optional[ValidatedUnaryArtifactEntry]:
        key = self.key(requirement_key, function_premise_digest)
        with self._lock:
            entry = self._entries.get(key)
            if entry is None:
                return None
            if (
                entry.function_snapshot_fingerprint != function_snapshot_fingerprint
                or entry.outcome_seed_digest != outcome_seed_digest
                or entry.artifact.producer_version != producer_version
                or entry.artifact.encoding_version != encoding_version
            ):
                return None
            self._entries.move_to_end(key)
            return entry
